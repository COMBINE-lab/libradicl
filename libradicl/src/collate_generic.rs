/*
 * Copyright (c) 2020-2026 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Generic, bounded-memory collation gather (see COMBINE-lab/libradicl#62).
//!
//! [`collate_bucket`] is the one record-type-agnostic bucket gather all
//! collation engines share. Given a temp bucket's records (already routed and
//! corrected by scatter) as a seekable stream, it groups them by collation key
//! and emits one per-cell [`crate::chunk`]-format chunk each, applying a per-chunk
//! [`ChunkCodec`]. It streams the bucket in two passes and holds only the output
//! (≈ one uncompressed bucket), never the whole input — so peak memory matches
//! the historical two-pass rather than an in-memory copy.
//!
//! It is generic over the record type through [`CollationScan`], whose one method
//! reads a record's collation key and on-disk length while advancing past it.
//! Fixed-layout records override it with a raw key-read + arithmetic skip
//! (optimal, no per-record parsing or `KnownSize`-free cost); any other record —
//! including variable-length or custom types from external consumers — gets a
//! parse-based scan via [`scan_by_parse`], with no `KnownSize` bound on the
//! engine.
//!
//! The caller records the emitted chunks' offsets in a [`ChunkIndexBuilder`]
//! (under its output-write lock, so offsets stay in file order).

use crate::codec::ChunkCodec;
use crate::rad_types::{RadIntId, RadType, TagRole, TagSection};
use crate::schema::U128Map;
use std::collections::hash_map::Entry;
use std::io::{Cursor, Read, Seek, SeekFrom};

/// One barcode level that contributes to a composite collation key: where its
/// bytes sit within a record (offset from the record start) and how wide it is.
#[derive(Clone, Debug)]
struct KeyPart {
    offset: usize,
    int: RadIntId,
    bits: u32,
}

/// Runtime description of how to read a record's collation key from its
/// read-level header — the tag-driven analogue of what the fast concrete records
/// bake in at compile time (see [`scan_fixed_bc_umi`] and the multi-barcode
/// composite in [`crate::record::MultiBarcodeReadRecordHeader`]).
///
/// Collatability is a property of a *layout*, not of a type: constructing a spec
/// from a read-level [`TagSection`] **fails** when no key field is identified, so
/// a non-collatable RAD is rejected at the collate entry point rather than deep in
/// the gather. Because [`CollationScan::scan`] for the generic record requires a
/// [`GenericCollateCtx`] (which embeds a spec), and the only way to obtain one is
/// this fallible constructor, the type system + the constructor together enforce
/// "you cannot gather a layout you have not proven collatable."
#[derive(Clone, Debug)]
pub struct CollationKeySpec {
    /// Key parts, outer→inner (e.g. `[sample, cell]`); a single-barcode key has one.
    parts: Vec<KeyPart>,
    /// Total bytes of the read-level header (`na` + all read-level tags), i.e. the
    /// offset of the first alignment within a record.
    read_header_bytes: usize,
}

impl CollationKeySpec {
    /// Build a spec from the read-level tag section, naming the barcode-level tags
    /// (outer→inner order, e.g. `["b0","b1"]` for sample+cell, or `["b"]` for a
    /// single barcode). Fails if a named tag is missing/non-integer, if a
    /// read-level tag is variable-width (so the header offset isn't fixed), if no
    /// key tags are named (not collatable), or if the composite exceeds 128 bits.
    pub fn from_read_tags(read_tags: &TagSection, key_tag_names: &[&str]) -> anyhow::Result<Self> {
        if key_tag_names.is_empty() {
            anyhow::bail!("no collation key tags specified: records are not collatable");
        }
        // offset of each read tag = 4 (na) + sum of preceding read-tag widths.
        let mut offsets: Vec<(String, usize, RadIntId)> = Vec::with_capacity(read_tags.tags.len());
        let mut off = std::mem::size_of::<u32>(); // past `na`
        for td in &read_tags.tags {
            let RadType::Int(int) = td.typeid else {
                anyhow::bail!(
                    "read-level tag `{}` is not a fixed-width integer; the generic collation key \
                     requires a fixed read header",
                    td.name
                );
            };
            offsets.push((td.name.clone(), off, int));
            off += int.bytes_for_type();
        }
        let read_header_bytes = off;

        let mut parts = Vec::with_capacity(key_tag_names.len());
        let mut total_bits = 0u32;
        for name in key_tag_names {
            let (_, offset, int) = offsets.iter().find(|(n, _, _)| n == name).ok_or_else(|| {
                anyhow::anyhow!("collation key tag `{name}` not found in read tags")
            })?;
            let bits = (int.bytes_for_type() * 8) as u32;
            total_bits += bits;
            parts.push(KeyPart {
                offset: *offset,
                int: *int,
                bits,
            });
        }
        if total_bits > 128 {
            anyhow::bail!(
                "composite collation key needs {total_bits} bits, exceeding the 128-bit key"
            );
        }
        Ok(Self {
            parts,
            read_header_bytes,
        })
    }

    /// Build a spec from the read-level tags' declared [`TagRole::Barcode`] roles
    /// (ordered by `level`, outer→inner), i.e. from the RAD describing itself
    /// rather than a caller naming the key tags. Returns `Ok(None)` when no read
    /// tag carries a `Barcode` role (an un-annotated / legacy layout) so the caller
    /// can fall back to the name-based bridge; otherwise defers to
    /// [`Self::from_read_tags`] for offset/width computation + validation.
    pub fn from_roles(read_tags: &TagSection) -> anyhow::Result<Option<Self>> {
        let mut barcodes: Vec<(u8, &str)> = read_tags
            .tags
            .iter()
            .filter_map(|t| match t.role {
                TagRole::Barcode { level, .. } => Some((level, t.name.as_str())),
                _ => None,
            })
            .collect();
        if barcodes.is_empty() {
            return Ok(None);
        }
        barcodes.sort_by_key(|(level, _)| *level);
        let names: Vec<&str> = barcodes.iter().map(|(_, n)| *n).collect();
        Ok(Some(Self::from_read_tags(read_tags, &names)?))
    }

    /// Extract the composite key from a record's read-level header bytes (at least
    /// [`Self::read_header_bytes`] long). Parts fold outer→inner: each shifts the
    /// accumulator by its bit width, so `[sample, cell]` yields
    /// `(sample << cell_bits) | cell` — matching the concrete multi-barcode rule.
    fn extract(&self, header: &[u8]) -> u128 {
        let mut key: u128 = 0;
        for p in &self.parts {
            let mut c = Cursor::new(&header[p.offset..]);
            let v = p.int.read_value_into_u128(&mut c);
            let mask = if p.bits >= 128 {
                u128::MAX
            } else {
                (1u128 << p.bits) - 1
            };
            key = (key << p.bits) | (v & mask);
        }
        key
    }
}

/// Collation context for the generic, tag-driven record: a validated key spec plus
/// the fixed per-alignment stride. Obtainable only via [`Self::new`], which is
/// where a layout's collatability is decided.
#[derive(Clone, Debug)]
pub struct GenericCollateCtx {
    key: CollationKeySpec,
    aln_stride: usize,
}

impl GenericCollateCtx {
    /// Build the collation context from the read/alignment tag sections and the
    /// barcode-level key tag names. Fails if the key spec can't be built (see
    /// [`CollationKeySpec::from_read_tags`]) or if any alignment tag is
    /// variable-width (the fixed-stride gather can't skip it; such layouts need a
    /// parse-based scan instead).
    pub fn new(
        read_tags: &TagSection,
        aln_tags: &TagSection,
        key_tag_names: &[&str],
    ) -> anyhow::Result<Self> {
        let key = CollationKeySpec::from_read_tags(read_tags, key_tag_names)?;
        Ok(Self {
            key,
            aln_stride: Self::aln_stride(aln_tags)?,
        })
    }

    /// Like [`Self::new`] but takes the collation key from the read tags' declared
    /// [`TagRole::Barcode`] roles (see [`CollationKeySpec::from_roles`]). Returns
    /// `Ok(None)` when the layout declares no barcode role, so the caller can fall
    /// back to the name-based bridge.
    pub fn from_roles(
        read_tags: &TagSection,
        aln_tags: &TagSection,
    ) -> anyhow::Result<Option<Self>> {
        match CollationKeySpec::from_roles(read_tags)? {
            Some(key) => Ok(Some(Self {
                key,
                aln_stride: Self::aln_stride(aln_tags)?,
            })),
            None => Ok(None),
        }
    }

    /// Fixed per-alignment stride = sum of the alignment tag widths; errors if any
    /// alignment tag is variable-width (the fixed-stride gather can't skip it).
    fn aln_stride(aln_tags: &TagSection) -> anyhow::Result<usize> {
        let mut stride = 0usize;
        for td in &aln_tags.tags {
            let RadType::Int(int) = td.typeid else {
                anyhow::bail!(
                    "alignment tag `{}` is not fixed-width; the fixed-stride generic gather \
                     cannot skip it",
                    td.name
                );
            };
            stride += int.bytes_for_type();
        }
        Ok(stride)
    }
}

impl CollationScan for crate::record::GenericReadRecord {
    type Ctx = GenericCollateCtx;
    fn scan<R: Read + Seek>(r: &mut R, ctx: &GenericCollateCtx) -> anyhow::Result<(u128, usize)> {
        // Read the fixed read-level header (na + read tags), extract the key, then
        // skip the fixed-stride alignment block.
        let hb = ctx.key.read_header_bytes;
        let mut header = vec![0u8; hb];
        r.read_exact(&mut header)?;
        let na = u32::from_le_bytes(header[0..4].try_into().unwrap()) as usize;
        let key = ctx.key.extract(&header);
        let skip = na * ctx.aln_stride;
        r.seek_relative(skip as i64)?;
        Ok((key, hb + skip))
    }
}

/// A record type the collation gather can group. Implementors read exactly one
/// on-disk record from `r` (positioned at its start), advance `r` to the next
/// record, and return the record's collation key and its on-disk byte length.
///
/// The length lets the gather relocate the record's raw bytes without
/// re-serializing. Fixed-layout records should implement `scan` as a raw key-read
/// plus an arithmetic `seek` over the alignment block (see [`scan_fixed_bc_umi`]);
/// records that can't (variable-length, or any [`CollatableMappedRecord`] a
/// consumer would rather not hand-optimize) can defer to [`scan_by_parse`].
pub trait CollationScan {
    /// Parsing context (RAD tags etc.); `()` when none is needed.
    type Ctx;

    /// Read the next record's collation key and advance past it; return
    /// `(key, on_disk_len_bytes)`.
    fn scan<R: Read + Seek>(r: &mut R, ctx: &Self::Ctx) -> anyhow::Result<(u128, usize)>;

    /// If this record has a fixed on-disk layout, return `(read_header_bytes,
    /// aln_stride)` — the byte length of the fixed header (`na` + read-level
    /// fields, up to the first alignment) and the fixed per-alignment stride. This
    /// lets the gather's pass 2 relocate a record forward with no backward seek
    /// (read the header, derive the key + length, read the alignment block straight
    /// into the output). `None` (the default) ⇒ variable layout; pass 2 falls back
    /// to `scan` + seek-back. When `Some`, [`Self::key_from_header`] must extract
    /// the key from the header bytes.
    ///
    /// This is the opt-in that decides whether a record type uses the pass-1
    /// `(cell index)` side table (fast pass 2, small per-bucket memory) or the
    /// re-scan fallback (no side table). It is worth overriding only when
    /// recomputing the key in pass 2 is expensive relative to a plain read — i.e.
    /// composite/multi-field keys over many small records (multi-barcode). For
    /// cheap single-field keys (the alevin-fry / long-read family) the re-scan is
    /// effectively free, so they leave this `None` and pay no side-table memory.
    /// The choice is per record *type* (key cost), not per file *size*: a
    /// size-based switch would be backwards, since it is precisely the large
    /// many-record case where the re-scan of an expensive key costs the most. If a
    /// future cheap-key record ever has enormous record counts where even the
    /// cheap re-scan adds up, overriding this is the (size-heuristic-free) lever.
    fn fixed_header_stride(_ctx: &Self::Ctx) -> Option<(usize, usize)> {
        None
    }

    /// Extract the collation key from a record's header bytes (`hdr` is at least
    /// `read_header_bytes` long). Only called when [`Self::fixed_header_stride`]
    /// returns `Some`; the default panics to catch a missing override.
    fn key_from_header(_hdr: &[u8], _ctx: &Self::Ctx) -> u128 {
        unreachable!("key_from_header called without a fixed_header_stride override")
    }
}

/// Parse-based [`CollationScan::scan`] for any [`CollatableMappedRecord`]: parse
/// one record (advancing `r`) and measure its length from the stream position.
/// Works for fixed- and variable-length records alike; needs no `KnownSize`.
pub fn scan_by_parse<T, B, R>(r: &mut R, ctx: &T::ParsingContext) -> anyhow::Result<(u128, usize)>
where
    B: crate::record::ConvertiblePrimitiveInteger,
    u128: From<B>,
    T: crate::record::CollatableMappedRecord<B>,
    R: Read + Seek,
{
    use crate::record::MappedRecord;
    let start = r.stream_position()?;
    let rec = <T as MappedRecord>::from_bytes_with_context(r, ctx);
    let len = (r.stream_position()? - start) as usize;
    Ok((u128::from(rec.collate_key()), len))
}

/// Read up to 8 little-endian bytes from `b` as a `u64` (a fixed-width barcode
/// field lifted out of an already-read header buffer, no reader round-trip).
#[inline]
fn le_u64(b: &[u8]) -> u64 {
    let mut v = 0u64;
    for (i, &x) in b.iter().enumerate().take(8) {
        v |= (x as u64) << (8 * i);
    }
    v
}

/// Fast [`CollationScan::scan`] for records with a fixed `[na:u32][bc][umi]`
/// header followed by `na` fixed-`stride` alignments (the alevin-fry
/// single-barcode family). Reads `na` and the barcode (the key), then seeks over
/// the umi and alignment block — no per-alignment parsing. `bct`/`umit` are the
/// barcode/umi integer widths and `stride` is the per-alignment byte size
/// (`KnownSize::nbytes_aln`).
pub fn scan_fixed_bc_umi<R: Read + Seek>(
    r: &mut R,
    bct: crate::rad_types::RadIntId,
    umit: crate::rad_types::RadIntId,
    stride: usize,
) -> anyhow::Result<(u128, usize)> {
    let mut na_buf = [0u8; 4];
    r.read_exact(&mut na_buf)?;
    let na = u32::from_le_bytes(na_buf) as usize;
    let key = bct.read_value_into_u128(r);
    let skip = umit.bytes_for_type() + na * stride;
    r.seek_relative(skip as i64)?;
    let len = 4 + bct.bytes_for_type() + skip;
    Ok((key, len))
}

// --- `CollationScan` for the built-in single-barcode-family records (fast) ---
macro_rules! fixed_bc_umi_scan {
    ($rec:ident) => {
        impl<B> CollationScan for crate::record::$rec<B>
        where
            B: crate::record::ConvertiblePrimitiveInteger,
            crate::record::$rec<B>: crate::record::MappedRecord<
                    ParsingContext = crate::record::AlevinFryRecordContext,
                > + crate::record::KnownSize,
        {
            type Ctx = crate::record::AlevinFryRecordContext;
            fn scan<R: Read + Seek>(
                r: &mut R,
                ctx: &crate::record::AlevinFryRecordContext,
            ) -> anyhow::Result<(u128, usize)> {
                let stride = <crate::record::$rec<B> as crate::record::KnownSize>::nbytes_aln(ctx);
                scan_fixed_bc_umi(r, ctx.bct, ctx.umit, stride)
            }
        }
    };
}
fixed_bc_umi_scan!(AlevinFryReadRecordT);
fixed_bc_umi_scan!(AlevinFryReadRecordWithPositionT);

// ScLong shares the `[na][bc][umi]` header + fixed per-alignment stride, but a
// distinct context type.
impl<B> CollationScan for crate::record::ScLongReadRecordT<B>
where
    B: crate::record::ConvertiblePrimitiveInteger,
    crate::record::ScLongReadRecordT<B>: crate::record::MappedRecord<ParsingContext = crate::record::ScLongReadRecordContext>
        + crate::record::KnownSize,
{
    type Ctx = crate::record::ScLongReadRecordContext;
    fn scan<R: Read + Seek>(
        r: &mut R,
        ctx: &crate::record::ScLongReadRecordContext,
    ) -> anyhow::Result<(u128, usize)> {
        let stride =
            <crate::record::ScLongReadRecordT<B> as crate::record::KnownSize>::nbytes_aln(ctx);
        scan_fixed_bc_umi(r, ctx.bct, ctx.umit, stride)
    }
}

/// `CollationScan` for the multi-barcode (Flex) record. Unlike the single-barcode
/// family, the collation key is the composite *group* key (sample + cell), not the
/// innermost barcode alone — so `scan_by_parse` (which keys on `collate_key`)
/// would wrongly merge samples. This reads the barcode fields directly and forms
/// the composite exactly as
/// [`MultiBarcodeReadRecordHeader::collation_group_key`](crate::record::CollatableRecordHeader::collation_group_key)
/// (first barcode = sample, last = cell), for any barcode/umi widths — covering
/// both the fast `u32`/`u32` layout and every other in one arithmetic path.
/// Compose the multi-barcode group key from a record's header bytes (`hdr[0..4]`
/// is `na`, barcodes follow at offset 4). Mirrors
/// [`MultiBarcodeReadRecordHeader::collation_group_key`]: single barcode ⇒ that
/// barcode; otherwise the first (sample) shifted above the last (cell) field.
fn multi_key_from_header(hdr: &[u8], ctx: &crate::record::MultiBarcodeRecordContext) -> u64 {
    let nbc = ctx.bc_types.len();
    let mut first: u64 = 0;
    let mut last: u64 = 0;
    let mut off = 4usize;
    for (i, bct) in ctx.bc_types.iter().enumerate() {
        let w = bct.bytes_for_type();
        let v = le_u64(&hdr[off..off + w]);
        if i == 0 {
            first = v;
        }
        if i + 1 == nbc {
            last = v;
        }
        off += w;
    }
    if nbc < 2 {
        last
    } else {
        let cell_bits = (ctx
            .bc_types
            .last()
            .expect("multi-barcode context has ≥1 barcode")
            .bytes_for_type()
            * 8) as u32;
        if cell_bits >= 64 {
            last
        } else {
            (first << cell_bits) | (last & ((1u64 << cell_bits) - 1))
        }
    }
}

impl<B> CollationScan for crate::record::MultiBarcodeReadRecordT<B>
where
    B: crate::record::ConvertiblePrimitiveInteger,
    crate::record::MultiBarcodeReadRecordT<B>: crate::record::MappedRecord<ParsingContext = crate::record::MultiBarcodeRecordContext>
        + crate::record::KnownSize,
{
    type Ctx = crate::record::MultiBarcodeRecordContext;
    fn scan<R: Read + Seek>(
        r: &mut R,
        ctx: &crate::record::MultiBarcodeRecordContext,
    ) -> anyhow::Result<(u128, usize)> {
        // Read `na` + the whole barcode block in one `read_exact` (read headers are
        // small), extract the composite key by offset (no reader round-trip per
        // barcode), then skip the umi + fixed-stride alignment block.
        let hdr = 4 + ctx.total_bc_bytes();
        let mut buf = [0u8; 64];
        if hdr > buf.len() {
            anyhow::bail!("multi-barcode read header ({hdr} bytes) exceeds the scan buffer");
        }
        r.read_exact(&mut buf[..hdr])?;
        let na = u32::from_le_bytes(buf[0..4].try_into().unwrap()) as usize;
        let key = multi_key_from_header(&buf, ctx);

        let (_hdr, stride) = Self::fixed_header_stride(ctx).expect("multi has a fixed layout");
        let skip = ctx.umit.bytes_for_type() + na * stride;
        r.seek_relative(skip as i64)?;
        Ok((u128::from(key), hdr + skip))
    }

    fn fixed_header_stride(ctx: &Self::Ctx) -> Option<(usize, usize)> {
        let hdr = 4 + ctx.total_bc_bytes() + ctx.umit.bytes_for_type();
        let stride =
            <crate::record::MultiBarcodeReadRecordT<B> as crate::record::KnownSize>::nbytes_aln(
                ctx,
            );
        Some((hdr, stride))
    }

    fn key_from_header(hdr: &[u8], ctx: &Self::Ctx) -> u128 {
        u128::from(multi_key_from_header(hdr, ctx))
    }
}

/// `CollationScan` for the scATAC record. Layout is `[na][bc][aln × na]` with a
/// fixed per-alignment stride (see [`AtacSeqReadRecord::nbytes_aln`]) and **no
/// UMI**; the collation key is the barcode. Fully fixed, so pass 2 relocates
/// records forward with no re-scan (`fixed_header_stride`/`key_from_header`).
impl CollationScan for crate::record::AtacSeqReadRecord {
    type Ctx = crate::record::AtacSeqRecordContext;
    fn scan<R: Read + Seek>(r: &mut R, ctx: &Self::Ctx) -> anyhow::Result<(u128, usize)> {
        let mut na_buf = [0u8; 4];
        r.read_exact(&mut na_buf)?;
        let na = u32::from_le_bytes(na_buf) as usize;
        let key = ctx.bct.read_value_into_u128(r);
        let stride =
            <crate::record::AtacSeqReadRecord as crate::record::KnownSize>::nbytes_aln(ctx);
        let skip = na * stride;
        r.seek_relative(skip as i64)?;
        let len = 4 + ctx.bct.bytes_for_type() + skip;
        Ok((key, len))
    }

    fn fixed_header_stride(ctx: &Self::Ctx) -> Option<(usize, usize)> {
        let hdr = 4 + ctx.bct.bytes_for_type();
        let stride =
            <crate::record::AtacSeqReadRecord as crate::record::KnownSize>::nbytes_aln(ctx);
        Some((hdr, stride))
    }

    fn key_from_header(hdr: &[u8], ctx: &Self::Ctx) -> u128 {
        // hdr = [na:u32][bc:bct]; the barcode begins at offset 4.
        u128::from(le_u64(&hdr[4..4 + ctx.bct.bytes_for_type()]))
    }
}

/// Collate one temp bucket: group its `num_records` records (a seekable stream
/// positioned at the bucket start) by [`CollationScan`] key and append one
/// per-cell chunk per key to `out` — each `[nbytes:u32][nrec:u32][payload]`,
/// `payload` `codec`-compressed (verbatim for [`ChunkCodec::None`]). Keys are
/// emitted in first-seen order (deterministic). Returns the number of chunks
/// written.
///
/// Two-pass and bounded-memory: pass one scans each record for `(key, len)`
/// (fixed records seek past alignments; others parse), sizes the per-cell chunks,
/// and records each record's `(cell_index, len)`; pass two rewinds and relocates
/// each record's raw bytes into its cell's slot with one sequential read (no
/// re-scan, no per-record hashing). Peak memory is the output buffer (≈ one
/// uncompressed bucket) plus an 8-byte/record side table — never a copy of the
/// whole input.
///
/// The caller records the appended region's offsets via
/// [`ChunkIndexBuilder::record_bucket`](crate::codec::ChunkIndexBuilder::record_bucket).
pub fn collate_bucket<S, R>(
    reader: &mut R,
    num_records: usize,
    ctx: &S::Ctx,
    codec: ChunkCodec,
    out: &mut Vec<u8>,
) -> anyhow::Result<usize>
where
    S: CollationScan,
    R: Read + Seek,
{
    const CHUNK_HEADER: usize = 8; // [nbytes: u32][nrec: u32]
    let base = reader.stream_position()?;

    // Pass 1: determine each record's `(key, len)` and size the per-cell chunks
    // (first-seen order). `index` maps a key to its cell; nothing is stored per
    // record — pass 2 relocates records with a single forward pass (see
    // [`fill_bucket`]), so peak memory stays at ~one bucket with no O(records)
    // side table. For fixed-layout records the layout constants are hoisted out of
    // the per-record loop (they'd otherwise be re-summed from the tag sections on
    // every one of potentially 10^8 records).
    let mut cells: Vec<CellSize> = Vec::new();
    let mut index: U128Map<u32> = U128Map::default();
    // For fixed-layout records we record each record's cell index (4 bytes) so
    // pass 2 relocates it without recomputing/rehashing the key: it reads `na`,
    // derives the length arithmetically, and routes by the stored index. For
    // variable records nothing is stored (pass 2 falls back to scan + seek-back).
    //
    // Invariant: the stored value is a *cell* index, not a record counter, and it
    // fits `u32`. A bucket holds at most `u32::MAX` records (every caller passes a
    // `u32` `num_records`; buckets are memory-bounded fractions, far below that),
    // so its distinct-cell count is also `<= u32::MAX` — enforced by the
    // `u32::try_from(cells.len())` check in `accumulate_cell`, which errors rather
    // than wrapping if that ever failed to hold.
    let fixed = S::fixed_header_stride(ctx);
    let mut recs: Vec<u32> = Vec::new();
    if let Some((hdr_bytes, stride)) = fixed {
        recs.reserve(num_records);
        let mut scratch = vec![0u8; hdr_bytes];
        for i in 0..num_records {
            reader.read_exact(&mut scratch)?;
            let na = u32::from_le_bytes(scratch[0..4].try_into().unwrap()) as usize;
            let key = S::key_from_header(&scratch, ctx);
            let len = hdr_bytes + na * stride;
            reader.seek_relative((len - hdr_bytes) as i64)?;
            let len =
                u32::try_from(len).map_err(|_| anyhow::anyhow!("record {i} exceeds u32 bytes"))?;
            recs.push(accumulate_cell(&mut cells, &mut index, key, len)?);
        }
    } else {
        for i in 0..num_records {
            let (key, len) = S::scan(reader, ctx)?;
            let len =
                u32::try_from(len).map_err(|_| anyhow::anyhow!("record {i} exceeds u32 bytes"))?;
            accumulate_cell(&mut cells, &mut index, key, len)?;
        }
    }

    // Lay out the uncompressed chunks (one per cell, first-seen order): compute
    // each cell's chunk offset and its running payload write cursor.
    let mut total = 0usize;
    let mut cursor: Vec<usize> = Vec::with_capacity(cells.len());
    for c in &cells {
        cursor.push(total + CHUNK_HEADER);
        total += CHUNK_HEADER + c.payload_bytes;
    }

    // Assemble the uncompressed bucket (chunk headers + pass-2 record relocation).
    // With no codec, build straight into `out` (no second full-bucket buffer);
    // otherwise stage in `tmp` and compress chunk-by-chunk into `out`. Either way
    // peak memory is ~one bucket.
    if codec == ChunkCodec::None {
        let out_start = out.len();
        out.resize(out_start + total, 0);
        fill_bucket::<S, R>(
            reader,
            base,
            num_records,
            ctx,
            fixed,
            &recs,
            &cells,
            &index,
            &mut cursor,
            &mut out[out_start..],
        )?;
    } else {
        let mut tmp = vec![0u8; total];
        fill_bucket::<S, R>(
            reader,
            base,
            num_records,
            ctx,
            fixed,
            &recs,
            &cells,
            &index,
            &mut cursor,
            &mut tmp,
        )?;
        // Reserve the compressed output up front (compressed ≤ uncompressed), so
        // appending never triggers a doubling realloc that transiently holds two
        // copies of the growing buffer (a large-bucket RSS spike). Matches the
        // historical `Vec::with_capacity(uncompressed.len())`.
        out.reserve(total);
        // Compress chunk-by-chunk straight into `out` (only a small per-chunk
        // scratch is held), rather than into a second full-bucket buffer.
        crate::codec::recompress_bucket_per_chunk_into(&tmp, codec, out)?;
    }
    Ok(cells.len())
}

/// Write the per-cell chunk headers into `dst`, then (pass two) rewind `reader` to
/// `base` and relocate each record's raw bytes into its cell's slot. `cursor[ci]`
/// starts at cell `ci`'s payload offset and advances as records land. No
/// per-record side table: routing keys come from a re-read of the header.
///
/// Two pass-2 strategies, both forward-only where it matters:
/// - **fixed layout** (record implements [`CollationScan::fixed_header_stride`]):
///   read the fixed header into a small reusable scratch, derive the key + length,
///   copy the header into the slot, and read the alignment block *straight into the
///   slot* — a single forward pass with no backward seek (matches the historical
///   engine; the win for records with many small entries, e.g. multi-barcode).
/// - **fallback**: `scan` the record (which may skip alignments via `seek`), then
///   seek back and read it into the slot. Correct for any record, including
///   variable-length ones, at the cost of re-reading the record's bytes.
#[allow(clippy::too_many_arguments)]
fn fill_bucket<S, R>(
    reader: &mut R,
    base: u64,
    num_records: usize,
    ctx: &S::Ctx,
    fixed: Option<(usize, usize)>,
    recs: &[u32],
    cells: &[CellSize],
    index: &U128Map<u32>,
    cursor: &mut [usize],
    dst: &mut [u8],
) -> anyhow::Result<()>
where
    S: CollationScan,
    R: Read + Seek,
{
    const CHUNK_HEADER: usize = 8;
    let mut off = 0usize;
    for c in cells {
        let nbytes = (CHUNK_HEADER + c.payload_bytes) as u32;
        dst[off..off + 4].copy_from_slice(&nbytes.to_le_bytes());
        dst[off + 4..off + 8].copy_from_slice(&c.nrec.to_le_bytes());
        off += CHUNK_HEADER + c.payload_bytes;
    }

    reader.seek(SeekFrom::Start(base))?;
    if let Some((hdr_bytes, stride)) = fixed {
        // Fixed-layout fast path: route by the pass-1 cell index (no key recompute,
        // no hashing), read each record forward straight into its slot. Length is
        // `hdr_bytes + na * stride`, with `na` read as the record's first field.
        for &ci in recs {
            let w = &mut cursor[ci as usize];
            reader.read_exact(&mut dst[*w..*w + 4])?;
            let na = u32::from_le_bytes(dst[*w..*w + 4].try_into().unwrap()) as usize;
            let len = hdr_bytes + na * stride;
            reader.read_exact(&mut dst[*w + 4..*w + len])?;
            *w += len;
        }
    } else {
        // Fallback for variable-layout records: scan (possibly seeking past
        // alignments), seek back, and read the record into its cell's slot.
        for _ in 0..num_records {
            let (key, len) = S::scan(reader, ctx)?;
            reader.seek_relative(-(len as i64))?;
            let ci = *index.get(&key).expect("cell present from pass 1") as usize;
            let w = &mut cursor[ci];
            reader.read_exact(&mut dst[*w..*w + len])?;
            *w += len;
        }
    }
    Ok(())
}

struct CellSize {
    payload_bytes: usize,
    nrec: u32,
}

/// Record one record of `len` bytes against its cell (keyed by `key`, first-seen
/// order): grow the cell's payload/nrec, creating the cell on first sight. Returns
/// the record's cell index.
///
/// The returned index is what pass 2's `recs` table stores; the
/// `u32::try_from(cells.len())` below is the sole guard that keeps it in `u32`
/// range (it errors, never wraps). A bucket cannot legitimately reach this limit
/// — record counts per bucket are `u32` and memory-bounded — but the check makes
/// the invariant total rather than assumed.
#[inline]
fn accumulate_cell(
    cells: &mut Vec<CellSize>,
    index: &mut U128Map<u32>,
    key: u128,
    len: u32,
) -> anyhow::Result<u32> {
    let ci = match index.entry(key) {
        Entry::Vacant(e) => {
            let ci = u32::try_from(cells.len())
                .map_err(|_| anyhow::anyhow!("bucket exceeds u32 cells"))?;
            cells.push(CellSize {
                payload_bytes: len as usize,
                nrec: 1,
            });
            e.insert(ci);
            ci
        }
        Entry::Occupied(e) => {
            let ci = *e.get();
            let c = &mut cells[ci as usize];
            c.payload_bytes += len as usize;
            c.nrec += 1;
            ci
        }
    };
    Ok(ci)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codec::{ChunkIndexBuilder, decompress_payload};
    use std::io::Cursor;

    // --- Two custom record types implementing only `CollationScan` (standing in
    // for an external consumer's record): one fixed-stride, one variable-length. ---

    /// Fixed-stride: `[na:u32][bc:u32][umi:u32][na × u32]`.
    struct FixedRec;
    impl CollationScan for FixedRec {
        type Ctx = ();
        fn scan<R: Read + Seek>(r: &mut R, _ctx: &()) -> anyhow::Result<(u128, usize)> {
            let mut b = [0u8; 4];
            r.read_exact(&mut b)?;
            let na = u32::from_le_bytes(b) as usize;
            r.read_exact(&mut b)?;
            let bc = u32::from_le_bytes(b) as u128;
            let skip = 4 + na * 4; // umi + alignments
            r.seek_relative(skip as i64)?;
            Ok((bc, 8 + skip))
        }
    }

    /// Variable-length: `[na:u32][bc:u32]` then `na` × `[len:u16][len bytes]`
    /// (data-dependent per-alignment size; cannot implement `KnownSize`).
    struct VarRec;
    impl CollationScan for VarRec {
        type Ctx = ();
        fn scan<R: Read + Seek>(r: &mut R, _ctx: &()) -> anyhow::Result<(u128, usize)> {
            let mut b4 = [0u8; 4];
            r.read_exact(&mut b4)?;
            let na = u32::from_le_bytes(b4) as usize;
            r.read_exact(&mut b4)?;
            let bc = u32::from_le_bytes(b4) as u128;
            let mut len = 8usize;
            let mut b2 = [0u8; 2];
            for _ in 0..na {
                r.read_exact(&mut b2)?;
                let l = u16::from_le_bytes(b2) as usize;
                r.seek_relative(l as i64)?;
                len += 2 + l;
            }
            Ok((bc, len))
        }
    }

    fn fixed_rec_bytes(bc: u32, umi: u32, alns: &[u32]) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(&(alns.len() as u32).to_le_bytes());
        v.extend_from_slice(&bc.to_le_bytes());
        v.extend_from_slice(&umi.to_le_bytes());
        for &a in alns {
            v.extend_from_slice(&a.to_le_bytes());
        }
        v
    }

    fn var_rec_bytes(bc: u32, alns: &[&[u8]]) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(&(alns.len() as u32).to_le_bytes());
        v.extend_from_slice(&bc.to_le_bytes());
        for a in alns {
            v.extend_from_slice(&(a.len() as u16).to_le_bytes());
            v.extend_from_slice(a);
        }
        v
    }

    /// Walk the collated `out`; decompress each chunk and re-scan its records,
    /// asserting one barcode per chunk. Returns `(bc, nrec)` per chunk + total.
    fn read_back<S: CollationScan>(
        out: &[u8],
        codec: ChunkCodec,
        ctx: &S::Ctx,
    ) -> (Vec<(u128, u32)>, usize) {
        let mut chunks = Vec::new();
        let mut total = 0usize;
        let mut pos = 0usize;
        while pos < out.len() {
            let nbytes = u32::from_le_bytes(out[pos..pos + 4].try_into().unwrap()) as usize;
            let nrec = u32::from_le_bytes(out[pos + 4..pos + 8].try_into().unwrap());
            let payload = decompress_payload(codec, &out[pos + 8..pos + nbytes]).unwrap();
            let mut cur = Cursor::new(payload.as_slice());
            let mut bc = None;
            for _ in 0..nrec {
                let (k, _len) = S::scan(&mut cur, ctx).unwrap();
                assert!(bc.is_none_or(|c| c == k), "chunk mixed barcodes");
                bc = Some(k);
                total += 1;
            }
            assert_eq!(
                cur.position() as usize,
                payload.len(),
                "trailing bytes in chunk"
            );
            chunks.push((bc.unwrap(), nrec));
            pos += nbytes;
        }
        assert_eq!(pos, out.len());
        (chunks, total)
    }

    fn run_case<S: CollationScan<Ctx = ()>>(input: Vec<u8>, num_records: usize) {
        for codec in [ChunkCodec::None, ChunkCodec::Lz4] {
            let mut out = Vec::new();
            let mut cur = Cursor::new(input.as_slice());
            let n_chunks =
                collate_bucket::<S, _>(&mut cur, num_records, &(), codec, &mut out).unwrap();

            let (chunks, total) = read_back::<S>(&out, codec, &());
            assert_eq!(total, num_records);
            assert_eq!(chunks.len(), n_chunks);
            let unique = {
                let mut b: Vec<u128> = chunks.iter().map(|c| c.0).collect();
                b.sort_unstable();
                b.dedup();
                b.len()
            };
            assert_eq!(unique, chunks.len(), "each barcode in exactly one chunk");

            let mut index = ChunkIndexBuilder::default();
            index.record_bucket(&out);
            let offsets = index.into_offsets();
            assert_eq!(offsets.len(), n_chunks + 1);
            assert_eq!(*offsets.last().unwrap(), out.len() as u64);
            for w in offsets.windows(2) {
                assert!(w[1] > w[0]);
                let nb =
                    u32::from_le_bytes(out[w[0] as usize..w[0] as usize + 4].try_into().unwrap())
                        as u64;
                assert_eq!(w[0] + nb, w[1], "offset lands on a chunk boundary");
            }
        }
    }

    #[test]
    fn fixed_record_collates_and_groups() {
        let recs = [
            fixed_rec_bytes(7, 100, &[1, 2, 3]),
            fixed_rec_bytes(3, 101, &[4]),
            fixed_rec_bytes(7, 102, &[5, 6]),
            fixed_rec_bytes(3, 103, &[]),
            fixed_rec_bytes(9, 104, &[7, 8, 9, 10]),
        ];
        let n = recs.len();
        run_case::<FixedRec>(recs.concat(), n);
    }

    #[test]
    fn variable_length_record_collates_and_groups() {
        let recs = [
            var_rec_bytes(42, &[b"MMMM", b"II"]),
            var_rec_bytes(5, &[b"S"]),
            var_rec_bytes(42, &[b"MMMMMMMMMM"]),
            var_rec_bytes(5, &[b"", b"DDDD", b"MMM"]),
            var_rec_bytes(42, &[]),
        ];
        let n = recs.len();
        run_case::<VarRec>(recs.concat(), n);
    }

    #[test]
    fn single_barcode_single_chunk() {
        let recs = [fixed_rec_bytes(1, 0, &[1]), fixed_rec_bytes(1, 1, &[2, 3])];
        run_case::<FixedRec>(recs.concat(), 2);
    }

    /// On-disk `AlevinFryReadRecordT<u64>`: `[na:u32][bc:u64][umi:u64][na×u32]`.
    fn af_u64(bc: u64, umi: u64, refs: &[u32]) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(&(refs.len() as u32).to_le_bytes());
        v.extend_from_slice(&bc.to_le_bytes());
        v.extend_from_slice(&umi.to_le_bytes());
        for &r in refs {
            v.extend_from_slice(&r.to_le_bytes());
        }
        v
    }

    // --- generic, tag-driven record collation (CollationKeySpec) ---

    use crate::rad_types::{RadType, TagDesc, TagSection, TagSectionLabel};

    fn tag_section(label: TagSectionLabel, tags: &[(&str, RadIntId)]) -> TagSection {
        TagSection {
            label,
            tags: tags
                .iter()
                .map(|(n, i)| TagDesc {
                    role: crate::rad_types::TagRole::None,
                    name: (*n).to_string(),
                    typeid: RadType::Int(*i),
                })
                .collect(),
        }
    }

    /// On-disk generic record: `na(u32)`, read tags `b0,b1,u` (u32 each), then
    /// `na ×` aln tags `refid,as` (u32 each).
    fn gen_rec(b0: u32, b1: u32, umi: u32, alns: &[(u32, u32)]) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(&(alns.len() as u32).to_le_bytes());
        v.extend_from_slice(&b0.to_le_bytes());
        v.extend_from_slice(&b1.to_le_bytes());
        v.extend_from_slice(&umi.to_le_bytes());
        for &(r, a) in alns {
            v.extend_from_slice(&r.to_le_bytes());
            v.extend_from_slice(&a.to_le_bytes());
        }
        v
    }

    #[test]
    fn generic_record_composite_key_collates() {
        use crate::record::GenericReadRecord;
        let read_tags = tag_section(
            TagSectionLabel::ReadTags,
            &[
                ("b0", RadIntId::U32),
                ("b1", RadIntId::U32),
                ("u", RadIntId::U32),
            ],
        );
        let aln_tags = tag_section(
            TagSectionLabel::AlignmentTags,
            &[("refid", RadIntId::U32), ("as", RadIntId::U32)],
        );
        // key = composite (sample=b0, cell=b1): (b0 << 32) | b1
        let ctx = GenericCollateCtx::new(&read_tags, &aln_tags, &["b0", "b1"]).unwrap();
        assert_eq!(ctx.aln_stride, 8);
        assert_eq!(ctx.key.read_header_bytes, 16);

        let recs = [
            gen_rec(1, 7, 100, &[(10, 1), (11, 2)]), // key (1<<32)|7
            gen_rec(2, 7, 101, &[(12, 3)]),          // key (2<<32)|7  — distinct sample
            gen_rec(1, 7, 102, &[(13, 4)]),          // key (1<<32)|7  — same as first
            gen_rec(1, 9, 103, &[]),                 // key (1<<32)|9
        ];
        let n = recs.len();
        let input = recs.concat();
        for codec in [ChunkCodec::None, ChunkCodec::Lz4] {
            let mut out = Vec::new();
            let mut cur = Cursor::new(input.as_slice());
            let nchunks =
                collate_bucket::<GenericReadRecord, _>(&mut cur, n, &ctx, codec, &mut out).unwrap();
            let (chunks, total) = read_back::<GenericReadRecord>(&out, codec, &ctx);
            assert_eq!(total, n);
            assert_eq!(nchunks, 3, "three distinct (sample,cell) groups");
            let m: std::collections::HashMap<u128, u32> = chunks.into_iter().collect();
            assert_eq!(m[&((1u128 << 32) | 7)], 2);
            assert_eq!(m[&((2u128 << 32) | 7)], 1);
            assert_eq!(m[&((1u128 << 32) | 9)], 1);
        }
    }

    #[test]
    fn generic_ctx_from_roles_matches_names_and_none_without_roles() {
        use crate::record::GenericReadRecord;
        // read tags b0,b1 (composite key via roles), u; aln refid,as
        let read_tags = TagSection {
            label: TagSectionLabel::ReadTags,
            tags: vec![
                TagDesc {
                    name: "b0".to_string(),
                    typeid: RadType::Int(RadIntId::U32),
                    role: crate::rad_types::TagRole::Barcode { level: 0, len: 16 },
                },
                TagDesc {
                    name: "b1".to_string(),
                    typeid: RadType::Int(RadIntId::U32),
                    role: crate::rad_types::TagRole::Barcode { level: 1, len: 16 },
                },
                TagDesc {
                    name: "u".to_string(),
                    typeid: RadType::Int(RadIntId::U32),
                    role: crate::rad_types::TagRole::Umi { len: 12 },
                },
            ],
        };
        let aln_tags = tag_section(
            TagSectionLabel::AlignmentTags,
            &[("refid", RadIntId::U32), ("as", RadIntId::U32)],
        );
        let ctx = GenericCollateCtx::from_roles(&read_tags, &aln_tags)
            .unwrap()
            .expect("barcode roles present");

        // Same records + expected composite grouping as the names-based test.
        let recs = [
            gen_rec(1, 7, 100, &[(10, 1)]),
            gen_rec(2, 7, 101, &[(12, 3)]),
            gen_rec(1, 7, 102, &[(13, 4)]),
        ];
        let n = recs.len();
        let mut out = Vec::new();
        let mut cur = Cursor::new(recs.concat());
        let nchunks =
            collate_bucket::<GenericReadRecord, _>(&mut cur, n, &ctx, ChunkCodec::None, &mut out)
                .unwrap();
        assert_eq!(nchunks, 2, "(1,7) grouped, (2,7) distinct");
        let (chunks, _) = read_back::<GenericReadRecord>(&out, ChunkCodec::None, &ctx);
        let m: std::collections::HashMap<u128, u32> = chunks.into_iter().collect();
        assert_eq!(m[&((1u128 << 32) | 7)], 2);
        assert_eq!(m[&((2u128 << 32) | 7)], 1);

        // A layout with no Barcode role → None (caller falls back to the bridge).
        let plain = tag_section(
            TagSectionLabel::ReadTags,
            &[("b", RadIntId::U32), ("u", RadIntId::U32)],
        );
        assert!(
            GenericCollateCtx::from_roles(&plain, &aln_tags)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn collation_key_spec_rejects_non_collatable_layouts() {
        let read_tags = tag_section(
            TagSectionLabel::ReadTags,
            &[("b", RadIntId::U32), ("u", RadIntId::U32)],
        );
        // no key tags named → not collatable
        assert!(CollationKeySpec::from_read_tags(&read_tags, &[]).is_err());
        // named key tag absent
        assert!(CollationKeySpec::from_read_tags(&read_tags, &["nope"]).is_err());
        // composite exceeds 128 bits (two u128 barcodes)
        let wide = tag_section(
            TagSectionLabel::ReadTags,
            &[("b0", RadIntId::U128), ("b1", RadIntId::U128)],
        );
        assert!(CollationKeySpec::from_read_tags(&wide, &["b0", "b1"]).is_err());
        // variable-width alignment tag → fixed-stride gather can't skip it
        let read_ok = tag_section(TagSectionLabel::ReadTags, &[("b", RadIntId::U32)]);
        let mut var_aln = tag_section(TagSectionLabel::AlignmentTags, &[("refid", RadIntId::U32)]);
        var_aln.tags.push(TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "cigar".to_string(),
            typeid: RadType::String,
        });
        assert!(GenericCollateCtx::new(&read_ok, &var_aln, &["b"]).is_err());
        // single-barcode key works
        assert!(CollationKeySpec::from_read_tags(&read_ok, &["b"]).is_ok());
    }

    #[test]
    fn builtin_alevin_fry_record_collates_via_fast_scan() {
        // A real built-in record collates through the generic gather via its fast
        // `CollationScan` override (raw key-read + arithmetic skip).
        use crate::rad_types::RadIntId;
        use crate::record::{AlevinFryReadRecordT, AlevinFryRecordContext};
        let ctx = AlevinFryRecordContext {
            bct: RadIntId::U64,
            umit: RadIntId::U64,
        };
        let recs = [
            af_u64(7, 100, &[1, 2, 3]),
            af_u64(3, 101, &[4]),
            af_u64(7, 102, &[5, 6]),
            af_u64(3, 103, &[]),
            af_u64(9, 104, &[7]),
        ];
        let n = recs.len();
        let input = recs.concat();
        for codec in [ChunkCodec::None, ChunkCodec::Lz4] {
            let mut out = Vec::new();
            let mut cur = Cursor::new(input.as_slice());
            let nchunks =
                collate_bucket::<AlevinFryReadRecordT<u64>, _>(&mut cur, n, &ctx, codec, &mut out)
                    .unwrap();
            let (chunks, total) = read_back::<AlevinFryReadRecordT<u64>>(&out, codec, &ctx);
            assert_eq!(total, n);
            assert_eq!(nchunks, 3);
            let m: std::collections::HashMap<u128, u32> = chunks.into_iter().collect();
            assert_eq!(m[&7], 2);
            assert_eq!(m[&3], 2);
            assert_eq!(m[&9], 1);
        }
    }

    #[test]
    fn atac_record_collates_and_groups() {
        // The scATAC record (fixed `[na][bc][aln]`, no UMI) groups correctly
        // through the unified `collate_bucket` via its `CollationScan` impl, for
        // both codecs — exercising the fixed-header fast pass 2. This is the
        // record type whose bespoke gather (`collate_temporary_bucket_twopass_atac`)
        // the unification retired.
        use crate::record::{AtacSeqReadRecord, AtacSeqRecordContext};

        // ATAC record on disk: [na:u32][bc:u32][ aln × na ], aln = 11 opaque bytes.
        fn atac_rec(bc: u32, aln_seeds: &[u8]) -> Vec<u8> {
            let na = aln_seeds.len() as u32;
            let mut v = Vec::new();
            v.extend_from_slice(&na.to_le_bytes());
            v.extend_from_slice(&bc.to_le_bytes());
            for &seed in aln_seeds {
                for k in 0..11u8 {
                    v.push(seed.wrapping_add(k).wrapping_add(bc as u8));
                }
            }
            v
        }

        let ctx = AtacSeqRecordContext::from_bct(RadIntId::U32);
        let recs = [
            atac_rec(100, &[1, 2, 3]),
            atac_rec(200, &[9]),
            atac_rec(100, &[4]),
            atac_rec(300, &[]), // zero-alignment record (edge case)
            atac_rec(200, &[5, 6]),
            atac_rec(100, &[7, 8]),
        ];
        let n = recs.len();
        let input = recs.concat();
        for codec in [ChunkCodec::None, ChunkCodec::Lz4] {
            let mut out = Vec::new();
            let mut cur = Cursor::new(input.as_slice());
            let nchunks =
                collate_bucket::<AtacSeqReadRecord, _>(&mut cur, n, &ctx, codec, &mut out).unwrap();
            let (chunks, total) = read_back::<AtacSeqReadRecord>(&out, codec, &ctx);
            assert_eq!(total, n);
            assert_eq!(nchunks, 3);
            let m: std::collections::HashMap<u128, u32> = chunks.into_iter().collect();
            assert_eq!(m[&100], 3);
            assert_eq!(m[&200], 2);
            assert_eq!(m[&300], 1);
        }
    }
}
