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
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::io::{Read, Seek, SeekFrom};

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

/// Collate one temp bucket: group its `num_records` records (a seekable stream
/// positioned at the bucket start) by [`CollationScan`] key and append one
/// per-cell chunk per key to `out` — each `[nbytes:u32][nrec:u32][payload]`,
/// `payload` `codec`-compressed (verbatim for [`ChunkCodec::None`]). Keys are
/// emitted in first-seen order (deterministic). Returns the number of chunks
/// written.
///
/// Two-pass and bounded-memory: pass one scans each record for `(key, len)`
/// (fixed records seek past alignments; others parse) and sizes the per-cell
/// chunks; pass two rewinds and relocates each record's raw bytes into its cell's
/// slot. Peak memory is the output buffer (≈ one uncompressed bucket) plus a
/// small per-record `(key, len)` table — never the whole input at once.
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

    // Pass 1: scan for keys + lengths; size per-cell chunks (first-seen order).
    let mut order: Vec<u128> = Vec::new();
    let mut cells: HashMap<u128, CellSize> = HashMap::new();
    let mut recs: Vec<(u128, u32)> = Vec::with_capacity(num_records);
    for i in 0..num_records {
        let (key, len) = S::scan(reader, ctx)?;
        match cells.entry(key) {
            Entry::Vacant(e) => {
                order.push(key);
                e.insert(CellSize {
                    payload_bytes: len,
                    nrec: 1,
                });
            }
            Entry::Occupied(mut e) => {
                let c = e.get_mut();
                c.payload_bytes += len;
                c.nrec += 1;
            }
        }
        recs.push((
            key,
            u32::try_from(len).map_err(|_| anyhow::anyhow!("record {i} exceeds u32 bytes"))?,
        ));
    }

    // Lay out the uncompressed output: one chunk per cell, in first-seen order.
    let mut total = 0usize;
    let mut write_cursor: HashMap<u128, usize> = HashMap::with_capacity(order.len());
    for &key in &order {
        let c = &cells[&key];
        let chunk_off = total;
        write_cursor.insert(key, chunk_off + CHUNK_HEADER);
        total += CHUNK_HEADER + c.payload_bytes;
    }
    let mut buf = vec![0u8; total];
    // chunk headers
    let mut off = 0usize;
    for &key in &order {
        let c = &cells[&key];
        let nbytes = (CHUNK_HEADER + c.payload_bytes) as u32;
        buf[off..off + 4].copy_from_slice(&nbytes.to_le_bytes());
        buf[off + 4..off + 8].copy_from_slice(&c.nrec.to_le_bytes());
        off += CHUNK_HEADER + c.payload_bytes;
    }

    // Pass 2: rewind and relocate each record's raw bytes into its cell's slot.
    reader.seek(SeekFrom::Start(base))?;
    let mut scratch = vec![0u8; 64 * 1024];
    for &(key, len) in &recs {
        let len = len as usize;
        if scratch.len() < len {
            scratch.resize(len, 0);
        }
        reader.read_exact(&mut scratch[..len])?;
        let w = write_cursor
            .get_mut(&key)
            .expect("cell present from pass 1");
        buf[*w..*w + len].copy_from_slice(&scratch[..len]);
        *w += len;
    }

    // Apply the per-chunk codec (verbatim for None) and append.
    if codec == ChunkCodec::None {
        out.extend_from_slice(&buf);
    } else {
        let compressed = crate::codec::recompress_bucket_per_chunk(&buf, codec)?;
        out.extend_from_slice(&compressed);
    }
    Ok(order.len())
}

struct CellSize {
    payload_bytes: usize,
    nrec: u32,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codec::{ChunkIndexBuilder, decompress_payload};
    use std::io::Cursor;

    fn ru32(c: &mut Cursor<&[u8]>) -> anyhow::Result<u32> {
        let mut b = [0u8; 4];
        c.read_exact(&mut b)?;
        Ok(u32::from_le_bytes(b))
    }
    fn ru16(c: &mut Cursor<&[u8]>) -> anyhow::Result<u16> {
        let mut b = [0u8; 2];
        c.read_exact(&mut b)?;
        Ok(u16::from_le_bytes(b))
    }

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
}
