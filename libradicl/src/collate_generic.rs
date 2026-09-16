/*
 * Copyright (c) 2020-2026 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Parse-based generic collation core (step 1 of the collation-engine
//! unification, see COMBINE-lab/libradicl#62).
//!
//! This is the record-type-agnostic heart of collation: given a bucket's
//! records and a way to read one record's *collation key* and *on-disk length*,
//! it groups records by key and emits one per-cell [`crate::chunk`]-format chunk
//! each, applying a per-chunk [`ChunkCodec`] and recording chunk offsets in a
//! [`ChunkIndexBuilder`]. It is generic over the record type through the lean
//! [`ScatterProbe`] trait and imposes **no** `KnownSize` bound, so it works for
//! any record — fixed- or variable-length — including custom record types
//! defined by external consumers of libradicl.
//!
//! The parallel scatter/spill machinery and barcode-correction plan that wrap
//! this core (retiring `single_collation` / `multi_collation` /
//! `collate_temporary_bucket_twopass_generic`) are later steps of #62; this
//! module establishes and tests the generic, extensible baseline.

use crate::codec::{ChunkCodec, ChunkIndexBuilder, compress_payload};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::io::Cursor;

/// The contract a record type satisfies to be collatable by the generic engine.
///
/// A `ScatterProbe` reads exactly one on-disk record starting at the cursor,
/// advances the cursor past it, and returns the record's collation key (e.g. the
/// corrected barcode as a `u64`). The cursor advance is what lets the engine
/// relocate the record's *raw bytes* without re-serializing, so the record's
/// on-disk length need not be known ahead of time.
///
/// The default obligation is a full parse — which works for any record,
/// including variable-length ones (their parse reads the variable fields and the
/// cursor advance yields the exact length). A record whose layout permits it may
/// implement `probe` as a cheaper key-read plus arithmetic skip; that
/// optimization lives entirely in the impl and is invisible to the engine.
pub trait ScatterProbe {
    /// Parsing context (RAD tags etc.); `()` when none is needed.
    type Ctx;

    /// Advance `cursor` past exactly one record and return its collation key.
    fn probe(cursor: &mut Cursor<&[u8]>, ctx: &Self::Ctx) -> anyhow::Result<u64>;
}

// --- `ScatterProbe` for the built-in single-barcode-family records ---
//
// These are the parse-based (correctness-baseline) probes: read the record via
// its `MappedRecord` impl (the cursor advances by exactly the record's on-disk
// length) and return its collation key. A faster raw-read + arithmetic-skip
// override for the fixed-stride layouts is a later step (#62); these establish
// that every built-in record collates through the generic core, at any barcode
// width, without a `KnownSize` bound on the engine.
macro_rules! parse_scatter_probe {
    ($rec:ident, $ctx:path) => {
        impl<B> ScatterProbe for crate::record::$rec<B>
        where
            B: crate::record::ConvertiblePrimitiveInteger,
            u64: From<B>,
            crate::record::$rec<B>: crate::record::MappedRecord<ParsingContext = $ctx>
                + crate::record::CollatableMappedRecord<B>,
        {
            type Ctx = $ctx;
            fn probe(cursor: &mut Cursor<&[u8]>, ctx: &$ctx) -> anyhow::Result<u64> {
                use crate::record::{CollatableMappedRecord, MappedRecord};
                let rec = <crate::record::$rec<B>>::from_bytes_with_context(cursor, ctx);
                Ok(u64::from(rec.collate_key()))
            }
        }
    };
}

parse_scatter_probe!(AlevinFryReadRecordT, crate::record::AlevinFryRecordContext);
parse_scatter_probe!(
    AlevinFryReadRecordWithPositionT,
    crate::record::AlevinFryRecordContext
);
parse_scatter_probe!(ScLongReadRecordT, crate::record::ScLongReadRecordContext);

/// Collate one bucket of records: group by [`ScatterProbe`] key and append one
/// per-cell chunk per key to `out`, each `[nbytes: u32][nrec: u32][payload]`
/// where `nbytes` counts the 8-byte header and `payload` is `codec`-compressed
/// (verbatim for [`ChunkCodec::None`]) — the same on-disk shape the standard and
/// parallel readers consume. Chunk offsets for the appended region are recorded
/// in `index`. Keys are emitted in first-seen order (deterministic for a given
/// input). Returns the number of chunks (distinct keys) written.
///
/// `input` holds `num_records` records in their on-disk encoding; the engine
/// copies each record's raw bytes verbatim, so no `KnownSize`/re-serialization is
/// required and variable-length records are handled transparently.
pub fn collate_bucket<P: ScatterProbe>(
    input: &[u8],
    num_records: usize,
    ctx: &P::Ctx,
    codec: ChunkCodec,
    index: &mut ChunkIndexBuilder,
    out: &mut Vec<u8>,
) -> anyhow::Result<usize> {
    // First pass: parse each record for its key and byte span, preserving
    // first-seen key order for a deterministic chunk layout.
    let mut cursor = Cursor::new(input);
    let mut order: Vec<u64> = Vec::new();
    let mut spans: HashMap<u64, Vec<(usize, usize)>> = HashMap::new();
    for r in 0..num_records {
        let start = cursor.position() as usize;
        let key = P::probe(&mut cursor, ctx)?;
        let end = cursor.position() as usize;
        if end <= start || end > input.len() {
            anyhow::bail!(
                "record {r} probe advanced {start}->{end} outside the bucket (len {})",
                input.len()
            );
        }
        match spans.entry(key) {
            Entry::Vacant(e) => {
                order.push(key);
                e.insert(vec![(start, end - start)]);
            }
            Entry::Occupied(mut e) => e.get_mut().push((start, end - start)),
        }
    }

    // Second pass: one chunk per key, codec-compressed, offsets recorded.
    let bucket_start = out.len();
    for key in &order {
        let recs = &spans[key];
        let nrec = recs.len() as u32;
        let mut payload = Vec::new();
        for &(s, l) in recs {
            payload.extend_from_slice(&input[s..s + l]);
        }
        let comp = compress_payload(codec, &payload)?;
        let nbytes = (comp.len() as u32) + 8;
        out.extend_from_slice(&nbytes.to_le_bytes());
        out.extend_from_slice(&nrec.to_le_bytes());
        out.extend_from_slice(&comp);
    }
    index.record_bucket(&out[bucket_start..]);
    Ok(order.len())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codec::decompress_payload;
    use std::io::Read;

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

    // --- Two custom record types that implement only `ScatterProbe` (not the
    // full `CollatableMappedRecord`), standing in for an external consumer's
    // record. One is fixed-stride, one is genuinely variable-length. ---

    /// Fixed-stride: `[na:u32][bc:u32][umi:u32][na × u32 alignment]`.
    struct FixedRec;
    impl ScatterProbe for FixedRec {
        type Ctx = ();
        fn probe(cursor: &mut Cursor<&[u8]>, _ctx: &()) -> anyhow::Result<u64> {
            let na = ru32(cursor)?;
            let bc = ru32(cursor)?;
            let _umi = ru32(cursor)?;
            cursor.set_position(cursor.position() + (na as u64) * 4); // skip alignments
            Ok(bc as u64)
        }
    }

    /// Variable-length: `[na:u32][bc:u32]` then `na` alignments, each a
    /// length-prefixed blob `[len:u16][len bytes]` (a stand-in for a
    /// CIGAR-carrying record whose per-alignment size is data-dependent and so
    /// cannot implement `KnownSize`).
    struct VarRec;
    impl ScatterProbe for VarRec {
        type Ctx = ();
        fn probe(cursor: &mut Cursor<&[u8]>, _ctx: &()) -> anyhow::Result<u64> {
            let na = ru32(cursor)?;
            let bc = ru32(cursor)?;
            for _ in 0..na {
                let len = ru16(cursor)? as u64;
                cursor.set_position(cursor.position() + len); // skip the variable blob
            }
            Ok(bc as u64)
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

    /// Walk the collated `out` chunks; for each, decompress the payload and
    /// return `(bc, per_record_bytes)` by re-probing, verifying every record in
    /// a chunk shares the chunk's barcode. Returns `Vec<(bc, nrec)>` in file
    /// order plus the total record count seen.
    fn read_back<P: ScatterProbe>(
        out: &[u8],
        codec: ChunkCodec,
        ctx: &P::Ctx,
    ) -> (Vec<(u64, u32)>, usize) {
        let mut chunks = Vec::new();
        let mut total = 0usize;
        let mut pos = 0usize;
        while pos < out.len() {
            let nbytes = u32::from_le_bytes(out[pos..pos + 4].try_into().unwrap()) as usize;
            let nrec = u32::from_le_bytes(out[pos + 4..pos + 8].try_into().unwrap());
            let payload = decompress_payload(codec, &out[pos + 8..pos + nbytes]).unwrap();
            // re-probe every record in the (decompressed) payload
            let mut cur = Cursor::new(payload.as_slice());
            let mut chunk_bc: Option<u64> = None;
            for _ in 0..nrec {
                let bc = P::probe(&mut cur, ctx).unwrap();
                assert!(chunk_bc.is_none_or(|c| c == bc), "chunk mixed barcodes");
                chunk_bc = Some(bc);
                total += 1;
            }
            assert_eq!(
                cur.position() as usize,
                payload.len(),
                "trailing bytes in chunk"
            );
            chunks.push((chunk_bc.unwrap(), nrec));
            pos += nbytes;
        }
        assert_eq!(pos, out.len());
        (chunks, total)
    }

    fn run_case<P: ScatterProbe<Ctx = ()>>(input: Vec<u8>, num_records: usize) {
        // Barcodes present (first-seen order) and their record counts.
        for codec in [ChunkCodec::None, ChunkCodec::Lz4] {
            let mut index = ChunkIndexBuilder::default();
            let mut out = Vec::new();
            let n_chunks =
                collate_bucket::<P>(&input, num_records, &(), codec, &mut index, &mut out).unwrap();

            let (chunks, total) = read_back::<P>(&out, codec, &());
            assert_eq!(total, num_records, "all records survive collation");
            assert_eq!(chunks.len(), n_chunks, "one chunk per distinct barcode");
            // barcodes are unique per chunk (grouping is complete)
            let mut bcs: Vec<u64> = chunks.iter().map(|c| c.0).collect();
            let unique = {
                let mut b = bcs.clone();
                b.sort_unstable();
                b.dedup();
                b.len()
            };
            assert_eq!(
                unique,
                chunks.len(),
                "each barcode appears in exactly one chunk"
            );
            bcs.sort_unstable();

            // chunk index: n_chunks + 1 offsets, last == collated byte length,
            // offsets strictly increasing and landing on chunk boundaries.
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
        // barcodes 7,3,7,3,9 -> 3 cells (7:2, 3:2, 9:1), variable #alignments.
        let recs = [
            fixed_rec_bytes(7, 100, &[1, 2, 3]),
            fixed_rec_bytes(3, 101, &[4]),
            fixed_rec_bytes(7, 102, &[5, 6]),
            fixed_rec_bytes(3, 103, &[]),
            fixed_rec_bytes(9, 104, &[7, 8, 9, 10]),
        ];
        let n = recs.len();
        let input: Vec<u8> = recs.concat();
        run_case::<FixedRec>(input, n);
    }

    #[test]
    fn variable_length_record_collates_and_groups() {
        // A record type that cannot implement KnownSize (data-dependent
        // per-alignment size) still collates end-to-end via the parse default.
        let recs = [
            var_rec_bytes(42, &[b"MMMM", b"II"]),
            var_rec_bytes(5, &[b"S"]),
            var_rec_bytes(42, &[b"MMMMMMMMMM"]),
            var_rec_bytes(5, &[b"", b"DDDD", b"MMM"]),
            var_rec_bytes(42, &[]),
        ];
        let n = recs.len();
        let input: Vec<u8> = recs.concat();
        run_case::<VarRec>(input, n);
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
    fn builtin_alevin_fry_record_collates_via_core() {
        // A real built-in record type collates through the generic core via its
        // `ScatterProbe` impl (proving the wiring, not just synthetic records).
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
        let input: Vec<u8> = recs.concat();
        for codec in [ChunkCodec::None, ChunkCodec::Lz4] {
            let mut index = ChunkIndexBuilder::default();
            let mut out = Vec::new();
            let nchunks = collate_bucket::<AlevinFryReadRecordT<u64>>(
                &input, n, &ctx, codec, &mut index, &mut out,
            )
            .unwrap();
            let (chunks, total) = read_back::<AlevinFryReadRecordT<u64>>(&out, codec, &ctx);
            assert_eq!(total, n);
            assert_eq!(nchunks, 3, "barcodes 7,3,9 -> 3 cells");
            let m: std::collections::HashMap<u64, u32> = chunks.into_iter().collect();
            assert_eq!(m[&7], 2);
            assert_eq!(m[&3], 2);
            assert_eq!(m[&9], 1);
            let offs = index.into_offsets();
            assert_eq!(offs.len(), nchunks + 1);
            assert_eq!(*offs.last().unwrap(), out.len() as u64);
        }
    }

    #[test]
    fn single_barcode_single_chunk() {
        let recs = [fixed_rec_bytes(1, 0, &[1]), fixed_rec_bytes(1, 1, &[2, 3])];
        let input: Vec<u8> = recs.concat();
        run_case::<FixedRec>(input, 2);
    }
}
