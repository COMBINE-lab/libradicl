# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

`libradicl` is a Rust library for reading, parsing, and writing RAD (Reduced Alignment Data) format files — a binary format encoding alignment information for sequencing reads. It primarily supports [`alevin-fry`](https://github.com/COMBINE-lab/alevin-fry) (single-cell RNA/ATAC-seq quantification) and is produced by [`piscem`](https://github.com/COMBINE-lab/piscem)/[`salmon`](https://github.com/COMBINE-lab/salmon).

The working RAD format spec is at https://hackmd.io/@PI7Og0l1ReeBZu_pjQGUQQ/HkbVOHXUR.

## Workspace Structure

This is a Cargo workspace with two crates:
- `libradicl/` — main library
- `libradicl-macros/` — procedural macros (provides `#[derive(UmiTagged)]`)

## Commands

```bash
# Build
cargo build --release

# Test
cargo test --all
cargo test <test_name>          # single test

# Lint & format (required before PRs)
cargo fmt
cargo clippy --all

# Documentation
cargo doc --open

# Run an example
cargo run --example read_header -- <path-to-rad-file>
```

## Contributing

- PRs go to the **`develop`** branch, not `main`
- Use [conventional commits](https://www.conventionalcommits.org/)
- Run `cargo fmt` and `cargo clippy --all` before submitting; resolve or explicitly document any clippy warnings

## Architecture

### RAD File Structure

A RAD file is organized as:
1. **Header** (`header.rs`) — paired flag, reference count/names, chunk count
2. **Tag sections** — `FileTags`, `ReadTags`, `AlignmentTags` describing dynamic fields at each level
3. **Chunks** (`chunk.rs`) — repeating blocks; each chunk contains records per cell barcode

### Type System (`rad_types.rs`)

RAD uses a dynamic tag system. `TagDesc` pairs a field name with a `RadType` (which wraps `RadIntId` enums for integer widths, or `Array` variants). This allows the format to be flexible about which fields appear and at what sizes.

### Record Traits (`record.rs`)

The library is generic over record types via traits:
- `MappedRecord` — base trait for any record that can be parsed from a RAD chunk
- `RecordHeader` — for the per-read header portion (barcode + UMI)
- `CollatableMappedRecord<B>` — for records that can be grouped/collated by barcode

Concrete record types:
- `AlevinFryReadRecord` / `AlevinFryReadRecordU128` — standard sc-RNA-seq (barcode as u64/u128)
- `AtacSeqReadRecord` — scATAC-seq with position/fragment-length fields
- `ScLongReadRecord<B>` — single-cell long reads

### Collation Pattern (`lib.rs`)

The two-pass collation is central to the library's use in `alevin-fry`:
1. **First pass**: scan all records, accumulate per-barcode byte/record counts
2. **Second pass**: write records into a collated (barcode-sorted) buffer, optionally Snappy-compressed

The main entry point is `collate_temporary_bucket_twopass_generic<B, T, U, R>`.

### Parallel Reading (`readers.rs`)

`ParallelChunkReader<R>` and `MetaChunk<R>` support multi-threaded chunk processing using `crossbeam-queue`. Chunks are dispatched to worker threads and results collected without per-record locking.

### Barcode Lookup (`lib.rs` — `BarcodeLookupMap`)

Sorted barcode list with prefix/suffix split for fast 1-mismatch neighbor search. Key methods:
- `find_exact()` — binary search, O(log n)
- `find_neighbors()` — tolerates one substitution with early exit

### Macros (`libradicl-macros/`)

`#[derive(UmiTagged)]` with `#[umi_tagged(umi = "field_name")]` generates the `UmiTaggedRecord` trait impl, pointing to the named field as the UMI.

### Key Dependencies

| Crate | Purpose |
|-------|---------|
| `scroll` | Binary parsing/writing |
| `snap` | Snappy compression for collated buckets |
| `noodles` | BAM/SAM record handling |
| `bio-types` | `Strand` enum for orientation filtering |
| `dashmap` | Concurrent hash maps |
| `crossbeam-queue` | Lock-free queue for parallel readers |
