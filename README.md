# libradicl

[![crates.io](https://img.shields.io/crates/v/libradicl.svg)](https://crates.io/crates/libradicl)
[![docs.rs](https://img.shields.io/docsrs/libradicl)](https://docs.rs/libradicl)

A [Rust](https://www.rust-lang.org/) library for reading, writing and manipulating **RAD**
(Reduced Alignment Data) files.

RAD is a binary format for recording how sequencing reads map to a set of targets — a
transcriptome, genome, or metagenome. It is "reduced" in that it is free to carry *less*
information than a [SAM/BAM](https://samtools.github.io/hts-specs/) file: only what a
downstream quantification tool actually needs. In exchange it is compact and cheap to parse
in parallel, which is the point.

RAD files are produced by [`piscem`](https://github.com/COMBINE-lab/piscem) and
[`salmon`](https://github.com/COMBINE-lab/salmon), and consumed by
[`alevin-fry`](https://github.com/COMBINE-lab/alevin-fry) and
[`piscem-infer`](https://github.com/COMBINE-lab/piscem-infer).

The working format specification lives
[here](https://hackmd.io/@PI7Og0l1ReeBZu_pjQGUQQ/HkbVOHXUR).

## Install

```toml
[dependencies]
libradicl = "0.18"
```

## Reading

Records are typed: you tell the reader *what kind* of record the file holds — one of
`AlevinFryReadRecord`, `PiscemBulkReadRecord`, `AtacSeqReadRecord`, `ScLongReadRecord`,
`GenericReadRecord` — and parsing is specialized to it.

Reading is built for parallelism. One thread parses chunks off the file and hands
**meta-chunks** to consumers through a shared queue. There are three levels of control;
prefer the highest one that fits.

### `process_parallel` — you just want the records

Spawns the workers, runs the producer, drains the queue, and joins.

```rust
use libradicl::{readers::ParallelRadReader, record::AlevinFryReadRecord};
use std::{fs::File, io::BufReader, num::NonZeroUsize};
use std::sync::atomic::{AtomicUsize, Ordering};

let nworkers = NonZeroUsize::new(8).unwrap();
let mut reader = ParallelRadReader::<AlevinFryReadRecord, _>::try_new(
    BufReader::new(File::open("map.rad")?),
    nworkers,
)?;

let nrec = AtomicUsize::new(0);
reader.process_parallel(nworkers, |meta_chunk| {
    for chunk in meta_chunk.iter() {
        nrec.fetch_add(chunk.reads.len(), Ordering::Relaxed);
    }
})?;
```

The closure may run on any worker concurrently, so it must be `Sync`. Keep per-worker state
inside the closure and merge afterwards.

### `chunk_iter` — you want to own the threads

The same guarantees, but you drive the workers: use this for scoped borrows, a thread pool
you already have, or per-worker accumulators.

```rust
std::thread::scope(|s| {
    for _ in 0..nworkers.get() {
        let chunks = reader.chunk_iter();   // one iterator per thread
        s.spawn(move || {
            let mut local = 0usize;
            for meta_chunk in chunks {
                for chunk in meta_chunk.iter() {
                    local += chunk.reads.len();
                }
            }
            local
        });
    }
    reader.start_chunk_parsing(None::<fn(u64, u64)>)
})?;
```

Construct one iterator per thread. Each is a pair of `Arc` clones over the same queue, so
work is still handed out atomically.

### `get_queue` / `is_done` — full control

The raw primitives, for when neither of the above fits.

> **Read the contract before using these.** The producer pushes *every* meta-chunk onto the
> queue and only *then* sets the done-flag. Observing the flag therefore tells you nothing
> about whether the queue is empty, and a loop that stops the moment it sees the flag can
> abandon queued chunks — returning fewer records, with no error. `chunk_iter` exists
> because that mistake is easy to make and fails quietly.

`ParallelChunkReader` offers the same three levels for the case where you already hold a
prelude, or are reading chunks from something that isn't seekable.

### Progress reporting

The `start_chunk_parsing` family takes an optional callback invoked with
`(new_bytes, new_records)` as parsing proceeds — enough to drive a progress bar. See
`examples/read_chunk_single_cell_parallel.rs`.

## Writing

`RadFileWriter` writes a prelude and then chunks, backpatching the chunk count when you
finalize:

```rust
use libradicl::writers::RadFileWriter;

let mut w = RadFileWriter::new(out, &prelude, &file_tag_values)?;
w.write_chunk(&chunk, &ctx)?;
let out = w.finalize()?;   // backpatches num_chunks
```

`ConcurrentChunkWriter` wraps one of those so several threads can append chunks to a single
file. `backpatch_file_tag_value` lets you reserve a fixed-size file tag up front and fill in
its value once it is known — used for things like a fragment-length distribution that isn't
available until the data has been seen.

## Chunk compression

Chunks may be stored uncompressed, LZ4, or zstd:

| codec | id | availability |
| --- | --- | --- |
| none | 0 | always (the default) |
| LZ4 | 1 | always — pure-Rust `lz4_flex` |
| zstd | 2 | `zstd` crate feature |

zstd is behind a feature flag so the crate stays pure Rust by default (it pulls in the C
`zstd-sys`). A reader built without the feature still reads uncompressed and LZ4 files, and
reports a clear error on a zstd chunk rather than mis-parsing it.

```toml
libradicl = { version = "0.18", features = ["zstd"] }
```

## Bounded collation

The `single_collation` and `multi_collation` modules provide bounded-memory,
parallel collators for single-cell and hierarchical multi-barcode RAD files.
Barcode resolution remains the caller's responsibility: pass the accepted
`(observed, corrected)` decisions to a plan constructor and libradicl privately
builds the fused correction-and-bucket lookup used by the record hot path.

For a single-barcode RAD file:

```rust
use libradicl::single_collation::SingleBarcodeCollationPlan;

let corrections = [(10_u64, 100_u64), (100, 100)];
let corrected_group_buckets = [(100_u64, 0_u32)];
let plan = SingleBarcodeCollationPlan::from_corrections(
    corrections,
    corrected_group_buckets,
    1,
)?;
assert_eq!(plan.num_buckets(), 1);
```

For a multi-barcode RAD file, compile the cell decisions independently within
each canonical sample before constructing the complete collation plan:

```rust
use libradicl::multi_collation::MultiBarcodeSampleCorrection;

let sample = MultiBarcodeSampleCorrection::from_corrections(
    0,
    [(10_u64, 100_u64), (100, 100)],
)?;
assert_eq!(sample.output_ordinal(), 0);
```

`SingleBarcodeCollationOptions` and `MultiBarcodeCollationOptions` both control
the total thread count, working-memory budget, and output compression. These
engines use two threads and 256 MiB as practical minima: smaller requests emit
a warning and continue with the corresponding minimum. The memory budget
excludes caller-owned indexes, the operating-system page cache, allocator
overhead, and the output writer.

## Fallible vs panicking constructors

Prefer `try_new` and `try_from_prelude`. The older `new` and `from_prelude` panic on a
malformed prelude, which is a poor outcome for input a user supplied: a truncated download
or an interrupted write should be reportable, not a backtrace. The panicking forms are
retained for compatibility.

## Examples

`libradicl/examples/` holds runnable programs:

| example | what it shows |
| --- | --- |
| `read_header` | dump a file's header and tag definitions |
| `read_chunk_single_cell` | sequential single-cell read |
| `read_chunk_single_cell_parallel` | parallel read with a progress bar |
| `read_chunk_single_cell_atac` | scATAC-seq records |
| `read_chunk_single_cell_long_read` | single-cell long reads |
| `read_chunk_bulk` | bulk (`piscem`-style) records |
| `read_chunk_generic` | reading without a purpose-built record type |

```sh
cargo run --release --example read_header -- <path-to-rad-file>
```

## Layout

| module | contents |
| --- | --- |
| `header` | `RadHeader`, `RadPrelude` |
| `rad_types` | the dynamic tag system — `TagDesc`, `RadType`, `TagMap` |
| `record` | record traits and the concrete record types |
| `chunk` | chunk representation and parsing |
| `readers` | `ParallelRadReader`, `ParallelChunkReader`, `MetaChunk` |
| `writers` | `RadFileWriter`, `ConcurrentChunkWriter` |
| `codec` | per-chunk compression codecs |
| `collation` | shared collation types, resource normalization, and legacy helpers |
| `single_collation` | bounded single-barcode collation with caller-compiled corrections |
| `multi_collation` | bounded hierarchical collation for multi-barcode protocols such as 10x Flex |
| `unmapped` | the self-describing side file recording unmapped barcode counts |

## Contributing

Pull requests go to the **`develop`** branch and use
[conventional commits](https://www.conventionalcommits.org/). Please run `cargo fmt` and
`cargo clippy --all` first, and either resolve warnings or say why they stand.

## Scope and stability

`libradicl` is developed primarily in support of COMBINE-lab tools, so features tend to land
in the order those tools need them, and the API is pre-1.0 — expect occasional breaking
changes on minor version bumps. The aim is nonetheless a genuinely general library for the
RAD format, so if you have a use case that doesn't fit, please open an issue. Contributions
are welcome.

## License

3-clause BSD — see [LICENSE](LICENSE).
