/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Types and traits providing a high-level interface for reading and parsing
//! RAD files, including parsing RAD chunks in parallel.
//!
//! # Reading a RAD file in parallel
//!
//! [`ParallelRadReader`] (and [`ParallelChunkReader`], for when you already hold
//! a prelude or are reading from something that is not seekable) parses chunks
//! on one thread and hands **meta-chunks** to consumers through a shared queue.
//!
//! There are three levels of control. **Prefer the highest one that fits.**
//!
//! | level | API | use when |
//! | --- | --- | --- |
//! | high | [`ParallelRadReader::process_parallel`] | you just want the records and do not care to own the threads |
//! | **middle** | [`ParallelRadReader::chunk_iter`] | you want to drive the worker threads yourself — the common case |
//! | low | [`ParallelRadReader::get_queue`] + [`ParallelRadReader::is_done`] | neither of the above fits |
//!
//! ## The contract the low level asks of you
//!
//! The producer pushes **every** meta-chunk onto the queue and only *then* sets
//! the done-flag. Observing that flag therefore tells you nothing about whether
//! the queue is empty. A loop shaped like
//!
//! ```ignore
//! while !done.load(Ordering::SeqCst) {
//!     while let Some(meta_chunk) = queue.pop() { /* ... */ }
//! }
//! ```
//!
//! abandons whatever is still queued if the flag becomes visible before its next
//! check. It does not error — it just returns fewer records than the file holds.
//!
//! [`MetaChunkStream`], returned by [`ParallelRadReader::chunk_iter`], holds that
//! invariant for you, and [`ParallelRadReader::process_parallel`] additionally
//! owns the worker lifecycle. Both are drain-safe by construction; reach for
//! [`ParallelRadReader::get_queue`] only when you genuinely need the primitives.
//!
//! ## Failure
//!
//! A truncated or corrupt file makes the producer stop early. When it does, the
//! done-flag is still set, so consumers finish rather than waiting on chunks
//! that will never arrive, and the producer returns the error: the call that
//! started it — [`ParallelRadReader::process_parallel`],
//! [`ParallelRadReader::start_chunk_parsing`] and friends — yields `Err`.
//!
//! The flag therefore means "no more meta-chunks are coming", **not** "the whole
//! file was read". Consumers see a short but well-formed stream; only the
//! producer's `Result` distinguishes a complete file from a truncated one, so
//! do not discard it.
//!
//! See `examples/read_chunk_single_cell_parallel.rs` for a complete program.

use crate::libradicl::chunk::Chunk;
use crate::libradicl::codec::{CHUNK_CODEC_TAG, ChunkCodec, decompress_payload};
use crate::libradicl::header::RadPrelude;
use crate::libradicl::rad_types::{TagMap, TagValue};
use crate::libradicl::record::{MappedRecord, RecordContext};
use crate::libradicl::utils;
use anyhow::Context;
use crossbeam_queue::ArrayQueue;
use crossbeam_utils::Backoff;
use scroll::Pwrite;
use std::io::{BufRead, Cursor, Seek};
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

/// This represents an empty callback of the appropriate type for the [ParallelChunkReader] and
/// [ParallelRadReader] functions.  Use this when you want the callback to be a no-op.
pub const EMPTY_METACHUNK_CALLBACK: Option<Box<dyn FnMut(u64, u64)>> = None;

/// Determine the chunk compression codec advertised by a file-tag map.
/// An absent [`CHUNK_CODEC_TAG`] means [`ChunkCodec::None`] (every RAD file
/// written before chunk compression existed reads unchanged).
fn codec_from_tag_map(file_tag_map: &TagMap) -> anyhow::Result<ChunkCodec> {
    match file_tag_map.get(CHUNK_CODEC_TAG) {
        None => Ok(ChunkCodec::None),
        Some(TagValue::U8(v)) => ChunkCodec::from_u8(*v),
        Some(_) => anyhow::bail!("'{CHUNK_CODEC_TAG}' file tag must be a U8"),
    }
}

/// Sets the done-flag when dropped, whatever the reason for the drop.
///
/// Consumers wait on this flag and on nothing else, so a producer that returns
/// early or panics would otherwise park them forever — and the error it
/// produced could never get past their joins. Releasing them from a `Drop`
/// makes that structural rather than a property of the happy path.
///
/// The ordering [`MetaChunkStream`] relies on still holds: created before the
/// first push, dropped after the last. So the flag means "nothing more is
/// coming", not "the file was read in full"; see
/// [`ParallelRadReader::is_done`].
struct DoneOnDrop(Arc<AtomicBool>);

impl Drop for DoneOnDrop {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

/// The size, in bytes, of the `[nbytes][nrec]` header that prefixes every
/// chunk. Since `nbytes` counts the header itself, it is also the smallest
/// legal value of `nbytes` (a chunk holding no records at all).
const CHUNK_HEADER_BYTES: u32 = 8;

/// Read the header of chunk `chunk_num`, failing rather than panicking on a
/// short or nonsensical one: truncation lands in these eight bytes as readily
/// as anywhere else, and an `nbytes` smaller than the header it counts would
/// underflow the payload length derived from it.
///
/// Only the small end is checked. Callers size their buffer from `nbytes`, so a
/// corrupt header claiming `u32::MAX` still asks for ~4 GiB before the read
/// fails — bounded by the u32 framing, and needing a corrupt file rather than a
/// merely truncated one. Validating it would mean knowing how much input
/// remains, which a [BufRead] cannot say. Tracked in COMBINE-lab/libradicl#48.
fn next_chunk_header<T: BufRead>(br: &mut T, chunk_num: usize) -> anyhow::Result<(u32, u32)> {
    let (nbytes, nrec) = utils::read_chunk_header(br).with_context(|| {
        format!("failed to read the header of chunk {chunk_num}; the RAD file may be truncated")
    })?;
    anyhow::ensure!(
        nbytes >= CHUNK_HEADER_BYTES,
        "chunk {chunk_num} declares a size of {nbytes} bytes, which cannot be right; \
         a chunk is at least {CHUNK_HEADER_BYTES} bytes (its own header). \
         The RAD file appears to be corrupt."
    );
    Ok((nbytes, nrec))
}

/// A [MetaChunk] consists of a series of [Chunk]s that may be grouped together
/// for efficiency.  One can easily iterate over the [Chunk]s of a [MetaChunk] by
/// calling the [MetaChunk::iter] method.
pub struct MetaChunk<R: MappedRecord> {
    pub first_chunk_index: usize,
    pub num_sub_chunks: usize,
    pub num_bytes: u32,
    pub num_records: u32,
    chunk_blob: Vec<u8>,
    record_context: <R as MappedRecord>::ParsingContext,
}

/// An iterator over the [Chunk]s of a [MetaChunk].
pub struct MetaChunkIterator<'a, 'b, R: MappedRecord> {
    curr_sub_chunk: usize,
    num_sub_chunks: usize,
    data: Cursor<&'a [u8]>,
    record_context: &'b <R as MappedRecord>::ParsingContext,
}

impl<'a, 'b, R: MappedRecord> Iterator for MetaChunkIterator<'a, 'b, R> {
    type Item = Chunk<R>;

    /// Return the next [Chunk] contained within this [MetaChunk], returns
    /// [None] when no chunks remain.
    fn next(&mut self) -> Option<Self::Item> {
        if self.curr_sub_chunk < self.num_sub_chunks {
            self.curr_sub_chunk += 1;
            //println!("number of bytes in data = {}", self.data.get_ref().len());
            let c = Chunk::<R>::from_bytes(&mut self.data, self.record_context);
            //println!("sub_chunk {} parsed, yielding it now", self.curr_sub_chunk - 1);
            Some(c)
        } else {
            None
        }
    }

    /// Since we know how many [Chunk]s compose each [MetaChunk], we provide the
    /// optimal `size_hint` directly
    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.num_sub_chunks - self.curr_sub_chunk;
        (rem, Some(rem))
    }
}

// We know exactly how many [Chunk]s a [MetaChunk] will yield, so this is also an
// [ExactSizeIterator].
impl<'a, 'b, R: MappedRecord> ExactSizeIterator for MetaChunkIterator<'a, 'b, R> {}

impl<R: MappedRecord> MetaChunk<R>
where
    <R as MappedRecord>::ParsingContext: RecordContext,
{
    /// Creates a new [MetaChunk]
    pub fn new(
        first_chunk_index: usize,
        num_sub_chunks: usize,
        num_bytes: u32,
        num_records: u32,
        record_context: <R as MappedRecord>::ParsingContext,
        chunk_blob: Vec<u8>,
    ) -> Self {
        Self {
            first_chunk_index,
            num_sub_chunks,
            num_bytes,
            num_records,
            chunk_blob,
            record_context,
        }
    }

    /// Returns a [MetaChunkIterator] that can iterate over the
    /// [Chunk]s of this [MetaChunk].
    pub fn iter(&self) -> MetaChunkIterator<'_, '_, R> {
        MetaChunkIterator {
            curr_sub_chunk: 0,
            num_sub_chunks: self.num_sub_chunks,
            data: Cursor::new(self.chunk_blob.as_slice()),
            record_context: &self.record_context,
        }
    }

    /// The number of records present in this entire [MetaChunk]
    pub fn num_records(&self) -> u32 {
        self.num_records
    }

    /// The number of bytes present in this entire [MetaChunk]
    pub fn num_bytes(&self) -> u32 {
        self.num_bytes
    }

    /// The id of the first chunk present in this [MetaChunk]
    pub fn first_chunk_index(&self) -> usize {
        self.first_chunk_index
    }
}

/// This free function is used within the [ParallelRadReader] and [ParallelChunkReader] to
/// fill a work queue with [MetaChunk]s from the current file position until the end of the
/// file is reached. It applies the "filter" function to each chunk to determine if the chunk
/// should be included in the output (`filter_fn` returns `true`) or not (`filter_fn` returns
/// `false`).
///
/// <div class="warning">
/// NOTE:: For this function to work correctly, it is assumed that, at the point this function is
/// invoked, the reader `br` is offset at the start of the first [Chunk] in the file (directly
/// after file-level tag values).
/// </div>
///
/// * `br` - The underlying reader from which the [Chunk]s are drawn
/// * `callback` - An optional callback to be invoked when each new [MetaChunk] is placed on the work
///   queue. The callback is given 2 values; the first is the number of bytes of the just-pushed
///   [MetaChunk] and the second is the number of records of the just-pushed [MetaChunk].
/// * `prelude` - A shared reference to the [RadPrelude] corresponding to the chunks in the file
/// * `meta_chunk_queue` - A parallel queue onto which the raw data for each [MetaChunk] will be
///   placed
/// * `done_var` - An [AtomicBool] that is set to true once this function stops enqueuing work —
///   whether because every [Chunk] of the underlying file has been read and added to the work
///   queue, or because parsing failed part way through (see [`DoneOnDrop`]). Consumers are
///   released either way; the returned [`anyhow::Result`] says which happened.
fn fill_work_queue_filtered<
    R: MappedRecord,
    T: BufRead,
    ChunkIt: Iterator<Item = usize> + BufReadProvider<T> + LastChunkSignaler,
    FilterF,
    F: FnMut(u64, u64),
>(
    mut chunk_iter: ChunkIt,
    filter_fn: FilterF,
    mut callback: Option<F>,
    prelude: &RadPrelude,
    codec: ChunkCodec,
    meta_chunk_queue: Arc<ArrayQueue<MetaChunk<R>>>,
    done_var: Arc<AtomicBool>,
) -> anyhow::Result<()>
where
    <R as MappedRecord>::ParsingContext: RecordContext,
    <R as MappedRecord>::ParsingContext: Clone,
    FilterF: Fn(&[u8], &<R as MappedRecord>::ParsingContext) -> bool,
{
    // Release the consumers on *every* exit path — including the `?`s below and
    // a panic — not just on a clean run through the loop.
    let _done_guard = DoneOnDrop(done_var);

    const BUFSIZE: usize = 524208;
    // the buffer that will hold our records
    let mut buf = vec![0u8; BUFSIZE];
    // scratch holding the compressed bytes of a chunk before decompression
    // (only used when `codec != ChunkCodec::None`)
    let mut scratch: Vec<u8> = Vec::new();
    // the number of bytes currently packed into the meta chunk
    let mut cbytes = 0u32;
    // the number of records currently packed into the meta chunk
    let mut crec = 0u32;
    // the number of chunks in the current meta chunk
    let mut chunks_in_meta_chunk = 0usize;
    // the offset of the first chunk in this chunk
    let mut first_chunk = 0usize;
    // if we had to expand the buffer already and should
    // forcibly push the current buffer onto the queue
    let mut force_push = false;
    // the number of bytes and records in the next chunk header
    let mut nbytes_chunk = 0u32;
    let mut nrec_chunk = 0u32;

    // we include the endpoint here because we will not actually
    // copy a chunk in the first iteration (since we have not yet
    // read the chunk header, which comes at the end of the loop).
    let record_context = prelude
        .get_record_context::<<R as MappedRecord>::ParsingContext>()
        .unwrap();
    while let Some(chunk_num) = chunk_iter.next() {
        // while until_fn(chunk_num, &mut br) {
        // in the first iteration we've not read a header yet
        // so we can't fill a chunk, otherwise we read the header
        // at the bottom of the previous iteration of this loop, and
        // we will fill in the buffer appropriately here.
        if chunk_num > 0 {
            // Decompress (if needed) into `buf` at `boffset`, yielding an
            // uncompressed `[eff_nbytes][nrec][records]` chunk; `eff_nbytes`
            // equals `nbytes_chunk` when codec is None. The filter then runs on
            // the uncompressed chunk bytes, exactly as before.
            let boffset = cbytes as usize;
            let eff_nbytes = if codec == ChunkCodec::None {
                if nbytes_chunk as usize > buf.len() {
                    force_push = true;
                    let chunk_resize = nbytes_chunk as usize + cbytes as usize;
                    buf.resize(chunk_resize, 0);
                }
                let br = chunk_iter.get_mut_buf_read();
                buf.pwrite::<u32>(nbytes_chunk, boffset)?;
                buf.pwrite::<u32>(nrec_chunk, boffset + 4)?;
                br.read_exact(&mut buf[(boffset + 8)..(boffset + nbytes_chunk as usize)])
                    .with_context(|| {
                        format!(
                            "failed to read the {nbytes_chunk} bytes of chunk {}; \
                             the RAD file may be truncated",
                            chunk_num - 1
                        )
                    })?;
                nbytes_chunk
            } else {
                let br = chunk_iter.get_mut_buf_read();
                scratch.resize(nbytes_chunk as usize - CHUNK_HEADER_BYTES as usize, 0);
                br.read_exact(&mut scratch).with_context(|| {
                    format!(
                        "failed to read the {nbytes_chunk} compressed bytes of chunk {}; \
                         the RAD file may be truncated",
                        chunk_num - 1
                    )
                })?;
                let decoded = decompress_payload(codec, &scratch)?;
                let eff = decoded.len() as u32 + 8;
                if boffset + eff as usize > buf.len() {
                    force_push = true;
                    buf.resize(boffset + eff as usize, 0);
                }
                buf.pwrite::<u32>(eff, boffset)?;
                buf.pwrite::<u32>(nrec_chunk, boffset + 4)?;
                buf[(boffset + 8)..(boffset + eff as usize)].copy_from_slice(&decoded);
                eff
            };
            // apply the filter
            if filter_fn(&buf[boffset..], &record_context) {
                chunks_in_meta_chunk += 1;
                cbytes += eff_nbytes;
                crec += nrec_chunk;
            } else {
                // if we are skipping this collated chunk, and it triggered a
                // force_push, then undo that.
                force_push = false;
            }
        }

        // in the last iteration of the loop, we will have read all headers already
        // and we are just filling up the buffer with the last chunk, and there will be no more
        // headers left to read
        let last_chunk = chunk_iter.is_last_chunk();
        if !last_chunk {
            let (nc, nr) = next_chunk_header(chunk_iter.get_mut_buf_read(), chunk_num)?;
            nbytes_chunk = nc;
            nrec_chunk = nr;
        }

        // determine if we should dump the current buffer to the work queue
        if force_push  // if we were told to push this chunk
                || // or if adding the next cell to this chunk would exceed the buffer size
                    ((cbytes + nbytes_chunk) as usize > buf.len() && chunks_in_meta_chunk > 0)
                    || // of if this was the last chunk
                    last_chunk
        {
            // launch off these cells on the queue
            let mut bclone = MetaChunk::<R>::new(
                first_chunk,
                chunks_in_meta_chunk,
                cbytes,
                crec,
                record_context.clone(),
                buf.clone(),
            );
            // keep trying until we can push this payload
            while let Err(t) = meta_chunk_queue.push(bclone) {
                bclone = t;
                // no point trying to push if the queue is full
                while meta_chunk_queue.is_full() {}
            }
            callback
                .iter_mut()
                .for_each(|f| f(cbytes as u64, chunks_in_meta_chunk as u64));

            // offset of the first cell in the next chunk
            first_chunk += chunks_in_meta_chunk;
            // reset the counters
            chunks_in_meta_chunk = 0;
            cbytes = 0;
            crec = 0;
            buf.resize(BUFSIZE, 0);
            force_push = false;
        }
    }
    // `_done_guard` sets the done-flag as it drops here.
    Ok(())
}

/// This free function is used within the [ParallelRadReader] and [ParallelChunkReader] to
/// fill a work queue with [MetaChunk]s from the current file position until the end of the
/// file is reached.
///
/// <div class="warning">
/// NOTE:: For this function to work correctly, it is assumed that, at the point this function is
/// invoked, the reader `br` is offset at the start of the first [Chunk] in the file (directly
/// after file-level tag values).
/// </div>
///
/// * `br` - The underlying reader from which the [Chunk]s are drawn
/// * `callback` - An optional callback to be invoked when each new [MetaChunk] is placed on the work
///   queue. The callback is given 2 values; the first is the number of bytes of the just-pushed
///   [MetaChunk] and the second is the number of records of the just-pushed [MetaChunk].
/// * `prelude` - A shared reference to the [RadPrelude] corresponding to the chunks in the file
/// * `meta_chunk_queue` - A parallel queue onto which the raw data for each [MetaChunk] will be
///   placed
/// * `done_var` - An [AtomicBool] that is set to true once this function stops enqueuing work —
///   whether because every [Chunk] of the underlying file has been read and added to the work
///   queue, or because parsing failed part way through (see [`DoneOnDrop`]). Consumers are
///   released either way; the returned [`anyhow::Result`] says which happened.
fn fill_work_queue<
    R: MappedRecord,
    T: BufRead,
    ChunkIt: Iterator<Item = usize> + BufReadProvider<T> + LastChunkSignaler,
    F: FnMut(u64, u64),
>(
    mut chunk_iter: ChunkIt,
    mut callback: Option<F>,
    prelude: &RadPrelude,
    codec: ChunkCodec,
    meta_chunk_queue: Arc<ArrayQueue<MetaChunk<R>>>,
    done_var: Arc<AtomicBool>,
) -> anyhow::Result<()>
where
    <R as MappedRecord>::ParsingContext: RecordContext,
    <R as MappedRecord>::ParsingContext: Clone,
{
    // Release the consumers on *every* exit path — including the `?`s below and
    // a panic — not just on a clean run through the loop.
    let _done_guard = DoneOnDrop(done_var);

    const BUFSIZE: usize = 524208;
    // the buffer that will hold our records
    let mut buf = vec![0u8; BUFSIZE];
    // scratch holding the compressed bytes of a chunk before decompression
    // (only used when `codec != ChunkCodec::None`)
    let mut scratch: Vec<u8> = Vec::new();
    // the number of bytes currently packed into the meta chunk
    let mut cbytes = 0u32;
    // the number of records currently packed into the meta chunk
    let mut crec = 0u32;
    // the number of chunks in the current meta chunk
    let mut chunks_in_meta_chunk = 0usize;
    // the offset of the first chunk in this chunk
    let mut first_chunk = 0usize;
    // if we had to expand the buffer already and should
    // forcibly push the current buffer onto the queue
    let mut force_push = false;
    // the number of bytes and records in the next chunk header
    let mut nbytes_chunk = 0u32;
    let mut nrec_chunk = 0u32;

    // we include the endpoint here because we will not actually
    // copy a chunk in the first iteration (since we have not yet
    // read the chunk header, which comes at the end of the loop).
    let record_context = prelude
        .get_record_context::<<R as MappedRecord>::ParsingContext>()
        .unwrap();

    while let Some(chunk_num) = chunk_iter.next() {
        //while until_fn(chunk_num, &mut br) {
        // in the first iteration we've not read a header yet
        // so we can't fill a chunk, otherwise we read the header
        // at the bottom of the previous iteration of this loop, and
        // we will fill in the buffer appropriately here.
        if chunk_num > 0 {
            if codec == ChunkCodec::None {
                // if the current chunk (the chunk whose header we read in the last iteration of
                // the loop) alone is too big for the buffer, then resize the buffer to be big enough
                if nbytes_chunk as usize > buf.len() {
                    // if we had to resize the buffer to fit this cell, then make sure we push
                    // immediately in the next round
                    force_push = true;
                    let chunk_resize = nbytes_chunk as usize + cbytes as usize;
                    buf.resize(chunk_resize, 0);
                }
                let br = chunk_iter.get_mut_buf_read();

                // copy the data for the current chunk into the buffer
                let boffset = cbytes as usize;
                buf.pwrite::<u32>(nbytes_chunk, boffset)?;
                buf.pwrite::<u32>(nrec_chunk, boffset + 4)?;
                // read everything from the end of the eader into the buffer
                br.read_exact(&mut buf[(boffset + 8)..(boffset + nbytes_chunk as usize)])
                    .with_context(|| {
                        format!(
                            "failed to read the {nbytes_chunk} bytes of chunk {}; \
                             the RAD file may be truncated",
                            chunk_num - 1
                        )
                    })?;
                chunks_in_meta_chunk += 1;
                cbytes += nbytes_chunk;
                crec += nrec_chunk;
            } else {
                // Compressed chunk: `nbytes_chunk` is the compressed framing size.
                // Read the compressed payload, decompress it, and write an
                // *uncompressed* `[eff_nbytes][nrec][records]` chunk into `buf`,
                // so downstream record parsing is identical to the codec=None case.
                let br = chunk_iter.get_mut_buf_read();
                scratch.resize(nbytes_chunk as usize - CHUNK_HEADER_BYTES as usize, 0);
                br.read_exact(&mut scratch).with_context(|| {
                    format!(
                        "failed to read the {nbytes_chunk} compressed bytes of chunk {}; \
                         the RAD file may be truncated",
                        chunk_num - 1
                    )
                })?;
                let decoded = decompress_payload(codec, &scratch)?;
                let eff_nbytes = decoded.len() as u32 + 8;
                let boffset = cbytes as usize;
                if boffset + eff_nbytes as usize > buf.len() {
                    // the decoded chunk doesn't fit; grow and push immediately next round
                    force_push = true;
                    buf.resize(boffset + eff_nbytes as usize, 0);
                }
                buf.pwrite::<u32>(eff_nbytes, boffset)?;
                buf.pwrite::<u32>(nrec_chunk, boffset + 4)?;
                buf[(boffset + 8)..(boffset + eff_nbytes as usize)].copy_from_slice(&decoded);
                chunks_in_meta_chunk += 1;
                cbytes += eff_nbytes;
                crec += nrec_chunk;
            }
        }

        // in the last iteration of the loop, we will have read all headers already
        // and we are just filling up the buffer with the last chunk, and there will be no more
        // headers left to read
        let last_chunk = chunk_iter.is_last_chunk();
        if !last_chunk {
            let (nc, nr) = next_chunk_header(chunk_iter.get_mut_buf_read(), chunk_num)?;
            nbytes_chunk = nc;
            nrec_chunk = nr;
        }

        // determine if we should dump the current buffer to the work queue
        if force_push  // if we were told to push this chunk
                || // or if adding the next cell to this chunk would exceed the buffer size
                    ((cbytes + nbytes_chunk) as usize > buf.len() && chunks_in_meta_chunk > 0)
                    || // of if this was the last chunk
                    last_chunk
        {
            // launch off these cells on the queue
            let mut bclone = MetaChunk::<R>::new(
                first_chunk,
                chunks_in_meta_chunk,
                cbytes,
                crec,
                record_context.clone(),
                buf.clone(),
            );
            // keep trying until we can push this payload
            while let Err(t) = meta_chunk_queue.push(bclone) {
                bclone = t;
                // no point trying to push if the queue is full
                while meta_chunk_queue.is_full() {}
            }
            callback
                .iter_mut()
                .for_each(|f| f(cbytes as u64, chunks_in_meta_chunk as u64));

            // offset of the first cell in the next chunk
            first_chunk += chunks_in_meta_chunk;
            // reset the counters
            chunks_in_meta_chunk = 0;
            cbytes = 0;
            crec = 0;
            buf.resize(BUFSIZE, 0);
            force_push = false;
        }
    }
    // `_done_guard` sets the done-flag as it drops here.
    Ok(())
}

/// Allows reading the underlying RAD file in parallel (for the chunks) by dedicating a single
/// thread (the one running functions on this structure) to filling
/// a work queue. The queue is filled with [MetaChunk]s, which themselves
/// provide an iterator over [Chunk]s. The [ParallelRadReader] first parses the
/// prelude and file tag values itself, and then the chunks.  The main distinction
/// between this type and [ParallelChunkReader] is that this takes care of parsing
/// the prelude and file-level tag values as well.
#[derive(Debug)]
pub struct ParallelRadReader<R: MappedRecord, T: BufRead + Seek> {
    pub prelude: RadPrelude,
    pub file_tag_map: TagMap,
    reader: T,
    pub meta_chunk_queue: Arc<ArrayQueue<MetaChunk<R>>>,
    done_var: Arc<AtomicBool>,
}

/// A drain-safe iterator over the [MetaChunk]s produced by a parallel reader.
///
/// This is the **recommended** way to consume meta-chunks. It encapsulates the
/// ordering contract between the producer and its consumers, which is easy to
/// get wrong when driving [`ArrayQueue`] and the done-flag directly:
///
/// > The producer pushes **every** meta-chunk onto the queue and only *then*
/// > sets the done-flag. A consumer that observes an empty queue, and then
/// > observes the flag, may be looking at a queue the producer filled in
/// > between those two observations.
///
/// A loop that breaks as soon as it sees the flag set can therefore abandon
/// chunks that are still queued, silently losing records. [`MetaChunkStream`]
/// makes one final pass over the queue after first observing the flag, which
/// closes that window.
///
/// # Termination and failure
///
/// The flag is set on *every* producer exit path, including a parse error and a
/// panic, so this iterator always terminates. It ends the same way whether the
/// file was read in full or the producer gave up on a truncated one — check the
/// producer's [`anyhow::Result`] to tell those apart.
///
/// # Sharing across threads
///
/// Construct **one iterator per consumer thread** — each is just two `Arc`
/// clones, exactly what [`ParallelRadReader::get_queue`] and
/// [`ParallelRadReader::is_done`] hand out today. All iterators pop from the
/// same queue, so the queue continues to distribute work atomically:
///
/// ```ignore
/// std::thread::scope(|s| {
///     for _ in 0..nworkers {
///         let chunks = reader.chunk_iter();   // one per thread
///         s.spawn(move || {
///             for meta_chunk in chunks {
///                 for chunk in meta_chunk.iter() { /* ... */ }
///             }
///         });
///     }
///     reader.start_chunk_parsing(None::<fn(u64, u64)>)
/// })?;
/// ```
///
/// A single iterator cannot be shared between threads ([`Iterator::next`] takes
/// `&mut self`); do not wrap one in a `Mutex`, as that would serialize the
/// consumers. Construct one each instead.
pub struct MetaChunkStream<R: MappedRecord> {
    queue: Arc<ArrayQueue<MetaChunk<R>>>,
    done: Arc<AtomicBool>,
}

impl<R: MappedRecord> MetaChunkStream<R> {
    /// Build an iterator over `queue`, terminating once `done` is set **and**
    /// the queue has been drained.
    pub fn new(queue: Arc<ArrayQueue<MetaChunk<R>>>, done: Arc<AtomicBool>) -> Self {
        Self { queue, done }
    }
}

impl<R: MappedRecord> Iterator for MetaChunkStream<R> {
    type Item = MetaChunk<R>;

    fn next(&mut self) -> Option<Self::Item> {
        // Waiting policy. The producer is I/O bound, so a consumer that finds
        // the queue empty may be waiting for a disk read rather than for a
        // hand-off that is microseconds away. Spinning through that is actively
        // harmful: it burns the cores the producer needs.
        //
        // `Backoff` ramps from short spins to `yield_now`, which covers the
        // fast case (a chunk is imminent) and stops a hot spin from monopolising
        // a core. Once it reports `is_completed`, though, further yielding does
        // nothing on an otherwise idle machine — `yield_now` returns
        // immediately when there is nothing else runnable, so the consumer is
        // back to a hot spin. That is the point at which the wait is clearly
        // I/O-bound and worth actually sleeping through.
        //
        // Measured with a stalling reader and 8 consumers (`process_parallel`,
        // ~0.94s of work), CPU time for the same wall time:
        //
        //                        all cores          pinned to 2 CPUs
        //   unconditional spin   —                  40.9s wall (43x slower)
        //   Backoff alone        0.944s / 7.54s     0.938s / 1.87s
        //   Backoff + sleep      0.945s / 0.08s     0.853s / 0.04s
        //
        // The sleep tier is what pays: ~100x less CPU on an idle machine, and
        // slightly *better* wall time when oversubscribed. It cannot penalise a
        // fast producer, because reaching it requires the whole `Backoff` ramp
        // to be exhausted first — a briefly empty queue never gets there.
        const IDLE_SLEEP: std::time::Duration = std::time::Duration::from_micros(50);
        let backoff = Backoff::new();

        loop {
            if let Some(meta_chunk) = self.queue.pop() {
                return Some(meta_chunk);
            }
            if self.done.load(Ordering::Acquire) {
                // The producer enqueues everything before setting the flag, so
                // anything pushed between our failed pop and that store is still
                // here. `None` from this final pop means genuinely exhausted.
                return self.queue.pop();
            }
            if backoff.is_completed() {
                std::thread::sleep(IDLE_SLEEP);
            } else {
                backoff.snooze();
            }
        }
    }
}

impl<R: MappedRecord, T: BufRead + Seek> ParallelRadReader<R, T> {
    /// Create a new [ParallelRadReader] over the contents provided by `reader`.
    /// This [ParallelRadReader] will expect to provide chunks to `num_consumers` different
    /// threads once the [Self::start_chunk_parsing()] method has been called.
    ///
    /// # Errors
    ///
    /// Returns an error if the prelude or file-level tag map cannot be parsed —
    /// an empty, truncated or otherwise malformed input, which is exactly what
    /// a partial download or an interrupted write looks like. Prefer this over
    /// [`Self::new`], which panics in that case.
    pub fn try_new(mut reader: T, num_consumers: std::num::NonZeroUsize) -> anyhow::Result<Self> {
        let prelude = RadPrelude::from_bytes(&mut reader).context(
            "could not parse the RAD prelude; the input may be truncated or not a RAD file",
        )?;
        let file_tag_map = prelude
            .file_tags
            .parse_tags_from_bytes(&mut reader)
            .context("could not parse the file-level tag map from the RAD prelude")?;

        Ok(Self {
            prelude,
            file_tag_map,
            reader,
            meta_chunk_queue: Arc::new(ArrayQueue::<MetaChunk<R>>::new(num_consumers.get() * 4)),
            done_var: Arc::new(AtomicBool::new(false)),
        })
    }

    /// Create a new [ParallelRadReader] over the contents provided by `reader`.
    /// This [ParallelRadReader] will expect to provide chunks to `num_consumers` different
    /// threads once the [Self::start_chunk_parsing()] method has been called.
    ///
    /// # Panics
    ///
    /// Panics if the prelude or file-level tag map cannot be parsed. Use
    /// [`Self::try_new`] to handle malformed input — reading a file the user
    /// supplied is not a situation where a panic is the useful outcome.
    pub fn new(reader: T, num_consumers: std::num::NonZeroUsize) -> Self {
        Self::try_new(reader, num_consumers).expect("could not create ParallelRadReader")
    }

    /// Create a new [ParallelRadReader] given the provided `prelude`. It is
    /// assumed that the input `reader` has been consumed up to the point of the end of the prelude.
    /// This function will read and parse the file_tag_map.
    /// This [ParallelRadReader] will expect to provide chunks to `num_consumers` different
    /// threads once the [Self::start_chunk_parsing()] method has been called.
    ///
    /// # Panics
    ///
    /// Panics if the file-level tag map cannot be parsed; see
    /// [`Self::try_from_prelude`] for the fallible form.
    pub fn from_prelude(
        reader: T,
        prelude: RadPrelude,
        num_consumers: std::num::NonZeroUsize,
    ) -> Self {
        Self::try_from_prelude(reader, prelude, num_consumers)
            .expect("could not create ParallelRadReader from prelude")
    }

    /// Create a new [ParallelRadReader] given the provided `prelude`. It is
    /// assumed that the input `reader` has been consumed up to the point of the end of the prelude.
    /// This function will read and parse the file_tag_map.
    ///
    /// # Errors
    ///
    /// Returns an error if the file-level tag map cannot be parsed.
    pub fn try_from_prelude(
        mut reader: T,
        prelude: RadPrelude,
        num_consumers: std::num::NonZeroUsize,
    ) -> anyhow::Result<Self> {
        let file_tag_map = prelude
            .file_tags
            .parse_tags_from_bytes(&mut reader)
            .context("could not parse the file-level tag map from the RAD prelude")?;
        Ok(Self {
            prelude,
            file_tag_map,
            reader,
            meta_chunk_queue: Arc::new(ArrayQueue::<MetaChunk<R>>::new(num_consumers.get() * 4)),
            done_var: Arc::new(AtomicBool::new(false)),
        })
    }

    /// Create a new [ParallelRadReader] given the provided `prelude` and `file_tag_map`.  It is
    /// assumed that the input `reader` has been consumed up to the point of the first chunk.
    /// This [ParallelRadReader] will expect to provide chunks to `num_consumers` different
    /// threads once the [Self::start_chunk_parsing()] method has been called.
    pub fn from_prelude_and_file_tag_map(
        reader: T,
        prelude: RadPrelude,
        file_tag_map: TagMap,
        num_consumers: std::num::NonZeroUsize,
    ) -> Self {
        Self {
            prelude,
            file_tag_map,
            reader,
            meta_chunk_queue: Arc::new(ArrayQueue::<MetaChunk<R>>::new(num_consumers.get() * 4)),
            done_var: Arc::new(AtomicBool::new(false)),
        }
    }

    /// Get an `std::sync::Arc` holding the underlying `ArrayQueue` associated with this reader.
    /// This allows independent parser threads to obtain `MetaChunk`s, over which they can iterate
    /// to parse records.
    ///
    /// This is a **low-level** accessor. Consuming the queue correctly requires
    /// honouring the ordering contract documented on [`MetaChunkStream`]: the
    /// producer enqueues every meta-chunk *before* setting the done-flag, so a
    /// consumer that stops as soon as it observes the flag can abandon queued
    /// chunks and silently lose records. Prefer [`Self::chunk_iter`], which
    /// handles this, or [`Self::process_parallel`], which handles the worker
    /// threads too.
    pub fn get_queue(&self) -> Arc<ArrayQueue<MetaChunk<R>>> {
        self.meta_chunk_queue.clone()
    }

    /// Get an [std::sync::Arc] holding the [AtomicBool] that records the status of the parsing of
    /// the input file.  If the [AtomicBool] is false, parsing of the input file has not completed,
    /// and it is still possible that new [MetaChunk]s will be placed on the work queue.  However, once
    /// the contained [AtomicBool] has been set to true, the parsing is done and no further
    /// [MetaChunk]s will be placed on the queue, other than those that are already "in flight".
    ///
    /// "Done" means only that nothing further will be enqueued. It is also set when the
    /// producer stops early on a truncated or corrupt file — deliberately, since consumers
    /// waiting on a flag that never arrives is a hang with no diagnostic. Use the
    /// [`anyhow::Result`] returned by the call that started the producer to tell a complete
    /// read from a failed one.
    pub fn is_done(&self) -> Arc<AtomicBool> {
        self.done_var.clone()
    }

    /// Obtain a drain-safe iterator over this reader's [MetaChunk]s.
    ///
    /// **Prefer this over [`Self::get_queue`] / [`Self::is_done`].** Those are
    /// the low-level primitives; using them correctly requires reproducing the
    /// producer/consumer ordering contract described on [`MetaChunkStream`], and
    /// getting it wrong silently drops records rather than failing loudly.
    ///
    /// Call once per consumer thread — see [`MetaChunkStream`] for an example.
    pub fn chunk_iter(&self) -> MetaChunkStream<R> {
        MetaChunkStream::new(self.meta_chunk_queue.clone(), self.done_var.clone())
    }

    /// Get the current byte offset into the underlying `reader` stream from which this
    /// RAD file is being consumed.
    pub fn get_byte_offset(&mut self) -> u64 {
        self.reader.stream_position().unwrap()
    }

    /// This function starts the process of parsing the [Chunk]s of the underlying RAD
    /// file into a work queue of [MetaChunk]s, which can then be consumed by multiple
    /// worker threads in parallel.
    /// <div class="warning">
    /// NOTE: This function will attempt to populate the queue until the
    /// file is exhausted (all Chunks have been placed on the queue). However, to control
    /// potential memory use, we use a bounded work queue.  Therefore, if the queue is not being
    /// emptied by workers, this function will spin endlessly waiting to put the next MetaChunk
    /// on the work queue. Since this is a blocking function, be sure to have the worker threads
    /// obtain a reference to the queue (via the get_queue() method) before calling this function!
    /// </div>
    /// Read the file and process every [MetaChunk] across `num_workers` threads,
    /// handling the worker lifecycle for you.
    ///
    /// This is the **highest-level** entry point: it spawns the consumers, runs
    /// the producer, drains the queue safely, and joins everything before
    /// returning. There is no ordering contract left for the caller to get
    /// wrong. Use it when you do not need to own the threading yourself.
    ///
    /// `process` is invoked once per meta-chunk and may run concurrently on any
    /// worker, so it must be `Sync`. Per-worker mutable state should live inside
    /// the closure (for example behind a thread-local or an accumulator you
    /// merge afterwards).
    ///
    /// ```ignore
    /// let seen = std::sync::atomic::AtomicUsize::new(0);
    /// reader.process_parallel(NonZeroUsize::new(8).unwrap(), |meta_chunk| {
    ///     for chunk in meta_chunk.iter() {
    ///         seen.fetch_add(chunk.reads.len(), Ordering::Relaxed);
    ///     }
    /// })?;
    /// ```
    ///
    /// For finer control — your own thread pool, scoped borrows, per-worker
    /// accumulators — use [`Self::chunk_iter`] instead and drive the threads
    /// yourself.
    pub fn process_parallel<P>(
        &mut self,
        num_workers: std::num::NonZeroUsize,
        process: P,
    ) -> anyhow::Result<()>
    where
        P: Fn(MetaChunk<R>) + Sync,
        R: Send,
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone + Send,
    {
        let queue = self.meta_chunk_queue.clone();
        let done = self.done_var.clone();
        let process = &process;

        std::thread::scope(|s| -> anyhow::Result<()> {
            for _ in 0..num_workers.get() {
                let chunks = MetaChunkStream::new(queue.clone(), done.clone());
                s.spawn(move || {
                    for meta_chunk in chunks {
                        process(meta_chunk);
                    }
                });
            }
            // Producer runs on this thread and sets the done-flag when finished;
            // the workers above drain whatever remains before exiting.
            self.start_chunk_parsing(None::<fn(u64, u64)>)
        })
    }

    pub fn start_chunk_parsing<F: FnMut(u64, u64)>(
        &mut self,
        callback: Option<F>,
    ) -> anyhow::Result<()>
    where
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone,
    {
        // The codec check below can fail before the producer starts — a file
        // written by a newer producer, or a corrupt tag map — and consumers are
        // already waiting by then. Guard the whole call, not just the parse
        // loop, so no early exit from here can strand them either.
        let _done_guard = DoneOnDrop(self.done_var.clone());

        let mut pcr = ParallelChunkReader::<R> {
            prelude: &self.prelude,
            meta_chunk_queue: self.meta_chunk_queue.clone(),
            done_var: self.done_var.clone(),
            codec: codec_from_tag_map(&self.file_tag_map)?,
        };

        pcr.start(&mut self.reader, callback)
    }

    /// This function starts the process of parsing the [Chunk]s of the underlying RAD
    /// file into a work queue of [MetaChunk]s, which can then be consumed by multiple
    /// worker threads in parallel. **Note**: This variant of the function will apply
    /// the filter function `filter_fn` and the resulting iterators returned to the
    /// consumer will include only chunks for which `filter_fn(chunk)` is `true`.
    /// <div class="warning">
    /// NOTE: This function will attempt to populate the queue until the
    /// file is exhausted (all Chunks have been placed on the queue). However, to control
    /// potential memory use, we use a bounded work queue.  Therefore, if the queue is not being
    /// emptied by workers, this function will spin endlessly waiting to put the next MetaChunk
    /// on the work queue. Since this is a blocking function, be sure to have the worker threads
    /// obtain a reference to the queue (via the get_queue() method) before calling this function!
    /// </div>
    pub fn start_chunk_parsing_filtered<FilterFn, F: FnMut(u64, u64)>(
        &mut self,
        filter_fn: FilterFn,
        callback: Option<F>,
    ) -> anyhow::Result<()>
    where
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone,
        FilterFn: Fn(&[u8], &<R as MappedRecord>::ParsingContext) -> bool,
    {
        // See the note in [`Self::start_chunk_parsing`]: the codec check can
        // fail before the producer starts, with consumers already waiting.
        let _done_guard = DoneOnDrop(self.done_var.clone());

        let mut pcr = ParallelChunkReader::<R> {
            prelude: &self.prelude,
            meta_chunk_queue: self.meta_chunk_queue.clone(),
            done_var: self.done_var.clone(),
            codec: codec_from_tag_map(&self.file_tag_map)?,
        };

        pcr.start_filtered(&mut self.reader, filter_fn, callback)
    }
}

/// This trait represents the behavior of being able to determine if we
/// are currently looking at the last chunk in a RAD file.
trait LastChunkSignaler {
    /// Returns true if the current chunk under consideration is the
    /// last chunk in a RAD file, and false otherwise.
    fn is_last_chunk(&mut self) -> bool;
}

/// This trait represents the behavior of being able to provide a shared
/// or mutable reference to some type 'T' such that `T :` [BufRead].
trait BufReadProvider<T: BufRead> {
    #[allow(dead_code)]
    /// return a shared reference to the [BufRead]
    fn get_buf_read(&self) -> &T;
    /// return a mutable reference to the [BufRead]
    fn get_mut_buf_read(&mut self) -> &mut T;
}

/// An iterator that will iterate over chunk IDs given the total number of
/// chunks to be parsed.
struct ChunkCountIterator<T: BufRead> {
    num_chunks: usize,
    current_chunk: usize,
    buf_reader: T,
}

impl<T: BufRead> Iterator for ChunkCountIterator<T> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let c = self.current_chunk;
        self.current_chunk += 1;
        if c <= self.num_chunks { Some(c) } else { None }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.num_chunks + 1 - self.current_chunk;
        (rem, Some(rem))
    }
}

impl<T: BufRead> ExactSizeIterator for ChunkCountIterator<T> {}

impl<T: BufRead> LastChunkSignaler for ChunkCountIterator<T> {
    fn is_last_chunk(&mut self) -> bool {
        // this is > instead of == because we have already
        // incremented the chunk by the time we call this
        // that is, our iteration loop is c in 0..=num_chunks
        self.current_chunk > self.num_chunks
    }
}

impl<T: BufRead> BufReadProvider<T> for ChunkCountIterator<T> {
    fn get_buf_read(&self) -> &T {
        &self.buf_reader
    }
    fn get_mut_buf_read(&mut self) -> &mut T {
        &mut self.buf_reader
    }
}

/// An iterator that will iterate over chunk IDs until there is
/// no more data to be parsed from the underlying [BufRead]
/// object.
struct ReadUntilEOFIter<T: BufRead> {
    current_chunk: usize,
    buf_reader: T,
}

impl<T: BufRead> Iterator for ReadUntilEOFIter<T> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let c = self.current_chunk;
        self.current_chunk += 1;
        if utils::has_data_left(&mut self.buf_reader).expect("encountered error reading input file")
        {
            Some(c)
        } else {
            None
        }
    }
}

impl<T: BufRead> BufReadProvider<T> for ReadUntilEOFIter<T> {
    fn get_buf_read(&self) -> &T {
        &self.buf_reader
    }
    fn get_mut_buf_read(&mut self) -> &mut T {
        &mut self.buf_reader
    }
}

impl<T: BufRead> LastChunkSignaler for ReadUntilEOFIter<T> {
    fn is_last_chunk(&mut self) -> bool {
        !utils::has_data_left(&mut self.buf_reader).expect("encountered error reading input file")
    }
}

/// Allows reading chunks from the underlying RAD file chunks
/// in parallel by dedicating a single thread (the one running
/// functions on this structure) to filling a work queue.
/// The queue is filled with [MetaChunk]s, which themselves
/// provide an iterator over [Chunk]s.  The [ParallelChunkReader]
/// takes a reference to the [RadPrelude] for this RAD file so
/// that it can produce [MetaChunk]s that know how to be properly
/// parsed into [Chunk]s.
#[derive(Debug)]
pub struct ParallelChunkReader<'a, R: MappedRecord> {
    pub prelude: &'a RadPrelude,
    pub meta_chunk_queue: Arc<ArrayQueue<MetaChunk<R>>>,
    /// Set once the producer stops enqueuing meta-chunks; see [`Self::is_done`].
    pub done_var: Arc<AtomicBool>,
    /// Chunk compression codec (from the file-tag map); chunks are decompressed
    /// transparently in the reader thread so consumers see uncompressed records.
    /// Private so adding it stays a non-breaking change; set via [`Self::new`]
    /// (defaults to [`ChunkCodec::None`]) or by [`ParallelRadReader`].
    codec: ChunkCodec,
}

impl<'a, R: MappedRecord> ParallelChunkReader<'a, R> {
    /// `prelude`: The `RadPrelude` corresponding to the file that will be parsed
    /// `num_consumers`: The estimated number of consumer threads that will draw `MetaChunk`s from
    /// this `ParallelChunkReader`
    pub fn new(prelude: &'a RadPrelude, num_consumers: std::num::NonZeroUsize) -> Self {
        Self {
            prelude,
            meta_chunk_queue: Arc::new(ArrayQueue::<MetaChunk<R>>::new(num_consumers.get() * 4)),
            done_var: Arc::new(AtomicBool::new(false)),
            // This constructor has no file-tag map, so it assumes no chunk
            // compression. Use [ParallelRadReader] (which parses the file tags)
            // to read compressed RAD files.
            codec: ChunkCodec::None,
        }
    }

    /// Get an [std::sync::Arc] holding the underlying [ArrayQueue] associated with this reader.
    /// This allows independent parser threads to obtain [MetaChunk]s, over which they can iterate
    /// to parse records.
    pub fn get_queue(&self) -> Arc<ArrayQueue<MetaChunk<R>>> {
        self.meta_chunk_queue.clone()
    }

    /// Get an [std::sync::Arc] holding the [AtomicBool] that records the status of the parsing of
    /// the input file.  If the [AtomicBool] is false, parsing of the input file has not completed,
    /// and it is still possible that new [MetaChunk]s will be placed on the work queue.  However, once
    /// the contained [AtomicBool] has been set to true, the parsing is done and no further
    /// [MetaChunk]s will be placed on the queue, other than those that are already "in flight".
    ///
    /// "Done" means only that nothing further will be enqueued. It is also set when the
    /// producer stops early on a truncated or corrupt file — deliberately, since consumers
    /// waiting on a flag that never arrives is a hang with no diagnostic. Use the
    /// [`anyhow::Result`] returned by the call that started the producer to tell a complete
    /// read from a failed one.
    pub fn is_done(&self) -> Arc<AtomicBool> {
        self.done_var.clone()
    }

    /// Obtain a drain-safe iterator over this reader's [MetaChunk]s.
    ///
    /// **Prefer this over [`Self::get_queue`] / [`Self::is_done`].** Those are
    /// the low-level primitives; using them correctly requires reproducing the
    /// producer/consumer ordering contract described on [`MetaChunkStream`], and
    /// getting it wrong silently drops records rather than failing loudly.
    ///
    /// Call once per consumer thread — see [`MetaChunkStream`] for an example.
    pub fn chunk_iter(&self) -> MetaChunkStream<R> {
        MetaChunkStream::new(self.meta_chunk_queue.clone(), self.done_var.clone())
    }
}

impl<'a, R: MappedRecord> ParallelChunkReader<'a, R> {
    /// Start this [ParallelChunkReader] processing input from the [BufRead] `br`.
    /// Note that this reader should be positioned at the start of the chunks for this
    /// RAD file, so that the prelude and file tag values have already been parsed/consumded.
    /// Read from `br` and process every [MetaChunk] across `num_workers` threads,
    /// handling the worker lifecycle for you.
    ///
    /// This is the **highest-level** entry point: it spawns the consumers, runs
    /// the producer, drains the queue safely, and joins everything before
    /// returning. There is no ordering contract left for the caller to get
    /// wrong. Use it when you do not need to own the threading yourself.
    ///
    /// `process` is invoked once per meta-chunk and may run concurrently on any
    /// worker, so it must be `Sync`. Per-worker mutable state should live inside
    /// the closure (for example behind a thread-local or an accumulator you
    /// merge afterwards).
    ///
    /// For finer control — your own thread pool, scoped borrows, per-worker
    /// accumulators — use [`Self::chunk_iter`] instead and drive the threads
    /// yourself.
    pub fn process_parallel<T: BufRead, P>(
        &mut self,
        br: T,
        num_workers: std::num::NonZeroUsize,
        process: P,
    ) -> anyhow::Result<()>
    where
        P: Fn(MetaChunk<R>) + Sync,
        R: Send,
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone + Send,
    {
        let queue = self.meta_chunk_queue.clone();
        let done = self.done_var.clone();
        let process = &process;

        std::thread::scope(|s| -> anyhow::Result<()> {
            for _ in 0..num_workers.get() {
                let chunks = MetaChunkStream::new(queue.clone(), done.clone());
                s.spawn(move || {
                    for meta_chunk in chunks {
                        process(meta_chunk);
                    }
                });
            }
            // Producer runs on this thread and sets the done-flag when finished;
            // the workers above drain whatever remains before exiting.
            self.start(br, None::<fn(u64, u64)>)
        })
    }

    pub fn start<T: BufRead, F: FnMut(u64, u64)>(
        &mut self,
        br: T,
        callback: Option<F>,
    ) -> anyhow::Result<()>
    where
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone,
    {
        if let Some(nchunks) = self.prelude.hdr.num_chunks() {
            let num_chunks: usize = nchunks.into();
            let chunk_iter = ChunkCountIterator::<T> {
                num_chunks,
                current_chunk: 0,
                buf_reader: br,
            };
            // fill queue known number of chunks
            fill_work_queue(
                chunk_iter,
                callback,
                self.prelude,
                self.codec,
                self.meta_chunk_queue.clone(),
                self.done_var.clone(),
            )?;
        } else {
            let chunk_iter = ReadUntilEOFIter::<T> {
                current_chunk: 0,
                buf_reader: br,
            };
            // fill queue unknown number of chunks
            fill_work_queue(
                chunk_iter,
                callback,
                self.prelude,
                self.codec,
                self.meta_chunk_queue.clone(),
                self.done_var.clone(),
            )?;
        }
        Ok(())
    }

    /// Start this [ParallelChunkReader] processing input from the [BufRead] `br`.
    /// Note that this reader should be positioned at the start of the chunks for this
    /// RAD file, so that the prelude and file tag values have already been parsed/consumded.
    /// The provided filter will be applied at the **chunk** level, and chunks passing the filter
    /// for which the filter function returns `true` will be retained; others will be
    /// discarded / skipped.
    pub fn start_filtered<T: BufRead, FilterF, F: FnMut(u64, u64)>(
        &mut self,
        br: T,
        filter_fn: FilterF,
        callback: Option<F>,
    ) -> anyhow::Result<()>
    where
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone,
        FilterF: Fn(&[u8], &<R as MappedRecord>::ParsingContext) -> bool,
    {
        if let Some(nchunks) = self.prelude.hdr.num_chunks() {
            let num_chunks: usize = nchunks.into();
            let chunk_iter = ChunkCountIterator::<T> {
                num_chunks,
                current_chunk: 0,
                buf_reader: br,
            };
            // fill queue known number of chunks filtered
            fill_work_queue_filtered(
                chunk_iter,
                filter_fn,
                callback,
                self.prelude,
                self.codec,
                self.meta_chunk_queue.clone(),
                self.done_var.clone(),
            )?;
        } else {
            let chunk_iter = ReadUntilEOFIter::<T> {
                current_chunk: 0,
                buf_reader: br,
            };
            // fill queue unknown number of chunks filtered
            fill_work_queue_filtered(
                chunk_iter,
                filter_fn,
                callback,
                self.prelude,
                self.codec,
                self.meta_chunk_queue.clone(),
                self.done_var.clone(),
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rad_types::RadIntId;
    use crate::record::{PiscemBulkReadRecord, PiscemBulkRecordContext};
    use std::sync::atomic::AtomicUsize;

    fn dummy_meta_chunk(index: usize) -> MetaChunk<PiscemBulkReadRecord> {
        MetaChunk {
            first_chunk_index: index,
            num_sub_chunks: 0,
            num_bytes: 0,
            num_records: 0,
            chunk_blob: Vec::new(),
            record_context: PiscemBulkRecordContext {
                frag_map_t: RadIntId::U8,
            },
        }
    }

    /// The contract this iterator exists to enforce: the producer enqueues
    /// every meta-chunk *before* setting the done-flag, so observing the flag
    /// says nothing about whether the queue is empty. A consumer that stops as
    /// soon as it sees the flag — the natural `while !done { while let Some(..)
    /// = q.pop() }` shape — abandons everything still queued.
    ///
    /// Here the flag is already set before any consumer starts, which is the
    /// worst case that shape gets wrong 100% of the time and this iterator
    /// must get right.
    #[test]
    fn chunk_iter_drains_a_queue_that_is_already_done() {
        const NCHUNKS: usize = 500;

        for nconsumers in [1_usize, 4, 8] {
            let queue = Arc::new(ArrayQueue::<MetaChunk<PiscemBulkReadRecord>>::new(NCHUNKS));
            let done = Arc::new(AtomicBool::new(false));
            let seen = AtomicUsize::new(0);

            for i in 0..NCHUNKS {
                queue.push(dummy_meta_chunk(i)).ok().unwrap();
            }
            done.store(true, Ordering::SeqCst);

            std::thread::scope(|s| {
                for _ in 0..nconsumers {
                    let chunks = MetaChunkStream::new(queue.clone(), done.clone());
                    let seen = &seen;
                    s.spawn(move || {
                        for _meta_chunk in chunks {
                            seen.fetch_add(1, Ordering::SeqCst);
                        }
                    });
                }
            });

            assert_eq!(
                seen.load(Ordering::SeqCst),
                NCHUNKS,
                "{nconsumers} consumer(s) stopped at the done-flag with chunks still queued"
            );
            assert!(queue.is_empty(), "queue not fully drained");
        }
    }

    /// Concurrent smoke test: consumers spin on an empty queue first, so the
    /// producer's pushes and its done-store race against live `next()` calls.
    /// Nothing may be lost or double-counted.
    #[test]
    fn chunk_iter_loses_nothing_racing_a_live_producer() {
        const NCHUNKS: usize = 500;

        for nconsumers in [1_usize, 4, 8] {
            let queue = Arc::new(ArrayQueue::<MetaChunk<PiscemBulkReadRecord>>::new(NCHUNKS));
            let done = Arc::new(AtomicBool::new(false));
            let seen = AtomicUsize::new(0);
            let started = Arc::new(AtomicUsize::new(0));

            std::thread::scope(|s| {
                for _ in 0..nconsumers {
                    let chunks = MetaChunkStream::new(queue.clone(), done.clone());
                    let started = started.clone();
                    let seen = &seen;
                    s.spawn(move || {
                        started.fetch_add(1, Ordering::SeqCst);
                        for _meta_chunk in chunks {
                            seen.fetch_add(1, Ordering::SeqCst);
                        }
                    });
                }

                // Every consumer is already spinning on an empty queue before
                // the producer does anything.
                while started.load(Ordering::SeqCst) < nconsumers {
                    std::hint::spin_loop();
                }
                for i in 0..NCHUNKS {
                    queue.push(dummy_meta_chunk(i)).ok().unwrap();
                }
                done.store(true, Ordering::SeqCst);
            });

            assert_eq!(
                seen.load(Ordering::SeqCst),
                NCHUNKS,
                "{nconsumers} consumer(s)"
            );
        }
    }

    /// A malformed RAD stream must surface as an error, not a panic. Reading a
    /// file the user supplied is a normal fallible operation: a truncated
    /// download or an interrupted write should be reportable, and `new`'s
    /// `unwrap` made that impossible.
    #[test]
    fn try_new_rejects_malformed_input() {
        let n = std::num::NonZeroUsize::new(2).unwrap();
        for (what, bytes) in [
            ("truncated", vec![0_u8; 12]),
            ("empty", Vec::new()),
            ("not a rad file", b"@HD\tVN:1.6\nnot rad at all".to_vec()),
        ] {
            let res = ParallelRadReader::<PiscemBulkReadRecord, _>::try_new(
                std::io::BufReader::new(Cursor::new(bytes)),
                n,
            );
            assert!(
                res.is_err(),
                "{what} input was accepted as a valid RAD stream"
            );
        }
    }

    /// Number of records each chunk of [`test_rad_stream`] holds.
    const RECS_PER_CHUNK: u32 = 3;

    /// Build a complete, well-formed alevin-fry RAD stream of `nchunks` chunks,
    /// each holding [`RECS_PER_CHUNK`] records.
    fn test_rad_stream(nchunks: usize) -> Vec<u8> {
        test_rad_stream_with_codec_tag(nchunks, None)
    }

    /// As [`test_rad_stream`], but optionally advertising `codec_tag` as the
    /// chunk codec — used to stand in for a file this build cannot read.
    fn test_rad_stream_with_codec_tag(nchunks: usize, codec_tag: Option<u8>) -> Vec<u8> {
        use crate::chunk::Chunk;
        use crate::header::RadPrelude;
        use crate::rad_types::{RadType, TagDesc, TagSection, TagSectionLabel};
        use crate::record::{AlevinFryReadRecord, AlevinFryRecordContext};
        use crate::writers::RadFileWriter;
        use std::io::Cursor;

        let hdr = crate::header::RadHeader {
            is_paired: 0,
            ref_count: 3,
            ref_names: vec!["tgt1".into(), "tgt2".into(), "tgt3".into()],
            num_chunks: 0,
        };
        let mut file_tags = TagSection::new_with_label(TagSectionLabel::FileTags);
        for name in ["bclen", "umilen"] {
            file_tags.add_tag_desc(TagDesc {
                name: name.to_string(),
                typeid: RadType::Int(RadIntId::U16),
            });
        }
        if codec_tag.is_some() {
            file_tags.add_tag_desc(TagDesc {
                name: crate::codec::CHUNK_CODEC_TAG.to_string(),
                typeid: RadType::Int(RadIntId::U8),
            });
        }
        let mut read_tags = TagSection::new_with_label(TagSectionLabel::ReadTags);
        for name in ["b", "u"] {
            read_tags.add_tag_desc(TagDesc {
                name: name.to_string(),
                typeid: RadType::Int(RadIntId::U32),
            });
        }
        let mut aln_tags = TagSection::new_with_label(TagSectionLabel::AlignmentTags);
        aln_tags.add_tag_desc(TagDesc {
            name: "compressed_ori_refid".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        let prelude = RadPrelude {
            hdr,
            file_tags,
            read_tags,
            aln_tags,
        };
        let mut file_tag_map = crate::rad_types::TagMap::with_keyset(&prelude.file_tags.tags);
        file_tag_map.add(crate::rad_types::TagValue::U16(16));
        file_tag_map.add(crate::rad_types::TagValue::U16(12));
        if let Some(id) = codec_tag {
            file_tag_map.add(crate::rad_types::TagValue::U8(id));
        }

        let ctx = AlevinFryRecordContext::get_context_from_tag_section(
            &prelude.file_tags,
            &prelude.read_tags,
            &prelude.aln_tags,
        )
        .unwrap();
        let rec = AlevinFryReadRecord {
            bc: 12345,
            umi: 6789,
            dirs: vec![true, false, true],
            refs: vec![0, 1, 2],
        };
        let chunk = Chunk::<AlevinFryReadRecord> {
            nbytes: 0,
            nrec: RECS_PER_CHUNK,
            reads: vec![rec.clone(), rec.clone(), rec],
        };

        let mut fw = RadFileWriter::new(Cursor::new(Vec::new()), &prelude, &file_tag_map).unwrap();
        for _ in 0..nchunks {
            fw.write_chunk(&chunk, &ctx).unwrap();
        }
        fw.finalize().unwrap().into_inner()
    }

    /// Run `f` on its own thread and fail the test if it has not returned within
    /// `secs`, rather than wedging the whole test binary.
    ///
    /// The failure this guards against *is* a hang, so a test that reproduces it
    /// must not itself hang. A timed-out thread is left parked; the harness
    /// exits the process once the run completes, which reaps it.
    fn run_with_timeout<T: Send + 'static>(
        what: &str,
        secs: u64,
        f: impl FnOnce() -> T + Send + 'static,
    ) -> T {
        use std::sync::mpsc::{RecvTimeoutError, channel};
        let (tx, rx) = channel();
        std::thread::spawn(move || {
            let _ = tx.send(f());
        });
        match rx.recv_timeout(std::time::Duration::from_secs(secs)) {
            Ok(v) => v,
            Err(RecvTimeoutError::Timeout) => {
                panic!("{what}: never returned — consumers are still waiting on the done-flag")
            }
            Err(RecvTimeoutError::Disconnected) => {
                panic!("{what}: panicked instead of returning an error")
            }
        }
    }

    /// End-to-end coverage of the high-level driver over a real RAD stream:
    /// every record written must be handed to the closure exactly once, at any
    /// worker count.
    #[test]
    fn process_parallel_visits_every_record() {
        use crate::record::AlevinFryReadRecord;

        const NCHUNKS: usize = 64;
        let bytes = test_rad_stream(NCHUNKS);

        let expected = NCHUNKS * RECS_PER_CHUNK as usize;
        for nworkers in [1_usize, 2, 8] {
            let n = std::num::NonZeroUsize::new(nworkers).unwrap();
            let mut reader = ParallelRadReader::<AlevinFryReadRecord, _>::new(
                std::io::BufReader::new(Cursor::new(bytes.clone())),
                n,
            );
            let seen = AtomicUsize::new(0);
            reader
                .process_parallel(n, |meta_chunk| {
                    for c in meta_chunk.iter() {
                        seen.fetch_add(c.reads.len(), Ordering::SeqCst);
                    }
                })
                .unwrap();
            assert_eq!(
                seen.load(Ordering::SeqCst),
                expected,
                "process_parallel with {nworkers} worker(s) did not visit every record"
            );
        }
    }

    /// A producer that stops early must still release its consumers.
    ///
    /// Consumers wait on the done-flag and on nothing else. While that flag was
    /// stored only after the parse loop ran to completion, any `?` in the loop
    /// returned before the store: every consumer parked forever, and the error —
    /// correctly produced — could never be delivered, because a caller inside
    /// `std::thread::scope` cannot return past its joins. A truncated RAD file
    /// (an interrupted write, a full disk) therefore hung the process with no
    /// diagnostic at all. See COMBINE-lab/libradicl#47.
    ///
    /// Where the cut lands does not matter, so this walks several of them.
    #[test]
    fn truncated_input_fails_instead_of_hanging() {
        use crate::record::AlevinFryReadRecord;

        let bytes = test_rad_stream(64);
        for pct in [99_usize, 80, 50, 20, 1] {
            let truncated = bytes[..bytes.len() * pct / 100].to_vec();
            let res = run_with_timeout(&format!("reading a file cut to {pct}%"), 60, move || {
                let n = std::num::NonZeroUsize::new(4).unwrap();
                let mut reader = ParallelRadReader::<AlevinFryReadRecord, _>::try_new(
                    std::io::BufReader::new(Cursor::new(truncated)),
                    n,
                )?;
                reader.process_parallel(n, |_meta_chunk| {})
            });
            assert!(
                res.is_err(),
                "a file cut to {pct}% was read as if it were complete"
            );
        }
    }

    /// The same guarantee at the low level, where the caller drives the flag
    /// itself: after a failed parse the flag must be set, since that is the only
    /// thing a hand-rolled `pop`/`is_done` loop has to go on.
    #[test]
    fn done_flag_is_set_when_parsing_fails() {
        use crate::record::AlevinFryReadRecord;

        let bytes = test_rad_stream(64);
        let truncated = bytes[..bytes.len() / 2].to_vec();

        let (failed, done) = run_with_timeout("parsing a truncated file", 60, move || {
            let mut reader = ParallelRadReader::<AlevinFryReadRecord, _>::try_new(
                std::io::BufReader::new(Cursor::new(truncated)),
                std::num::NonZeroUsize::new(8).unwrap(),
            )
            .unwrap();
            let done = reader.is_done();
            let failed = reader
                .start_chunk_parsing(EMPTY_METACHUNK_CALLBACK)
                .is_err();
            (failed, done.load(Ordering::SeqCst))
        });

        assert!(failed, "truncated input parsed without error");
        assert!(done, "the producer failed without releasing its consumers");
    }

    /// A chunk header claiming a size smaller than the header itself is corrupt.
    /// Believing it underflows the payload length derived from it — a panic, or
    /// an enormous allocation — so it has to be rejected up front.
    #[test]
    fn undersized_chunk_header_is_rejected() {
        use crate::header::RadPrelude;
        use crate::record::AlevinFryReadRecord;

        let mut bytes = test_rad_stream(8);

        // Locate the first chunk header: immediately past the prelude and the
        // file-level tag values.
        let first_chunk_offset = {
            let mut cursor = Cursor::new(&bytes[..]);
            let prelude = RadPrelude::from_bytes(&mut cursor).unwrap();
            prelude
                .file_tags
                .parse_tags_from_bytes(&mut cursor)
                .unwrap();
            cursor.position() as usize
        };
        // ... and claim it is 3 bytes long, header included.
        bytes[first_chunk_offset..first_chunk_offset + 4].copy_from_slice(&3u32.to_le_bytes());

        let res = run_with_timeout("reading a corrupt chunk header", 60, move || {
            let n = std::num::NonZeroUsize::new(4).unwrap();
            let mut reader = ParallelRadReader::<AlevinFryReadRecord, _>::try_new(
                std::io::BufReader::new(Cursor::new(bytes)),
                n,
            )?;
            reader.process_parallel(n, |_meta_chunk| {})
        });

        assert!(res.is_err(), "a corrupt chunk header was accepted");
    }

    /// The producer is not the only thing that can fail after the consumers are
    /// already waiting: `start_chunk_parsing` checks the chunk codec first, and
    /// a file advertising one this build cannot read fails there, before the
    /// parse loop is ever entered. That exit has to release the consumers too.
    #[test]
    fn unreadable_codec_fails_instead_of_hanging() {
        use crate::record::AlevinFryReadRecord;

        // Codec id 42: no such codec here — what a file from a future producer
        // looks like to this build.
        let bytes = test_rad_stream_with_codec_tag(8, Some(42));

        let res = run_with_timeout("reading an unknown chunk codec", 60, move || {
            let n = std::num::NonZeroUsize::new(4).unwrap();
            let mut reader = ParallelRadReader::<AlevinFryReadRecord, _>::try_new(
                std::io::BufReader::new(Cursor::new(bytes)),
                n,
            )?;
            reader.process_parallel(n, |_meta_chunk| {})
        });

        assert!(res.is_err(), "an unknown chunk codec was accepted");
    }
}
