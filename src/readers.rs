/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! This module contains types and traits that provide a high-level iterface to
//! reading and parsing RAD files.  Additionally, it provides types that give an
//! interface for parsing RAD chunks in parallel for improved processing performance.

use crate::libradicl::chunk::Chunk;
use crate::libradicl::header::RadPrelude;
use crate::libradicl::rad_types::TagMap;
use crate::libradicl::record::{MappedRecord, RecordContext};
use crate::libradicl::utils;
use anyhow::Context;
use crossbeam_queue::ArrayQueue;
use scroll::Pwrite;
use std::io::{BufRead, Cursor, Seek};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

/// This represents an empty callback of the appropriate type for the [ParallelChunkReader] and
/// [ParallelRadReader] functions.  Use this when you want the callback to be a no-op.
pub const EMPTY_METACHUNK_CALLBACK: Option<Box<dyn FnMut(u64, u64)>> = None;

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
    pub fn iter(&self) -> MetaChunkIterator<R> {
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
/// queue. The callback is given 2 values; the first is the number of bytes of the just-pushed
/// [MetaChunk] and the second is the number of records of the just-pushed [MetaChunk].
/// * `prelude` - A shared reference to the [RadPrelude] corresponding to the chunks in the file
/// * `meta_chunk_queue` - A parallel queue onto which the raw data for each [MetaChunk] will be
/// placed
/// * `done_var` - An [AtomicBool] that will be set to true only once all of the [Chunk]s of the
/// underlying file have been read and added to the work queue.
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
    meta_chunk_queue: Arc<ArrayQueue<MetaChunk<R>>>,
    done_var: Arc<AtomicBool>,
) -> anyhow::Result<()>
where
    <R as MappedRecord>::ParsingContext: RecordContext,
    <R as MappedRecord>::ParsingContext: Clone,
    FilterF: Fn(&[u8], &<R as MappedRecord>::ParsingContext) -> bool,
{
    const BUFSIZE: usize = 524208;
    // the buffer that will hold our records
    let mut buf = vec![0u8; BUFSIZE];
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
                .context("failed to read from work queue.")?;
            // apply the filter
            if filter_fn(&buf[boffset..], &record_context) {
                chunks_in_meta_chunk += 1;
                cbytes += nbytes_chunk;
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
            let (nc, nr) = Chunk::<R>::read_header(chunk_iter.get_mut_buf_read());
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
    done_var.store(true, Ordering::SeqCst);
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
/// queue. The callback is given 2 values; the first is the number of bytes of the just-pushed
/// [MetaChunk] and the second is the number of records of the just-pushed [MetaChunk].
/// * `prelude` - A shared reference to the [RadPrelude] corresponding to the chunks in the file
/// * `meta_chunk_queue` - A parallel queue onto which the raw data for each [MetaChunk] will be
/// placed
/// * `done_var` - An [AtomicBool] that will be set to true only once all of the [Chunk]s of the
/// underlying file have been read and added to the work queue.
fn fill_work_queue<
    R: MappedRecord,
    T: BufRead,
    ChunkIt: Iterator<Item = usize> + BufReadProvider<T> + LastChunkSignaler,
    F: FnMut(u64, u64),
>(
    mut chunk_iter: ChunkIt,
    mut callback: Option<F>,
    prelude: &RadPrelude,
    meta_chunk_queue: Arc<ArrayQueue<MetaChunk<R>>>,
    done_var: Arc<AtomicBool>,
) -> anyhow::Result<()>
where
    <R as MappedRecord>::ParsingContext: RecordContext,
    <R as MappedRecord>::ParsingContext: Clone,
{
    const BUFSIZE: usize = 524208;
    // the buffer that will hold our records
    let mut buf = vec![0u8; BUFSIZE];
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
                .context("failed to read from work queue.")?;
            chunks_in_meta_chunk += 1;
            cbytes += nbytes_chunk;
            crec += nrec_chunk;
        }

        // in the last iteration of the loop, we will have read all headers already
        // and we are just filling up the buffer with the last chunk, and there will be no more
        // headers left to read
        let last_chunk = chunk_iter.is_last_chunk();
        if !last_chunk {
            let (nc, nr) = Chunk::<R>::read_header(chunk_iter.get_mut_buf_read());
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
    done_var.store(true, Ordering::SeqCst);
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

impl<R: MappedRecord, T: BufRead + Seek> ParallelRadReader<R, T> {
    /// Create a new [ParallelRadReader] over the contents provided by `reader`.
    /// This [ParallelRadReader] will expect to provide chunks to `num_consumers` different
    /// threads once the [Self::start_chunk_parsing()] method has been called.
    pub fn new(mut reader: T, num_consumers: std::num::NonZeroUsize) -> Self {
        let prelude = RadPrelude::from_bytes(&mut reader).unwrap();
        let file_tag_map = prelude
            .file_tags
            .parse_tags_from_bytes(&mut reader)
            .unwrap();

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
    pub fn get_queue(&self) -> Arc<ArrayQueue<MetaChunk<R>>> {
        self.meta_chunk_queue.clone()
    }

    /// Get an [std::sync::Arc] holding the [AtomicBool] that records the status of the parsing of
    /// the input file.  If the [AtomicBool] is false, parsing of the input file has not completed,
    /// and it is still possible that new [MetaChunk]s will be placed on the work queue.  However, once
    /// the contained [AtomicBool] has been set to true, the parsing is done and no further
    /// [MetaChunk]s will be placed on the queue, other than those that are already "in flight".
    pub fn is_done(&self) -> Arc<AtomicBool> {
        self.done_var.clone()
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
    pub fn start_chunk_parsing<F: FnMut(u64, u64)>(
        &mut self,
        callback: Option<F>,
    ) -> anyhow::Result<()>
    where
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone,
    {
        let mut pcr = ParallelChunkReader::<R> {
            prelude: &self.prelude,
            meta_chunk_queue: self.meta_chunk_queue.clone(),
            done_var: self.done_var.clone(),
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
        let mut pcr = ParallelChunkReader::<R> {
            prelude: &self.prelude,
            meta_chunk_queue: self.meta_chunk_queue.clone(),
            done_var: self.done_var.clone(),
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
        if c <= self.num_chunks {
            Some(c)
        } else {
            None
        }
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
    pub done_var: Arc<AtomicBool>,
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
    pub fn is_done(&self) -> Arc<AtomicBool> {
        self.done_var.clone()
    }
}

impl<'a, R: MappedRecord> ParallelChunkReader<'a, R> {
    /// Start this [ParallelChunkReader] processing input from the [BufRead] `br`.
    /// Note that this reader should be positioned at the start of the chunks for this
    /// RAD file, so that the prelude and file tag values have already been parsed/consumded.
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
                self.meta_chunk_queue.clone(),
                self.done_var.clone(),
            )?;
        }
        Ok(())
    }
}
