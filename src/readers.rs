/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

use crate::libradicl::chunk::Chunk;
use crate::libradicl::header::RadPrelude;
use crate::libradicl::rad_types::TagMap;
use crate::libradicl::record::{MappedRecord, RecordContext};
use crate::libradicl::utils;
use anyhow::Context;
use crossbeam_queue::ArrayQueue;
use scroll::Pwrite;
use std::io::{BufRead, Cursor};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

/// A [MetaChunk] consists of a series of [Chunk]s that may be grouped together
/// for efficiency.  One can easily iterate over the [Chunk]s of a [MetaChunk] by
/// calling the [MetaChunk::iter] method.
pub struct MetaChunk<R: MappedRecord> {
    first_chunk_index: usize,
    num_sub_chunks: usize,
    num_bytes: u32,
    num_records: u32,
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

    pub fn iter(&self) -> MetaChunkIterator<R> {
        MetaChunkIterator {
            curr_sub_chunk: 0,
            num_sub_chunks: self.num_sub_chunks,
            data: Cursor::new(self.chunk_blob.as_slice()),
            record_context: &self.record_context,
        }
    }

    pub fn num_records(&self) -> u32 {
        self.num_records
    }
    pub fn num_bytes(&self) -> u32 {
        self.num_bytes
    }
    pub fn first_chunk_index(&self) -> usize {
        self.first_chunk_index
    }
}

fn fill_work_queue_until_eof<R: MappedRecord, T: BufRead>(
    mut br: T,
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
    let mut last_chunk = false;

    // we include the endpoint here because we will not actually
    // copy a chunk in the first iteration (since we have not yet
    // read the chunk header, which comes at the end of the loop).
    let mut chunk_num = 0;
    let record_context = prelude
        .get_record_context::<<R as MappedRecord>::ParsingContext>()
        .unwrap();
    while utils::has_data_left(&mut br).expect("encountered error reading input file") {
        // in the first iteration we've not read a header yet
        // so we can't fill a chunk, otherwise we read the header
        // at the bottom of the previous iteration of this loop, and
        // we will fill in the buffer appropriately here.
        if chunk_num > 0 {
            println!("reading data for chunk {}", chunk_num - 1);
            // if the current chunk (the chunk whose header we read in the last iteration of
            // the loop) alone is too big for the buffer, then resize the buffer to be big enough
            if nbytes_chunk as usize > buf.len() {
                // if we had to resize the buffer to fit this cell, then make sure we push
                // immediately in the next round
                force_push = true;
                let chunk_resize = nbytes_chunk as usize + cbytes as usize;
                buf.resize(chunk_resize, 0);
            }

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
        if utils::has_data_left(&mut br).expect("encountered error reading input file") {
            //println!("reading header for chunk {}", chunk_num);
            let (nc, nr) = Chunk::<R>::read_header(&mut br);
            nbytes_chunk = nc;
            nrec_chunk = nr;
        } else {
            //println!("last chunk!");
            last_chunk = true;
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
            // pbar.inc(cells_in_chunk as u64);

            // offset of the first cell in the next chunk
            first_chunk += chunks_in_meta_chunk;
            // reset the counters
            chunks_in_meta_chunk = 0;
            cbytes = 0;
            crec = 0;
            buf.resize(BUFSIZE, 0);
            force_push = false;
        }
        chunk_num += 1;
    }
    done_var.store(true, Ordering::SeqCst);
    Ok(())
}

/// Allows reading the underlying RAD file in parallel (for the chunks) by dedicating a single
/// thread (the one running functions on this structure) to filling
/// a work queue. The queue is filled with `MetaChunk`s, which themselves
/// provide an iterator over `Chunk`s. The `ParallelRadReader` first parses the
/// prelude and file tag values itself, and then the chunks.  The main distinction
/// between this type and [ParallelChunkReader] is that this takes care of parsing
/// the prelude and file-level tag values as well.
#[derive(Debug)]
pub struct ParallelRadReader<R: MappedRecord, T: BufRead> {
    pub prelude: RadPrelude,
    pub file_tag_map: TagMap,
    reader: T,
    pub meta_chunk_queue: Arc<ArrayQueue<MetaChunk<R>>>,
    done_var: Arc<AtomicBool>,
}

impl<R: MappedRecord, T: BufRead> ParallelRadReader<R, T> {
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

    pub fn is_done(&self) -> Arc<AtomicBool> {
        self.done_var.clone()
    }

    /// NOTE: Blocking function; get the queue before calling this!
    pub fn start_chunk_parsing(&mut self) -> anyhow::Result<()>
    where
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone,
    {
        let mut pcr = ParallelChunkReader::<R> {
            prelude: &self.prelude,
            meta_chunk_queue: self.meta_chunk_queue.clone(),
            done_var: self.done_var.clone(),
        };

        pcr.start(&mut self.reader)
    }
}

/// Allows reading chunks from the underlying RAD file chunks
/// in parallel by dedicating a single thread (the one running
/// functions on this structure) to filling a work queue.
/// The queue is filled with `MetaChunk`s, which themselves
/// provide an iterator over `Chunk`s.  The `ParallelChunkReader`
/// takes a reference to the `RadPrelude` for this RAD file so
/// that it can produce `MetaChunk`s that know how to be properly
/// parsed into `Chunk`s.
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

    /// Get an `std::sync::Arc` holding the underlying `ArrayQueue` associated with this reader.
    /// This allows independent parser threads to obtain `MetaChunk`s, over which they can iterate
    /// to parse records.
    pub fn get_queue(&self) -> Arc<ArrayQueue<MetaChunk<R>>> {
        self.meta_chunk_queue.clone()
    }

    pub fn is_done(&self) -> Arc<AtomicBool> {
        self.done_var.clone()
    }
}

impl<'a, R: MappedRecord> ParallelChunkReader<'a, R> {
    /// Start this `ParallelChunkReader` processing input from the `BufRead` `br`.
    /// Note that this reader should be positioned at the start of the chunks for this
    /// RAD file, so that the prelude and file tag values have already been parsed/consumded.
    pub fn start<T: BufRead>(&mut self, br: T) -> anyhow::Result<()>
    where
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone,
    {
        if let Some(_nchunks) = self.prelude.hdr.num_chunks() {
            // fill queue known number of chunks
            println!("known number of chunks");
            fill_work_queue_until_eof(
                br,
                self.prelude,
                self.meta_chunk_queue.clone(),
                self.done_var.clone(),
            )?;
        } else {
            // fill queue unknown
            println!("unknown number of chunks");
            fill_work_queue_until_eof(
                br,
                self.prelude,
                self.meta_chunk_queue.clone(),
                self.done_var.clone(),
            )?;
        }
        Ok(())
    }
}
