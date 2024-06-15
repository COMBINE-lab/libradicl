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

pub struct MetaChunk<R: MappedRecord> {
    first_chunk_index: usize,
    num_sub_chunks: usize,
    num_bytes: u32,
    num_records: u32,
    chunk_blob: Vec<u8>,
    record_context: <R as MappedRecord>::ParsingContext,
}

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
}

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

/// Allows reading chunks from the underlying RAD file
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
    // *NOTE*: The field below is a temporary hack, and shouldn't
    // be necessary once the implementations converge.
    pub header_incl_in_bytes: bool,
}

impl<'a, R: MappedRecord> ParallelChunkReader<'a, R> {
    pub fn new(
        prelude: &'a RadPrelude,
        num_consumers: std::num::NonZeroUsize,
        header_incl_in_bytes: bool,
    ) -> Self {
        Self {
            prelude,
            meta_chunk_queue: Arc::new(ArrayQueue::<MetaChunk<R>>::new(num_consumers.get() * 4)),
            header_incl_in_bytes,
        }
    }

    pub fn get_queue(&self) -> Arc<ArrayQueue<MetaChunk<R>>> {
        self.meta_chunk_queue.clone()
    }
}

impl<'a, R: MappedRecord> ParallelChunkReader<'a, R> {
    pub fn start<T: BufRead>(&mut self, done_var: Arc<AtomicBool>, br: T) -> anyhow::Result<()>
    where
        <R as MappedRecord>::ParsingContext: RecordContext,
        <R as MappedRecord>::ParsingContext: Clone,
    {
        if let Some(_nchunks) = self.prelude.hdr.num_chunks() {
            // fill queue known number of chunks
            println!("known number of chunks");
            self.fill_work_queue_until_eof(done_var, br)?;
        } else {
            // fill queue unknown
            println!("unknown number of chunks");
            self.fill_work_queue_until_eof(done_var, br)?;
        }
        Ok(())
    }

    fn fill_work_queue_until_eof<T: BufRead>(
        &mut self,
        done_var: Arc<AtomicBool>,
        mut br: T,
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
        let record_context = self
            .prelude
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
                nbytes_chunk = nc + if self.header_incl_in_bytes { 0 } else { 8 };
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
                while let Err(t) = self.meta_chunk_queue.push(bclone) {
                    bclone = t;
                    // no point trying to push if the queue is full
                    while self.meta_chunk_queue.is_full() {}
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
}
