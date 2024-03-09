/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Types and functions that primarily deal with the reading and writing of
//! data [Chunk]s in the RAD file.

use crate::{self as libradicl};
use libradicl::record::MappedRecord;
use scroll::Pread;
use std::io::Write;
use std::io::{Cursor, Read};

#[derive(Debug)]
pub struct Chunk<T: MappedRecord> {
    pub nbytes: u32,
    pub nrec: u32,
    pub reads: Vec<T>,
}

/// A [CorrectedCbChunk] represents a [Chunk] of RAD records
/// that share the same underlying corrected cell barcode
/// `corrected_bc`.
#[derive(Debug)]
#[allow(dead_code)]
pub struct CorrectedCbChunk {
    pub(crate) remaining_records: u32,
    pub(crate) corrected_bc: u64,
    pub(crate) nrec: u32,
    pub(crate) data: Cursor<Vec<u8>>,
}

impl CorrectedCbChunk {
    pub fn from_label_and_counter(corrected_bc_in: u64, num_remain: u32) -> CorrectedCbChunk {
        let mut cc = CorrectedCbChunk {
            remaining_records: num_remain,
            corrected_bc: corrected_bc_in,
            nrec: 0u32,
            data: Cursor::new(Vec::<u8>::with_capacity((num_remain * 24) as usize)),
        };
        let dummy = 0u32;
        cc.data.write_all(&dummy.to_le_bytes()).unwrap();
        cc.data.write_all(&dummy.to_le_bytes()).unwrap();
        cc
    }
}

#[deprecated(
    since = "0.9.0",
    note = "This type is deprecated as it's name implies it is general, but it is specalized for the single-cell context. \
            This is replaced more generally by the ChunkContext trait and individual structures implementing this trait \
            For specific RAD file types."
)]
pub struct ChunkConfig {
    pub num_chunks: u64,
    pub bc_type: u8,
    pub umi_type: u8,
}

pub trait ChunkContext {}

pub struct AlevinFryChunkContext {
    pub num_chunks: u64,
    pub bc_type: u8,
    pub umi_type: u8,
}

impl ChunkContext for AlevinFryChunkContext {}

impl<R: MappedRecord> Chunk<R> {
    /// Read the header of the next [Chunk] from the provided `reader`. This
    /// function returns a tuple representing the number of bytes and number of
    /// records, respectively, in the chunk.
    #[inline]
    pub fn read_header<T: Read>(reader: &mut T) -> (u32, u32) {
        let mut buf = [0u8; 8];
        reader.read_exact(&mut buf).unwrap();
        let nbytes = buf.pread::<u32>(0).unwrap();
        let nrec = buf.pread::<u32>(4).unwrap();
        (nbytes, nrec)
    }

    /// Read the next [Chunk] from the provided reader and return it.
    #[inline]
    pub fn from_bytes_with_tags<T: Read>(_reader: &mut T, _ctx: &R::ParsingContext) -> Self {
        // think about how best to implement this, and where to store the tags
        // (a) should the tags be part of the record, or stored externally (e.g. in a parallel
        // Vec)?
        // (b) should the tags be read into an "unparsed" structure (e.g. a binary blob) and
        // then parsed on demand, or parsed as they are read here?
        // (c) What's the best mechanism to allow the user to access the tags?
        todo!("Should read and store the optional tags associated with each record.");
    }

    /// Read the next [Chunk] from the provided reader and return it.
    #[inline]
    pub fn from_bytes<T: Read>(reader: &mut T, ctx: &R::ParsingContext) -> Self {
        let (nbytes, nrec) = Self::read_header(reader);
        let mut c = Self {
            nbytes,
            nrec,
            reads: Vec::<R>::with_capacity(nrec as usize),
        };

        for _ in 0..(nrec as usize) {
            c.reads.push(R::from_bytes_with_context(reader, ctx));
        }

        c
    }

    /// Peeks to the first [libradicl::record::AlevinFryReadRecord] in the buffer `buf`, and returns
    /// the barcode and umi associated with this record.  It is assumed
    /// that there is at least one [libradicl::record::AlevinFryReadRecord] present in the buffer.
    #[inline]
    pub fn peek_record(buf: &[u8], ctx: &R::ParsingContext) -> R::PeekResult {
        R::peek_record(buf, ctx)
    }
}
