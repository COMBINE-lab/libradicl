use crate::{self as libradicl};
use libradicl::record::MappedRecord;
use scroll::Pread;
use std::io::{Cursor, Read};

#[derive(Debug)]
pub struct Chunk<T: MappedRecord> {
    pub nbytes: u32,
    pub nrec: u32,
    pub reads: Vec<T>,
}

#[derive(Debug)]
#[allow(dead_code)]
pub struct CorrectedCbChunk {
    pub(crate) remaining_records: u32,
    pub(crate) corrected_bc: u64,
    pub(crate) nrec: u32,
    pub(crate) data: Cursor<Vec<u8>>, /*,
                                      umis: Vec<u64>,
                                      ref_offsets: Vec<u32>,
                                      ref_ids: Vec<u32>,
                                      */
}

pub struct ChunkConfig {
    pub num_chunks: u64,
    pub bc_type: u8,
    pub umi_type: u8,
}

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
