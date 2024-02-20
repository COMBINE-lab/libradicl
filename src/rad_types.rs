/*
 * Copyright (c) 2020-2021 Rob Patro, Avi Srivastava, Hirak Sarkar, Dongze He, Mohsen Zakeri.
 *
 * This file is part of alevin-fry
 * (see https://github.com/COMBINE-lab/alevin-fry).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

use crate::{self as libradicl, constants};

use self::libradicl::utils;

use anyhow;
use bio_types::strand::*;
use num::cast::AsPrimitive;
use noodles_sam as sam;
use scroll::Pread;
use std::io::Write;
use std::io::{Cursor, Read};
use std::mem;

pub struct RadHeader {
    pub is_paired: u8,
    pub ref_count: u64,
    pub ref_names: Vec<String>,
    pub num_chunks: u64,
}

#[derive(Debug)]
pub struct TagDesc {
    pub name: String,
    pub typeid: u8,
}

#[derive(Debug)]
pub struct TagSection {
    pub tags: Vec<TagDesc>,
}

// The below are currently hard-coded
// until we decide how to solve this
// generally
#[derive(Debug)]
pub struct FileTags {
    pub bclen: u16,
    pub umilen: u16,
}
#[derive(Debug)]
pub struct ReadRecord {
    pub bc: u64,
    pub umi: u64,
    pub dirs: Vec<bool>,
    pub refs: Vec<u32>,
}
#[derive(Debug)]
pub struct Chunk {
    pub nbytes: u32,
    pub nrec: u32,
    pub reads: Vec<ReadRecord>,
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

#[derive(Copy, Clone)]
pub enum RadIntId {
    U8,
    U16,
    U32,
    U64,
}

pub trait PrimitiveInteger:
    AsPrimitive<u8>
    + AsPrimitive<u16>
    + AsPrimitive<u32>
    + AsPrimitive<u64>
    + AsPrimitive<usize>
    + AsPrimitive<i8>
    + AsPrimitive<i16>
    + AsPrimitive<i32>
    + AsPrimitive<i64>
    + AsPrimitive<isize>
{
}

impl<
        T: AsPrimitive<u8>
            + AsPrimitive<u16>
            + AsPrimitive<u32>
            + AsPrimitive<u64>
            + AsPrimitive<usize>
            + AsPrimitive<i8>
            + AsPrimitive<i16>
            + AsPrimitive<i32>
            + AsPrimitive<i64>
            + AsPrimitive<isize>,
    > PrimitiveInteger for T
{
}

impl RadIntId {
    pub fn bytes_for_type(&self) -> usize {
        match self {
            Self::U8 => std::mem::size_of::<u8>(),
            Self::U16 => std::mem::size_of::<u16>(),
            Self::U32 => std::mem::size_of::<u32>(),
            Self::U64 => std::mem::size_of::<u64>(),
        }
    }

    /// Based on the variant of the current enum, write the value `v`
    /// out using `owrite`.  Here, `v` is bound to be some primitive
    /// integer type.  It is the responsibility of the caller to ensure
    /// that, if `v` is wider than the enum type on which this function
    /// is called, no important information is lost by discarding the higher
    /// order bits.
    pub fn write_to<T: PrimitiveInteger, U: Write>(
        &self,
        v: T,
        owriter: &mut U,
    ) -> std::io::Result<()> {
        match self {
            Self::U8 => {
                let vo: u8 = v.as_();
                owriter.write_all(&vo.to_le_bytes())
            }
            Self::U16 => {
                let vo: u16 = v.as_();
                owriter.write_all(&vo.to_le_bytes())
            }
            Self::U32 => {
                let vo: u32 = v.as_();
                owriter.write_all(&vo.to_le_bytes())
            }
            Self::U64 => {
                let vo: u64 = v.as_();
                owriter.write_all(&vo.to_le_bytes())
            }
        }
    }
}

pub struct ChunkConfig {
    pub num_chunks: u64,
    pub bc_type: u8,
    pub umi_type: u8,
}

#[derive(Copy, Clone)]
pub enum RadType {
    Bool,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

pub fn encode_type_tag(type_tag: RadType) -> Option<u8> {
    match type_tag {
        RadType::Bool => Some(0),
        RadType::U8 => Some(1),
        RadType::U16 => Some(2),
        RadType::U32 => Some(3),
        RadType::U64 => Some(4),
        RadType::F32 => Some(5),
        RadType::F64 => Some(6),
        //_ => None,
    }
}

pub fn decode_int_type_tag(type_id: u8) -> Option<RadIntId> {
    match type_id {
        1 => Some(RadIntId::U8),
        2 => Some(RadIntId::U16),
        3 => Some(RadIntId::U32),
        4 => Some(RadIntId::U64),
        _ => None,
    }
}

fn read_into_u64<T: Read>(reader: &mut T, rt: &RadIntId) -> u64 {
    let mut rbuf = [0u8; 8];

    let v: u64 = match rt {
        RadIntId::U8 => {
            reader.read_exact(&mut rbuf[0..1]).unwrap();
            rbuf.pread::<u8>(0).unwrap() as u64
        }
        RadIntId::U16 => {
            reader.read_exact(&mut rbuf[0..2]).unwrap();
            rbuf.pread::<u16>(0).unwrap() as u64
        }
        RadIntId::U32 => {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            rbuf.pread::<u32>(0).unwrap() as u64
        }
        RadIntId::U64 => {
            reader.read_exact(&mut rbuf[0..8]).unwrap();
            rbuf.pread::<u64>(0).unwrap()
        }
    };
    v
}

impl ReadRecord {
    pub fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    pub fn from_bytes<T: Read>(reader: &mut T, bct: &RadIntId, umit: &RadIntId) -> Self {
        let mut rbuf = [0u8; 255];

        reader.read_exact(&mut rbuf[0..4]).unwrap();
        let na = rbuf.pread::<u32>(0).unwrap();
        let bc = read_into_u64(reader, bct);
        let umi = read_into_u64(reader, umit);

        let mut rec = Self {
            bc,
            umi,
            dirs: Vec::with_capacity(na as usize),
            refs: Vec::with_capacity(na as usize),
        };

        //println!("number of records : {:?}",na);

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();
            let dir = (v & utils::MASK_LOWER_31_U32) != 0;
            rec.dirs.push(dir);
            rec.refs.push(v & utils::MASK_TOP_BIT_U32);
        }

        rec
    }

    pub fn from_bytes_record_header<T: Read>(
        reader: &mut T,
        bct: &RadIntId,
        umit: &RadIntId,
    ) -> (u64, u64, u32) {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf); //.pread::<u32>(0).unwrap();
        let bc = read_into_u64(reader, bct);
        let umi = read_into_u64(reader, umit);
        (bc, umi, na)
    }

    pub fn from_bytes_with_header_keep_ori<T: Read>(
        reader: &mut T,
        bc: u64,
        umi: u64,
        na: u32,
        expected_ori: &Strand,
    ) -> Self {
        let mut rbuf = [0u8; 255];
        let mut rec = Self {
            bc,
            umi,
            dirs: Vec::with_capacity(na as usize),
            refs: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();

            // fw if the leftmost bit is 1, otherwise rc
            let strand = if (v & utils::MASK_LOWER_31_U32) > 0 {
                Strand::Forward
            } else {
                Strand::Reverse
            };

            if expected_ori.same(&strand) || expected_ori.is_unknown() {
                rec.refs.push(v & utils::MASK_TOP_BIT_U32);
            }
        }

        // make sure these are sorted in this step.
        rec.refs.sort_unstable();
        rec
    }

    pub fn from_bytes_keep_ori<T: Read>(
        reader: &mut T,
        bct: &RadIntId,
        umit: &RadIntId,
        expected_ori: &Strand,
    ) -> Self {
        let mut rbuf = [0u8; 255];

        reader.read_exact(&mut rbuf[0..4]).unwrap();
        let na = rbuf.pread::<u32>(0).unwrap();

        let bc = read_into_u64(reader, bct);
        let umi = read_into_u64(reader, umit);

        let mut rec = Self {
            bc,
            umi,
            dirs: Vec::with_capacity(na as usize),
            refs: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();

            // fw if the leftmost bit is 1, otherwise rc
            let strand = if (v & utils::MASK_LOWER_31_U32) > 0 {
                Strand::Forward
            } else {
                Strand::Reverse
            };

            if expected_ori.same(&strand) || expected_ori.is_unknown() {
                rec.refs.push(v & utils::MASK_TOP_BIT_U32);
            }
        }

        // make sure these are sorted in this step.
        rec.refs.sort_unstable();
        rec
    }
}

impl Chunk {
    pub fn read_header<T: Read>(reader: &mut T) -> (u32, u32) {
        let mut buf = [0u8; 8];

        reader.read_exact(&mut buf).unwrap();
        let nbytes = buf.pread::<u32>(0).unwrap();
        let nrec = buf.pread::<u32>(4).unwrap();
        (nbytes, nrec)
    }

    pub fn from_bytes<T: Read>(reader: &mut T, bct: &RadIntId, umit: &RadIntId) -> Self {
        let mut buf = [0u8; 8];

        reader.read_exact(&mut buf).unwrap();
        let nbytes = buf.pread::<u32>(0).unwrap();
        let nrec = buf.pread::<u32>(4).unwrap();
        let mut c = Self {
            nbytes,
            nrec,
            reads: Vec::with_capacity(nrec as usize),
        };

        for _ in 0..(nrec as usize) {
            c.reads.push(ReadRecord::from_bytes(reader, bct, umit));
        }

        c
    }

    /// peeks to the first record in the buffer `buf`, and returns
    /// the barcode and umi associated with this record.  It is assumed
    /// that there is at least one record present in the buffer.
    pub fn peek_record(buf: &[u8], bct: &RadIntId, umit: &RadIntId) -> (u64, u64) {
        let na_size = mem::size_of::<u32>();
        let bc_size = bct.bytes_for_type();

        let _na = buf.pread::<u32>(0).unwrap();

        let bc = match bct {
            RadIntId::U8 => buf.pread::<u8>(na_size).unwrap() as u64,
            RadIntId::U16 => buf.pread::<u16>(na_size).unwrap() as u64,
            RadIntId::U32 => buf.pread::<u32>(na_size).unwrap() as u64,
            RadIntId::U64 => buf.pread::<u64>(na_size).unwrap(),
        };
        let umi = match umit {
            RadIntId::U8 => buf.pread::<u8>(na_size + bc_size).unwrap() as u64,
            RadIntId::U16 => buf.pread::<u16>(na_size + bc_size).unwrap() as u64,
            RadIntId::U32 => buf.pread::<u32>(na_size + bc_size).unwrap() as u64,
            RadIntId::U64 => buf.pread::<u64>(na_size + bc_size).unwrap(),
        };
        (bc, umi)
    }
}

impl FileTags {
    pub fn from_bytes<T: Read>(reader: &mut T) -> Self {
        let mut buf = [0u8; 4];
        reader.read_exact(&mut buf).unwrap();

        Self {
            bclen: buf.pread::<u16>(0).unwrap(),
            umilen: buf.pread::<u16>(2).unwrap(),
        }
    }
}

impl TagDesc {
    /// Attempts to read a [TagDesc] from the provided `reader`. If the 
    /// `reader` is positioned at the start of a valid [TagDesc], then this 
    /// [TagDesc] is returned.  Otherwise, a description of the error is returned 
    /// via an [anyhow::Error].
    pub fn from_bytes<T: Read>(reader: &mut T) -> anyhow::Result<TagDesc> {
        // space for the string length (1 byte)
        // the longest string possible (255 char)
        // and the typeid
        let mut buf = [0u8; 257];
        reader.read_exact(&mut buf[0..2])?;
        let str_len = buf.pread::<u16>(0)? as usize;

        // read str_len + 1 to get the type id that follows the string
        reader.read_exact(&mut buf[0..str_len + 1])?;
        Ok(TagDesc {
            name: std::str::from_utf8(&buf[0..str_len])?.to_string(),
            typeid: buf.pread(str_len)?,
        })
    }
}

impl TagSection {
    /// Attempts to read a [TagSection] from the provided `reader`. If the 
    /// `reader` is positioned at the start of a valid [TagSection], then this 
    /// [TagSection] is returned.  Otherwise, a description of the error is returned 
    /// via an [anyhow::Error].
    pub fn from_bytes<T: Read>(reader: &mut T) -> anyhow::Result<TagSection> {
        let mut buf = [0u8; 2];
        reader.read_exact(&mut buf)?;
        let num_tags = buf.pread::<u16>(0)? as usize;

        let mut ts = TagSection {
            tags: Vec::with_capacity(num_tags),
        };

        for _ in 0..num_tags {
            ts.tags.push(TagDesc::from_bytes(reader)?);
        }
        Ok(ts)
    }
}

impl RadHeader {
    /// Create a new empty [RadHeader]
    pub fn new() -> Self {
        Self {
            is_paired: 0,
            ref_count: 0,
            ref_names: vec![],
            num_chunks: 0
        }
    }

    /// Create and return a new [RadHeader] by reading the contents of the 
    /// `reader`. If the reader is positioned such that a valid [RadHeader] comes 
    /// next, then this function returns [Ok(RadHeader)], otherwise, it returns 
    /// an [anyhow::Error] explaining the failure to parse the [RadHeader].
    pub fn from_bytes<T: Read>(reader: &mut T) -> anyhow::Result<RadHeader> {
        let mut rh = RadHeader::new();

        // size of the longest allowable string.
        let mut buf = [0u8; constants::MAX_REF_NAME_LEN];
        reader.read_exact(&mut buf[0..9])?;
        rh.is_paired = buf.pread(0)?;
        rh.ref_count = buf.pread::<u64>(1)?;

        // we know how many names we will read in.
        rh.ref_names.reserve_exact(rh.ref_count as usize);

        let mut num_read = 0u64;
        while num_read < rh.ref_count {
            // the length of the string
            reader.read_exact(&mut buf[0..2])?;
            let l: usize = buf.pread::<u16>(0)? as usize;
            // the string itself
            reader.read_exact(&mut buf[0..l])?;
            rh.ref_names
                .push(std::str::from_utf8(&buf[0..l])?.to_string());
            num_read += 1;
        }

        reader.read_exact(&mut buf[0..8])?;
        rh.num_chunks = buf.pread::<u64>(0)?;
        Ok(rh)
    }

    /// Create and return a [RadHeader] from the provided BAM/SAM header 
    /// (represented by the noodles [sam::Header] `header`).  
    /// **Note**: The returned [RadHeader] will *not* have a value for the `num_chunks`
    /// field, which will remain set at 0, nor will it set a meaningful value for the 
    /// `is_paried` flag, since the SAM/BAM header itself doesn't encode this information.
    pub fn from_bam_header(header: &sam::Header) -> RadHeader {
        let mut rh = RadHeader {
            is_paired: 0,
            ref_count: 0,
            ref_names: vec![],
            num_chunks: 0,
        };

        let ref_seqs = header.reference_sequences();
        rh.ref_count = ref_seqs.len() as u64;
        // we know how many names we will read in.
        rh.ref_names.reserve_exact(rh.ref_count as usize);
        for (k, _v) in ref_seqs.iter() {
            rh.ref_names.push(k.to_string());
        }
        rh
    }

    /// Returns the size, in bytes, that this [RadHeader] will take 
    /// if written to an output stream.
    pub fn get_size(&self) -> usize {
        let mut tot_size = 0usize;
        tot_size += std::mem::size_of_val(&self.is_paired) + 
            std::mem::size_of_val(&self.ref_count);
        // each name takes 2 bytes for the length, plus the actual 
        // number of bytes required by the string itself.
        for (_i, t) in self.ref_names.iter().map(|a| a.len()).enumerate() {
            tot_size += std::mem::size_of::<u16>() + t;
        }
        tot_size += std::mem::size_of_val(&self.num_chunks);
        tot_size
    }

    pub fn summary(&self, num_refs: Option<usize>) -> anyhow::Result<String> {
        use std::fmt::Write as _;
        let mut s = String::new();
        writeln!(&mut s, "RadHeader {{")?;
        writeln!(&mut s, "is_paired: {}", self.is_paired)?;
        writeln!(&mut s, "ref_count: {}", self.ref_count)?;
        
        let refs_to_print = match num_refs {
            Some(rcount) => rcount.min(self.ref_count as usize),
            None => (self.ref_count as usize).min(10_usize) 
        };

        for rn in self.ref_names.iter().take(refs_to_print) {
            writeln!(&mut s, "  ref: {}", rn)?;
        }
        writeln!(&mut s, "  ...")?;

        writeln!(&mut s, "num_chunks: {}", self.num_chunks)?;
        writeln!(&mut s, "}}")?;
        Ok(s)
    }
}

pub fn write_str_bin(v: &str, type_id: &RadIntId, owriter: &mut Cursor<Vec<u8>>) {
    match type_id {
        RadIntId::U8 => {
            owriter
                .write_all(&(v.len() as u8).to_le_bytes())
                .expect("coudn't write to output file");
        }
        RadIntId::U16 => {
            owriter
                .write_all(&(v.len() as u16).to_le_bytes())
                .expect("coudn't write to output file");
        }
        RadIntId::U32 => {
            owriter
                .write_all(&(v.len() as u32).to_le_bytes())
                .expect("coudn't write to output file");
        }
        RadIntId::U64 => {
            owriter
                .write_all(&(v.len() as u64).to_le_bytes())
                .expect("coudn't write to output file");
        }
    }
    owriter
        .write_all(v.as_bytes())
        .expect("coudn't write to output file");
}
