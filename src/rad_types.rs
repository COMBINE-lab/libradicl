/*
 * Copyright (c) 2020-2021 Rob Patro, Avi Srivastava, Hirak Sarkar, Dongze He, Mohsen Zakeri.
 *
 * This file is part of alevin-fry
 * (see https://github.com/COMBINE-lab/alevin-fry).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

use crate::{self as libradicl, constants, io as rad_io};

use self::libradicl::utils;
use anyhow::{self, bail};
use bio_types::strand::*;
use noodles_sam as sam;
use num::cast::AsPrimitive;
use scroll::Pread;
use std::io::Write;
use std::io::{Cursor, Read};
use std::mem;

/// The [RadPrelude] groups together the [RadHeader]
/// as well as the relevant top-level [TagSection]s of the file.
/// It constitutes everything in the initial file prior to the
/// start of the first [Chunk].
pub struct RadPrelude {
    pub hdr: RadHeader,
    pub file_tags: TagSection,
    pub read_tags: TagSection,
    pub aln_tags: TagSection,
}

/// The [RadHeader] contains the relevant information about the
/// references against which the reads in this file were mapped and
/// information about the way in which mapping was performed.
pub struct RadHeader {
    pub is_paired: u8,
    pub ref_count: u64,
    pub ref_names: Vec<String>,
    pub num_chunks: u64,
}

impl Default for RadHeader {
    fn default() -> Self {
        Self::new()
    }
}

impl RadHeader {
    /// Create a new empty [RadHeader]
    pub fn new() -> Self {
        Self {
            is_paired: 0,
            ref_count: 0,
            ref_names: vec![],
            num_chunks: 0,
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
        tot_size += std::mem::size_of_val(&self.is_paired) + std::mem::size_of_val(&self.ref_count);
        // each name takes 2 bytes for the length, plus the actual
        // number of bytes required by the string itself.
        for t in self.ref_names.iter().map(|a| a.len()) {
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
            None => (self.ref_count as usize).min(10_usize),
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

#[derive(Clone, Debug)]
pub struct TagDesc {
    pub name: String,
    pub typeid: RadType,
}

#[derive(Clone, Debug)]
pub enum TagSectionLabel {
    FileTags,
    ReadTags,
    AlignmentTags,
    Unlabeled,
}

/// A [TagSection] consists of a series of [TagDesc]s that are
/// logically grouped together as tags for a specific unit
#[derive(Clone, Debug)]
pub struct TagSection {
    pub label: TagSectionLabel,
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
pub struct AlevinFryReadRecord {
    pub bc: u64,
    pub umi: u64,
    pub dirs: Vec<bool>,
    pub refs: Vec<u32>,
}

pub trait MappedRecord {
    type ReadTagTypes;
    type PeekResult;
    fn peek_record(buf: &[u8], ctx: &Self::ReadTagTypes) -> Self::PeekResult;
    fn from_bytes_with_context<T: Read>(reader:&mut T, ctx: &Self::ReadTagTypes) -> Self;
}


/// context needed to read an alevin-fry record 
/// (the types of the barcode and umi)
#[derive(Debug)]
pub struct AlevinFryRecordContext {
    pub bct: RadIntId,
    pub umit: RadIntId,
}

pub trait RecordContext {
    type Context;
    fn get_context_from_tag_section(ts: &TagSection) -> Self;
}

impl RecordContext for AlevinFryRecordContext {
    type Context = Self;
    fn get_context_from_tag_section(ts: &TagSection) -> Self { 
        let bct = ts.get_tag_type("b").expect("alevin-fry record context requires a \'b\' read-level tag");
        let umit = ts.get_tag_type("b").expect("alevin-fry record context requires a \'u\' read-level tag");
        if let (RadType::Int(x), RadType::Int(y)) = (bct, umit) {
            Self {
                bct: x,
                umit: y
            }
        } else {
            panic!("alevin-fry record context requires that b and u tags are of type RadType::Int");
        }
    }

}

impl AlevinFryRecordContext {
    pub fn from_bct_umit(bct: RadIntId, umit: RadIntId) -> Self {
        Self{ bct, umit }
    }
}

impl From<&AlevinFryRecordContext> for (RadIntId, RadIntId) {
    fn from(item: &AlevinFryRecordContext) -> Self {
        (item.bct, item.umit)
    }
}


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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RadIntId {
    U8,
    U16,
    U32,
    U64,
}

impl RadIntId {
    #[inline]
    pub fn size_of(&self) -> usize {
        match self {
            Self::U8 => mem::size_of::<u8>(),
            Self::U16 => mem::size_of::<u16>(),
            Self::U32 => mem::size_of::<u32>(),
            Self::U64 => mem::size_of::<u64>(),
        }
    }
}

impl From<u8> for RadIntId {
    fn from(x: u8) -> Self {
        match x {
            1 => Self::U8,
            2 => Self::U16,
            3 => Self::U32,
            4 => Self::U64,
            _ => panic!("Should not happen"),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RadFloatId {
    F32,
    F64,
}

impl RadFloatId {
    #[inline]
    pub fn size_of(&self) -> usize {
        match self {
            Self::F32 => mem::size_of::<f32>(),
            Self::F64 => mem::size_of::<f64>(),
        }
    }
}

impl From<u8> for RadFloatId {
    fn from(x: u8) -> Self {
        match x {
            5 => Self::F32,
            6 => Self::F64,
            _ => panic!("Should not happen"),
        }
    }
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
    #[inline]
    pub fn bytes_for_type(&self) -> usize {
        self.size_of()
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

    pub fn read_into_usize(&self, buf: &[u8]) -> usize {
        match self {
            Self::U8 => buf.pread::<u8>(0).unwrap() as usize,
            Self::U16 => buf.pread::<u16>(0).unwrap() as usize,
            Self::U32 => buf.pread::<u32>(0).unwrap() as usize,
            Self::U64 => buf.pread::<u64>(0).unwrap() as usize,
        }
    }
}

pub struct ChunkConfig {
    pub num_chunks: u64,
    pub bc_type: u8,
    pub umi_type: u8,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RadNumId {
    Int(RadIntId),
    Float(RadFloatId),
}

impl RadNumId {
    #[inline]
    pub fn size_of(&self) -> usize {
        match self {
            Self::Int(x) => x.size_of(),
            Self::Float(x) => x.size_of(),
        }
    }
}

impl From<u8> for RadNumId {
    fn from(x: u8) -> Self {
        match x {
            1 => Self::Int(RadIntId::U8),
            2 => Self::Int(RadIntId::U16),
            3 => Self::Int(RadIntId::U32),
            4 => Self::Int(RadIntId::U64),
            5 => Self::Float(RadFloatId::F32),
            6 => Self::Float(RadFloatId::F64),
            _ => panic!("Should not happen"),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RadType {
    Bool,
    Int(RadIntId),
    Float(RadFloatId),
    // holds length type and value type, but not length
    // and data themselves
    Array(RadIntId, RadNumId),
    // does not hold length, just a marker for the type
    String,
}

pub fn encode_type_tag(type_tag: RadType) -> Option<u8> {
    match type_tag {
        RadType::Bool => Some(0),
        RadType::Int(RadIntId::U8) => Some(1),
        RadType::Int(RadIntId::U16) => Some(2),
        RadType::Int(RadIntId::U32) => Some(3),
        RadType::Int(RadIntId::U64) => Some(4),
        RadType::Float(RadFloatId::F32) => Some(5),
        RadType::Float(RadFloatId::F64) => Some(6),
        RadType::Array(_, _) => Some(7),
        RadType::String => Some(8), //_ => None,
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

impl MappedRecord for AlevinFryReadRecord {
    type ReadTagTypes = AlevinFryRecordContext;
    type PeekResult = (u64, u64);
         
    #[inline]
    fn peek_record(buf: &[u8], ctx: &Self::ReadTagTypes) -> Self::PeekResult {
        let na_size = mem::size_of::<u32>();
        let bc_size = ctx.bct.bytes_for_type();

        let _na = buf.pread::<u32>(0).unwrap();

        let bc = match ctx.bct {
            RadIntId::U8 => buf.pread::<u8>(na_size).unwrap() as u64,
            RadIntId::U16 => buf.pread::<u16>(na_size).unwrap() as u64,
            RadIntId::U32 => buf.pread::<u32>(na_size).unwrap() as u64,
            RadIntId::U64 => buf.pread::<u64>(na_size).unwrap(),
        };
        let umi = match ctx.umit {
            RadIntId::U8 => buf.pread::<u8>(na_size + bc_size).unwrap() as u64,
            RadIntId::U16 => buf.pread::<u16>(na_size + bc_size).unwrap() as u64,
            RadIntId::U32 => buf.pread::<u32>(na_size + bc_size).unwrap() as u64,
            RadIntId::U64 => buf.pread::<u64>(na_size + bc_size).unwrap(),
        };
        (bc, umi)
    }
   
    #[inline]
    fn from_bytes_with_context<T: Read>(reader:&mut T, ctx: &Self::ReadTagTypes) -> Self {
        let mut rbuf = [0u8; 255];

        let (bc, umi, na) = Self::from_bytes_record_header(reader, &ctx.bct, &ctx.umit);

        let mut rec = Self {
            bc,
            umi,
            dirs: Vec::with_capacity(na as usize),
            refs: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();
            let dir = (v & utils::MASK_LOWER_31_U32) != 0;
            rec.dirs.push(dir);
            rec.refs.push(v & utils::MASK_TOP_BIT_U32);
        }
        rec
    }
}

impl AlevinFryReadRecord {
    /// Returns `true` if this [AlevinFryReadRecord] contains no references and
    /// `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    /// Obtains the next [AlevinFryReadRecord] in the stream from the reader `reader`.
    /// The barcode should be encoded with the [RadIntId] type `bct` and
    /// the umi should be encoded with the [RadIntId] type `umit`.
    pub fn from_bytes<T: Read>(reader: &mut T, bct: &RadIntId, umit: &RadIntId) -> Self {
        let mut rbuf = [0u8; 255];

        let (bc, umi, na) = Self::from_bytes_record_header(reader, bct, umit);

        let mut rec = Self {
            bc,
            umi,
            dirs: Vec::with_capacity(na as usize),
            refs: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();
            let dir = (v & utils::MASK_LOWER_31_U32) != 0;
            rec.dirs.push(dir);
            rec.refs.push(v & utils::MASK_TOP_BIT_U32);
        }
        rec
    }

    #[inline]
    pub fn from_bytes_record_header<T: Read>(
        reader: &mut T,
        bct: &RadIntId,
        umit: &RadIntId,
    ) -> (u64, u64, u32) {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf); //.pread::<u32>(0).unwrap();
        let bc = rad_io::read_into_u64(reader, bct);
        let umi = rad_io::read_into_u64(reader, umit);
        (bc, umi, na)
    }

    /// Read the next [AlevinFryReadRecord] from `reader`, but retain only those
    /// alignment records that match the prescribed orientation provided in
    /// `expected_ori` (which is a [Strand]). This function assumes the
    /// read header has already been parsed, and just reads the raw
    /// record contents consisting of the references and directions.
    #[inline]
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

    /// Read the next [AlevinFryReadRecord], including the header, from `reader`, but
    /// retain only those alignment records that match the prescribed
    /// orientation provided in `expected_ori` (which is a [Strand]).
    #[inline]
    pub fn from_bytes_keep_ori<T: Read>(
        reader: &mut T,
        bct: &RadIntId,
        umit: &RadIntId,
        expected_ori: &Strand,
    ) -> Self {
        let (bc, umi, na) = Self::from_bytes_record_header(reader, bct, umit);
        Self::from_bytes_with_header_keep_ori(reader, bc, umi, na, expected_ori)
    }
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
    pub fn from_bytes<T: Read>(reader: &mut T, ctx: &R::ReadTagTypes) -> Self {
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

    /// Peeks to the first [AlevinFryReadRecord] in the buffer `buf`, and returns
    /// the barcode and umi associated with this record.  It is assumed
    /// that there is at least one [AlevinFryReadRecord] present in the buffer.
    #[inline]
    pub fn peek_record(buf: &[u8], ctx: &R::ReadTagTypes) -> R::PeekResult { 
        R::peek_record(buf, ctx)
    }
}

impl FileTags {
    /// Reads the FileTags from the provided `reader` and return the
    /// barcode length and umi length
    pub fn from_bytes<T: Read>(reader: &mut T) -> Self {
        let mut buf = [0u8; 4];
        reader.read_exact(&mut buf).unwrap();

        Self {
            bclen: buf.pread::<u16>(0).unwrap(),
            umilen: buf.pread::<u16>(2).unwrap(),
        }
    }
}

impl From<u8> for RadType {
    fn from(x: u8) -> Self {
        match x {
            0 => RadType::Bool,
            1 => RadType::Int(RadIntId::U8),
            2 => RadType::Int(RadIntId::U16),
            3 => RadType::Int(RadIntId::U32),
            4 => RadType::Int(RadIntId::U64),
            5 => RadType::Float(RadFloatId::F32),
            6 => RadType::Float(RadFloatId::F64),
            7 => panic!("Should not happen"),
            8 => RadType::String,
            _ => panic!("Should not happen"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TagValue {
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    F32(f32),
    F64(f64),
    ArrayU8(Vec<u8>),
    ArrayU16(Vec<u16>),
    ArrayU32(Vec<u32>),
    ArrayU64(Vec<u64>),
    ArrayF32(Vec<f32>),
    ArrayF64(Vec<f64>),
    String(String),
}

// macro generalizing solution from
// https://stackoverflow.com/questions/77388769/convert-vecu8-to-vecfloat-in-rust
macro_rules! u8_to_vec_of {
    ($a:expr, $b:ty) => {
        $a.chunks_exact(std::mem::size_of::<$b>())
            .map(TryInto::try_into)
            .map(Result::unwrap)
            .map(<$b>::from_le_bytes)
            .collect()
    };
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
        let mut buf = [0u8; constants::MAX_REF_NAME_LEN];
        reader.read_exact(&mut buf[0..2])?;
        let str_len = buf.pread::<u16>(0)? as usize;

        // read str_len + 1 to get the type id that follows the string
        reader.read_exact(&mut buf[0..str_len + 1])?;
        let name = std::str::from_utf8(&buf[0..str_len])?.to_string();
        let typeid = buf.pread(str_len)?;
        // if the type id is 7, need to read the types of
        // the length and element type, otherwise just turn the
        // id into a proper RatType and we're done.
        let rad_t = match typeid {
            0..=6 | 8 => typeid.into(),
            7 => {
                reader.read_exact(&mut buf[0..2])?;
                let t1: RadIntId = buf.pread::<u8>(0)?.into();
                let t2: RadNumId = buf.pread::<u8>(1)?.into();
                RadType::Array(t1, t2)
            }
            _ => {
                bail!("{typeid} is an unrecognized RAD type id")
            }
        };

        Ok(TagDesc {
            name,
            typeid: rad_t,
        })
    }

    /// reads a [TagValue] from `reader` based on the type encoded in the
    /// current [TagDesc], and returns this [TagValue]. This function
    /// will `panic` if it cannot succesfully read the [TagValue]
    /// from `reader`.
    pub fn value_from_bytes<T: Read>(&self, reader: &mut T) -> TagValue {
        let mut small_buf = [0u8; 8];
        match self.typeid {
            RadType::Bool => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<u8>()]);
                TagValue::Bool(small_buf[0] > 1)
            }
            RadType::Int(RadIntId::U8) => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<u8>()]);
                TagValue::U8(small_buf[0])
            }
            RadType::Int(RadIntId::U16) => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<u16>()]);
                TagValue::U16(small_buf.pread::<u16>(0).unwrap())
            }
            RadType::Int(RadIntId::U32) => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<u32>()]);
                TagValue::U32(small_buf.pread::<u32>(0).unwrap())
            }
            RadType::Int(RadIntId::U64) => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<u64>()]);
                TagValue::U64(small_buf.pread::<u64>(0).unwrap())
            }
            RadType::Float(RadFloatId::F32) => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<f32>()]);
                TagValue::F32(small_buf.pread::<f32>(0).unwrap())
            }
            RadType::Float(RadFloatId::F64) => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<f64>()]);
                TagValue::F64(small_buf.pread::<f64>(0).unwrap())
            }
            RadType::Array(len_t, val_t) => {
                let _ = reader.read_exact(&mut small_buf[0..len_t.size_of()]);
                let vec_len = len_t.read_into_usize(&small_buf);
                let num_bytes = val_t.size_of() * vec_len;
                let mut data = vec![0u8; num_bytes];
                let _ = reader.read_exact(data.as_mut_slice());
                match val_t {
                    RadNumId::Int(RadIntId::U8) => TagValue::ArrayU8(data),
                    RadNumId::Int(RadIntId::U16) => TagValue::ArrayU16(u8_to_vec_of!(data, u16)),
                    RadNumId::Int(RadIntId::U32) => TagValue::ArrayU32(u8_to_vec_of!(data, u32)),
                    RadNumId::Int(RadIntId::U64) => TagValue::ArrayU64(u8_to_vec_of!(data, u64)),
                    RadNumId::Float(RadFloatId::F32) => {
                        TagValue::ArrayF32(u8_to_vec_of!(data, f32))
                    }
                    RadNumId::Float(RadFloatId::F64) => {
                        TagValue::ArrayF64(u8_to_vec_of!(data, f64))
                    }
                }
            }
            RadType::String => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<u16>()]);
                let slen = small_buf.pread::<u16>(0).unwrap();
                let mut dat: Vec<u8> = vec![0_u8; slen as usize];
                let _ = reader.read_exact(dat.as_mut_slice());
                let s = unsafe { String::from_utf8_unchecked(dat) };
                TagValue::String(s)
            }
        }
    }

    /// Returns `true` if the [RadType] component of the current [TagDesc] matches
    /// the type of the provided [TagValue] of `o` and `false` otherwise.
    #[inline]
    pub fn matches_value_type(&self, o: &TagValue) -> bool {
        match (&self.typeid, o) {
            (RadType::Bool, TagValue::Bool(_)) => true,
            (RadType::Int(RadIntId::U8), TagValue::U8(_)) => true,
            (RadType::Int(RadIntId::U16), TagValue::U16(_)) => true,
            (RadType::Int(RadIntId::U32), TagValue::U32(_)) => true,
            (RadType::Int(RadIntId::U64), TagValue::U64(_)) => true,
            (RadType::Float(RadFloatId::F32), TagValue::F32(_)) => true,
            (RadType::Float(RadFloatId::F64), TagValue::F64(_)) => true,
            (RadType::Array(_, RadNumId::Int(RadIntId::U8)), TagValue::ArrayU8(_)) => true,
            (RadType::Array(_, RadNumId::Int(RadIntId::U16)), TagValue::ArrayU16(_)) => true,
            (RadType::Array(_, RadNumId::Int(RadIntId::U32)), TagValue::ArrayU32(_)) => true,
            (RadType::Array(_, RadNumId::Int(RadIntId::U64)), TagValue::ArrayU64(_)) => true,
            (RadType::Array(_, RadNumId::Float(RadFloatId::F32)), TagValue::ArrayF32(_)) => true,
            (RadType::Array(_, RadNumId::Float(RadFloatId::F64)), TagValue::ArrayF64(_)) => true,
            (RadType::String, TagValue::String(_)) => true,
            (_, _) => false,
        }
    }
}

/// This type represents a mapping from [TagDesc]s to a corresponding set of
/// values conforming to these descriptions (i.e. in terms of types). The
/// [TagMap] allows you to fetch the value for a specific tag by name or index, or
/// to add values to a corresponding set of descriptions.
#[derive(Debug)]
pub struct TagMap<'a> {
    keys: &'a [TagDesc],
    dat: Vec<TagValue>,
}

impl<'a> TagMap<'a> {
    /// Create a new TagMap whose set of keys is determined by
    /// the provided `keyset`. This will have one value slot for
    /// each provided key.
    pub fn with_keyset(keyset: &'a [TagDesc]) -> Self {
        Self {
            keys: keyset,
            dat: Vec::with_capacity(keyset.len()),
        }
    }

    /// Try to add the next tag value. If there is space and the type
    /// matches, add it and return `true`, otherwise return `false`.
    pub fn add_checked(&mut self, val: TagValue) -> bool {
        let next_idx = self.dat.len();
        if next_idx >= self.keys.len() || !self.keys[next_idx].matches_value_type(&val) {
            false
        } else {
            self.dat.push(val);
            true
        }
    }

    /// add the next TagValue to the data for this TagMap.
    /// This function doesn't check if the type is correct or
    /// if too many tag values have been added. It should
    /// only be used when one is certain that the next tag value
    /// appropriately matches the next available key.
    pub fn add(&mut self, val: TagValue) {
        self.dat.push(val);
    }

    /// get the value for the tag associated with the name `key`, returns
    /// Some(&TagValue) for the appropriate tag if it exists, and None otherwise.
    pub fn get(&self, key: &str) -> Option<&TagValue> {
        for (k, val) in self.keys.iter().zip(self.dat.iter()) {
            if k.name == key {
                return Some(val);
            }
        }
        None
    }

    /// get the value for the tag at index `idx` returns Some(&TagValue) if `idx`
    /// is in bounds and None otherwise.
    pub fn get_at_index(&self, idx: usize) -> Option<&TagValue> {
        self.dat.get(idx)
    }
}

impl<'a> std::ops::Index<usize> for TagMap<'a> {
    type Output = TagValue;
    /// Returns a reference to the [TagValue] in the [TagMap] at the 
    /// provided `index`, panics if `index` is out of bounds.
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.dat[index]
    }
}

impl TagSection {
    /// Attempts to read a [TagSection] from the provided `reader`. If the
    /// `reader` is positioned at the start of a valid [TagSection], then this
    /// [TagSection] is returned.  Otherwise, a description of the error is returned
    /// via an [anyhow::Error].
    pub fn from_bytes<T: Read>(reader: &mut T) -> anyhow::Result<Self> {
        Self::from_bytes_with_label(reader, TagSectionLabel::Unlabeled)
    }

    /// Attempts to read a [TagSection] from the provided `reader`. If the
    /// `reader` is positioned at the start of a valid [TagSection], then this
    /// [TagSection] is returned.  Otherwise, a description of the error is returned
    /// via an [anyhow::Error]. The returned [TagSection] will be labeled with the
    /// provided `label`.
    pub fn from_bytes_with_label<T: Read>(
        reader: &mut T,
        label: TagSectionLabel,
    ) -> anyhow::Result<Self> {
        let mut buf = [0u8; 2];
        reader.read_exact(&mut buf)?;
        let num_tags = buf.pread::<u16>(0)? as usize;

        let mut ts = Self {
            label,
            tags: Vec::with_capacity(num_tags),
        };

        for _ in 0..num_tags {
            ts.tags.push(TagDesc::from_bytes(reader)?);
        }
        Ok(ts)
    }

    pub fn parse_tags_from_bytes<T: Read>(&self, reader: &mut T) -> anyhow::Result<TagMap> {
        // loop over all of the tag descriptions in this section, and parse a
        // tag value for each.
        //let mut tv = Vec::<TagValue>::new();
        let mut tm = TagMap::with_keyset(&self.tags);
        for tag_desc in &self.tags {
            tm.add(tag_desc.value_from_bytes(reader));
        }
        Ok(tm)
    }

    pub fn parse_tags_from_bytes_checked<T: Read>(&self, reader: &mut T) -> anyhow::Result<TagMap> {
        // loop over all of the tag descriptions in this section, and parse a
        // tag value for each.
        //let mut tv = Vec::<TagValue>::new();
        let mut tm = TagMap::with_keyset(&self.tags);
        for tag_desc in &self.tags {
            if !tm.add_checked(tag_desc.value_from_bytes(reader)) {
                panic!("Tried to read value for non-matching type");
            }
        }
        Ok(tm)
    }

    pub fn get_tag_type(&self, name: &str) -> Option<RadType> {
        for td in &self.tags {
            if name == td.name {
                return Some(td.typeid);
            }
        }
        None
    }
}

impl RadPrelude {
    pub fn from_bytes<T: Read>(reader: &mut T) -> anyhow::Result<Self> {
        let hdr = RadHeader::from_bytes(reader)?;
        let file_tags = TagSection::from_bytes_with_label(reader, TagSectionLabel::FileTags)?;
        let read_tags = TagSection::from_bytes_with_label(reader, TagSectionLabel::ReadTags)?;
        let aln_tags = TagSection::from_bytes_with_label(reader, TagSectionLabel::AlignmentTags)?;

        //let file_tag_vals = file_tags.parse_tags_from_bytes(reader)?;
        //println!("file-level tag values: {:?}", file_tag_vals);
        
        Ok(Self {
            hdr,
            file_tags,
            read_tags,
            aln_tags,
        })
    }

    pub fn summary(&self, num_refs: Option<usize>) -> anyhow::Result<String> {
        use std::fmt::Write as _;
        let mut s = self.hdr.summary(num_refs)?;
        writeln!(&mut s, "[[{:?}]]", self.file_tags)?;
        writeln!(&mut s, "[[{:?}]]", self.read_tags)?;
        writeln!(&mut s, "[[{:?}]]", self.aln_tags)?;
        //writeln!(&mut s, "file-level tag values [{:?}]", self.file_tag_vals)?;
        Ok(s)
    }
}

#[cfg(test)]
mod tests {
    use crate::rad_types::RadType;
    use crate::rad_types::{RadIntId, RadNumId, TagSection, TagSectionLabel, TagValue};
    use std::io::Write;

    use super::TagDesc;
    #[test]
    fn can_parse_simple_tag_desc() {
        let mut buf = Vec::<u8>::new();
        let tag_name = b"mytag";
        let _ = buf.write_all(&5_u16.to_ne_bytes());
        let _ = buf.write_all(tag_name);
        let tag_type = 4_u8;
        let _ = buf.write_all(&tag_type.to_ne_bytes());

        let desc = TagDesc::from_bytes(&mut buf.as_slice()).unwrap();
        assert_eq!(desc.name, "mytag");
        assert_eq!(desc.typeid, RadType::Int(RadIntId::U64));
    }

    #[test]
    fn can_parse_array_tag_desc() {
        let mut buf = Vec::<u8>::new();
        let tag_name = b"mytag";
        let _ = buf.write_all(&5_u16.to_ne_bytes());
        let _ = buf.write_all(tag_name);
        let tag_type = 7_u8;
        let _ = buf.write_all(&tag_type.to_ne_bytes());
        // length type
        let _ = buf.write_all(&1_u8.to_ne_bytes());
        // element type
        let _ = buf.write_all(&2_u8.to_ne_bytes());

        let desc = TagDesc::from_bytes(&mut buf.as_slice()).unwrap();
        assert_eq!(desc.name, "mytag");
        assert_eq!(
            desc.typeid,
            RadType::Array(RadIntId::U8, RadNumId::Int(RadIntId::U16))
        );
    }

    #[test]
    fn can_parse_tag_values_from_section() {
        let mut buf = Vec::<u8>::new();
        let tag_name = b"mytag";
        let _ = buf.write_all(&5_u16.to_ne_bytes());
        let _ = buf.write_all(tag_name);
        let tag_type = 7_u8;
        let _ = buf.write_all(&tag_type.to_ne_bytes());
        // length type
        let _ = buf.write_all(&1_u8.to_ne_bytes());
        // element type
        let _ = buf.write_all(&2_u8.to_ne_bytes());

        let desc = TagDesc::from_bytes(&mut buf.as_slice()).unwrap();
        assert_eq!(desc.name, "mytag");
        assert_eq!(
            desc.typeid,
            RadType::Array(RadIntId::U8, RadNumId::Int(RadIntId::U16))
        );

        buf.clear();
        let tag_name = b"stringtag";
        let _ = buf.write_all(&9_u16.to_ne_bytes());
        let _ = buf.write_all(tag_name);
        // type id
        let _ = buf.write_all(&8_u8.to_ne_bytes());
        let desc_str = TagDesc::from_bytes(&mut buf.as_slice()).unwrap();

        let tag_sec = TagSection {
            label: TagSectionLabel::FileTags,
            tags: vec![desc, desc_str],
        };

        buf.clear();
        let _ = buf.write_all(&3_u8.to_ne_bytes());
        let _ = buf.write_all(&1_u16.to_ne_bytes());
        let _ = buf.write_all(&2_u16.to_ne_bytes());
        let _ = buf.write_all(&3_u16.to_ne_bytes());

        let _ = buf.write_all(&6_u16.to_ne_bytes());
        let _ = buf.write_all(b"hi_rad");

        let map = tag_sec.parse_tags_from_bytes(&mut buf.as_slice()).unwrap();
        assert_eq!(
            map.get("mytag").unwrap(),
            &TagValue::ArrayU16(vec![1, 2, 3])
        );
        assert_eq!(
            map.get("stringtag").unwrap(),
            &TagValue::String(String::from("hi_rad"))
        );

        assert_eq!(
            map.get_at_index(0).unwrap(),
            &TagValue::ArrayU16(vec![1, 2, 3])
        );
        assert_eq!(
            map.get_at_index(1).unwrap(),
            &TagValue::String(String::from("hi_rad"))
        );

        let map = tag_sec
            .parse_tags_from_bytes_checked(&mut buf.as_slice())
            .unwrap();
        assert_eq!(
            map.get("mytag").unwrap(),
            &TagValue::ArrayU16(vec![1, 2, 3])
        );
        assert_eq!(
            map.get("stringtag").unwrap(),
            &TagValue::String(String::from("hi_rad"))
        );

        assert_eq!(
            map.get_at_index(0).unwrap(),
            &TagValue::ArrayU16(vec![1, 2, 3])
        );
        assert_eq!(
            map.get_at_index(1).unwrap(),
            &TagValue::String(String::from("hi_rad"))
        );

        assert_eq!(map[0], TagValue::ArrayU16(vec![1, 2, 3]));
        assert_eq!(map[1], TagValue::String(String::from("hi_rad")));
    }
}
