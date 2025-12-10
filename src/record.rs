/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! This module contains types and traits related to RAD records, including the
//! traits for [MappedRecord]s and [RecordContext]s. It also defines concrete types
//! implementing these traits for `alevin-fry` and `piscem-infer`.

use crate::io::{
    NewI128, NewI16, NewI32, NewI64, NewI8, NewU128, NewU16, NewU32, NewU64, NewU8, TryWrapper,
};
use crate::{
    io as rad_io,
    rad_types::{
        MappedFragmentOrientation, MappingType, PrimitiveInteger, RadIntId, RadType, 
        TagSection, TagValue,
    },
    utils,
};
use anyhow::{self, bail, Context};
use bio_types::strand::*;
use scroll::Pread;
use std::io::{Read, Write};
use std::mem;

/// The default [AlevinFryReadRecordT] holds the barcode in a [u64]
pub type AlevinFryReadRecord = AlevinFryReadRecordT<u64>;

/// An [AlevinFryReadRecordT] that also holds the barcode in a [u64] and is explicit about this
pub type AlevinFryReadRecordU64 = AlevinFryReadRecordT<u64>;

/// An [AlevinFryReadRecordT] that holds the barcode in a [u128] and is explicit about this
pub type AlevinFryReadRecordU128 = AlevinFryReadRecordT<u128>;

/// The default [ScLongReadRecordT] holds the barcode in a [u64]
pub type ScLongReadRecord = ScLongReadRecordT<u64>;

/// An [ScLongReadRecordT] that also holds the barcode in a [u64] and is explicit about this
pub type ScLongReadRecordU64 = ScLongReadRecordT<u64>;

/// An [ScLongReadRecordT] that holds the barcode in a [u128] and is explicit about this
pub type ScLongReadRecordU128 = ScLongReadRecordT<u128>;

/// A concrete struct representing a [MappedRecord]
/// that is as generic as possible. Here, the tags should
/// be as arbitrary as possible. This record type should
/// **not** be used for high-throughput processing as it will
/// induce much more overhead than the specialized implementations
/// but should allow us to easily test out RAD files containing
/// different information
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenericReadRecord {
    pub naln: u32,
    pub naln_tags: u32,
    pub rtags: Vec<TagValue>,
    pub atags: Vec<TagValue>,
}

impl GenericReadRecord {
    pub fn fmt_with_context(&self, ctx: &GenericReadRecordContext, f: &mut impl Write) -> std::io::Result<()> {
        f.write_all(format!("GenericReadRecord{{ naln: {}, naln_tags: {},\nrtags: {},\natags:  {} }}\n", 
                self.naln, 
                self.naln_tags,
                ctx.read_tags.iter_desc().zip(self.rtags.iter()).map( |(td, tv)| format!("{} : [{:?}]", td.name, tv)).collect::<Vec<_>>().join(", "),
                self.atags.chunks_exact(self.naln_tags as usize).map( |vchunk| {
                    ctx.aln_tags.iter_desc().zip(vchunk.iter()).map( |(td, tv)| format!("{} : [{:?}]", td.name, tv)).collect::<Vec<_>>().join(", ")
                }).collect::<Vec<_>>().join("\n\t")
        ).as_bytes())
    }
}

/// context needed to read a generic record
#[derive(Debug, Clone)]
pub struct GenericReadRecordContext {
    pub read_tags: TagSection,
    pub aln_tags: TagSection,
}

pub trait KnownSize {
    // returns the number of bytes taken for a record of the given type 
    // with na alignments
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize where Self : MappedRecord;
}

impl<B: ConvertiblePrimitiveInteger> KnownSize for AlevinFryReadRecordT<B> {
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // for na field
        std::mem::size_of::<u32>() +
        // for bc
        ctx.bct.bytes_for_type() +
        // for umi 
        ctx.umit.bytes_for_type() +
        // an ori_ref for each alignment
        (na as usize * std::mem::size_of::<u32>())
    }
}

impl KnownSize for PiscemBulkReadRecord {
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // for na field
        std::mem::size_of::<u32>() +
        // for frag type
        ctx.frag_map_t.bytes_for_type() +
        // for each alignment a 
        // (mapped_fragment_orientation + reference): u32, 
        // position: u32
        // frag length: u16
        (na as usize * (std::mem::size_of::<u32>() + std::mem::size_of::<u32>() + std::mem::size_of::<u16>()))
    }
}

impl<B: ConvertiblePrimitiveInteger> KnownSize for ScLongReadRecordT<B> {
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // for na field
        std::mem::size_of::<u32>() +
        // for barcode type
        ctx.bct.bytes_for_type() +
        // for the umi
        ctx.umit.bytes_for_type() +
        // for each alignment a 
        // (ori_refernce): u32, 
        // read_start : u32, 
        // read_end: u32, 
        // alignment_score: i32, 
        (na as usize * (std::mem::size_of::<u32>() + std::mem::size_of::<u32>() + std::mem::size_of::<u32>() + std::mem::size_of::<i32>()))
    }
}

impl KnownSize for AtacSeqReadRecord {
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // for na field
        std::mem::size_of::<u32>() +
        // for barcode type
        ctx.bct.bytes_for_type() +
        // for each alignment a 
        // (ori_refernce): u32, 
        // read_start : u32, 
        // read_end: u32, 
        // alignment_score: i32, 
        (na as usize * (std::mem::size_of::<u32>() + std::mem::size_of::<u32>() + std::mem::size_of::<u32>() + std::mem::size_of::<i32>()))
    }
}



/// A concrete struct representing a [MappedRecord]
/// for reads processed upstream with `piscem` (or `salmon alevin`).
/// This represents the set of alignments and relevant information
/// for a basic alevin-fry record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlevinFryReadRecordT<B: ConvertiblePrimitiveInteger> {
    pub bc: B,
    pub umi: u64,
    pub dirs: Vec<bool>,
    pub refs: Vec<u32>,
}

/// A concrete struct representing a [MappedRecord] for
/// reads processed upstream with `piscem`. This represents a set of
/// alignments and relevant information for a basic piscem bulk
/// record.
#[derive(Debug)]
pub struct PiscemBulkReadRecord {
    pub frag_type: u8,
    pub dirs: Vec<MappedFragmentOrientation>,
    pub refs: Vec<u32>,
    pub positions: Vec<u32>,
    pub frag_lengths: Vec<u16>,
}

/// A concrete struct representing a [MappedRecord] for
/// reads processed upstream with `alevin-fry` for long read data.
/// This represents a set of alignments and relevant information for
/// long read single cell data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScLongReadRecordT<B: ConvertiblePrimitiveInteger> {
    pub bc: B,
    pub umi: u64,
    pub dirs: Vec<bool>,
    pub refs: Vec<u32>,
    pub as_scores: Vec<i32>,
    pub starts: Vec<u32>,
    pub ends: Vec<u32>,
    // TODO: Move this to a file-level tag
    pub tlens: Vec<u32>,
}

/// A concrete struct representing a [MappedRecord] for
/// reads processed upstream with `piscem` for ATAC-seq data.
/// This represents a set of alignments and relevant information for
/// a basic piscem ATAC record.
#[derive(Debug)]
pub struct AtacSeqReadRecord {
    pub bc: u64,
    pub start_pos: Vec<u32>,
    pub refs: Vec<u32>,
    pub frag_lengths: Vec<u16>,
    pub map_type: Vec<u8>,
}

/// This trait represents a mapped read record that should be stored
/// in the [crate::chunk::Chunk] of a RAD file.  The [crate::chunk::Chunk] type is parameterized on
/// some concrete struct that must implement this [MappedRecord] trait.
/// This trat defines the necessary functions required to be able to parse
/// the read record from the underlying reader, as well as the associated
/// types that are necessary to provide the context to perform this parsing.
pub trait MappedRecord {
    /// the information necessary to be able to correctly
    /// parse a concrete instance of a struct implementing
    /// [MappedRecord] from an input stream. This should
    /// encapsulate any context necessary to perform such
    /// parsing.
    type ParsingContext;
    /// The information that should be returned if one wishes
    /// to peek at the next record in the input stream.
    type PeekResult;

    /// Peek into the provided buffer `buf`, and return the [Self::PeekResult] for this
    /// [MappedRecord].
    fn peek_record(buf: &[u8], ctx: &Self::ParsingContext) -> Self::PeekResult;

    /// Produce a [MappedRecord] by reading from `reader` using the provided `ctx`
    fn from_bytes_with_context<T: Read>(reader: &mut T, ctx: &Self::ParsingContext) -> Self;

    /// Write this [MappedRecord] to `writer` using the provided `ctx`; returns Ok(())
    /// on success and propagates any errors otherwise.
    fn write<W: Write>(&self, writer: &mut W, ctx: &Self::ParsingContext) -> anyhow::Result<()>;
}

/// This trait allows obtaining and passing along necessary information that
/// may be required for a [MappedRecord] to be properly parsed from a file.
/// Typically, this information will be relevant information about the tags
/// that are used for parsing these records. It gets information about the
/// file, read, and alignment-level [TagSection]s from the [crate::header::RadPrelude] and
/// can then copy any information that may be later necessary for parsing.
pub trait RecordContext {
    fn get_context_from_tag_section(
        ft: &TagSection,
        rt: &TagSection,
        at: &TagSection,
    ) -> anyhow::Result<Self>
    where
        Self: Sized;
}

// Modified from https://stackoverflow.com/questions/69764050/how-to-get-the-indices-that-would-sort-a-vec
// kmdreko
pub fn argsort<T: Ord>(data: &[T]) -> Vec<usize> {
    let mut indices = (0..data.len()).collect::<Vec<_>>();
    indices.sort_unstable_by_key(|&i| &data[i]);
    indices
}

impl RecordContext for GenericReadRecordContext {
    /// Currently, the [AlevinFryRecordContext] only cares about and provides the read tags that
    /// correspond to the types used to encode the barcode and the UMI. Here, these are parsed from the
    /// corresponding [TagSection].
    fn get_context_from_tag_section(
        _ft: &TagSection,
        rt: &TagSection,
        at: &TagSection,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            read_tags: rt.clone(),
            aln_tags: at.clone(),
        })
    }
}

/// context needed to read an alevin-fry record
/// (the types of the barcode and umi)
#[derive(Debug, Clone)]
pub struct AlevinFryRecordContext {
    pub bct: RadIntId,
    pub umit: RadIntId,
}

impl RecordContext for AlevinFryRecordContext {
    /// Currently, the [AlevinFryRecordContext] only cares about and provides the read tags that
    /// correspond to the types used to encode the barcode and the UMI. Here, these are parsed from the
    /// corresponding [TagSection].
    fn get_context_from_tag_section(
        _ft: &TagSection,
        rt: &TagSection,
        _at: &TagSection,
    ) -> anyhow::Result<Self> {
        // the tags we expect to exist
        let bct = rt
            .get_tag_type("b")
            .expect("alevin-fry record context requires a \'b\' read-level tag");
        let umit = rt
            .get_tag_type("u")
            .expect("alevin-fry record context requires a \'u\' read-level tag");
        if let (RadType::Int(x), RadType::Int(y)) = (bct, umit) {
            Ok(Self { bct: x, umit: y })
        } else {
            bail!("alevin-fry record context requires that b and u tags are of type RadType::Int");
        }
    }
}

impl AlevinFryRecordContext {
    /// Create a new AlevinFryRecordContext from the barcode and umi [RadIntId] types.
    pub fn from_bct_umit(bct: RadIntId, umit: RadIntId) -> Self {
        Self { bct, umit }
    }
}

/// Context necessary for reading a piscem bulk record
#[derive(Debug, Clone)]
pub struct PiscemBulkRecordContext {
    pub frag_map_t: RadIntId,
}

impl RecordContext for PiscemBulkRecordContext {
    fn get_context_from_tag_section(
        _ft: &TagSection,
        rt: &TagSection,
        _at: &TagSection,
    ) -> anyhow::Result<Self> {
        let frag_map_t = rt
            .get_tag_type("frag_map_type")
            .expect("psicem bulk record context requires a \"frag_map_type\" read-level tag");
        if let RadType::Int(x) = frag_map_t {
            Ok(Self { frag_map_t: x })
        } else {
            bail!("piscem bulk record context requries that \"frag_map_type\" tag is of type RadType::Int");
        }
    }
}

impl MappedRecord for PiscemBulkReadRecord {
    type ParsingContext = PiscemBulkRecordContext;
    type PeekResult = Option<u64>;

    #[inline]
    fn from_bytes_with_context<T: Read>(reader: &mut T, ctx: &Self::ParsingContext) -> Self {
        const MASK_LOWER_30_BITS: u32 = 0xC0000000;
        const MASK_UPPER_2_BITS: u32 = 0x3FFFFFFF;
        let mut rbuf = [0u8; 255];

        reader.read_exact(&mut rbuf[0..4]).unwrap();
        let na = rbuf.pread::<u32>(0).unwrap();
        let fmt = rad_io::read_into_u64(reader, &ctx.frag_map_t);
        let f = MappingType::from_u8(fmt as u8);

        let mut rec = Self {
            frag_type: fmt as u8,
            dirs: Vec::with_capacity(na as usize),
            refs: Vec::with_capacity(na as usize),
            positions: Vec::with_capacity(na as usize),
            frag_lengths: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();

            let dir_int = (v & MASK_LOWER_30_BITS) >> 30;
            let dir = MappedFragmentOrientation::from_u32_paired_status(dir_int, f);
            rec.dirs.push(dir);
            rec.refs.push(v & MASK_UPPER_2_BITS);
            // position
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let pos = rbuf.pread::<u32>(0).unwrap();
            rec.positions.push(pos);
            // length
            reader.read_exact(&mut rbuf[0..2]).unwrap();
            let flen = rbuf.pread::<u16>(0).unwrap();
            rec.frag_lengths.push(flen);
        }

        rec
    }

    #[inline]
    fn peek_record(_buf: &[u8], _ctx: &Self::ParsingContext) -> Self::PeekResult {
        unimplemented!("Currently there is no implementation for peek_record for PiscemBulkReadRecord. This should not be needed");
    }

    #[inline]
    fn write<W: Write>(&self, writer: &mut W, _ctx: &Self::ParsingContext) -> anyhow::Result<()> {
        let na: u32 = self.refs.len().try_into()?;
        // first write the number of alignments
        writer
            .write_all(&na.to_le_bytes())
            .context("couldn't write number of alignments for record")?;

        let fmt: u8 = self.frag_type;
        writer
            .write_all(&fmt.to_le_bytes())
            .context("couldn't write frag_map_t for the record")?;

        for (dir, ref_idx, pos, length) in
            itertools::izip!(&self.dirs, &self.refs, &self.positions, &self.frag_lengths)
        {
            // pack info about the mapped type into the
            // higher order bits. First get the encoding
            // then shift it to the left.
            let encoded_dir: u32 = (*dir).into();
            let encoded_dir_idx: u32 = (encoded_dir << 30) | ref_idx;
            writer
                .write_all(&encoded_dir_idx.to_le_bytes())
                .context("couldn't write frag_map_type and ref for record")?;
            writer
                .write_all(&pos.to_le_bytes())
                .context("couldn't write position for record")?;
            writer
                .write_all(&length.to_le_bytes())
                .context("couldn't write fragment length for record")?;
        }
        Ok(())
    }
}

impl<B: ConvertiblePrimitiveInteger> MappedRecord for AlevinFryReadRecordT<B> {
    type ParsingContext = AlevinFryRecordContext;
    type PeekResult = (B, u64);

    #[inline]
    fn peek_record(buf: &[u8], ctx: &Self::ParsingContext) -> Self::PeekResult {
        let na_size = mem::size_of::<u32>();
        let bc_size = ctx.bct.bytes_for_type();

        let _na = buf.pread::<u32>(0).unwrap();

        let bc: B = match ctx.bct {
            RadIntId::U8 => NewU8(buf.pread::<u8>(na_size).unwrap()).into(),
            RadIntId::U16 => NewU16(buf.pread::<u16>(na_size).unwrap()).into(),
            RadIntId::U32 => NewU32(buf.pread::<u32>(na_size).unwrap()).into(),
            RadIntId::U64 => NewU64(buf.pread::<u64>(na_size).unwrap()).into(),
            RadIntId::U128 => NewU128(buf.pread::<u128>(na_size).unwrap()).into(),
            _ => panic!("signed barcode integer encodings are not supported"),
        };
        let umi = match ctx.umit {
            RadIntId::U8 => buf.pread::<u8>(na_size + bc_size).unwrap() as u64,
            RadIntId::U16 => buf.pread::<u16>(na_size + bc_size).unwrap() as u64,
            RadIntId::U32 => buf.pread::<u32>(na_size + bc_size).unwrap() as u64,
            RadIntId::U64 => buf.pread::<u64>(na_size + bc_size).unwrap(),
            RadIntId::U128 => panic!("u128 is currently not supported as a umi type"),
            _ => panic!("signed umi integer encodings are not supported"),
        };
        (bc, umi)
    }

    #[inline]
    fn from_bytes_with_context<T: Read>(reader: &mut T, ctx: &Self::ParsingContext) -> Self {
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

    #[inline]
    fn write<W: Write>(&self, writer: &mut W, ctx: &Self::ParsingContext) -> anyhow::Result<()> {
        let na: u32 = self.refs.len() as u32;
        RadIntId::U32
            .write_to(na, writer)
            .context("couldn't write number of alignments for record")?;
        ctx.bct
            .write_to(self.bc, writer)
            .context("couldn't write bc field for record")?;
        ctx.umit
            .write_to(self.umi, writer)
            .context("couldn't write umi field for record")?;

        for (dir, ref_idx) in itertools::izip!(&self.dirs, &self.refs) {
            let encoded_dir: u32 = if *dir { 1_u32 << 31 } else { 0_u32 };
            let encoded_dir_ref: u32 = ref_idx | encoded_dir;
            writer
                .write_all(&encoded_dir_ref.to_le_bytes())
                .context("couldn't write compressed_ori_refid for record")?;
        }
        Ok(())
    }
}

impl MappedRecord for GenericReadRecord {
    type ParsingContext = GenericReadRecordContext;
    type PeekResult = Option<u64>;

    #[inline]
    fn from_bytes_with_context<T: Read>(reader: &mut T, ctx: &Self::ParsingContext) -> Self {
        let mut rbuf = [0u8; 255];

        // fixed field, must always be present
        reader.read_exact(&mut rbuf[0..4]).unwrap();
        let na = rbuf.pread::<u32>(0).unwrap();

        // now any read level information
        let rtags: Vec<TagValue> = ctx
            .read_tags
            .iter_desc()
            .map(|td| td.value_from_bytes(reader))
            .collect();

        let naln_tags = &ctx.aln_tags.iter_desc().len();
        let mut atags = Vec::<TagValue>::new();
        for _ in 0..(na as usize) {
            let aln_tags: Vec<TagValue> = ctx
                .aln_tags
                .iter_desc()
                .map(|td| td.value_from_bytes(reader))
                .collect();
            atags.extend(aln_tags);
        }

        Self {
            naln: na,
            naln_tags: *naln_tags as u32,
            rtags,
            atags,
        }
    }

    #[inline]
    fn peek_record(_buf: &[u8], _ctx: &Self::ParsingContext) -> Self::PeekResult {
        unimplemented!("Currently there is no implementation for peek_record for GenericRecord. This should not be needed");
    }

    #[inline]
    fn write<W: Write>(&self, _writer: &mut W, _ctx: &Self::ParsingContext) -> anyhow::Result<()> {
        unimplemented!("Currently there is no implementation for write for the GenericReadRecord");
    }
}

// TODO: The below is a mess, think about how to clean it up.
// We have to provide these now because our number trait encoding
// does not quite fit right. We want certain types to only be allowed
// to be unsigned, but it's unclear how to model this with our
// existing PrimitiveInteger and ConvertiblePrimitiveInteger types.
// The below implementations allow everything to compile but say that
// we cannot convert from a signed type (NewIX or TryWrapper<NewIX>)
// into a u64.
impl From<NewI8> for u64 {
    fn from(_x: NewI8) -> Self {
        unimplemented!()
    }
}
impl From<NewI16> for u64 {
    fn from(_x: NewI16) -> Self {
        unimplemented!()
    }
}
impl From<NewI32> for u64 {
    fn from(_x: NewI32) -> Self {
        unimplemented!()
    }
}
impl From<NewI64> for u64 {
    fn from(_x: NewI64) -> Self {
        unimplemented!()
    }
}
impl From<NewI128> for u64 {
    fn from(_x: NewI128) -> Self {
        unimplemented!()
    }
}
impl From<TryWrapper<NewI8>> for u64 {
    fn from(_x: TryWrapper<NewI8>) -> Self {
        unimplemented!()
    }
}
impl From<TryWrapper<NewI16>> for u64 {
    fn from(_x: TryWrapper<NewI16>) -> Self {
        unimplemented!()
    }
}
impl From<TryWrapper<NewI32>> for u64 {
    fn from(_x: TryWrapper<NewI32>) -> Self {
        unimplemented!()
    }
}
impl From<TryWrapper<NewI64>> for u64 {
    fn from(_x: TryWrapper<NewI64>) -> Self {
        unimplemented!()
    }
}
impl From<TryWrapper<NewI128>> for u64 {
    fn from(_x: TryWrapper<NewI128>) -> Self {
        unimplemented!()
    }
}

pub trait ConvertiblePrimitiveInteger:
    PrimitiveInteger
    + std::convert::From<NewU8>
    + std::convert::From<NewU16>
    + std::convert::From<NewU32>
    + std::convert::From<NewU64>
    + std::convert::From<NewU128>
    + std::convert::TryFrom<TryWrapper<NewU8>>
    + std::convert::TryFrom<TryWrapper<NewU16>>
    + std::convert::TryFrom<TryWrapper<NewU32>>
    + std::convert::TryFrom<TryWrapper<NewU64>>
    + std::convert::TryFrom<TryWrapper<NewU128>>
    + std::convert::From<NewI8>
    + std::convert::From<NewI16>
    + std::convert::From<NewI32>
    + std::convert::From<NewI64>
    + std::convert::From<NewI128>
    + std::convert::TryFrom<TryWrapper<NewI8>>
    + std::convert::TryFrom<TryWrapper<NewI16>>
    + std::convert::TryFrom<TryWrapper<NewI32>>
    + std::convert::TryFrom<TryWrapper<NewI64>>
    + std::convert::TryFrom<TryWrapper<NewI128>>
    + std::convert::TryFrom<TryWrapper<NewI128>>
{
}

impl<
        T: PrimitiveInteger
            + std::convert::From<NewU8>
            + std::convert::From<NewU16>
            + std::convert::From<NewU32>
            + std::convert::From<NewU64>
            + std::convert::From<NewU128>
            + std::convert::TryFrom<TryWrapper<NewU8>>
            + std::convert::TryFrom<TryWrapper<NewU16>>
            + std::convert::TryFrom<TryWrapper<NewU32>>
            + std::convert::TryFrom<TryWrapper<NewU64>>
            + std::convert::TryFrom<TryWrapper<NewU128>>
            + std::convert::From<NewI8>
            + std::convert::From<NewI16>
            + std::convert::From<NewI32>
            + std::convert::From<NewI64>
            + std::convert::From<NewI128>
            + std::convert::TryFrom<TryWrapper<NewI8>>
            + std::convert::TryFrom<TryWrapper<NewI16>>
            + std::convert::TryFrom<TryWrapper<NewI32>>
            + std::convert::TryFrom<TryWrapper<NewI64>>
            + std::convert::TryFrom<TryWrapper<NewI128>>
            + std::convert::TryFrom<TryWrapper<NewI128>>,
    > ConvertiblePrimitiveInteger for T
{
}

impl<B: ConvertiblePrimitiveInteger> AlevinFryReadRecordT<B> {
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

    /// Reads the record header, consisting of the number of the barcode,
    /// umi, and number of alignments for this record, from the provided `reader`,
    /// using the provided [RadIntId] description for the barcode and umi types.
    #[inline]
    pub fn from_bytes_record_header<T: Read>(
        reader: &mut T,
        bct: &RadIntId,
        umit: &RadIntId,
    ) -> (B, u64, u32) {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf);
        let bc = rad_io::read_into::<T, B>(reader, bct);
        // NOTE: We likely will want to make the UMI generic as well
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
        bc: B,
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

#[derive(Debug, Clone)]
pub struct AtacSeqRecordContext {
    pub bct: RadIntId,
}

impl RecordContext for AtacSeqRecordContext {
    /// Currently, the [AtacSeqRecordContext] only cares about and provides the read tags that
    /// correspond to the length of the barcode. Here, these are parsed from the
    /// corresponding [TagSection].
    fn get_context_from_tag_section(
        _ft: &TagSection,
        rt: &TagSection,
        _at: &TagSection,
    ) -> anyhow::Result<Self> {
        // the tags we expect to exist
        let bct = rt
            .get_tag_type("barcode")
            .expect("atac-reader record context requires a \'barcode\' read-level tag");

        if let RadType::Int(x) = bct {
            Ok(Self { bct: x })
        } else {
            bail!("atac-reader record context requires that barcode tags are of type RadType::Int");
        }
    }
}

impl AtacSeqRecordContext {
    pub fn from_bct(bct: RadIntId) -> Self {
        Self { bct }
    }
}

impl MappedRecord for AtacSeqReadRecord {
    type ParsingContext = AtacSeqRecordContext;
    type PeekResult = u64;

    #[inline]
    fn peek_record(buf: &[u8], ctx: &Self::ParsingContext) -> Self::PeekResult {
        let na_size = mem::size_of::<u32>();
        // let bc_size = ctx.bct.bytes_for_type();

        let _na = buf.pread::<u32>(0).unwrap();

        match ctx.bct {
            RadIntId::U8 => buf.pread::<u8>(na_size).unwrap() as u64,
            RadIntId::U16 => buf.pread::<u16>(na_size).unwrap() as u64,
            RadIntId::U32 => buf.pread::<u32>(na_size).unwrap() as u64,
            RadIntId::U64 => buf.pread::<u64>(na_size).unwrap(),
            RadIntId::U128 => panic!("u128 is currently not supported as a barcode type"),
            _ => panic!("signed integer types are not supported as a barcode type"),
        }
    }

    #[inline]
    fn from_bytes_with_context<T: Read>(reader: &mut T, ctx: &Self::ParsingContext) -> Self {
        let mut rbuf = [0u8; 255];

        let (bc, na) = Self::from_bytes_record_header(reader, &ctx.bct);
        let mut rec = Self {
            bc,
            refs: Vec::with_capacity(na as usize),
            map_type: Vec::with_capacity(na as usize),
            start_pos: Vec::with_capacity(na as usize),
            frag_lengths: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let ref_id = rbuf.pread::<u32>(0).unwrap();
            // println!("ref_id {}", ref_id);
            rec.refs.push(ref_id);
            reader.read_exact(&mut rbuf[0..1]).unwrap();
            let map_type = rbuf.pread::<u8>(0).unwrap();
            // println!("type {}", map_type);
            rec.map_type.push(map_type);
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let start_pos = rbuf.pread::<u32>(0).unwrap();
            rec.start_pos.push(start_pos);
            // println!("start_pos {}", start_pos);
            reader.read_exact(&mut rbuf[0..2]).unwrap();
            let frag_length = rbuf.pread::<u16>(0).unwrap();
            rec.frag_lengths.push(frag_length);
            // println!("frag {}", frag_length);
        }
        rec
    }

    #[inline]
    fn write<W: Write>(&self, _writer: &mut W, _ctx: &Self::ParsingContext) -> anyhow::Result<()> {
        todo!();
        /*
        let na: u32 = self.refs.len().try_into()?;
        // first write the number of alignments
        writer
            .write_all(&na.to_le_bytes())
            .context("couldn't write number of alignments for record")?;

        let fmt: u8 = self.frag_type;
        writer
            .write_all(&fmt.to_le_bytes())
            .context("couldn't write frag_map_t for the record")?;

        for (dir, ref_idx, pos, length) in
            itertools::izip!(&self.dirs, &self.refs, &self.positions, &self.frag_lengths)
        {
            // pack info about the mapped type into the
            // higher order bits. First get the encoding
            // then shift it to the left.
            let encoded_dir: u32 = (*dir).into();
            let encoded_dir_idx: u32 = (encoded_dir << 30) | ref_idx;
            writer
                .write_all(&encoded_dir_idx.to_le_bytes())
                .context("couldn't write frag_map_type and ref for record")?;
            writer
                .write_all(&pos.to_le_bytes())
                .context("couldn't write position for record")?;
            writer
                .write_all(&length.to_le_bytes())
                .context("couldn't write fragment length for record")?;
        }
        Ok(())
        */
    }
}

impl AtacSeqReadRecord {
    /// Returns `true` if this [AtacSeqReadRecord] contains no references and
    /// `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    /// Obtains the next [AtacSeqReadRecord] in the stream from the reader `reader`.
    /// The barcode should be encoded with the [RadIntId] type `bct` and
    pub fn from_bytes<T: Read>(reader: &mut T, bct: &RadIntId) -> Self {
        let mut rbuf = [0u8; 255];

        let (bc, na) = Self::from_bytes_record_header(reader, bct);

        let mut rec = Self {
            bc,
            refs: Vec::with_capacity(na as usize),
            map_type: Vec::with_capacity(na as usize),
            start_pos: Vec::with_capacity(na as usize),
            frag_lengths: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let ref_id = rbuf.pread::<u32>(0).unwrap();
            rec.refs.push(ref_id);

            reader.read_exact(&mut rbuf[0..1]).unwrap();
            let map_type = rbuf.pread::<u8>(0).unwrap();
            rec.map_type.push(map_type);

            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let start_pos = rbuf.pread::<u32>(0).unwrap();
            rec.start_pos.push(start_pos);

            reader.read_exact(&mut rbuf[0..2]).unwrap();
            let frag_length = rbuf.pread::<u16>(0).unwrap();
            rec.frag_lengths.push(frag_length);
        }
        rec
    }

    #[inline]
    pub fn from_bytes_record_header<T: Read>(reader: &mut T, bct: &RadIntId) -> (u64, u32) {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf); //.pread::<u32>(0).unwrap();
        let bc = rad_io::read_into_u64(reader, bct);
        (bc, na)
    }

    pub fn from_bytes_with_header<T: Read>(reader: &mut T, bc: u64, na: u32) -> Self {
        let mut rbuf = [0u8; 255];
        let mut rec = Self {
            bc,
            refs: Vec::with_capacity(na as usize),
            map_type: Vec::with_capacity(na as usize),
            start_pos: Vec::with_capacity(na as usize),
            frag_lengths: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let ref_id = rbuf.pread::<u32>(0).unwrap();
            rec.refs.push(ref_id);

            reader.read_exact(&mut rbuf[0..1]).unwrap();
            let map_type = rbuf.pread::<u8>(0).unwrap();
            rec.map_type.push(map_type);

            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let start_pos = rbuf.pread::<u32>(0).unwrap();
            rec.start_pos.push(start_pos);

            reader.read_exact(&mut rbuf[0..2]).unwrap();
            let frag_length = rbuf.pread::<u16>(0).unwrap();
            rec.frag_lengths.push(frag_length);
        }

        // make sure these are sorted in this step.
        // reimplement in a better way
        let indices = argsort(&rec.refs);
        let refs = rec.refs.clone();
        let map_type = rec.map_type.clone();
        let start_pos = rec.start_pos.clone();
        let f_len = rec.frag_lengths.clone();
        for i in 0..indices.len() {
            rec.refs[i] = refs[indices[i]];
            rec.map_type[i] = map_type[indices[i]];
            rec.start_pos[i] = start_pos[indices[i]];
            rec.frag_lengths[i] = f_len[indices[i]];
        }
        rec
    }
}

//implementing the single cell long read record
#[derive(Debug, Clone)]
pub struct ScLongReadRecordContext {
    pub bct: RadIntId,
    pub umit: RadIntId,
}

impl RecordContext for ScLongReadRecordContext {
    fn get_context_from_tag_section(
        _ft: &TagSection,
        rt: &TagSection,
        _at: &TagSection,
    ) -> anyhow::Result<Self> {
        let bct = rt
            .get_tag_type("b")
            .expect("scLongRead record requires a 'b' barcode tag");

        let umit = rt
            .get_tag_type("u")
            .expect("scLongRead record requires a 'u' umi tag");

        match (bct, umit) {
            (RadType::Int(bct), RadType::Int(umit)) => Ok(Self { bct, umit }),
            _ => bail!("barcode/umi must be RadType::Int"),
        }
    }
}

impl ScLongReadRecordContext {
    /// Create a new AlevinFryRecordContext from the barcode and umi [RadIntId] types.
    pub fn from_bct_umit(bct: RadIntId, umit: RadIntId) -> Self {
        Self { bct, umit }
    }
}

impl<B: ConvertiblePrimitiveInteger> MappedRecord for ScLongReadRecordT<B> {
    type ParsingContext = ScLongReadRecordContext;
    type PeekResult = (B, u64);

    #[inline]
    fn peek_record(buf: &[u8], ctx: &Self::ParsingContext) -> Self::PeekResult {
        let na_size = mem::size_of::<u32>();
        let bc_size = ctx.bct.bytes_for_type();

        let _na = buf.pread::<u32>(0).unwrap();

        let bc: B = match ctx.bct {
            RadIntId::U8 => NewU8(buf.pread::<u8>(na_size).unwrap()).into(),
            RadIntId::U16 => NewU16(buf.pread::<u16>(na_size).unwrap()).into(),
            RadIntId::U32 => NewU32(buf.pread::<u32>(na_size).unwrap()).into(),
            RadIntId::U64 => NewU64(buf.pread::<u64>(na_size).unwrap()).into(),
            RadIntId::U128 => NewU128(buf.pread::<u128>(na_size).unwrap()).into(),
            _ => panic!("signed barcode integer encodings are not supported"),
        };
        let umi = match ctx.umit {
            RadIntId::U8 => buf.pread::<u8>(na_size + bc_size).unwrap() as u64,
            RadIntId::U16 => buf.pread::<u16>(na_size + bc_size).unwrap() as u64,
            RadIntId::U32 => buf.pread::<u32>(na_size + bc_size).unwrap() as u64,
            RadIntId::U64 => buf.pread::<u64>(na_size + bc_size).unwrap(),
            RadIntId::U128 => panic!("u128 is currently not supported as a umi type"),
            _ => panic!("signed umi integer encodings are not supported"),
        };
        (bc, umi)
    }

    #[inline]
    fn from_bytes_with_context<T: Read>(reader: &mut T, ctx: &Self::ParsingContext) -> Self {
        let mut rbuf = [0u8; 255];

        let (bc, umi, na) = Self::from_bytes_record_header(reader, &ctx.bct, &ctx.umit);
        let mut rec = Self {
            bc,
            umi,
            dirs: Vec::with_capacity(na as usize),
            refs: Vec::with_capacity(na as usize),
            as_scores: Vec::with_capacity(na as usize),
            starts: Vec::with_capacity(na as usize),
            ends: Vec::with_capacity(na as usize),
            tlens: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            // 1) direction + ref_id, if you’re packing them like AF
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();
            let dir = (v & utils::MASK_LOWER_31_U32) != 0;
            let ref_id = v & utils::MASK_TOP_BIT_U32;
            rec.dirs.push(dir);
            rec.refs.push(ref_id);

            // 2) AS score
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let as_score = rbuf.pread::<i32>(0).unwrap();
            rec.as_scores.push(as_score);

            // 3) start
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let start = rbuf.pread::<u32>(0).unwrap();
            rec.starts.push(start);

            // 4) end
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let end = rbuf.pread::<u32>(0).unwrap();
            rec.ends.push(end);

            // 5) tlen
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let tlen = rbuf.pread::<u32>(0).unwrap();
            rec.tlens.push(tlen);
        }
        rec
    }

    #[inline]
    fn write<W: Write>(&self, writer: &mut W, ctx: &Self::ParsingContext) -> anyhow::Result<()> {
        let na: u32 = self.refs.len() as u32;
        RadIntId::U32
            .write_to(na, writer)
            .context("couldn't write number of alignments for record")?;
        ctx.bct
            .write_to(self.bc, writer)
            .context("couldn't write bc field for record")?;
        ctx.umit
            .write_to(self.umi, writer)
            .context("couldn't write umi field for record")?;

        for i in 0..(na as usize) {
            let ref_idx = self.refs[i];
            let dir = self.dirs[i];
            let as_i32 = self.as_scores[i];
            let start = self.starts[i];
            let end = self.ends[i];
            let tlen = self.tlens[i];

            let encoded_dir: u32 = if dir { 1_u32 << 31 } else { 0_u32 };
            let encoded_dir_ref: u32 = ref_idx | encoded_dir;
            writer
                .write_all(&encoded_dir_ref.to_le_bytes())
                .context("couldn't write compressed_ori_refid for record")?;
            writer
                .write_all(&as_i32.to_le_bytes())
                .context("couldn't write AS for record")?;
            writer
                .write_all(&start.to_le_bytes())
                .context("couldn't write start for record")?;
            writer
                .write_all(&end.to_le_bytes())
                .context("couldn't write end for record")?;
            writer
                .write_all(&tlen.to_le_bytes())
                .context("couldn't write tlen for record")?;
        }
        Ok(())
    }
}

impl<B: ConvertiblePrimitiveInteger> ScLongReadRecordT<B> {
    /// Returns `true` if this [ScLongReadRecord] contains no references and
    /// `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    /// Obtains the next [ScLongReadRecord] in the stream from the reader `reader`.
    /// The barcode should be encoded with the [RadIntId] type `bct` and
    /// the umi should be encoded with the [RadIntId] type `umit`.
    pub fn from_bytes<T: Read>(reader: &mut T, bct: &RadIntId, umit: &RadIntId) -> Self {
        let ctx = ScLongReadRecordContext::from_bct_umit(*bct, *umit);
        Self::from_bytes_with_context(reader, &ctx)
    }

    #[inline]
    pub fn from_bytes_record_header<T: Read>(
        reader: &mut T,
        bct: &RadIntId,
        umit: &RadIntId,
    ) -> (B, u64, u32) {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf); //.pread::<u32>(0).unwrap();
        let bc: B = rad_io::read_into(reader, bct);
        let umi = rad_io::read_into_u64(reader, umit);
        (bc, umi, na)
    }

    pub fn from_bytes_with_header<T: Read>(_reader: &mut T, _bc: u64, _umi: u64, _na: u32) -> Self {
        unimplemented!(
            "from_bytes_with_header is not implemented for extended AlevinFryReadRecordT"
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::rad_types::{RadIntId, TagSection, TagSectionLabel};
    use crate::rad_types::{RadType, TagDesc};
    use crate::record::{AlevinFryReadRecord, AlevinFryRecordContext, MappedRecord, RecordContext};
    use std::io::Cursor;

    #[test]
    fn can_write_af_record() {
        let rec = AlevinFryReadRecord {
            bc: 12345_u64,
            umi: 6789_u64,
            dirs: vec![true, true, true, false],
            refs: vec![123, 456, 78, 910],
        };

        let ft = TagSection::new_with_label(TagSectionLabel::FileTags);
        let mut rt = TagSection::new_with_label(TagSectionLabel::ReadTags);
        rt.add_tag_desc(TagDesc {
            name: "b".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        rt.add_tag_desc(TagDesc {
            name: "u".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        let at = TagSection::new_with_label(TagSectionLabel::AlignmentTags);

        let ctx = AlevinFryRecordContext::get_context_from_tag_section(&ft, &rt, &at).unwrap();

        let mut buf: Vec<u8> = Vec::new();
        rec.write(&mut buf, &ctx).expect("couldn't write record");

        let mut cursor = Cursor::new(buf);
        let new_rec = AlevinFryReadRecord::from_bytes_with_context(&mut cursor, &ctx);

        //println!("rec = {:?}, new_rec = {:?}", rec, new_rec);
        assert_eq!(rec, new_rec);
    }
}
