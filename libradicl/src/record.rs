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

use crate::collation::BarcodeRole;
use crate::io::{
    NewI8, NewI16, NewI32, NewI64, NewI128, NewU8, NewU16, NewU32, NewU64, NewU128, TryWrapper,
};
use crate::{
    io as rad_io,
    rad_types::{
        MappedFragmentOrientation, MappingType, PrimitiveInteger, RadIntId, RadType, TagSection,
        TagValue,
    },
    utils,
};
use anyhow::{self, Context, bail};
use bio_types::strand::{Same, Strand};
use libradicl_macros::UmiTagged;
use scroll::Pread;
use smallvec::SmallVec;
use std::io::{Read, Write};
use std::mem;

// Modified from https://stackoverflow.com/questions/69764050/how-to-get-the-indices-that-would-sort-a-vec
// kmdreko
fn argsort<T: Ord>(data: &[T]) -> Vec<usize> {
    let mut indices = (0..data.len()).collect::<Vec<_>>();
    indices.sort_unstable_by_key(|&i| &data[i]);
    indices
}

/// initially suggested by Claude
#[allow(unused)]
fn argsort_by<T, F>(data: &[T], mut compare: F) -> Vec<usize>
where
    F: FnMut(&T, &T) -> std::cmp::Ordering,
{
    let mut indices: Vec<usize> = (0..data.len()).collect();
    indices.sort_unstable_by(|&i, &j| compare(&data[i], &data[j]));
    indices
}

/// Reorder a vector in-place using the given permutation indices.
/// This is more memory-efficient but modifies the original vector.
/// Time: O(n), Space: O(n) for tracking visited indices.
fn reorder_in_place<T>(data: &mut [T], indices: &[usize]) {
    let mut visited = vec![false; data.len()];

    for start in 0..data.len() {
        if visited[start] {
            continue;
        }

        let mut current = start;
        let mut next = indices[current];

        while next != start {
            visited[current] = true;
            data.swap(current, next);
            current = next;
            next = indices[next];
        }
        visited[current] = true;
    }
}

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

pub type AlevinFryReadRecordWithPosition = AlevinFryReadRecordWithPositionT<u64>;
pub type AlevinFryReadRecordWithPositionU64 = AlevinFryReadRecordWithPositionT<u64>;
pub type AlevinFryReadRecordWithPositionU128 = AlevinFryReadRecordWithPositionT<u128>;

/// Trait for a RecordHeader, contains at least the number of alignments
/// but might contain other information
pub trait RecordHeader {
    /// The associated [MappedRecord] that has this header
    type RecordType: MappedRecord;

    /// All records contain the number of alignments, and this allows
    /// retreiving that value.
    fn naln(&self) -> u32;
}

/// This trait specifies that a [RecordHeader] is collatable by some `B` which can be converted
/// to a primitive integer.  For example, the header might be collatable by the barcode, and this
/// trait allows retriving that barcode / key as something convertible to an integer and also
/// allows writing the header out to a stream.
pub trait CollatableRecordHeader<B: ConvertiblePrimitiveInteger>: RecordHeader {
    /// Retreives the key by which this record header (and the coresponding record) can be collated
    fn collate_key(&self) -> B;
    /// Retrieves the key by which this record header should be grouped into an
    /// output chunk during collation.
    fn collation_group_key(
        &self,
        _ctx: &<<Self as RecordHeader>::RecordType as MappedRecord>::ParsingContext,
    ) -> u64
    where
        u64: From<B>,
    {
        self.collate_key().into()
    }
    /// Writes the header to the provided `writer`.
    fn write_fields<W: Write>(
        &self,
        writer: &mut W,
        _ctx: &<<Self as RecordHeader>::RecordType as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<()>;
}

// === standard alevin-fry reads

/// Header information for an [AlevinFryReadRecord].
/// note this header can be re-used for the record with position information
/// since the read-level tags (i.e. header) doesn't contain any extra information
pub struct AlevinFryReadRecordHeader<B: ConvertiblePrimitiveInteger> {
    /// number of alignments
    pub naln: u32,
    /// barcode
    pub bc: B,
    /// umi
    pub umi: u64,
}

impl<B: ConvertiblePrimitiveInteger> RecordHeader for AlevinFryReadRecordHeader<B> {
    type RecordType = AlevinFryReadRecordT<B>;
    fn naln(&self) -> u32 {
        self.naln
    }
}

impl<B: ConvertiblePrimitiveInteger> CollatableRecordHeader<B> for AlevinFryReadRecordHeader<B> {
    fn collate_key(&self) -> B {
        self.bc
    }
    fn write_fields<W: Write>(
        &self,
        writer: &mut W,
        ctx: &<<Self as RecordHeader>::RecordType as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<()> {
        let na: u32 = self.naln();
        RadIntId::U32
            .write_to(na, writer)
            .context("couldn't write number of alignments for record")?;
        ctx.bct
            .write_to(self.bc, writer)
            .context("couldn't write bc field for record")?;
        ctx.umit
            .write_to(self.umi, writer)
            .context("couldn't write umi field for record")?;
        Ok(())
    }
}

// === long reads

/// Header information for an [ScLongReadRecord]; technically this could
/// be suared with a regular [AlevinFryReadRecord], but it's kept separate
/// for now in case the record format changes.
pub struct ScLongReadRecordHeader<B: ConvertiblePrimitiveInteger> {
    pub naln: u32,
    pub bc: B,
    pub umi: u64,
}

impl<B: ConvertiblePrimitiveInteger> RecordHeader for ScLongReadRecordHeader<B> {
    type RecordType = ScLongReadRecordT<B>;
    fn naln(&self) -> u32 {
        self.naln
    }
}

impl<B: ConvertiblePrimitiveInteger> CollatableRecordHeader<B> for ScLongReadRecordHeader<B> {
    fn collate_key(&self) -> B {
        self.bc
    }
    fn write_fields<W: Write>(
        &self,
        writer: &mut W,
        ctx: &<<Self as RecordHeader>::RecordType as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<()> {
        let na: u32 = self.naln();
        RadIntId::U32
            .write_to(na, writer)
            .context("couldn't write number of alignments for record")?;
        ctx.bct
            .write_to(self.bc, writer)
            .context("couldn't write bc field for record")?;
        ctx.umit
            .write_to(self.umi, writer)
            .context("couldn't write umi field for record")?;
        Ok(())
    }
}

// ==== ATAC seq read

/// Header information for an [AtacSeqReadRecord]
pub struct AtacSeqReadRecordHeader {
    pub naln: u32,
    pub bc: u64,
}

impl RecordHeader for AtacSeqReadRecordHeader {
    type RecordType = AtacSeqReadRecord;
    fn naln(&self) -> u32 {
        self.naln
    }
}

impl CollatableRecordHeader<u64> for AtacSeqReadRecordHeader {
    fn collate_key(&self) -> u64 {
        self.bc
    }
    fn write_fields<W: Write>(
        &self,
        writer: &mut W,
        ctx: &<<Self as RecordHeader>::RecordType as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<()> {
        let na: u32 = self.naln();
        RadIntId::U32
            .write_to(na, writer)
            .context("couldn't write number of alignments for record")?;
        ctx.bct
            .write_to(self.bc, writer)
            .context("couldn't write bc field for record")?;
        Ok(())
    }
}

/*
pub trait CollatableRecord<B: ConvertiblePrimitiveInteger> : MappedRecord where
    // to help the trait solver
    <Self as CollatableRecord<B>>::CollatableRecordHeader: RecordHeader,
    <<Self as CollatableRecord<B>>::CollatableRecordHeader as RecordHeader>::RecordType: MappedRecord<ParsingContext = Self::ParsingContext> {
    type CollatableRecordHeader: CollatableRecordHeader<B>;
    fn from_bytes_collatable_header<T: Read>(
        reader: &mut T,
        context: &<Self as MappedRecord>::ParsingContext) -> anyhow::Result<Self::CollatableRecordHeader>;
}
*/

// ====== bulk

/// Header for a bulk RNA-seq read record
#[allow(unused)]
struct PiscemBulkReadRecordHeader {
    pub na: u32,
}
impl RecordHeader for PiscemBulkReadRecordHeader {
    type RecordType = PiscemBulkReadRecord;
    fn naln(&self) -> u32 {
        self.na
    }
}

// ====== generic

/// Header for a generic record type, the only guaranteed field is
/// the number of alignments
#[allow(unused)]
struct GenericReadRecordHeader {
    pub na: u32,
}

impl RecordHeader for GenericReadRecordHeader {
    type RecordType = GenericReadRecord;
    fn naln(&self) -> u32 {
        self.na
    }
}

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
    pub fn fmt_with_context(
        &self,
        ctx: &GenericReadRecordContext,
        f: &mut impl Write,
    ) -> std::io::Result<()> {
        f.write_all(
            format!(
                "GenericReadRecord{{ naln: {}, naln_tags: {},\nrtags: {},\natags:  {} }}\n",
                self.naln,
                self.naln_tags,
                ctx.read_tags
                    .iter_desc()
                    .zip(self.rtags.iter())
                    .map(|(td, tv)| format!("{} : [{:?}]", td.name, tv))
                    .collect::<Vec<_>>()
                    .join(", "),
                self.atags
                    .chunks_exact(self.naln_tags as usize)
                    .map(|vchunk| {
                        ctx.aln_tags
                            .iter_desc()
                            .zip(vchunk.iter())
                            .map(|(td, tv)| format!("{} : [{:?}]", td.name, tv))
                            .collect::<Vec<_>>()
                            .join(", ")
                    })
                    .collect::<Vec<_>>()
                    .join("\n\t")
            )
            .as_bytes(),
        )
    }
}

/// context needed to read a generic record
#[derive(Debug, Clone)]
pub struct GenericReadRecordContext {
    pub read_tags: TagSection,
    pub aln_tags: TagSection,
}

// ### Known size trait

pub trait KnownSize {
    // returns the number of bytes taken for a record of the given type
    // with na alignments
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize
    where
        Self: MappedRecord;

    /// number of bytes for an individual alignment record
    fn nbytes_aln(ctx: &<Self as MappedRecord>::ParsingContext) -> usize
    where
        Self: MappedRecord;
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
        (na as usize * Self::nbytes_aln(ctx))
    }

    fn nbytes_aln(_ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // ori_ref
        std::mem::size_of::<u32>()
    }
}

impl<B: ConvertiblePrimitiveInteger> KnownSize for AlevinFryReadRecordWithPositionT<B> {
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // for na field
        std::mem::size_of::<u32>() +
        // for bc
        ctx.bct.bytes_for_type() +
        // for umi 
        ctx.umit.bytes_for_type() +
        // an ori_ref for each alignment
        (na as usize * Self::nbytes_aln(ctx))
    }

    fn nbytes_aln(_ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // ori_ref
        std::mem::size_of::<u32>()
        // position
        + std::mem::size_of::<u32>()
    }
}

impl KnownSize for PiscemBulkReadRecord {
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // for na field
        std::mem::size_of::<u32>() +
        // for frag type
        ctx.frag_map_t.bytes_for_type() +
        // for each alignment a 
        (na as usize * Self::nbytes_aln(ctx))
    }

    fn nbytes_aln(_ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // (mapped_fragment_orientation + reference): u32,
        // position: u32
        // frag length: u16
        std::mem::size_of::<u32>() + std::mem::size_of::<u32>() + std::mem::size_of::<u16>()
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
        (na as usize * Self::nbytes_aln(ctx))
    }

    fn nbytes_aln(_ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // (ori_refernce): u32,
        std::mem::size_of::<u32>()
        // read_start : u32,
        + std::mem::size_of::<u32>()
        // read_end: u32,
        + std::mem::size_of::<u32>()
        // alignment_score: i32,
        + std::mem::size_of::<i32>()
        // tlen: u32 (NOTE: this should be moved to a file-level tag)
        + std::mem::size_of::<u32>()
    }
}

impl KnownSize for AtacSeqReadRecord {
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // for na field
        std::mem::size_of::<u32>() +
        // for barcode type
        ctx.bct.bytes_for_type() +
        // for each alignment a 
        (na as usize * Self::nbytes_aln(ctx))
    }

    fn nbytes_aln(_ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // start_pos: u32,
        // ref: u32,
        // frag_len: u16,
        // map_type: u8,
        std::mem::size_of::<u32>()
            + std::mem::size_of::<u32>()
            + std::mem::size_of::<u16>()
            + std::mem::size_of::<u8>()
    }
}

/// Trait to represent records that are tagged with a UMI
pub trait UmiTaggedRecord {
    fn umi(&self) -> u64;
}

/// A concrete struct representing a [MappedRecord]
/// for reads processed upstream with `piscem` (or `salmon alevin`).
/// This represents the set of alignments and relevant information
/// for a basic alevin-fry record.
#[derive(Clone, Debug, PartialEq, Eq, UmiTagged)]
pub struct AlevinFryReadRecordT<B: ConvertiblePrimitiveInteger> {
    pub bc: B,
    pub umi: u64,
    pub dirs: Vec<bool>,
    pub refs: Vec<u32>,
}

/// A concrete struct representing a [MappedRecord]
/// for reads processed upstream with `piscem` (or `salmon alevin`).
/// This represents the set of alignments and relevant information
/// for an alevin-fry record that also records read position.
#[derive(Clone, Debug, PartialEq, Eq, UmiTagged)]
pub struct AlevinFryReadRecordWithPositionT<B: ConvertiblePrimitiveInteger> {
    pub bc: B,
    pub umi: u64,
    pub dirs: Vec<bool>,
    pub refs: Vec<u32>,
    pub pos: Vec<u32>,
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
#[derive(Clone, Debug, PartialEq, Eq, UmiTagged)]
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

pub trait CollatableMappedRecord<B: ConvertiblePrimitiveInteger>: MappedRecord
where
    // to help the trait solver
    <Self as CollatableMappedRecord<B>>::CollatableRecordHeader: RecordHeader,
    <<Self as CollatableMappedRecord<B>>::CollatableRecordHeader as RecordHeader>::RecordType:
        MappedRecord<ParsingContext = Self::ParsingContext>,
{
    type CollatableRecordHeader: CollatableRecordHeader<B>;
    /// Given a [RecordHeader] for this record (which has already been read and parsed), read
    /// a set of alignments for the record while retaining only those matching the prescribed
    /// oreientation
    fn from_bytes_with_header_retain_ori<T: Read>(
        reader: &mut T,
        hdr: &mut Self::CollatableRecordHeader,
        ctx: &<Self as MappedRecord>::ParsingContext,
        expected_ori: &MappedFragmentOrientation,
    ) -> Self;

    /// set the key by which this record should be collated
    fn set_collate_key(&mut self, k: B);

    /// get the key by which this record should be collated (e.g. call barcode)
    fn collate_key(&self) -> B;

    fn from_bytes_collatable_header<T: Read>(
        reader: &mut T,
        context: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader>;

    fn peek_collatable_header(
        reader: &[u8],
        context: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader>;
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

    /// true if there are no alignments for this mapped record, false otherwise
    fn is_empty(&self) -> bool;

    /// The number of alignments for this mapped record
    fn num_aln(&self) -> usize;

    /// return a reference to the targets to which this
    /// record aligns.
    fn refs(&self) -> &[u32];

    /// Returns true if this record has any alignment records occuring on the provided
    /// strand.
    /// NOTE:
    ///   - all alignments are compatible with an unknown strand
    ///   - for paired-end mappings, this function looks for cases where read 1 matches the
    ///     provided strand
    fn has_alignment_on_strand(&self, s: Strand) -> bool;
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
/// NOTE: This context is shared between the basic and positionally aware
/// AlevinFryReadRecord types
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
            bail!(
                "piscem bulk record context requries that \"frag_map_type\" tag is of type RadType::Int"
            );
        }
    }
}

impl MappedRecord for PiscemBulkReadRecord {
    type ParsingContext = PiscemBulkRecordContext;
    type PeekResult = Option<u64>;

    fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    fn num_aln(&self) -> usize {
        self.refs.len()
    }

    fn refs(&self) -> &[u32] {
        &self.refs
    }

    fn has_alignment_on_strand(&self, s: Strand) -> bool {
        match s {
            Strand::Unknown => !self.refs.is_empty(),
            Strand::Forward => self.dirs.iter().any(|&x| {
                matches!(
                    x,
                    MappedFragmentOrientation::Forward
                        | MappedFragmentOrientation::ForwardReverse
                        | MappedFragmentOrientation::ForwardForward
                        | MappedFragmentOrientation::Unknown
                )
            }),
            Strand::Reverse => self.dirs.iter().any(|&x| {
                matches!(
                    x,
                    MappedFragmentOrientation::Reverse
                        | MappedFragmentOrientation::ReverseForward
                        | MappedFragmentOrientation::ReverseReverse
                        | MappedFragmentOrientation::Unknown
                )
            }),
        }
    }

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
        unimplemented!(
            "Currently there is no implementation for peek_record for PiscemBulkReadRecord. This should not be needed"
        );
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

impl<B: ConvertiblePrimitiveInteger> CollatableMappedRecord<B> for AlevinFryReadRecordT<B> {
    type CollatableRecordHeader = AlevinFryReadRecordHeader<B>;
    #[inline]
    fn from_bytes_with_header_retain_ori<T: Read>(
        reader: &mut T,
        hdr: &mut Self::CollatableRecordHeader,
        _ctx: &<Self as MappedRecord>::ParsingContext,
        expected_ori: &MappedFragmentOrientation,
    ) -> Self {
        let rec = AlevinFryReadRecordT::<B>::from_bytes_with_header_keep_ori(
            reader,
            hdr.bc,
            hdr.umi,
            hdr.naln,
            expected_ori.into(),
        );
        hdr.naln = rec.refs.len() as u32;
        rec
    }

    fn set_collate_key(&mut self, k: B) {
        self.bc = k;
    }
    fn collate_key(&self) -> B {
        self.bc
    }

    fn from_bytes_collatable_header<T: Read>(
        reader: &mut T,
        context: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf);
        let bc = rad_io::read_into::<T, B>(reader, &context.bct);
        // NOTE: We likely will want to make the UMI generic as well
        let umi = rad_io::read_into_u64(reader, &context.umit);
        Ok(Self::CollatableRecordHeader { naln: na, bc, umi })
    }

    fn peek_collatable_header(
        buf: &[u8],
        ctx: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let na_size = mem::size_of::<u32>();
        let bc_size = ctx.bct.bytes_for_type();

        let na = buf.pread::<u32>(0).unwrap();

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
        Ok(Self::CollatableRecordHeader { naln: na, bc, umi })
    }
}

impl<B: ConvertiblePrimitiveInteger> CollatableMappedRecord<B>
    for AlevinFryReadRecordWithPositionT<B>
{
    type CollatableRecordHeader = AlevinFryReadRecordHeader<B>;
    #[inline]
    fn from_bytes_with_header_retain_ori<T: Read>(
        reader: &mut T,
        hdr: &mut Self::CollatableRecordHeader,
        _ctx: &<Self as MappedRecord>::ParsingContext,
        expected_ori: &MappedFragmentOrientation,
    ) -> Self {
        let rec = AlevinFryReadRecordWithPositionT::<B>::from_bytes_with_header_keep_ori(
            reader,
            hdr.bc,
            hdr.umi,
            hdr.naln,
            expected_ori.into(),
        );
        hdr.naln = rec.refs.len() as u32;
        rec
    }

    fn set_collate_key(&mut self, k: B) {
        self.bc = k;
    }
    fn collate_key(&self) -> B {
        self.bc
    }

    fn from_bytes_collatable_header<T: Read>(
        reader: &mut T,
        context: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf);
        let bc = rad_io::read_into::<T, B>(reader, &context.bct);
        // NOTE: We likely will want to make the UMI generic as well
        let umi = rad_io::read_into_u64(reader, &context.umit);
        Ok(Self::CollatableRecordHeader { naln: na, bc, umi })
    }

    fn peek_collatable_header(
        buf: &[u8],
        ctx: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let na_size = mem::size_of::<u32>();
        let bc_size = ctx.bct.bytes_for_type();

        let na = buf.pread::<u32>(0).unwrap();

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
        Ok(Self::CollatableRecordHeader { naln: na, bc, umi })
    }
}

impl<B: ConvertiblePrimitiveInteger> MappedRecord for AlevinFryReadRecordT<B> {
    type ParsingContext = AlevinFryRecordContext;
    type PeekResult = (B, u64);
    /// Returns `true` if this [AlevinFryReadRecord] contains no references and
    /// `false` otherwise.
    fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }
    /// Returns `true` if this [AlevinFryReadRecord] contains no references and
    /// `false` otherwise.
    fn num_aln(&self) -> usize {
        self.refs.len()
    }

    fn refs(&self) -> &[u32] {
        &self.refs
    }

    fn has_alignment_on_strand(&self, s: Strand) -> bool {
        match s {
            Strand::Unknown => !self.refs.is_empty(),
            Strand::Forward => self.dirs.iter().any(|&x| x),
            Strand::Reverse => self.dirs.iter().any(|&x| !x),
        }
    }

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

        // if we don't have orientations (because of filtering) then just pretend they are false
        let dir_iter = self.dirs.iter();
        for (dir, ref_idx) in
            itertools::izip!(dir_iter.chain(std::iter::repeat(&false)), &self.refs)
        {
            let encoded_dir: u32 = if *dir { 1_u32 << 31 } else { 0_u32 };
            let encoded_dir_ref: u32 = ref_idx | encoded_dir;
            writer
                .write_all(&encoded_dir_ref.to_le_bytes())
                .context("couldn't write compressed_ori_refid for record")?;
        }
        Ok(())
    }
}

impl<B: ConvertiblePrimitiveInteger> MappedRecord for AlevinFryReadRecordWithPositionT<B> {
    type ParsingContext = AlevinFryRecordContext;
    type PeekResult = (B, u64);
    /// Returns `true` if this [AlevinFryReadRecord] contains no references and
    /// `false` otherwise.
    fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }
    /// Returns `true` if this [AlevinFryReadRecord] contains no references and
    /// `false` otherwise.
    fn num_aln(&self) -> usize {
        self.refs.len()
    }

    fn refs(&self) -> &[u32] {
        &self.refs
    }

    fn has_alignment_on_strand(&self, s: Strand) -> bool {
        match s {
            Strand::Unknown => !self.refs.is_empty(),
            Strand::Forward => self.dirs.iter().any(|&x| x),
            Strand::Reverse => self.dirs.iter().any(|&x| !x),
        }
    }

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
            pos: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..8]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();
            let dir = (v & utils::MASK_LOWER_31_U32) != 0;
            rec.dirs.push(dir);
            rec.refs.push(v & utils::MASK_TOP_BIT_U32);
            let pos = rbuf.pread::<u32>(std::mem::size_of::<u32>()).unwrap();
            rec.pos.push(pos);
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

        // if we don't have orientations (because of filtering) then just pretend they are false
        let dir_iter = self.dirs.iter();
        for (dir, ref_idx, pos) in itertools::izip!(
            dir_iter.chain(std::iter::repeat(&false)),
            &self.refs,
            &self.pos
        ) {
            let encoded_dir: u32 = if *dir { 1_u32 << 31 } else { 0_u32 };
            let encoded_dir_ref: u32 = ref_idx | encoded_dir;
            writer
                .write_all(&encoded_dir_ref.to_le_bytes())
                .context("couldn't write compressed_ori_refid for record")?;
            writer
                .write_all(&pos.to_le_bytes())
                .context("couldn't write position for record")?;
        }
        Ok(())
    }
}

impl MappedRecord for GenericReadRecord {
    type ParsingContext = GenericReadRecordContext;
    type PeekResult = Option<u64>;

    fn is_empty(&self) -> bool {
        self.atags.is_empty()
    }

    fn num_aln(&self) -> usize {
        self.naln as usize
    }

    fn has_alignment_on_strand(&self, _s: Strand) -> bool {
        unimplemented!("no implementation of has_alignment_on_strand for GenericReadRecord")
    }

    fn refs(&self) -> &[u32] {
        unimplemented!("no implementation of refs() for GenericReadRecord yet")
    }

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

    /*
    #[inline]
    fn from_bytes_with_header_retain_ori<T: Read>(reader: &mut T, hdr: &Self::RecordHeader, ctx: &Self::ParsingContext, expected_ori: &MappedFragmentOrientation) -> Self {
        // NOTE: Don't know if there is an ori here so right now pass through everything
        let na = hdr.na;
        let mut rbuf = [0u8; 255];

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
    */

    #[inline]
    fn peek_record(_buf: &[u8], _ctx: &Self::ParsingContext) -> Self::PeekResult {
        unimplemented!(
            "Currently there is no implementation for peek_record for GenericRecord. This should not be needed"
        );
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
                let dir = (v & utils::MASK_LOWER_31_U32) != 0;
                rec.dirs.push(dir);
                rec.refs.push(v & utils::MASK_TOP_BIT_U32);
            }
        }

        // make sure these are sorted in this step.
        let indices = argsort(&rec.refs);
        reorder_in_place(&mut rec.refs, &indices);
        reorder_in_place(&mut rec.dirs, &indices);
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

impl<B: ConvertiblePrimitiveInteger> AlevinFryReadRecordWithPositionT<B> {
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
            pos: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..8]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();
            let dir = (v & utils::MASK_LOWER_31_U32) != 0;
            rec.dirs.push(dir);
            rec.refs.push(v & utils::MASK_TOP_BIT_U32);
            let pos = rbuf.pread::<u32>(std::mem::size_of::<u32>()).unwrap();
            rec.pos.push(pos);
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
            pos: Vec::with_capacity(na as usize),
        };

        for _ in 0..(na as usize) {
            reader.read_exact(&mut rbuf[0..8]).unwrap();
            let v = rbuf.pread::<u32>(0).unwrap();

            // fw if the leftmost bit is 1, otherwise rc
            let strand = if (v & utils::MASK_LOWER_31_U32) > 0 {
                Strand::Forward
            } else {
                Strand::Reverse
            };

            if expected_ori.same(&strand) || expected_ori.is_unknown() {
                let pos = rbuf.pread::<u32>(std::mem::size_of::<u32>()).unwrap();
                let dir = (v & utils::MASK_LOWER_31_U32) != 0;
                rec.dirs.push(dir);
                rec.refs.push(v & utils::MASK_TOP_BIT_U32);
                rec.pos.push(pos);
            }
        }

        // make sure these are sorted in this step.
        let indices = argsort(&rec.refs);
        reorder_in_place(&mut rec.refs, &indices);
        reorder_in_place(&mut rec.dirs, &indices);
        reorder_in_place(&mut rec.pos, &indices);
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
        // The scATAC barcode read-level tag is named "barcode" by the original
        // C++ piscem writer, but "b" by the Rust piscem-rs writer (which reuses
        // the scRNA convention). Accept either so we can read RAD files produced
        // by both implementations. Return an error rather than panicking so a
        // genuinely missing tag surfaces cleanly instead of wedging a reader
        // thread.
        let bct = rt
            .get_tag_type("barcode")
            .or_else(|| rt.get_tag_type("b"))
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "atac-reader record context requires a 'barcode' (or 'b') read-level tag"
                )
            })?;

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

impl CollatableMappedRecord<u64> for AtacSeqReadRecord {
    type CollatableRecordHeader = AtacSeqReadRecordHeader;
    fn from_bytes_collatable_header<T: Read>(
        reader: &mut T,
        context: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf);
        let bc = rad_io::read_into_u64(reader, &context.bct);
        Ok(Self::CollatableRecordHeader { naln: na, bc })
    }

    fn peek_collatable_header(
        buf: &[u8],
        ctx: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let na_size = mem::size_of::<u32>();

        let na = buf.pread::<u32>(0).unwrap();

        let bc: u64 = match ctx.bct {
            RadIntId::U8 => NewU8(buf.pread::<u8>(na_size).unwrap()).into(),
            RadIntId::U16 => NewU16(buf.pread::<u16>(na_size).unwrap()).into(),
            RadIntId::U32 => NewU32(buf.pread::<u32>(na_size).unwrap()).into(),
            RadIntId::U64 => NewU64(buf.pread::<u64>(na_size).unwrap()).into(),
            RadIntId::U128 => NewU128(buf.pread::<u128>(na_size).unwrap()).into(),
            _ => panic!("signed barcode integer encodings are not supported"),
        };
        Ok(Self::CollatableRecordHeader { naln: na, bc })
    }

    fn set_collate_key(&mut self, k: u64) {
        self.bc = k;
    }
    fn collate_key(&self) -> u64 {
        self.bc
    }

    #[inline]
    fn from_bytes_with_header_retain_ori<T: Read>(
        reader: &mut T,
        hdr: &mut Self::CollatableRecordHeader,
        _ctx: &<Self as MappedRecord>::ParsingContext,
        _expected_ori: &MappedFragmentOrientation,
    ) -> Self {
        // NOTE: No orientation recorded for ATACSeq records, so everything is retained
        let mut rbuf = [0u8; 255];
        let na = hdr.naln;
        let bc = hdr.bc;

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
        hdr.naln = rec.refs.len() as u32;
        rec
    }
}

impl MappedRecord for AtacSeqReadRecord {
    type ParsingContext = AtacSeqRecordContext;
    type PeekResult = u64;

    /// Returns `true` if this [AtacSeqReadRecord] contains no references and
    /// `false` otherwise.
    fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    fn num_aln(&self) -> usize {
        self.refs.len()
    }

    fn has_alignment_on_strand(&self, _s: Strand) -> bool {
        // we don't record the orientation, so right now
        // treat everything as compatible
        !self.refs.is_empty()
    }

    fn refs(&self) -> &[u32] {
        &self.refs
    }

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
    fn write<W: Write>(&self, writer: &mut W, ctx: &Self::ParsingContext) -> anyhow::Result<()> {
        let na: u32 = self.refs.len() as u32;
        RadIntId::U32
            .write_to(na, writer)
            .context("couldn't write number of alignments for AtacSeq record")?;
        ctx.bct
            .write_to(self.bc, writer)
            .context("couldn't write bc field for AtacSeq record")?;

        for i in 0..(na as usize) {
            writer
                .write_all(&self.refs[i].to_le_bytes())
                .context("couldn't write ref for AtacSeq alignment")?;
            writer
                .write_all(&self.map_type[i].to_le_bytes())
                .context("couldn't write map_type for AtacSeq alignment")?;
            writer
                .write_all(&self.start_pos[i].to_le_bytes())
                .context("couldn't write start_pos for AtacSeq alignment")?;
            writer
                .write_all(&self.frag_lengths[i].to_le_bytes())
                .context("couldn't write frag_length for AtacSeq alignment")?;
        }
        Ok(())
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
        reorder_in_place(&mut rec.refs, &indices);
        reorder_in_place(&mut rec.map_type, &indices);
        reorder_in_place(&mut rec.start_pos, &indices);
        reorder_in_place(&mut rec.frag_lengths, &indices);
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

impl<B: ConvertiblePrimitiveInteger> CollatableMappedRecord<B> for ScLongReadRecordT<B> {
    type CollatableRecordHeader = ScLongReadRecordHeader<B>;
    fn from_bytes_collatable_header<T: Read>(
        reader: &mut T,
        context: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf);
        let bc = rad_io::read_into::<T, B>(reader, &context.bct);
        // NOTE: We likely will want to make the UMI generic as well
        let umi = rad_io::read_into_u64(reader, &context.umit);
        Ok(Self::CollatableRecordHeader { naln: na, bc, umi })
    }

    fn peek_collatable_header(
        buf: &[u8],
        ctx: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let na_size = mem::size_of::<u32>();
        let bc_size = ctx.bct.bytes_for_type();

        let na = buf.pread::<u32>(0).unwrap();

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
        Ok(Self::CollatableRecordHeader { naln: na, bc, umi })
    }

    fn set_collate_key(&mut self, k: B) {
        self.bc = k;
    }
    fn collate_key(&self) -> B {
        self.bc
    }

    #[inline]
    fn from_bytes_with_header_retain_ori<T: Read>(
        reader: &mut T,
        hdr: &mut Self::CollatableRecordHeader,
        _ctx: &<Self as MappedRecord>::ParsingContext,
        expected_ori: &MappedFragmentOrientation,
    ) -> Self {
        let na = hdr.naln;
        let bc = hdr.bc;
        let umi = hdr.umi;
        let mut rbuf = [0u8; 255];

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

            // 2) AS score
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let as_score = rbuf.pread::<i32>(0).unwrap();

            // 3) start
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let start = rbuf.pread::<u32>(0).unwrap();

            // 4) end
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let end = rbuf.pread::<u32>(0).unwrap();

            // 5) tlen
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            let tlen = rbuf.pread::<u32>(0).unwrap();

            // fw if the leftmost bit is 1, otherwise rc
            let strand = if (v & utils::MASK_LOWER_31_U32) > 0 {
                Strand::Forward
            } else {
                Strand::Reverse
            }
            .into();

            if expected_ori.same(&strand) || expected_ori.is_unknown() {
                rec.dirs.push(dir);
                rec.refs.push(ref_id);
                rec.as_scores.push(as_score);
                rec.starts.push(start);
                rec.ends.push(end);
                rec.tlens.push(tlen);
            }
        }
        hdr.naln = rec.refs.len() as u32;
        // sort all fields by ref
        let indices = argsort(&rec.refs);
        reorder_in_place(&mut rec.dirs, &indices);
        reorder_in_place(&mut rec.refs, &indices);
        reorder_in_place(&mut rec.as_scores, &indices);
        reorder_in_place(&mut rec.starts, &indices);
        reorder_in_place(&mut rec.ends, &indices);
        reorder_in_place(&mut rec.tlens, &indices);
        rec
    }
}

impl<B: ConvertiblePrimitiveInteger> MappedRecord for ScLongReadRecordT<B> {
    type ParsingContext = ScLongReadRecordContext;
    type PeekResult = (B, u64);

    /// Returns `true` if this [ScLongReadRecord] contains no references and
    /// `false` otherwise.
    fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    fn num_aln(&self) -> usize {
        self.refs.len()
    }

    fn refs(&self) -> &[u32] {
        &self.refs
    }

    fn has_alignment_on_strand(&self, s: Strand) -> bool {
        match s {
            Strand::Unknown => !self.refs.is_empty(),
            Strand::Forward => self.dirs.iter().any(|&x| x),
            Strand::Reverse => self.dirs.iter().any(|&x| !x),
        }
    }

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
        unimplemented!("from_bytes_with_header is not implemented for ScLongReadRecordT");
    }
}

// ====== Multi-barcode records (for 10x Flex and similar protocols) ======

/// The default [MultiBarcodeReadRecordT] holds barcodes in [u64]
pub type MultiBarcodeReadRecord = MultiBarcodeReadRecordT<u64>;

/// A [MultiBarcodeReadRecordT] that holds barcodes in [u64] and is explicit about this
pub type MultiBarcodeReadRecordU64 = MultiBarcodeReadRecordT<u64>;

/// A [MultiBarcodeReadRecordT] that holds barcodes in [u128] and is explicit about this
pub type MultiBarcodeReadRecordU128 = MultiBarcodeReadRecordT<u128>;

/// Maximum number of barcode levels supported inline (no heap allocation).
/// This covers all known protocols (typically 2, at most ~4).
pub const MAX_INLINE_BARCODES: usize = 4;

/// A read record carrying multiple barcodes for multi-barcode protocols.
/// Uses SmallVec with a small inline capacity since the number of barcodes
/// per read is always very small (typically 2, at most ~4).
/// SmallVec avoids heap allocation for these small counts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultiBarcodeReadRecordT<B: ConvertiblePrimitiveInteger> {
    /// Barcodes at each level: b0, b1, ..., b{N-1} in order.
    /// For 10x Flex: b0 = sample barcode, b1 = cell barcode.
    pub barcodes: SmallVec<[B; MAX_INLINE_BARCODES]>,
    pub umi: u64,
    pub dirs: Vec<bool>,
    pub refs: Vec<u32>,
}

impl<B: ConvertiblePrimitiveInteger> UmiTaggedRecord for MultiBarcodeReadRecordT<B> {
    fn umi(&self) -> u64 {
        self.umi
    }
}

/// Context needed to read a multi-barcode record.
/// Stores the integer type for each barcode level and the UMI type.
#[derive(Debug, Clone)]
pub struct MultiBarcodeRecordContext {
    /// The integer type of each barcode level (b0, b1, ...)
    pub bc_types: SmallVec<[RadIntId; MAX_INLINE_BARCODES]>,
    /// The integer type of the UMI
    pub umit: RadIntId,
    /// The semantic roles of each barcode level
    pub roles: SmallVec<[BarcodeRole; MAX_INLINE_BARCODES]>,
}

impl RecordContext for MultiBarcodeRecordContext {
    fn get_context_from_tag_section(
        ft: &TagSection,
        rt: &TagSection,
        _at: &TagSection,
    ) -> anyhow::Result<Self> {
        // Determine the number of barcodes from the file-level tag
        let num_barcodes_tag = ft.get_tag_type("num_barcodes");
        let num_barcodes = if let Some(RadType::Int(_)) = num_barcodes_tag {
            // We'll read the actual value from the tag map at a higher level;
            // here we discover barcode tags from the read-level tag section.
            // Count how many b0, b1, b2, ... tags exist.
            let mut count = 0usize;
            while rt.get_tag_type(&format!("b{}", count)).is_some() {
                count += 1;
            }
            if count == 0 {
                bail!(
                    "multi-barcode record context: num_barcodes file tag present but no bN read-level tags found"
                );
            }
            count
        } else {
            bail!("multi-barcode record context requires a 'num_barcodes' file-level tag");
        };

        let mut bc_types = SmallVec::new();
        for i in 0..num_barcodes {
            let tag_name = format!("b{}", i);
            let bct = rt.get_tag_type(&tag_name).ok_or_else(|| {
                anyhow::anyhow!(
                    "multi-barcode record context requires a '{}' read-level tag",
                    tag_name
                )
            })?;
            if let RadType::Int(x) = bct {
                bc_types.push(x);
            } else {
                bail!(
                    "multi-barcode record context requires that '{}' tag is of type RadType::Int",
                    tag_name
                );
            }
        }

        let umit = rt
            .get_tag_type("u")
            .expect("multi-barcode record context requires a 'u' read-level tag");
        let umit = if let RadType::Int(x) = umit {
            x
        } else {
            bail!("multi-barcode record context requires that 'u' tag is of type RadType::Int");
        };

        // Parse barcode roles from file-level tag if present, otherwise use defaults
        let roles = Self::parse_roles_or_default(ft, num_barcodes)?;

        Ok(Self {
            bc_types,
            umit,
            roles,
        })
    }
}

impl MultiBarcodeRecordContext {
    /// Create a new context from explicit barcode types, UMI type, and roles.
    pub fn new(
        bc_types: SmallVec<[RadIntId; MAX_INLINE_BARCODES]>,
        umit: RadIntId,
        roles: SmallVec<[BarcodeRole; MAX_INLINE_BARCODES]>,
    ) -> Self {
        Self {
            bc_types,
            umit,
            roles,
        }
    }

    /// Number of barcode levels in this context.
    pub fn num_barcodes(&self) -> usize {
        self.bc_types.len()
    }

    /// Total bytes for all barcode fields in a record.
    pub fn total_bc_bytes(&self) -> usize {
        self.bc_types.iter().map(|t| t.bytes_for_type()).sum()
    }

    /// Parse barcode roles from the file-level tag section, or use defaults.
    fn parse_roles_or_default(
        ft: &TagSection,
        num_barcodes: usize,
    ) -> anyhow::Result<SmallVec<[BarcodeRole; MAX_INLINE_BARCODES]>> {
        // TODO: Parse barcode_roles from file-level tag when the ArrayString
        // tag type is implemented. For now, use defaults.
        let _ = ft;
        let mut roles = SmallVec::new();
        for i in 0..num_barcodes {
            if i == 0 && num_barcodes > 1 {
                roles.push(BarcodeRole::Sample);
            } else {
                roles.push(BarcodeRole::Cell);
            }
        }
        Ok(roles)
    }
}

/// Header information for a [MultiBarcodeReadRecord].
pub struct MultiBarcodeReadRecordHeader<B: ConvertiblePrimitiveInteger> {
    pub naln: u32,
    pub barcodes: SmallVec<[B; MAX_INLINE_BARCODES]>,
    pub umi: u64,
}

impl<B: ConvertiblePrimitiveInteger> RecordHeader for MultiBarcodeReadRecordHeader<B> {
    type RecordType = MultiBarcodeReadRecordT<B>;
    fn naln(&self) -> u32 {
        self.naln
    }
}

impl<B: ConvertiblePrimitiveInteger> CollatableRecordHeader<B> for MultiBarcodeReadRecordHeader<B> {
    /// Returns the innermost (last) barcode as the collation key,
    /// which is typically the cell barcode.
    fn collate_key(&self) -> B {
        *self
            .barcodes
            .last()
            .expect("multi-barcode header must have at least one barcode")
    }

    fn collation_group_key(
        &self,
        ctx: &<<Self as RecordHeader>::RecordType as MappedRecord>::ParsingContext,
    ) -> u64
    where
        u64: From<B>,
    {
        if self.barcodes.len() < 2 {
            return self.collate_key().into();
        }

        let cell_bits = (ctx
            .bc_types
            .last()
            .expect("multi-barcode context must have at least one barcode type")
            .bytes_for_type()
            * 8) as u32;
        let sample = u64::from(self.barcodes[0]);
        let cell = u64::from(
            *self
                .barcodes
                .last()
                .expect("multi-barcode header must have at least one barcode"),
        );

        if cell_bits >= 64 {
            cell
        } else {
            (sample << cell_bits) | (cell & ((1_u64 << cell_bits) - 1))
        }
    }

    fn write_fields<W: Write>(
        &self,
        writer: &mut W,
        ctx: &<<Self as RecordHeader>::RecordType as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<()> {
        let na: u32 = self.naln();
        RadIntId::U32
            .write_to(na, writer)
            .context("couldn't write number of alignments for multi-barcode record")?;
        for (bc, bct) in self.barcodes.iter().zip(ctx.bc_types.iter()) {
            bct.write_to(*bc, writer)
                .context("couldn't write barcode field for multi-barcode record")?;
        }
        ctx.umit
            .write_to(self.umi, writer)
            .context("couldn't write umi field for multi-barcode record")?;
        Ok(())
    }
}

impl<B: ConvertiblePrimitiveInteger> KnownSize for MultiBarcodeReadRecordT<B> {
    fn nbytes(na: u32, ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // for na field
        std::mem::size_of::<u32>()
        // for all barcodes
        + ctx.total_bc_bytes()
        // for umi
        + ctx.umit.bytes_for_type()
        // an ori_ref for each alignment
        + (na as usize * Self::nbytes_aln(ctx))
    }

    fn nbytes_aln(_ctx: &<Self as MappedRecord>::ParsingContext) -> usize {
        // ori_ref
        std::mem::size_of::<u32>()
    }
}

impl<B: ConvertiblePrimitiveInteger> MappedRecord for MultiBarcodeReadRecordT<B> {
    type ParsingContext = MultiBarcodeRecordContext;
    /// Peek returns all barcodes and the UMI
    type PeekResult = (SmallVec<[B; MAX_INLINE_BARCODES]>, u64);

    fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    fn num_aln(&self) -> usize {
        self.refs.len()
    }

    fn refs(&self) -> &[u32] {
        &self.refs
    }

    fn has_alignment_on_strand(&self, s: Strand) -> bool {
        match s {
            Strand::Unknown => !self.refs.is_empty(),
            Strand::Forward => self.dirs.iter().any(|&x| x),
            Strand::Reverse => self.dirs.iter().any(|&x| !x),
        }
    }

    #[inline]
    fn peek_record(buf: &[u8], ctx: &Self::ParsingContext) -> Self::PeekResult {
        let na_size = mem::size_of::<u32>();
        let _na = buf.pread::<u32>(0).unwrap();

        let mut offset = na_size;
        let mut barcodes = SmallVec::new();
        for bct in &ctx.bc_types {
            let bc: B = match bct {
                RadIntId::U8 => NewU8(buf.pread::<u8>(offset).unwrap()).into(),
                RadIntId::U16 => NewU16(buf.pread::<u16>(offset).unwrap()).into(),
                RadIntId::U32 => NewU32(buf.pread::<u32>(offset).unwrap()).into(),
                RadIntId::U64 => NewU64(buf.pread::<u64>(offset).unwrap()).into(),
                RadIntId::U128 => NewU128(buf.pread::<u128>(offset).unwrap()).into(),
                _ => panic!("signed barcode integer encodings are not supported"),
            };
            barcodes.push(bc);
            offset += bct.bytes_for_type();
        }

        let umi = match ctx.umit {
            RadIntId::U8 => buf.pread::<u8>(offset).unwrap() as u64,
            RadIntId::U16 => buf.pread::<u16>(offset).unwrap() as u64,
            RadIntId::U32 => buf.pread::<u32>(offset).unwrap() as u64,
            RadIntId::U64 => buf.pread::<u64>(offset).unwrap(),
            RadIntId::U128 => panic!("u128 is currently not supported as a umi type"),
            _ => panic!("signed umi integer encodings are not supported"),
        };
        (barcodes, umi)
    }

    #[inline]
    fn from_bytes_with_context<T: Read>(reader: &mut T, ctx: &Self::ParsingContext) -> Self {
        let mut rbuf = [0u8; 255];

        // Read naln
        reader.read_exact(&mut rbuf[0..4]).unwrap();
        let na = u32::from_le_bytes([rbuf[0], rbuf[1], rbuf[2], rbuf[3]]);

        // Read all barcodes
        let mut barcodes = SmallVec::new();
        for bct in &ctx.bc_types {
            let bc: B = rad_io::read_into(reader, bct);
            barcodes.push(bc);
        }

        // Read UMI
        let umi = rad_io::read_into_u64(reader, &ctx.umit);

        let mut rec = Self {
            barcodes,
            umi,
            dirs: Vec::with_capacity(na as usize),
            refs: Vec::with_capacity(na as usize),
        };

        // Read alignment records (same format as AlevinFryReadRecordT)
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
            .context("couldn't write number of alignments for multi-barcode record")?;

        // Write all barcodes
        for (bc, bct) in self.barcodes.iter().zip(ctx.bc_types.iter()) {
            bct.write_to(*bc, writer)
                .context("couldn't write barcode field for multi-barcode record")?;
        }

        ctx.umit
            .write_to(self.umi, writer)
            .context("couldn't write umi field for multi-barcode record")?;

        // Write alignment records
        let dir_iter = self.dirs.iter();
        for (dir, ref_idx) in
            itertools::izip!(dir_iter.chain(std::iter::repeat(&false)), &self.refs)
        {
            let encoded_dir: u32 = if *dir { 1_u32 << 31 } else { 0_u32 };
            let encoded_dir_ref: u32 = ref_idx | encoded_dir;
            writer
                .write_all(&encoded_dir_ref.to_le_bytes())
                .context("couldn't write compressed_ori_refid for multi-barcode record")?;
        }
        Ok(())
    }
}

impl<B: ConvertiblePrimitiveInteger> CollatableMappedRecord<B> for MultiBarcodeReadRecordT<B> {
    type CollatableRecordHeader = MultiBarcodeReadRecordHeader<B>;

    #[inline]
    fn from_bytes_with_header_retain_ori<T: Read>(
        reader: &mut T,
        hdr: &mut Self::CollatableRecordHeader,
        _ctx: &<Self as MappedRecord>::ParsingContext,
        expected_ori: &MappedFragmentOrientation,
    ) -> Self {
        let rec = MultiBarcodeReadRecordT::<B>::from_bytes_with_header_keep_ori(
            reader,
            hdr.barcodes.clone(),
            hdr.umi,
            hdr.naln,
            expected_ori.into(),
        );
        hdr.naln = rec.refs.len() as u32;
        rec
    }

    /// The collation key is the innermost (last) barcode, typically the cell barcode.
    fn set_collate_key(&mut self, k: B) {
        if let Some(last) = self.barcodes.last_mut() {
            *last = k;
        }
    }

    fn collate_key(&self) -> B {
        *self
            .barcodes
            .last()
            .expect("multi-barcode record must have at least one barcode")
    }

    fn from_bytes_collatable_header<T: Read>(
        reader: &mut T,
        context: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf);

        let mut barcodes = SmallVec::new();
        for bct in &context.bc_types {
            let bc: B = rad_io::read_into(reader, bct);
            barcodes.push(bc);
        }

        let umi = rad_io::read_into_u64(reader, &context.umit);

        Ok(Self::CollatableRecordHeader {
            naln: na,
            barcodes,
            umi,
        })
    }

    fn peek_collatable_header(
        buf: &[u8],
        ctx: &<Self as MappedRecord>::ParsingContext,
    ) -> anyhow::Result<Self::CollatableRecordHeader> {
        let na_size = mem::size_of::<u32>();
        let na = buf.pread::<u32>(0).unwrap();

        let mut offset = na_size;
        let mut barcodes = SmallVec::new();
        for bct in &ctx.bc_types {
            let bc: B = match bct {
                RadIntId::U8 => NewU8(buf.pread::<u8>(offset).unwrap()).into(),
                RadIntId::U16 => NewU16(buf.pread::<u16>(offset).unwrap()).into(),
                RadIntId::U32 => NewU32(buf.pread::<u32>(offset).unwrap()).into(),
                RadIntId::U64 => NewU64(buf.pread::<u64>(offset).unwrap()).into(),
                RadIntId::U128 => NewU128(buf.pread::<u128>(offset).unwrap()).into(),
                _ => panic!("signed barcode integer encodings are not supported"),
            };
            barcodes.push(bc);
            offset += bct.bytes_for_type();
        }

        let umi = match ctx.umit {
            RadIntId::U8 => buf.pread::<u8>(offset).unwrap() as u64,
            RadIntId::U16 => buf.pread::<u16>(offset).unwrap() as u64,
            RadIntId::U32 => buf.pread::<u32>(offset).unwrap() as u64,
            RadIntId::U64 => buf.pread::<u64>(offset).unwrap(),
            RadIntId::U128 => panic!("u128 is currently not supported as a umi type"),
            _ => panic!("signed umi integer encodings are not supported"),
        };

        Ok(Self::CollatableRecordHeader {
            naln: na,
            barcodes,
            umi,
        })
    }
}

// ====== Hierarchical collation trait ======

/// Trait for records that support hierarchical collation across multiple
/// barcode levels. This extends [CollatableMappedRecord] to provide
/// level-indexed access to barcodes.
///
/// Standard single-barcode record types do NOT implement this trait,
/// preserving the zero-overhead guarantee for the common case.
pub trait HierarchicallyCollatable<B: ConvertiblePrimitiveInteger>:
    CollatableMappedRecord<B>
{
    /// Number of barcode levels in this record (e.g., 2 for sample + cell).
    fn num_collation_levels(&self) -> usize;

    /// Get the collation key at a specific level.
    /// Level 0 is the outermost (e.g., sample), level N-1 is the innermost (e.g., cell).
    fn collation_key_at_level(&self, level: usize) -> B;

    /// Set the collation key at a specific level.
    fn set_collation_key_at_level(&mut self, level: usize, k: B);
}

impl<B: ConvertiblePrimitiveInteger> HierarchicallyCollatable<B> for MultiBarcodeReadRecordT<B> {
    fn num_collation_levels(&self) -> usize {
        self.barcodes.len()
    }

    fn collation_key_at_level(&self, level: usize) -> B {
        self.barcodes[level]
    }

    fn set_collation_key_at_level(&mut self, level: usize, k: B) {
        self.barcodes[level] = k;
    }
}

// Helper methods for MultiBarcodeReadRecordT
impl<B: ConvertiblePrimitiveInteger> MultiBarcodeReadRecordT<B> {
    /// Read the record header (naln, all barcodes, umi) from a reader.
    pub fn from_bytes_record_header<T: Read>(
        reader: &mut T,
        bc_types: &[RadIntId],
        umit: &RadIntId,
    ) -> (SmallVec<[B; MAX_INLINE_BARCODES]>, u64, u32) {
        let mut rbuf = [0u8; 4];
        reader.read_exact(&mut rbuf).unwrap();
        let na = u32::from_le_bytes(rbuf);

        let mut barcodes = SmallVec::new();
        for bct in bc_types {
            let bc: B = rad_io::read_into(reader, bct);
            barcodes.push(bc);
        }

        let umi = rad_io::read_into_u64(reader, umit);
        (barcodes, umi, na)
    }

    /// Read a record from a reader, retaining only alignments matching the
    /// prescribed orientation.
    #[inline]
    pub fn from_bytes_with_header_keep_ori<T: Read>(
        reader: &mut T,
        barcodes: SmallVec<[B; MAX_INLINE_BARCODES]>,
        umi: u64,
        na: u32,
        expected_ori: &Strand,
    ) -> Self {
        let mut rbuf = [0u8; 255];
        let mut rec = Self {
            barcodes,
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
                let dir = (v & utils::MASK_LOWER_31_U32) != 0;
                rec.dirs.push(dir);
                rec.refs.push(v & utils::MASK_TOP_BIT_U32);
            }
        }

        // make sure these are sorted in this step.
        let indices = argsort(&rec.refs);
        reorder_in_place(&mut rec.refs, &indices);
        reorder_in_place(&mut rec.dirs, &indices);
        rec
    }
}

/// Reusable alignment storage for allocation-free multi-barcode record
/// filtering and rewriting during collation.
#[derive(Debug, Default)]
pub struct MultiBarcodeRecordScratch {
    alignments: Vec<u32>,
}

impl MultiBarcodeRecordScratch {
    pub fn new() -> Self {
        Self::default()
    }

    /// Read and retain the alignments selected by `expected_ori`, then sort
    /// them by reference id while preserving the packed orientation bit.
    pub fn read_filtered<T: Read>(
        &mut self,
        reader: &mut T,
        num_alignments: u32,
        expected_ori: &MappedFragmentOrientation,
    ) -> anyhow::Result<()> {
        self.alignments.clear();
        self.alignments.reserve(num_alignments as usize);
        let mut bytes = [0_u8; 4];
        for _ in 0..num_alignments {
            reader.read_exact(&mut bytes)?;
            let encoded = u32::from_le_bytes(bytes);
            let observed = if encoded & utils::MASK_LOWER_31_U32 != 0 {
                MappedFragmentOrientation::Forward
            } else {
                MappedFragmentOrientation::Reverse
            };
            if expected_ori.is_unknown() || expected_ori.same(&observed) {
                self.alignments.push(encoded);
            }
        }

        if !self
            .alignments
            .windows(2)
            .all(|pair| (pair[0] & utils::MASK_TOP_BIT_U32) <= (pair[1] & utils::MASK_TOP_BIT_U32))
        {
            self.alignments
                .sort_unstable_by_key(|encoded| encoded & utils::MASK_TOP_BIT_U32);
        }
        Ok(())
    }

    pub fn num_alignments(&self) -> usize {
        self.alignments.len()
    }

    pub fn is_empty(&self) -> bool {
        self.alignments.is_empty()
    }

    #[inline]
    fn append_packed_alignments(&self, output: &mut Vec<u8>) {
        #[cfg(target_endian = "little")]
        output.extend_from_slice(bytemuck::cast_slice(&self.alignments));
        #[cfg(not(target_endian = "little"))]
        for encoded in &self.alignments {
            output.extend_from_slice(&encoded.to_le_bytes());
        }
    }

    /// Append the common two-`u32`-barcode, `u32`-UMI record encoding.
    ///
    /// Callers must select this only after validating the record context. It
    /// exists separately from [`Self::append_corrected`] so a fixed-layout
    /// decoder does not need to construct a generic barcode header merely to
    /// serialize the corrected record.
    #[inline]
    pub fn append_u32_pair_corrected(
        &self,
        umi: u32,
        sample_ordinal: u32,
        corrected_cell: u32,
        output: &mut Vec<u8>,
    ) {
        output.extend_from_slice(&(self.alignments.len() as u32).to_le_bytes());
        output.extend_from_slice(&sample_ordinal.to_le_bytes());
        output.extend_from_slice(&corrected_cell.to_le_bytes());
        output.extend_from_slice(&umi.to_le_bytes());
        self.append_packed_alignments(output);
    }

    /// Write a corrected record header and the retained packed alignments.
    #[inline]
    pub fn write_corrected<W: Write>(
        &self,
        header: &MultiBarcodeReadRecordHeader<u64>,
        context: &MultiBarcodeRecordContext,
        sample_ordinal: u64,
        corrected_cell: u64,
        writer: &mut W,
    ) -> anyhow::Result<()> {
        let mut corrected_barcodes = header.barcodes.clone();
        let first = corrected_barcodes
            .first_mut()
            .context("multi-barcode record has no sample barcode")?;
        *first = sample_ordinal;
        let last = corrected_barcodes
            .last_mut()
            .context("multi-barcode record has no cell barcode")?;
        *last = corrected_cell;

        RadIntId::U32.write_to(self.alignments.len() as u32, writer)?;
        for (barcode, barcode_type) in corrected_barcodes.iter().zip(&context.bc_types) {
            barcode_type.write_to(*barcode, writer)?;
        }
        context.umit.write_to(header.umi, writer)?;
        for encoded in &self.alignments {
            writer.write_all(&encoded.to_le_bytes())?;
        }
        Ok(())
    }

    /// Append a corrected record directly to a byte vector.
    ///
    /// This is the collation hot path. The common Flex encoding (two `u32`
    /// barcodes and a `u32` UMI) is written without cloning the barcode list,
    /// virtualized integer writes, or one `write_all` call per alignment.
    #[inline]
    pub fn append_corrected(
        &self,
        header: &MultiBarcodeReadRecordHeader<u64>,
        context: &MultiBarcodeRecordContext,
        sample_ordinal: u64,
        corrected_cell: u64,
        output: &mut Vec<u8>,
    ) -> anyhow::Result<()> {
        if context.bc_types.as_slice() == [RadIntId::U32, RadIntId::U32]
            && context.umit == RadIntId::U32
        {
            self.append_u32_pair_corrected(
                header.umi as u32,
                sample_ordinal as u32,
                corrected_cell as u32,
                output,
            );
            return Ok(());
        } else {
            output.extend_from_slice(&(self.alignments.len() as u32).to_le_bytes());
            let last_index = header
                .barcodes
                .len()
                .checked_sub(1)
                .context("multi-barcode record has no barcode fields")?;
            for (index, (barcode, barcode_type)) in
                header.barcodes.iter().zip(&context.bc_types).enumerate()
            {
                let corrected = if index == 0 {
                    sample_ordinal
                } else if index == last_index {
                    corrected_cell
                } else {
                    *barcode
                };
                barcode_type.write_to(corrected, output)?;
            }
            context.umit.write_to(header.umi, output)?;
        }
        self.append_packed_alignments(output);
        Ok(())
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

    #[test]
    fn can_write_multi_barcode_record() {
        use crate::collation::BarcodeRole;
        use crate::record::{MultiBarcodeReadRecord, MultiBarcodeRecordContext};
        use smallvec::smallvec;

        let rec = MultiBarcodeReadRecord {
            barcodes: smallvec![42_u64, 12345_u64],
            umi: 6789_u64,
            dirs: vec![true, false, true],
            refs: vec![100, 200, 300],
        };

        let ctx = MultiBarcodeRecordContext {
            bc_types: smallvec![RadIntId::U32, RadIntId::U32],
            umit: RadIntId::U32,
            roles: smallvec![BarcodeRole::Sample, BarcodeRole::Cell],
        };

        let mut buf: Vec<u8> = Vec::new();
        rec.write(&mut buf, &ctx)
            .expect("couldn't write multi-barcode record");

        let mut cursor = Cursor::new(buf);
        let new_rec = MultiBarcodeReadRecord::from_bytes_with_context(&mut cursor, &ctx);

        assert_eq!(rec, new_rec);
    }

    #[test]
    fn multi_barcode_collation_key_is_last_barcode() {
        use crate::record::{
            CollatableMappedRecord, HierarchicallyCollatable, MultiBarcodeReadRecord,
        };
        use smallvec::smallvec;

        let rec = MultiBarcodeReadRecord {
            barcodes: smallvec![42_u64, 12345_u64],
            umi: 6789_u64,
            dirs: vec![true],
            refs: vec![100],
        };

        // collate_key() should return the last (cell) barcode
        assert_eq!(rec.collate_key(), 12345_u64);

        // level 0 = sample, level 1 = cell
        assert_eq!(rec.collation_key_at_level(0), 42_u64);
        assert_eq!(rec.collation_key_at_level(1), 12345_u64);
        assert_eq!(rec.num_collation_levels(), 2);
    }

    #[test]
    fn multi_barcode_header_grouping_key_includes_sample() {
        use crate::collation::BarcodeRole;
        use crate::record::{
            CollatableRecordHeader, MultiBarcodeReadRecordHeader, MultiBarcodeRecordContext,
        };
        use smallvec::smallvec;

        let ctx = MultiBarcodeRecordContext {
            bc_types: smallvec![RadIntId::U32, RadIntId::U32],
            umit: RadIntId::U32,
            roles: smallvec![BarcodeRole::Sample, BarcodeRole::Cell],
        };

        let hdr_a = MultiBarcodeReadRecordHeader {
            naln: 1,
            barcodes: smallvec![1_u64, 12345_u64],
            umi: 7,
        };
        let hdr_b = MultiBarcodeReadRecordHeader {
            naln: 1,
            barcodes: smallvec![2_u64, 12345_u64],
            umi: 8,
        };

        assert_eq!(hdr_a.collate_key(), 12345_u64);
        assert_eq!(hdr_b.collate_key(), 12345_u64);
        assert_ne!(
            hdr_a.collation_group_key(&ctx),
            hdr_b.collation_group_key(&ctx)
        );
    }

    #[test]
    fn multi_barcode_scratch_filters_sorts_and_rewrites() {
        use crate::collation::BarcodeRole;
        use crate::rad_types::MappedFragmentOrientation;
        use crate::record::{
            MultiBarcodeReadRecord, MultiBarcodeReadRecordHeader, MultiBarcodeRecordContext,
            MultiBarcodeRecordScratch,
        };
        use smallvec::smallvec;

        let context = MultiBarcodeRecordContext {
            bc_types: smallvec![RadIntId::U32, RadIntId::U32],
            umit: RadIntId::U32,
            roles: smallvec![BarcodeRole::Sample, BarcodeRole::Cell],
        };
        let encoded = [0x8000_0005_u32, 3, 0x8000_0001];
        let bytes: Vec<u8> = encoded
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect();
        let mut scratch = MultiBarcodeRecordScratch::new();
        scratch
            .read_filtered(
                &mut Cursor::new(bytes),
                encoded.len() as u32,
                &MappedFragmentOrientation::Forward,
            )
            .unwrap();

        let header = MultiBarcodeReadRecordHeader {
            naln: encoded.len() as u32,
            barcodes: smallvec![99, 88],
            umi: 42,
        };
        let mut rewritten = Vec::new();
        scratch
            .append_corrected(&header, &context, 2, 7, &mut rewritten)
            .unwrap();
        let record =
            MultiBarcodeReadRecord::from_bytes_with_context(&mut Cursor::new(rewritten), &context);
        assert_eq!(record.barcodes.as_slice(), &[2, 7]);
        assert_eq!(record.umi, 42);
        assert_eq!(record.refs, vec![1, 5]);
        assert_eq!(record.dirs, vec![true, true]);
    }
}
