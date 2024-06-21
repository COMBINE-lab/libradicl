/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! This module contains the relevant structures and traits for most of the **core**
//! RAD types. This includes the integer, numeric and composite types, as well as
//! other relevant types built from them (e.g. [TagSection]s). It also contains the
//! types and traits related to parsing and writing values of specific types.

use crate::{self as libradicl, constants};
use anyhow::{self, bail, Context};
use libradicl::{tag_value_try_into_int, u8_to_vec_of, u8_to_vec_of_bool, write_tag_value_array};
use num::cast::AsPrimitive;
use scroll::Pread;

use std::io::Read;
use std::io::Write;
use std::mem;

/// A **description** for a type tag. This  specifies the name
/// that the tag should be given, and the type of value that it
/// holds.  At other points in the file, when this tag is used
/// it will conform to this type description.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TagDesc {
    pub name: String,
    pub typeid: RadType,
}

impl TagDesc {
    /// Write this [TagDesc] to the provided `writer`, propagating any
    /// error that may occur.
    pub fn write<W: Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        // write the name
        let name_len: u16 = self
            .name
            .len()
            .try_into()
            .context("TagDesc name must have size < 65536")?;
        writer
            .write_all(&name_len.to_le_bytes())
            .context("could not write name length to writer")?;
        writer
            .write_all(self.name.as_bytes())
            .context("could not write name to writer")?;

        let type_enc: u8 =
            encode_type_tag(self.typeid).context("RadType tag doesn't have valid encoding")?;
        writer
            .write_all(&type_enc.to_le_bytes())
            .context("could not write name length to writer")?;
        if let RadType::Array(len_t, val_t) = self.typeid {
            let len_id: u8 = len_t.into();
            let val_id: u8 = val_t.into();
            writer
                .write_all(&len_id.to_le_bytes())
                .context("could not write Array length type")?;
            writer
                .write_all(&val_id.to_le_bytes())
                .context("could not write Array value type")?;
        };
        Ok(())
    }
}

/// A label of the type of a [TagSection]. The RAD format
/// has file, read, and alignment-level tags, though the
/// `Unlabeled` variant is reserved for potential other
/// applications.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TagSectionLabel {
    FileTags,
    ReadTags,
    AlignmentTags,
    Unlabeled,
}

/// A [TagSection] consists of a series of [TagDesc]s that are
/// logically grouped together as tags for a specific unit
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TagSection {
    pub label: TagSectionLabel,
    pub tags: Vec<TagDesc>,
}

impl TagSection {
    /// Create a new tag section with the provided label
    /// type, but with no tags descripitons.
    pub fn new_with_label(label: TagSectionLabel) -> Self {
        TagSection {
            label,
            tags: vec![],
        }
    }

    /// Add a [TagDesc] to the list of tags in this section
    pub fn add_tag_desc(&mut self, desc: TagDesc) {
        self.tags.push(desc);
    }

    /// Write the tag section to the provided writer
    pub fn write<W: Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        let num_tags: u16 = self
            .tags
            .len()
            .try_into()
            .unwrap_or_else(|_| panic!("should have < {} tags", u16::MAX));
        writer
            .write_all(&num_tags.to_le_bytes())
            .context("couldn't write number of tags to writer")?;

        for tag in &self.tags {
            tag.write(writer)?;
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RadIntId {
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl RadIntId {
    /// Return the size (in bytes) of the a *value* associated
    /// with a [RadIntId] of this type.
    #[inline]
    pub fn size_of(&self) -> usize {
        match self {
            Self::U8 => mem::size_of::<u8>(),
            Self::U16 => mem::size_of::<u16>(),
            Self::U32 => mem::size_of::<u32>(),
            Self::U64 => mem::size_of::<u64>(),
            Self::U128 => mem::size_of::<u128>(),
        }
    }

    /// Read a value whose size matches this [RadIntId] and return
    /// the value in a [u64] container
    #[inline]
    pub fn read_value_into_u64<R: Read>(&self, reader: &mut R) -> u64 {
        let mut rbuf = [0u8; 8];

        let v: u64 = match self {
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
            RadIntId::U128 => {
                panic!("cannot read a u128 into a u64");
            }
        };
        v
    }

    /// Read a value whose size matches this [RadIntId] and return
    /// the value in a [u128] container
    #[inline]
    pub fn read_value_into_u128<R: Read>(&self, reader: &mut R) -> u128 {
        let mut rbuf = [0u8; 16];

        let v: u128 = match self {
            RadIntId::U8 => {
                reader.read_exact(&mut rbuf[0..1]).unwrap();
                rbuf.pread::<u8>(0).unwrap() as u128
            }
            RadIntId::U16 => {
                reader.read_exact(&mut rbuf[0..2]).unwrap();
                rbuf.pread::<u16>(0).unwrap() as u128
            }
            RadIntId::U32 => {
                reader.read_exact(&mut rbuf[0..4]).unwrap();
                rbuf.pread::<u32>(0).unwrap() as u128
            }
            RadIntId::U64 => {
                reader.read_exact(&mut rbuf[0..8]).unwrap();
                rbuf.pread::<u64>(0).unwrap() as u128
            }
            RadIntId::U128 => {
                reader.read_exact(&mut rbuf[0..16]).unwrap();
                rbuf.pread::<u128>(0).unwrap()
            }
        };
        v
    }
}

/// Convert from a [RadIntId], to the corresponding type id (`u8`)
/// encoding.
impl From<RadIntId> for u8 {
    fn from(r: RadIntId) -> Self {
        match r {
            RadIntId::U8 => 1_u8,
            RadIntId::U16 => 2_u8,
            RadIntId::U32 => 3_u8,
            RadIntId::U64 => 4_u8,
            RadIntId::U128 => 9_u8,
        }
    }
}

/// Convert from a `u8` (type tag id) to a [RadIntId].
/// This will fail (`panic`) if the type id is not a valid
/// id for a [RadIntId].
impl From<u8> for RadIntId {
    fn from(x: u8) -> Self {
        match x {
            1 => Self::U8,
            2 => Self::U16,
            3 => Self::U32,
            4 => Self::U64,
            9 => Self::U128,
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
    /// The size (in bytes) of *values* associated with this
    /// type of [RadFloatId].
    #[inline]
    pub fn size_of(&self) -> usize {
        match self {
            Self::F32 => mem::size_of::<f32>(),
            Self::F64 => mem::size_of::<f64>(),
        }
    }
}

/// Convert from a `u8` (type tag id) to a [RadFloatId].
/// This will fail (`panic`) if the type id is not a valid
/// id for a [RadFloatId]
impl From<u8> for RadFloatId {
    #[inline]
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
    + AsPrimitive<u128>
    + AsPrimitive<usize>
    + AsPrimitive<i8>
    + AsPrimitive<i16>
    + AsPrimitive<i32>
    + AsPrimitive<i64>
    + AsPrimitive<i128>
    + AsPrimitive<isize>
{
}

impl<
        T: AsPrimitive<u8>
            + AsPrimitive<u16>
            + AsPrimitive<u32>
            + AsPrimitive<u64>
            + AsPrimitive<u128>
            + AsPrimitive<usize>
            + AsPrimitive<i8>
            + AsPrimitive<i16>
            + AsPrimitive<i32>
            + AsPrimitive<i64>
            + AsPrimitive<i128>
            + AsPrimitive<isize>,
    > PrimitiveInteger for T
{
}

impl RadIntId {
    /// Return the number of bytes required
    /// to store a *value* associated with
    /// this type of [RadIntId].
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
            Self::U128 => {
                let vo: u128 = v.as_();
                owriter.write_all(&vo.to_le_bytes())
            }
        }
    }

    /// Read a value, whose size is determined by this [RadIntId],
    /// from the provided `buf` and return the value in a [usize] type
    /// container.
    #[inline]
    pub fn read_value_into_usize(&self, buf: &[u8]) -> usize {
        match self {
            Self::U8 => buf.pread::<u8>(0).unwrap() as usize,
            Self::U16 => buf.pread::<u16>(0).unwrap() as usize,
            Self::U32 => buf.pread::<u32>(0).unwrap() as usize,
            Self::U64 => buf.pread::<u64>(0).unwrap() as usize,
            Self::U128 => {
                panic!("cannot read u128 into usize!")
            }
        }
    }
}

/// This type represents any **non-aggregate**
/// [RadType], differentiating between an Int,
/// Float, Bool and String types. Each Int and Float
/// type contains a further description of the width
/// of that type as a [RadIntId].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RadAtomicId {
    Int(RadIntId),
    Float(RadFloatId),
    Bool,
    String,
}

impl RadAtomicId {
    /// Return the size_of this [RadAtomicId] in bytes; as with the
    /// underlying Rust type, a [bool] is 1 byte.
    #[inline]
    pub fn size_of(&self) -> usize {
        match self {
            Self::Int(x) => x.size_of(),
            Self::Float(x) => x.size_of(),
            Self::Bool => std::mem::size_of::<bool>(),
            Self::String => panic!("RadAtomicId::String does not have a fixed type"),
        }
    }
}

/// Map from each possible [RadAtomicId] type to the corresponidng
/// u8 encoding.  
impl From<RadAtomicId> for u8 {
    fn from(x: RadAtomicId) -> Self {
        match x {
            RadAtomicId::Bool => 0,
            RadAtomicId::Int(RadIntId::U8) => 1,
            RadAtomicId::Int(RadIntId::U16) => 2,
            RadAtomicId::Int(RadIntId::U32) => 3,
            RadAtomicId::Int(RadIntId::U64) => 4,
            RadAtomicId::Int(RadIntId::U128) => 9,
            RadAtomicId::Float(RadFloatId::F32) => 5,
            RadAtomicId::Float(RadFloatId::F64) => 6,
            RadAtomicId::String => 8,
        }
    }
}

/// Map from each possible integer tag to the corresponding
/// [RadAtomicId] type.  This function **panics** if the provided
/// [u8] is not a valid [RadAtomicId] (i.e. is 7 or > 8).
impl From<u8> for RadAtomicId {
    fn from(x: u8) -> Self {
        match x {
            0 => Self::Bool,
            1 => Self::Int(RadIntId::U8),
            2 => Self::Int(RadIntId::U16),
            3 => Self::Int(RadIntId::U32),
            4 => Self::Int(RadIntId::U64),
            9 => Self::Int(RadIntId::U128),
            5 => Self::Float(RadFloatId::F32),
            6 => Self::Float(RadFloatId::F64),
            8 => Self::String,
            x => panic!("Should not happen, num is {x}"),
        }
    }
}

/// The top-level enum representing the different types that
/// can be encoded in the tag system.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RadType {
    Bool,
    Int(RadIntId),
    Float(RadFloatId),
    // holds length type and value type, but not length
    // and data themselves
    Array(RadIntId, RadAtomicId),
    // does not hold length, just a marker for the type
    String,
}

impl RadType {
    /// Returns true if this [RadType] encodes some type of
    /// integer, and false otherwise.
    #[inline]
    pub fn is_int_type(&self) -> bool {
        matches!(self, Self::Int(_))
    }

    /// Reads a [RadType] from the provided reader `r`.
    /// **Note**: This function expects that a valid [RadType] encoding
    /// must occur next within `r`, and panics if this is not the case.
    pub fn from_bytes<R: Read>(r: &mut R) -> Self {
        // read the type id
        let mut type_num = 0_u8;
        r.read_exact(std::slice::from_mut(&mut type_num))
            .expect("cannot read RadType id from file");
        if type_num == 7 {
            let mut len_id = 0_u8;
            let mut member_id = 0_u8;
            r.read_exact(std::slice::from_mut(&mut len_id))
                .expect("cannot read Array length type from file");
            r.read_exact(std::slice::from_mut(&mut member_id))
                .expect("cannot read Array value type from file");
            let len_type: RadIntId = len_id.into();
            let member_type: RadAtomicId = member_id.into();
            RadType::Array(len_type, member_type)
        } else {
            type_num.into()
        }
    }

    /// Reads a [RadType] from the provided reader `r`.
    /// This function expects that a valid [RadType] encoding
    /// must occur next within `r`; it returns an [Ok(RadType)] if this
    /// is the case and propagates encountered errors otherwise.
    pub fn try_from_bytes<R: Read>(r: &mut R) -> anyhow::Result<Self> {
        // read the type id
        let mut type_num = 0_u8;
        r.read_exact(std::slice::from_mut(&mut type_num))
            .context("cannot read RadType id from file")?;
        if type_num == 7 {
            let mut len_id = 0_u8;
            let mut member_id = 0_u8;
            r.read_exact(std::slice::from_mut(&mut len_id))
                .context("cannot read Array length type from file")?;
            r.read_exact(std::slice::from_mut(&mut member_id))
                .context("cannot read Array value type from file")?;
            let len_type: RadIntId = len_id.into();
            let member_type: RadAtomicId = member_id.into();
            Ok(RadType::Array(len_type, member_type))
        } else {
            Ok(type_num.into())
        }
    }
}

/// This function takes a [RadType] and returns the
/// underlying id (i.e. [u8] value) that defines the type in
/// the RAD format.
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
        RadType::Int(RadIntId::U128) => Some(9),
    }
}

/// This function takes a [u8] and returns the corresponding
/// [RadIntId]. If the `type_id` represents a valid [RadIntId]
/// then return `Some(`[RadIntId]`)`, otherwise return [None].
pub fn decode_int_type_tag(type_id: u8) -> Option<RadIntId> {
    match type_id {
        1 => Some(RadIntId::U8),
        2 => Some(RadIntId::U16),
        3 => Some(RadIntId::U32),
        4 => Some(RadIntId::U64),
        9 => Some(RadIntId::U128),
        _ => None,
    }
}

/// Represents the manner in which a fragment (read or read pair)
/// may map to a target. This type does not encode orientation, but
/// rather the mapping status.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum MappingType {
    Unmapped,
    SingleMapped,
    MappedFirstOrphan,
    MappedSecondOrphan,
    MappedPair,
}

impl MappingType {
    /// convert from the [u8] representation to the
    /// corresponding [MappingType].
    #[inline]
    pub fn from_u8(t: u8) -> Self {
        match t {
            0 => MappingType::Unmapped,
            1 => MappingType::SingleMapped,
            2 => MappingType::MappedFirstOrphan,
            3 => MappingType::MappedSecondOrphan,
            4 => MappingType::MappedPair,
            _ => MappingType::Unmapped,
        }
    }

    /// Return the mask that is relevant given the current
    /// [MappingType].
    #[inline]
    pub fn get_mask(&self) -> u32 {
        match &self {
            // if unmapped, we ignore flags all together.
            MappingType::Unmapped => 0b00,
            // if paired we care about both read and mate.
            MappingType::MappedPair => 0b11,
            // if orphan or single, we care only about read
            // mate flag should be ignored.
            _ => 0b10,
        }
    }

    /// Returns `true` if the current [MappingType] is an orphan
    /// (i.e. a fragment paired in sequencing for which only a single
    /// end is mapped to the current target) and `false` otherwise.
    #[inline]
    pub fn is_orphan(&self) -> bool {
        matches!(
            &self,
            MappingType::MappedFirstOrphan | MappingType::MappedSecondOrphan
        )
    }
}

/// Encodes the orientation of a mapped fragment. If the fragment is
/// a single-end mapping (or orphan), then there are only 2 possible
/// orientations, while for paired and mapped reads, there are 4 possible
/// orientations. Finally, this `enum` can also represent an "Unknown"
/// orientation.
#[derive(Debug, Copy, Clone)]
pub enum MappedFragmentOrientation {
    Reverse,
    Forward,
    ReverseReverse,
    ReverseForward,
    ForwardReverse,
    ForwardForward,
    Unknown,
}

impl MappedFragmentOrientation {
    /// Given an encoding of the mapped fragment information (`n`) and
    /// the corresponding [MappingType], return the [MappedFragmentOrientation]
    #[inline]
    pub fn from_u32_paired_status(n: u32, m: MappingType) -> Self {
        // if not paired, then we don't care about
        // the lowest order bit so shift it off
        if matches!(
            m,
            MappingType::SingleMapped
                | MappingType::MappedFirstOrphan
                | MappingType::MappedSecondOrphan
        ) {
            if (n & 0b10) == 2 {
                MappedFragmentOrientation::Forward
            } else {
                MappedFragmentOrientation::Reverse
            }
        } else {
            match n {
                0 => MappedFragmentOrientation::ReverseReverse,
                1 => MappedFragmentOrientation::ReverseForward,
                2 => MappedFragmentOrientation::ForwardReverse,
                3 => MappedFragmentOrientation::ForwardForward,
                _ => MappedFragmentOrientation::Unknown,
            }
        }
    }
}

/// For a given [MappedFragmentOrientation], return the [u32]
/// that corresponds to this orientation.
impl From<MappedFragmentOrientation> for u32 {
    fn from(item: MappedFragmentOrientation) -> Self {
        match item {
            MappedFragmentOrientation::ForwardReverse => 0b011,
            MappedFragmentOrientation::ForwardForward => 0b101,
            MappedFragmentOrientation::ReverseReverse => 0b110,
            MappedFragmentOrientation::ReverseForward => 0b100,
            MappedFragmentOrientation::Forward => 0b1,
            MappedFragmentOrientation::Reverse => 0b10,
            MappedFragmentOrientation::Unknown => 0b0,
        }
    }
}

/// For a given [u32], interpret it as a [MappedFragmentOrientation],
/// and return the appropriate variant.
impl From<u32> for MappedFragmentOrientation {
    fn from(item: u32) -> Self {
        match item {
            0b011 => MappedFragmentOrientation::ForwardReverse,
            0b101 => MappedFragmentOrientation::ForwardForward,
            0b110 => MappedFragmentOrientation::ReverseReverse,
            0b100 => MappedFragmentOrientation::ReverseForward,
            0b1 => MappedFragmentOrientation::Forward,
            0b10 => MappedFragmentOrientation::Reverse,
            _ => MappedFragmentOrientation::Unknown,
        }
    }
}

/// Convert from a u8 to the corresponding RadType.
/// This will only work for *non-aggregate* types
/// (i.e. it will not work for the array type, since
/// the type requiers more than a u8 worth of information).
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
            9 => RadType::Int(RadIntId::U128),
            _ => panic!("Should not happen"),
        }
    }
}

/// This enum holds the different values that can be represented
/// in a RAD tag. For the aggregate (i.e. array) types, the type
/// of the element being stored in the array is encoded in the
/// [TagValue] variant, but the length of the array is not.
#[derive(Debug, PartialEq)]
pub enum TagValue {
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    F32(f32),
    F64(f64),
    ArrayBool(Vec<bool>),
    ArrayU8(Vec<u8>),
    ArrayU16(Vec<u16>),
    ArrayU32(Vec<u32>),
    ArrayU64(Vec<u64>),
    ArrayU128(Vec<u128>),
    ArrayF32(Vec<f32>),
    ArrayF64(Vec<f64>),
    ArrayString(Vec<String>),
    String(String),
}

tag_value_try_into_int!(u8);
tag_value_try_into_int!(u16);
tag_value_try_into_int!(u32);
tag_value_try_into_int!(u64);

impl TagValue {
    /// Write this tag value to the provided writer
    #[inline]
    pub fn write_with_type<W: Write>(
        &self,
        tag_type: &RadType,
        writer: &mut W,
    ) -> anyhow::Result<()> {
        match self {
            Self::Bool(b) => {
                let b = if *b { 1_u8 } else { 0_u8 };
                writer
                    .write_all(&b.to_le_bytes())
                    .context("couldn't write Bool tag value")?;
            }
            Self::U8(v) => {
                writer
                    .write_all(&v.to_le_bytes())
                    .context("couldn't write U8 tag value")?;
            }
            Self::U16(v) => {
                writer
                    .write_all(&v.to_le_bytes())
                    .context("couldn't write U16 tag value")?;
            }
            Self::U32(v) => {
                writer
                    .write_all(&v.to_le_bytes())
                    .context("couldn't write U32 tag value")?;
            }
            Self::U64(v) => {
                writer
                    .write_all(&v.to_le_bytes())
                    .context("couldn't write U64 tag value")?;
            }
            Self::U128(v) => {
                writer
                    .write_all(&v.to_le_bytes())
                    .context("couldn't write U128 tag value")?;
            }
            Self::F32(v) => {
                writer
                    .write_all(&v.to_le_bytes())
                    .context("couldn't write U8 tag value")?;
            }
            Self::F64(v) => {
                writer
                    .write_all(&v.to_le_bytes())
                    .context("couldn't write U8 tag value")?;
            }
            Self::ArrayBool(vb) => {
                if let RadType::Array(len_t, _) = tag_type {
                    write_tag_value_array!(vb, len_t, bool, x, writer);
                } else {
                    bail!("Array TagValue didn't correspond to an Array RadType");
                }
            }
            Self::ArrayU8(vb) => {
                if let RadType::Array(len_t, _) = tag_type {
                    write_tag_value_array!(vb, len_t, u8, x, writer);
                } else {
                    bail!("Array TagValue didn't correspond to an Array RadType");
                }
            }
            Self::ArrayU16(vb) => {
                if let RadType::Array(len_t, _) = tag_type {
                    write_tag_value_array!(vb, len_t, u16, x, writer);
                } else {
                    bail!("Array TagValue didn't correspond to an Array RadType");
                }
            }
            Self::ArrayU32(vb) => {
                if let RadType::Array(len_t, _) = tag_type {
                    write_tag_value_array!(vb, len_t, u32, x, writer);
                } else {
                    bail!("Array TagValue didn't correspond to an Array RadType");
                }
            }
            Self::ArrayU64(vb) => {
                if let RadType::Array(len_t, _) = tag_type {
                    write_tag_value_array!(vb, len_t, u64, x, writer);
                } else {
                    bail!("Array TagValue didn't correspond to an Array RadType");
                }
            }
            Self::ArrayU128(vb) => {
                if let RadType::Array(len_t, _) = tag_type {
                    write_tag_value_array!(vb, len_t, u128, x, writer);
                } else {
                    bail!("Array TagValue didn't correspond to an Array RadType");
                }
            }
            Self::ArrayF32(vb) => {
                if let RadType::Array(len_t, _) = tag_type {
                    write_tag_value_array!(vb, len_t, f32, x, writer);
                } else {
                    bail!("Array TagValue didn't correspond to an Array RadType");
                }
            }
            Self::ArrayF64(vb) => {
                if let RadType::Array(len_t, _) = tag_type {
                    write_tag_value_array!(vb, len_t, f64, x, writer);
                } else {
                    bail!("Array TagValue didn't correspond to an Array RadType");
                }
            }
            Self::ArrayString(_vb) => {
                todo!("Not yet implemented")
            }
            Self::String(s) => {
                let slen: u16 = s.len() as u16;
                writer
                    .write_all(&slen.to_le_bytes())
                    .context("couldn't write String tag value's length")?;
                writer
                    .write_all(s.as_bytes())
                    .context("couldn't write String tag value's content")?;
            }
        }
        Ok(())
    }
}

impl TagDesc {
    /// Attempts to read a [TagDesc] from the provided `reader`. If the
    /// `reader` is positioned at the start of a valid [TagDesc], then this
    /// [TagDesc] is returned.  Otherwise, a description of the error is returned
    /// via an [anyhow::Error].
    pub fn from_bytes<T: Read>(reader: &mut T) -> anyhow::Result<TagDesc> {
        // space for the string length (2 bytes)
        // the longest string possible (255 char)
        // and the typeid
        let mut buf = [0u8; constants::MAX_REF_NAME_LEN];
        reader
            .read_exact(&mut buf[0..2])
            .context("failed to read the string length for the Tag Description.")?;
        let str_len = buf.pread::<u16>(0)? as usize;

        // read str_len + 1 to get the type id that follows the string
        reader
            .read_exact(&mut buf[0..str_len + 1])
            .context("failed to read string name or type-id from Tag Description.")?;
        let name = std::str::from_utf8(&buf[0..str_len])
            .context("failed to convert string name to a valid string.")?
            .to_string();
        let typeid = buf
            .pread(str_len)
            .context("failed to read RadType id from the buffer.")?;
        // if the type id is 7, need to read the types of
        // the length and element type, otherwise just turn the
        // id into a proper RatType and we're done.
        let rad_t = match typeid {
            0..=6 | 8 => typeid.into(),
            7 => {
                reader.read_exact(&mut buf[0..2]).context("failed to read aggregate type parameters (array length and element types) from the reader.")?;
                let t1: RadIntId = buf
                    .pread::<u8>(0)
                    .context("failed to parse the array length type")?
                    .into();
                let t2: RadAtomicId = buf
                    .pread::<u8>(1)
                    .context("failed to parse the array value type")?
                    .into();
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
        let mut small_buf = [0u8; 16];
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
            RadType::Int(RadIntId::U128) => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<u128>()]);
                TagValue::U128(small_buf.pread::<u128>(0).unwrap())
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
                let vec_len = len_t.read_value_into_usize(&small_buf);
                if val_t == RadAtomicId::String {
                    let mut strings = Vec::with_capacity(vec_len);
                    let sl: u16 = 0;
                    let mut buf = [0u8; 65536];
                    for _ in 0..vec_len {
                        let _ = reader.read_exact(&mut sl.to_ne_bytes());
                        let l = sl as usize;
                        let _ = reader.read_exact(&mut buf[0..l]);
                        unsafe {
                            strings.push(std::str::from_utf8_unchecked(&buf[0..l]).to_string());
                        }
                    }
                    TagValue::ArrayString(strings)
                } else {
                    let num_bytes = val_t.size_of() * vec_len;
                    let mut data = vec![0u8; num_bytes];
                    let _ = reader.read_exact(data.as_mut_slice());
                    match val_t {
                        RadAtomicId::Bool => TagValue::ArrayBool(u8_to_vec_of_bool!(data)),
                        RadAtomicId::Int(RadIntId::U8) => TagValue::ArrayU8(data),
                        RadAtomicId::Int(RadIntId::U16) => {
                            TagValue::ArrayU16(u8_to_vec_of!(data, u16))
                        }
                        RadAtomicId::Int(RadIntId::U32) => {
                            TagValue::ArrayU32(u8_to_vec_of!(data, u32))
                        }
                        RadAtomicId::Int(RadIntId::U64) => {
                            TagValue::ArrayU64(u8_to_vec_of!(data, u64))
                        }
                        RadAtomicId::Int(RadIntId::U128) => {
                            TagValue::ArrayU128(u8_to_vec_of!(data, u128))
                        }
                        RadAtomicId::Float(RadFloatId::F32) => {
                            TagValue::ArrayF32(u8_to_vec_of!(data, f32))
                        }
                        RadAtomicId::Float(RadFloatId::F64) => {
                            TagValue::ArrayF64(u8_to_vec_of!(data, f64))
                        }
                        RadAtomicId::String => {
                            unimplemented!("match of RadAtomicId should not occur in this branch")
                        }
                    }
                }
            }
            RadType::String => {
                let _ = reader.read_exact(&mut small_buf[0..std::mem::size_of::<u16>()]);
                let slen = small_buf.pread::<u16>(0).unwrap();
                let mut dat: Vec<u8> = vec![0_u8; slen as usize];
                let _ = reader.read_exact(dat.as_mut_slice());
                // safety: a *valid* input RAD file will only have written a
                // valid utf8 string into the file at this position.
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
            (RadType::Int(RadIntId::U128), TagValue::U128(_)) => true,
            (RadType::Float(RadFloatId::F32), TagValue::F32(_)) => true,
            (RadType::Float(RadFloatId::F64), TagValue::F64(_)) => true,
            (RadType::Array(_, RadAtomicId::Bool), TagValue::ArrayBool(_)) => true,
            (RadType::Array(_, RadAtomicId::Int(RadIntId::U8)), TagValue::ArrayU8(_)) => true,
            (RadType::Array(_, RadAtomicId::Int(RadIntId::U16)), TagValue::ArrayU16(_)) => true,
            (RadType::Array(_, RadAtomicId::Int(RadIntId::U32)), TagValue::ArrayU32(_)) => true,
            (RadType::Array(_, RadAtomicId::Int(RadIntId::U64)), TagValue::ArrayU64(_)) => true,
            (RadType::Array(_, RadAtomicId::Int(RadIntId::U128)), TagValue::ArrayU128(_)) => true,
            (RadType::Array(_, RadAtomicId::Float(RadFloatId::F32)), TagValue::ArrayF32(_)) => true,
            (RadType::Array(_, RadAtomicId::Float(RadFloatId::F64)), TagValue::ArrayF64(_)) => true,
            (RadType::Array(_, RadAtomicId::String), TagValue::ArrayString(_)) => true,
            (RadType::String, TagValue::String(_)) => true,
            (_, _) => false,
        }
    }
}

/// This type represents a mapping from [TagDesc]s to a corresponding set of
/// values conforming to these descriptions (i.e. in terms of types). The
/// [TagMap] allows you to fetch the value for a specific tag by name or index, or
/// to add values to a corresponding set of descriptions. This type is much like a
/// [TagMap], except that it relies on a shared reference to the [TagDesc]s, rather
/// than an owned copy (usually a clone) of them.
#[derive(Debug, PartialEq)]
pub struct TagViewMap<'a> {
    keys: &'a [TagDesc],
    dat: Vec<TagValue>,
}

/// TODO: Figure out how to minimize duplcation between
/// TagMap and TagViewMap

/// Free functions that reduce redundancy in the implementations of
/// TagMap and TagViewMap.
///

#[inline(always)]
fn try_add(dat: &mut Vec<TagValue>, keys: &[TagDesc], val: TagValue) -> anyhow::Result<()> {
    let next_idx = dat.len();
    anyhow::ensure!(next_idx < keys.len(), "Attempted to add a TagVal {val:?} at index {next_idx}, but there are only {} keys in the keyset", keys.len());
    anyhow::ensure!(
        keys[next_idx].matches_value_type(&val),
        "The TagValue that was attempted to be added {val:?} didn't match the next TagDesc {:?}",
        keys[next_idx]
    );
    dat.push(val);
    Ok(())
}

#[inline(always)]
fn get_tag_by_name<'a>(
    key: &str,
    dat: &'a Vec<TagValue>,
    keys: &[TagDesc],
) -> Option<&'a TagValue> {
    for (k, val) in keys.iter().zip(dat.iter()) {
        if k.name == key {
            return Some(val);
        }
    }
    None
}

#[inline(always)]
fn write_tag_map_values<W: Write>(
    dat: &[TagValue],
    keys: &[TagDesc],
    writer: &mut W,
) -> anyhow::Result<()> {
    for (n, v) in keys.iter().zip(dat.iter()) {
        v.write_with_type(&n.typeid, writer)
            .with_context(|| format!("couldn't write tag value for tag {}", n.name))?;
    }
    Ok(())
}

impl<'a> TagViewMap<'a> {
    /// Create a new TagViewMap whose set of keys is determined by
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
    pub fn try_add(&mut self, val: TagValue) -> anyhow::Result<()> {
        try_add(&mut self.dat, &self.keys, val)
    }

    /// add the next TagValue to the data for this TagViewMap.
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
        get_tag_by_name(key, &self.dat, &self.keys)
    }

    /// get the value for the tag at index `idx` returns Some(&TagValue) if `idx`
    /// is in bounds and None otherwise.
    pub fn get_at_index(&self, idx: usize) -> Option<&TagValue> {
        self.dat.get(idx)
    }

    /// writes the values contained in this [TagViewMap], in order, to the provided
    /// writer, propagating any errors or returning Ok(()) on success.
    pub fn write_values<W: Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        write_tag_map_values(&self.dat, &self.keys, writer)
    }
}

impl<'a> std::ops::Index<usize> for TagViewMap<'a> {
    type Output = TagValue;
    /// Returns a reference to the [TagValue] in the [TagViewMap] at the
    /// provided `index`, panics if `index` is out of bounds.
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.dat[index]
    }
}

/// This type represents a mapping from [TagDesc]s to a corresponding set of
/// values conforming to these descriptions (i.e. in terms of types). The
/// [TagMap] allows you to fetch the value for a specific tag by name or index, or
/// to add values to a corresponding set of descriptions.
#[derive(Debug, PartialEq)]
pub struct TagMap {
    keys: Vec<TagDesc>,
    dat: Vec<TagValue>,
}

impl TagMap {
    /// Create a new [TagMap] whose set of keys is determined by
    /// the provided `keyset`. This will have one value slot for
    /// each provided key.
    pub fn with_keyset(keyset: &[TagDesc]) -> Self {
        Self {
            keys: Vec::from(keyset),
            dat: Vec::with_capacity(keyset.len()),
        }
    }

    /// Try to add the next tag value. If there is space and the type
    /// matches, add it and return `true`, otherwise return `false`.
    pub fn try_add(&mut self, val: TagValue) -> anyhow::Result<()> {
        try_add(&mut self.dat, &self.keys, val)
    }

    /// add the next TagValue to the data for this [TagMap].
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
        get_tag_by_name(key, &self.dat, &self.keys)
    }

    /// get the value for the tag at index `idx` returns Some(&TagValue) if `idx`
    /// is in bounds and None otherwise.
    pub fn get_at_index(&self, idx: usize) -> Option<&TagValue> {
        self.dat.get(idx)
    }

    /// writes the values contained in this [TagMap], in order, to the provided
    /// writer, propagating any errors or returning Ok(()) on success.
    pub fn write_values<W: Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        write_tag_map_values(&self.dat, &self.keys, writer)
    }
}

impl std::ops::Index<usize> for TagMap {
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

    /// Parse a set of tag **values**, having types described by this [TagSection], from the
    /// provided `reader`. This function returns the [TagMap] on success, or an error if the
    /// map could not be produced.
    pub fn parse_tags_from_bytes<T: Read>(&self, reader: &mut T) -> anyhow::Result<TagMap> {
        // loop over all of the tag descriptions in this section, and parse a
        // tag value for each.
        let mut tm = TagMap::with_keyset(&self.tags);
        for tag_desc in &self.tags {
            tm.add(tag_desc.value_from_bytes(reader));
        }
        Ok(tm)
    }

    /// Parse a set of tag **values**, having types described by this [TagSection], from the
    /// provided `reader`. This function returns the [TagViewMap] on success, or an error if the
    /// map could not be produced.
    pub fn parse_tags_view_from_bytes<T: Read>(
        &self,
        reader: &mut T,
    ) -> anyhow::Result<TagViewMap> {
        // loop over all of the tag descriptions in this section, and parse a
        // tag value for each.
        let mut tm = TagViewMap::with_keyset(&self.tags);
        for tag_desc in &self.tags {
            tm.add(tag_desc.value_from_bytes(reader));
        }
        Ok(tm)
    }

    /// Parse a set of tag **values**, having types described by this [TagSection], from the
    /// provided `reader`. This function returns the [TagMap] on success, or an error if the
    /// map could not be produced. It propagates more errors than does `parse_tags_from_bytes`
    /// by checking that the number of values in this [TagMap] never exceeds the size of the
    /// `keyset`.
    pub fn try_parse_tags_from_bytes<T: Read>(&self, reader: &mut T) -> anyhow::Result<TagMap> {
        // loop over all of the tag descriptions in this section, and parse a
        // tag value for each.
        //let mut tv = Vec::<TagValue>::new();
        let mut tm = TagMap::with_keyset(&self.tags);
        for tag_desc in &self.tags {
            tm.try_add(tag_desc.value_from_bytes(reader))?;
        }
        Ok(tm)
    }

    /// Parse a set of tag **values**, having types described by this [TagSection], from the
    /// provided `reader`. This function returns the [TagViewMap] on success, or an error if the
    /// map could not be produced. It propagates more errors than does `parse_tags_from_bytes`
    /// by checking that the number of values in this [TagViewMap] never exceeds the size of the
    /// `keyset`.
    pub fn try_parse_tags_view_from_bytes<T: Read>(
        &self,
        reader: &mut T,
    ) -> anyhow::Result<TagViewMap> {
        // loop over all of the tag descriptions in this section, and parse a
        // tag value for each.
        //let mut tv = Vec::<TagValue>::new();
        let mut tm = TagViewMap::with_keyset(&self.tags);
        for tag_desc in &self.tags {
            tm.try_add(tag_desc.value_from_bytes(reader))?;
        }
        Ok(tm)
    }

    /// return the [RadType] associated with the tag having the provided
    /// `name`. Returns [Some(RadType)] if the tag exists in the map and
    /// [None] otherwise.
    pub fn get_tag_type(&self, name: &str) -> Option<RadType> {
        for td in &self.tags {
            if name == td.name {
                return Some(td.typeid);
            }
        }
        None
    }

    /// return `true` if this [TagSection] has a [TagDesc] with a
    /// name matching `name`, and `false` otherwise.
    pub fn has_tag(&self, name: &str) -> bool {
        for td in &self.tags {
            if name == td.name {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use crate::rad_types::RadType;
    use crate::rad_types::{RadAtomicId, RadIntId, TagSection, TagSectionLabel, TagValue};
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
            RadType::Array(RadIntId::U8, RadAtomicId::Int(RadIntId::U16))
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
            RadType::Array(RadIntId::U8, RadAtomicId::Int(RadIntId::U16))
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
            .try_parse_tags_from_bytes(&mut buf.as_slice())
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
