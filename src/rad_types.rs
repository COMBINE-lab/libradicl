/*
 * Copyright (c) 2020-2021 Rob Patro, Avi Srivastava, Hirak Sarkar, Dongze He, Mohsen Zakeri.
 *
 * This file is part of alevin-fry
 * (see https://github.com/COMBINE-lab/alevin-fry).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

use crate::{self as libradicl, constants};
use anyhow::{self, bail};
use libradicl::{u8_to_vec_of, u8_to_vec_of_bool, tag_value_try_into_int};
use num::cast::AsPrimitive;
use scroll::Pread;
use std::io::Read;
use std::io::Write;
use std::mem;

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

/// The below are currently hard-coded
/// until we decide how to solve this
/// generally
#[derive(Debug)]
pub struct FileTags {
    pub bclen: u16,
    pub umilen: u16,
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
        };
        v
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
    F32(f32),
    F64(f64),
    ArrayBool(Vec<bool>),
    ArrayU8(Vec<u8>),
    ArrayU16(Vec<u16>),
    ArrayU32(Vec<u32>),
    ArrayU64(Vec<u64>),
    ArrayF32(Vec<f32>),
    ArrayF64(Vec<f64>),
    ArrayString(Vec<String>),
    String(String),
}

tag_value_try_into_int!(u8);
tag_value_try_into_int!(u16);
tag_value_try_into_int!(u32);
tag_value_try_into_int!(u64);
/* impl TryInto<u16> for TagValue {
    type Error = anyhow::Error;

    fn try_into(self) -> std::result::Result<u16, Self::Error> {
        match self {
            Self::U8(x) => { Ok(x as u16) },
            Self::U16(x) => { Ok(x) },
            Self::U32(x) => { 
                if x > u16::MAX as u32 {
                    bail!("Cannot convert value {x} to u16; too large")
                } else {
                    Ok(x as u16)
                }
            },
            Self::U64(x) => { 
                if x > u16::MAX as u64 {
                    bail!("Cannot convert value {x} to u16; too large")
                } else {
                    Ok(x as u16)
                }
            },
            _ => { bail!("cannot convert non-int TagValue to u16") }
        }
    }
}
*/

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
                let t2: RadAtomicId = buf.pread::<u8>(1)?.into();
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
            (RadType::Array(_, RadAtomicId::Bool), TagValue::ArrayBool(_)) => true,
            (RadType::Array(_, RadAtomicId::Int(RadIntId::U8)), TagValue::ArrayU8(_)) => true,
            (RadType::Array(_, RadAtomicId::Int(RadIntId::U16)), TagValue::ArrayU16(_)) => true,
            (RadType::Array(_, RadAtomicId::Int(RadIntId::U32)), TagValue::ArrayU32(_)) => true,
            (RadType::Array(_, RadAtomicId::Int(RadIntId::U64)), TagValue::ArrayU64(_)) => true,
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
