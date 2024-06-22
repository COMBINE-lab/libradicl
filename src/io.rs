/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Free functions to help with reading and writing specific `libradicl` types
//! into and out of primitive types.

use crate::{libradicl::rad_types::RadIntId, libradicl::record::ConvertiblePrimitiveInteger};
use anyhow::Context;
use scroll::Pread;
use std::io::Write;
use std::io::{Cursor, Read};

pub struct NewU8(pub u8);

pub struct NewU16(pub u16);

pub struct NewU32(pub u32);

pub struct NewU64(pub u64);

pub struct NewU128(pub u128);

pub struct TryWrapper<T>(pub T);

macro_rules! as_u64 {
    ("NewU128") => {
        impl std::convert::From<$from_type> for u64 {
            #[inline(always)]
            fn from(x: $from_type) -> Self {
                panic!("cannot convert u128 into u64");
            }
        }
    };
    ($from_type: ty) => {
        impl std::convert::From<$from_type> for u64 {
            #[inline(always)]
            fn from(x: $from_type) -> Self {
                x.0 as u64
            }
        }
    };
}

macro_rules! as_u128 {
    ($from_type: ty) => {
        impl std::convert::From<$from_type> for u128 {
            #[inline(always)]
            fn from(x: $from_type) -> Self {
                x.0 as u128
            }
        }
    };
}

macro_rules! try_as_u64 {
    ("NewU128") => {
        impl std::convert::TryFrom<TryWrapper<$from_type>> for u64 {
            type Error = &'static str;
            #[inline(always)]
            fn try_from(x: TryWrapper<$from_type>) -> Result<Self, Self::Error> {
                Err("Cannot convert u128 into u64")
            }
        }
    };
    ($from_type: ty) => {
        impl std::convert::TryFrom<TryWrapper<$from_type>> for u64 {
            type Error = &'static str;
            #[inline(always)]
            fn try_from(x: TryWrapper<$from_type>) -> Result<Self, Self::Error> {
                Ok(x.0 .0 as u64)
            }
        }
    };
}

macro_rules! try_as_u128 {
    ($from_type: ty) => {
        impl std::convert::TryFrom<TryWrapper<$from_type>> for u128 {
            type Error = &'static str;
            #[inline(always)]
            fn try_from(x: TryWrapper<$from_type>) -> Result<Self, Self::Error> {
                Ok(x.0 .0 as u128)
            }
        }
    };
}

as_u64!(NewU8);
as_u64!(NewU16);
as_u64!(NewU32);
as_u64!(NewU64);
as_u64!(NewU128);
try_as_u64!(NewU8);
try_as_u64!(NewU16);
try_as_u64!(NewU32);
try_as_u64!(NewU64);
try_as_u64!(NewU128);

as_u128!(NewU8);
as_u128!(NewU16);
as_u128!(NewU32);
as_u128!(NewU64);
as_u128!(NewU128);
try_as_u128!(NewU8);
try_as_u128!(NewU16);
try_as_u128!(NewU32);
try_as_u128!(NewU64);
try_as_u128!(NewU128);

/// A free function to read an integer, described by the provided [RadIntId]
/// into a `u64` container. Returns the u64 containing the value
/// read, panics on error.
pub fn read_into_u64<T: Read>(reader: &mut T, rt: &RadIntId) -> u64 {
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
        RadIntId::U128 => {
            panic!("cannot read u128 into a u64");
        }
    };
    v
}

/// A free function to read into an integer type that is generic over
/// the size of the integer being returned.  Specifically, the type `B`
/// can be either a [u64] or a [u128], and the approriate number of
/// bytes of the underlying reader will be consumed and converted into
/// an integer of the appropriate width.
///
/// <section class="warning">
/// If the `rt` argument is a [RadIntId::U128] and the user is requesting to
/// read into a u64, this will cause a runtime `panic!`.  All types can be
/// safely converted into a `u128`, but only `u8`, `u16`, `u32`, and `u64` can be read
/// into a `u64` safely.
/// </section>
pub fn read_into<T: Read, B>(reader: &mut T, rt: &RadIntId) -> B
where
    B: ConvertiblePrimitiveInteger,
{
    let mut rbuf = [0u8; 16];

    let v: B = match rt {
        RadIntId::U8 => {
            reader.read_exact(&mut rbuf[0..1]).unwrap();
            NewU8(rbuf.pread::<u8>(0).unwrap()).into()
        }
        RadIntId::U16 => {
            reader.read_exact(&mut rbuf[0..2]).unwrap();
            NewU16(rbuf.pread::<u16>(0).unwrap()).into()
        }
        RadIntId::U32 => {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            NewU32(rbuf.pread::<u32>(0).unwrap()).into()
        }
        RadIntId::U64 => {
            reader.read_exact(&mut rbuf[0..8]).unwrap();
            NewU64(rbuf.pread::<u64>(0).unwrap()).into()
        }
        RadIntId::U128 => {
            reader.read_exact(&mut rbuf[0..16]).unwrap();
            NewU128(rbuf.pread::<u128>(0).unwrap()).into()
        }
    };
    v
}

/// A fallible free function to read into an integer type that is generic over
/// the size of the integer being returned.  Specifically, the type `B`
/// can be either a [u64] or a [u128], and the approriate number of
/// bytes of the underlying reader will be consumed and converted into
/// an integer of the appropriate width. Attempting to read a [RadIntId::U128] into
/// a `u64` will produce an [anyhow::Error], while all other conversions should be
/// successful.
pub fn try_read_into<T: Read, B>(reader: &mut T, rt: &RadIntId) -> anyhow::Result<B>
where
    B: ConvertiblePrimitiveInteger,
{
    let mut rbuf = [0u8; 16];
    match rt {
        RadIntId::U8 => {
            reader
                .read_exact(&mut rbuf[0..1])
                .context("couldn't read u8 from the reader")?;

            //let r: Result<B, <B as TryFrom<TryWrapper<NewU8>>>::Error> =
            match TryWrapper(NewU8(
                rbuf.pread::<u8>(0).context("couldn't parse result as u8")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert u8 to the requested type"),
            }
        }
        RadIntId::U16 => {
            reader
                .read_exact(&mut rbuf[0..2])
                .context("couldn't read u16 from the reader")?;

            match TryWrapper(NewU16(
                rbuf.pread::<u16>(0)
                    .context("couldn't parse result as u16")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert u16 to the requested type"),
            }
        }
        RadIntId::U32 => {
            reader
                .read_exact(&mut rbuf[0..4])
                .context("couldn't read u32 from the reader")?;

            match TryWrapper(NewU32(
                rbuf.pread::<u32>(0)
                    .context("couldn't parse result as u32")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert u32 to the requested type"),
            }
        }
        RadIntId::U64 => {
            reader
                .read_exact(&mut rbuf[0..8])
                .context("couldn't read u64 from the reader")?;

            match TryWrapper(NewU64(
                rbuf.pread::<u64>(0)
                    .context("couldn't parse result as u64")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert u64 to the requested type"),
            }
        }
        RadIntId::U128 => {
            reader
                .read_exact(&mut rbuf[0..16])
                .context("couldn't read u128 from the reader")?;
            match TryWrapper(NewU128(
                rbuf.pread::<u128>(0)
                    .context("couldn't parse result as u128")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert u128 to the requested type"),
            }
        }
    }
}

/// A free function to read an integer, described by the provided [RadIntId]
/// into a `u128` container (which is guaranteed to be large enough to
/// fit any valid [RadIntId] type). Returns the u128 containing the value
/// read, panics on error.
pub fn read_into_u128<T: Read>(reader: &mut T, rt: &RadIntId) -> u128 {
    if matches!(rt, RadIntId::U128) {
        let mut rbuf = [0u8; 16];
        reader.read_exact(&mut rbuf[0..16]).unwrap();
        rbuf.pread::<u128>(0).unwrap()
    } else {
        read_into_u64(reader, rt) as u128
    }
}

/// A free function to read an integer, described by the provided [RadIntId]
/// into a `u64` container.  Returns an [anyhow::Result] containing
/// the u64 value read on success, or an error otherwise.
pub fn try_read_into_u64<T: Read>(reader: &mut T, rt: &RadIntId) -> anyhow::Result<u64> {
    let mut rbuf = [0u8; 8];

    let v: u64 = match rt {
        RadIntId::U8 => {
            reader
                .read_exact(&mut rbuf[0..1])
                .context("couldn't read u8 from the reader")?;
            rbuf.pread::<u8>(0).context("couldn't parse result as u8")? as u64
        }
        RadIntId::U16 => {
            reader
                .read_exact(&mut rbuf[0..2])
                .context("couldn't read u16 from the reader")?;
            rbuf.pread::<u16>(0)
                .context("couldn't parse result as u8")? as u64
        }
        RadIntId::U32 => {
            reader
                .read_exact(&mut rbuf[0..4])
                .context("couldn't read u32 from the reader")?;
            rbuf.pread::<u32>(0)
                .context("couldn't parse result as u8")? as u64
        }
        RadIntId::U64 => {
            reader
                .read_exact(&mut rbuf[0..8])
                .context("couldn't read u64 from the reader")?;
            rbuf.pread::<u64>(0)
                .context("couldn't parse result as u8")?
        }
        RadIntId::U128 => {
            anyhow::bail!("cannot read u128 into u64");
        }
    };
    Ok(v)
}

/// A free function to read an integer, described by the provided [RadIntId]
/// into a `u128` container (which is guaranteed to be large enough to
/// fit any valid [RadIntId] type).  Returns an [anyhow::Result] containing
/// the u128 value read on success, or an error otherwise.
pub fn try_read_into_u128<T: Read>(reader: &mut T, rt: &RadIntId) -> anyhow::Result<u128> {
    if matches!(rt, RadIntId::U128) {
        let mut rbuf = [0u8; 16];
        reader
            .read_exact(&mut rbuf[0..16])
            .context("couldn't read u64 from the reader")?;
        let v: u128 = rbuf
            .pread::<u128>(0)
            .context("couldn't parse result as u128")?;
        Ok(v)
    } else {
        Ok(try_read_into_u64(reader, rt).unwrap() as u128)
    }
}

/// A free function write a Name, RadIntId pair to the provided `owriter`.
/// **Note**: panics on error.
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
        RadIntId::U128 => {
            owriter
                .write_all(&(v.len() as u128).to_le_bytes())
                .expect("coudn't write to output file");
        }
    }
    owriter
        .write_all(v.as_bytes())
        .expect("coudn't write to output file");
}
