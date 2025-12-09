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

use crate::{
    as_u128, as_u64, as_i128, as_i64, libradicl::rad_types::RadIntId,
    libradicl::record::ConvertiblePrimitiveInteger, try_as_u128, try_as_u64,
    try_as_i128, try_as_i64,
};
use anyhow::Context;
use scroll::Pread;
use std::io::Write;
use std::io::{Cursor, Read};

// Since we cannot implement [From] for the
// relevant builtin types ([u8], [u16], [u32],
// [u64], [u128]), we have to wrap them in a
// newtype to implement this trait. These are
// the corresponding newtypes for each of the
// supported primitive integer types.

/// Wrapper type for [u8] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewU8(pub u8);

/// Wrapper type for [u16] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewU16(pub u16);

/// Wrapper type for [u32] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewU32(pub u32);

/// Wrapper type for [u64] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewU64(pub u64);

/// Wrapper type for [u128] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewU128(pub u128);

/// Wrapper type for [i8] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewI8(pub i8);

/// Wrapper type for [i16] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewI16(pub i16);

/// Wrapper type for [i32] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewI32(pub i32);

/// Wrapper type for [i64] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewI64(pub i64);

/// Wrapper type for [i128] so that we can implement [From]
/// to read into the relevant builtin type in a generic manner.
pub struct NewI128(pub i128);


/// Allows a distinct [TryFrom] implementation for
/// converting types read from file into [u64] or [u128]
pub struct TryWrapper<T>(pub T);

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

as_i64!(NewI8);
as_i64!(NewI16);
as_i64!(NewI32);
as_i64!(NewI64);
as_i64!(NewI128);
try_as_i64!(NewI8);
try_as_i64!(NewI16);
try_as_i64!(NewI32);
try_as_i64!(NewI64);
try_as_i64!(NewI128);

as_i128!(NewI8);
as_i128!(NewI16);
as_i128!(NewI32);
as_i128!(NewI64);
as_i128!(NewI128);
try_as_i128!(NewI8);
try_as_i128!(NewI16);
try_as_i128!(NewI32);
try_as_i128!(NewI64);
try_as_i128!(NewI128);

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
        _ => {
            panic!("attempt to read signed RadIntId type into u64");
        }
    };
    v
}

/// A free function to read an integer, described by the provided [RadIntId]
/// into a `i64` container. Returns the u64 containing the value
/// read, panics on error.
pub fn read_into_i64<T: Read>(reader: &mut T, rt: &RadIntId) -> i64 {
    let mut rbuf = [0u8; 8];

    let v: i64 = match rt {
        RadIntId::I8 => {
            reader.read_exact(&mut rbuf[0..1]).unwrap();
            rbuf.pread::<i8>(0).unwrap() as i64
        }
        RadIntId::I16 => {
            reader.read_exact(&mut rbuf[0..2]).unwrap();
            rbuf.pread::<i16>(0).unwrap() as i64
        }
        RadIntId::I32 => {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            rbuf.pread::<i32>(0).unwrap() as i64
        }
        RadIntId::I64 => {
            reader.read_exact(&mut rbuf[0..8]).unwrap();
            rbuf.pread::<i64>(0).unwrap()
        }
        RadIntId::I128 => {
            panic!("cannot read i128 into a i64");
        }
        _ => {
            panic!("attempt to read unsigned RadIntId type into i64");
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
///
/// If the `rt` argument is a [RadIntId::U128] and the user is requesting to
/// read into a u64, this will cause a runtime `panic!`.  All types can be
/// safely converted into a `u128`, but only `u8`, `u16`, `u32`, and `u64` can be read
/// into a `u64` safely.
///
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
        RadIntId::I8 => {
            reader.read_exact(&mut rbuf[0..1]).unwrap();
            NewI8(rbuf.pread::<i8>(0).unwrap()).into()
        }
        RadIntId::I16 => {
            reader.read_exact(&mut rbuf[0..2]).unwrap();
            NewI16(rbuf.pread::<i16>(0).unwrap()).into()
        }
        RadIntId::I32 => {
            reader.read_exact(&mut rbuf[0..4]).unwrap();
            NewI32(rbuf.pread::<i32>(0).unwrap()).into()
        }
        RadIntId::I64 => {
            reader.read_exact(&mut rbuf[0..8]).unwrap();
            NewI64(rbuf.pread::<i64>(0).unwrap()).into()
        }
        RadIntId::I128 => {
            reader.read_exact(&mut rbuf[0..16]).unwrap();
            NewI128(rbuf.pread::<i128>(0).unwrap()).into()
        }
    };
    v
}


/// A fallible free function to read into an integer type that is generic over
/// the size of the integer being returned.  Specifically, the type `B`
/// can be either a [u64]/[i64] or a [u128]/[i128], and the approriate number of
/// bytes of the underlying reader will be consumed and converted into
/// an integer of the appropriate width. Attempting to read a [RadIntId::U128] into
/// a `u64` or a [RadIntId::I128] into a `i64` will produce an [anyhow::Error], while all 
/// other conversions should be successful.
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
        RadIntId::I8 => {
            reader
                .read_exact(&mut rbuf[0..1])
                .context("couldn't read i8 from the reader")?;

            match TryWrapper(NewI8(
                rbuf.pread::<i8>(0).context("couldn't parse result as i8")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert i8 to the requested type"),
            }
        }
        RadIntId::I16 => {
            reader
                .read_exact(&mut rbuf[0..2])
                .context("couldn't read i16 from the reader")?;
            match TryWrapper(NewI16(
                rbuf.pread::<i16>(0)
                    .context("couldn't parse result as i16")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert i16 to the requested type"),
            }
        }
        RadIntId::I32 => {
            reader
                .read_exact(&mut rbuf[0..4])
                .context("couldn't read i32 from the reader")?;

            match TryWrapper(NewI32(
                rbuf.pread::<i32>(0)
                    .context("couldn't parse result as i32")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert i32 to the requested type"),
            }
        }
        RadIntId::I64 => {
            reader
                .read_exact(&mut rbuf[0..8])
                .context("couldn't read i64 from the reader")?;

            match TryWrapper(NewI64(
                rbuf.pread::<i64>(0)
                    .context("couldn't parse result as i64")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert i64 to the requested type"),
            }
        }
        RadIntId::I128 => {
            reader
                .read_exact(&mut rbuf[0..16])
                .context("couldn't read i128 from the reader")?;
            match TryWrapper(NewI128(
                rbuf.pread::<i128>(0)
                    .context("couldn't parse result as i128")?,
            ))
            .try_into()
            {
                Ok(x) => Ok(x),
                Err(_) => anyhow::bail!("could not convert i128 to the requested type"),
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
/// into a `i128` container (which is guaranteed to be large enough to
/// fit any valid [RadIntId] type). Returns the i128 containing the value
/// read, panics on error.
pub fn read_into_i128<T: Read>(reader: &mut T, rt: &RadIntId) -> i128 {
    if matches!(rt, RadIntId::I128) {
        let mut rbuf = [0u8; 16];
        reader.read_exact(&mut rbuf[0..16]).unwrap();
        rbuf.pread::<i128>(0).unwrap()
    } else {
        read_into_i64(reader, rt) as i128
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
        _ => {
            anyhow::bail!("cannot read signed RadIntId type into u64");
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


/// A free function to read an integer, described by the provided [RadIntId]
/// into a `i64` container.  Returns an [anyhow::Result] containing
/// the i64 value read on success, or an error otherwise.
pub fn try_read_into_i64<T: Read>(reader: &mut T, rt: &RadIntId) -> anyhow::Result<i64> {
    let mut rbuf = [0u8; 8];

    let v: i64 = match rt {
        RadIntId::I8 => {
            reader
                .read_exact(&mut rbuf[0..1])
                .context("couldn't read i8 from the reader")?;
            rbuf.pread::<i8>(0).context("couldn't parse result as i8")? as i64
        }
        RadIntId::I16 => {
            reader
                .read_exact(&mut rbuf[0..2])
                .context("couldn't read i16 from the reader")?;
            rbuf.pread::<i16>(0)
                .context("couldn't parse result as i8")? as i64
        }
        RadIntId::I32 => {
            reader
                .read_exact(&mut rbuf[0..4])
                .context("couldn't read i32 from the reader")?;
            rbuf.pread::<i32>(0)
                .context("couldn't parse result as i8")? as i64
        }
        RadIntId::I64 => {
            reader
                .read_exact(&mut rbuf[0..8])
                .context("couldn't read i64 from the reader")?;
            rbuf.pread::<i64>(0)
                .context("couldn't parse result as i8")?
        }
        RadIntId::I128 => {
            anyhow::bail!("cannot read i128 into i64");
        }
        _ => {
            anyhow::bail!("cannot read unsigned RadIntId type into i64");
        }

    };
    Ok(v)
}

/// A free function to read an integer, described by the provided [RadIntId]
/// into a `i128` container (which is guaranteed to be large enough to
/// fit any valid [RadIntId] type).  Returns an [anyhow::Result] containing
/// the i128 value read on success, or an error otherwise.
pub fn try_read_into_i128<T: Read>(reader: &mut T, rt: &RadIntId) -> anyhow::Result<i128> {
    if matches!(rt, RadIntId::I128) {
        let mut rbuf = [0u8; 16];
        reader
            .read_exact(&mut rbuf[0..16])
            .context("couldn't read i64 from the reader")?;
        let v: i128 = rbuf
            .pread::<i128>(0)
            .context("couldn't parse result as i128")?;
        Ok(v)
    } else {
        Ok(try_read_into_i64(reader, rt).unwrap() as i128)
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
        RadIntId::I8 => {
            owriter
                .write_all(&(v.len() as i8).to_le_bytes())
                .expect("coudn't write to output file");
        }
        RadIntId::I16 => {
            owriter
                .write_all(&(v.len() as i16).to_le_bytes())
                .expect("coudn't write to output file");
        }
        RadIntId::I32 => {
            owriter
                .write_all(&(v.len() as i32).to_le_bytes())
                .expect("coudn't write to output file");
        }
        RadIntId::I64 => {
            owriter
                .write_all(&(v.len() as i64).to_le_bytes())
                .expect("coudn't write to output file");
        }
        RadIntId::I128 => {
            owriter
                .write_all(&(v.len() as i128).to_le_bytes())
                .expect("coudn't write to output file");
        }
    }
    owriter
        .write_all(v.as_bytes())
        .expect("coudn't write to output file");
}
