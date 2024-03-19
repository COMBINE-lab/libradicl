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

use crate::libradicl::rad_types::RadIntId;
use anyhow::Context;
use scroll::Pread;
use std::io::Write;
use std::io::{Cursor, Read};

/// A free function to read an integer, described by the provided [RadIntId]
/// into a `u64` container (which is guaranteed to be large enough to
/// fit any valid [RadIntId] type). Returns the u64 containing the value
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
    };
    v
}

/// A free function to read an integer, described by the provided [RadIntId]
/// into a `u64` container (which is guaranteed to be large enough to
/// fit any valid [RadIntId] type).  Returns an [anyhow::Result] containing
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
    };
    Ok(v)
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
    }
    owriter
        .write_all(v.as_bytes())
        .expect("coudn't write to output file");
}
