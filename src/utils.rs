/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! This module contains some utility constants and functions that are
//! helpful in processing RAD information.

use scroll::Pread;

pub const MASK_TOP_BIT_U32: u32 = 0x7FFFFFFF;
pub const MASK_LOWER_31_U32: u32 = 0x80000000;
pub const SPLICE_MASK_U32: u32 = 0xFFFFFFFE;

/// Check if more can be read from the underlying file buffer (e.g. to check if another chunk may exist).
/// **NOTE**: This doesn't guarantee that an entire properly formed semantic object exists in the file
/// starting at the current point, but just that it may.  In the future, we should consider adding
/// `try_from_bytes` to the relevant structures to complement the `from_bytes` in the case that reading the next
/// object may fail.
/// **NOTE**: This is taken from [Rust's std
/// library](https://doc.rust-lang.org/src/std/io/mod.rs.html#2279-2281).
/// **TODO**: Replace this with Rust's own `has_data_left` once that is stabilized.
#[inline]
pub fn has_data_left<T: std::io::BufRead>(reader: &mut T) -> std::io::Result<bool> {
    reader.fill_buf().map(|b| !b.is_empty())
}

/// Reads the header of a chunk, returning the number of bytes and number of records.
/// Returns [Ok(u32, u32)] on success and an [std::io::Error] if there was a problem
/// reading the header.
///
/// In the returned tuple, the first [u32] is the number of bytes in the chunk and the
/// second [u32] is the number of records in the chunk.
///
/// This function lives in util and outside of the [Chunk] trait because it is agnostic
/// to the type of the chunk (i.e. the record type).
#[inline]
pub fn read_chunk_header<T: std::io::BufRead>(reader: &mut T) -> std::io::Result<(u32, u32)> {
    let mut buf = [0_u8; 2 * std::mem::size_of::<u32>()];
    reader.read_exact(&mut buf)?;
    let nbytes = buf.pread::<u32>(0).unwrap();
    let nrec = buf.pread::<u32>(std::mem::size_of::<u32>()).unwrap();
    Ok((nbytes, nrec))
}
