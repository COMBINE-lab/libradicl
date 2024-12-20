/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! This module contains basic type-related information that doesn't fit cleanly into the other,
//! more focused modules.

use bio_types;

#[allow(unused_imports)]
use bio_types::strand::Strand;

pub struct TempCellInfo {
    pub offset: u64,
    pub nbytes: u32,
    pub nrec: u32,
}

#[derive(Debug)]
pub struct ProtocolInfo {
    // TODO: only makes sense
    // for single-strand protocols
    // right now.  Expand to be generic.
    pub expected_ori: Strand,
}

pub enum CollateKey<'a> {
    Barcode,
    Pos(Box<dyn Fn(u32, usize) -> usize + 'a>)
}