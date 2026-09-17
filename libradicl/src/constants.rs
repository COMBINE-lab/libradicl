/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Constants relevant for the `RAD` format
pub(crate) const MAX_REF_NAME_LEN: usize = 65536;

/// Magic signature at the very start of a *versioned* (spec ≥ 2) RAD prelude,
/// immediately followed by a little-endian `u16` spec version. Its first byte
/// (`b'R'` = 0x52) can never begin a legacy prelude — whose first byte is the
/// `is_paired` flag ∈ {0, 1} — so a reader distinguishes versioned from legacy
/// files by sniffing these bytes without ambiguity. See [`RAD_SPEC_VERSION`].
pub const RAD_MAGIC: [u8; 8] = *b"RAD_FILE";

/// The RAD spec version this build writes for versioned files. Legacy files
/// (produced before the magic + version were introduced) carry no magic and are
/// read as version 0. Versioned files start at 2 (1 is reserved to mean
/// "implicitly legacy"), which is the first version to carry, e.g., per-tag
/// collation role annotations.
pub const RAD_SPEC_VERSION: u16 = 2;

/// The spec version reported for a legacy (magic-less) RAD prelude.
pub const RAD_LEGACY_VERSION: u16 = 0;
