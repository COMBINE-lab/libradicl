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

/// Magic signature at the very start of a *versioned* RAD prelude, immediately
/// followed by two version bytes `[major: u8][minor: u8]`. Its first byte
/// (`b'R'` = 0x52) can never begin a legacy prelude — whose first byte is the
/// `is_paired` flag ∈ {0, 1} — so a reader distinguishes versioned from legacy
/// files by sniffing these bytes without ambiguity. See [`RAD_SPEC_MAJOR`].
pub const RAD_MAGIC: [u8; 8] = *b"RAD_FILE";

/// Spec **major** version this build writes/understands. Major bumps are
/// *breaking* prelude-layout changes: a reader must reject a file whose major is
/// unknown (see the reader's too-new guard). Legacy (magic-less) files report
/// major 0; major 1 is reserved to mean "implicitly legacy"; versioned files
/// begin at 2 — the first to carry, e.g., per-tag collation role annotations.
pub const RAD_SPEC_MAJOR: u8 = 2;

/// Spec **minor** version this build writes. Minor bumps are *additive*
/// (e.g. new optional tags/roles): within a supported major, a reader accepts a
/// higher minor best-effort, ignoring fields it does not know.
pub const RAD_SPEC_MINOR: u8 = 0;

/// First major version that carries the magic prefix (i.e. is "versioned").
/// Majors below this (0 legacy, 1 reserved) are not written with a prefix.
pub const RAD_FIRST_VERSIONED_MAJOR: u8 = 2;
