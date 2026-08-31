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
use std::hash::{BuildHasher, Hasher};

#[allow(unused_imports)]
use bio_types::strand::Strand;

pub struct TempCellInfo {
    pub offset: u64,
    pub nbytes: u32,
    pub nrec: u32,
}

/// A `HashMap` keyed on a `u64` with the fixed, non-cryptographic [`U64BuildHasher`].
///
/// Used for the collation byte-accounting maps (`cell_map` / `cb_byte_map`),
/// which are keyed on a barcode or a `(sample, cell)` composite and touched once
/// per record over the whole RAD. See [`U64BuildHasher`] for why the general
/// randomized hasher was replaced here.
pub type U64Map<V> = std::collections::HashMap<u64, V, U64BuildHasher>;

/// A fixed-seed, allocation-free `BuildHasher` specialised for `u64` keys.
///
/// The collation maps hash one `u64` per record across the entire input, so the
/// per-operation hasher cost is on the collate critical path. The previous
/// `ahash::RandomState` pays for that generality twice over here: it draws a
/// randomised state (so each `build_hasher` reconstitutes an `AHasher` from that
/// state) and mixes with AES rounds sized for arbitrary byte streams — overkill
/// for a single `u64`.
///
/// This is the `FxHash` step (rustc's own hasher): one rotate/xor/multiply by a
/// fixed odd constant, which for a single `u64` key reduces to `key * K`. A
/// microbenchmark of the collate inner loop measured ~23% off the hashing
/// component versus `ahash` on this access pattern; the alternative of a fuller
/// finalizer (moremur) measured no gain, its longer dependency chain costing as
/// much as the AES rounds it replaced.
///
/// Distribution: multiplicative hashing mixes all input bits into the high bits
/// of the product, and SwissTable takes its control byte from the top 7 bits, so
/// the top-bit spread stays good on structured keys — the guard against the
/// identity-hash collision failure that made `ahash` necessary (see the
/// `top_bits_spread_on_structured_keys` test). This is exactly what `FxHash`
/// does in rustc's hash maps.
///
/// It is deterministic across runs. That does not affect output — hashing only
/// governs bucketing — and it is not exposed to adversarial input, so the lack of
/// per-run randomisation (HashDoS resistance) is irrelevant here.
#[derive(Clone, Copy, Default)]
pub struct U64BuildHasher;

impl BuildHasher for U64BuildHasher {
    type Hasher = U64Hasher;
    #[inline]
    fn build_hasher(&self) -> U64Hasher {
        U64Hasher(0)
    }
}

/// The [`Hasher`] produced by [`U64BuildHasher`]. See its docs.
pub struct U64Hasher(u64);

/// Odd multiplier with good high-bit mixing (the `FxHash` constant).
const K: u64 = 0x51_7C_C1_B7_27_22_0A_95;

impl Hasher for U64Hasher {
    #[inline]
    fn write_u64(&mut self, i: u64) {
        // The FxHash combine step; for a single u64 key this is `i * K`.
        self.0 = (self.0.rotate_left(5) ^ i).wrapping_mul(K);
    }

    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64);
    }

    /// Fallback for keys that are not a single `u64`. The collation maps never
    /// hit this (every key is `u64`), but keeping the hasher correct for general
    /// keys avoids a silent trap if it is ever reused: the same FxHash step, one
    /// byte at a time.
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut acc = self.0;
        for &b in bytes {
            acc = (acc.rotate_left(5) ^ u64::from(b)).wrapping_mul(K);
        }
        self.0 = acc;
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

#[cfg(test)]
mod hash_tests {
    use super::*;
    use std::hash::BuildHasher;

    fn hash_one(k: u64) -> u64 {
        let mut h = U64BuildHasher.build_hasher();
        h.write_u64(k);
        h.finish()
    }

    #[test]
    fn deterministic() {
        assert_eq!(hash_one(42), hash_one(42));
        assert_eq!(hash_one(0), hash_one(0));
        assert_ne!(hash_one(0), hash_one(1));
    }

    /// The SwissTable failure mode is a weak top-7-bit distribution on
    /// structured keys. Sequential keys and shifted-composite keys (like the
    /// `(sample << 32) | cell` collation key) must spread their control byte.
    #[test]
    fn top_bits_spread_on_structured_keys() {
        let mut tags = [0u64; 128];
        for i in 0..10_000u64 {
            tags[(hash_one(i) >> 57) as usize] += 1; // top 7 bits
        }
        let seen = tags.iter().filter(|&&c| c > 0).count();
        assert!(seen > 120, "only {seen}/128 control-byte values seen");

        // Composite keys that share a high sample field must still spread.
        let mut tags2 = [0u64; 128];
        for cell in 0..10_000u64 {
            let key = (7u64 << 32) | cell;
            tags2[(hash_one(key) >> 57) as usize] += 1;
        }
        let seen2 = tags2.iter().filter(|&&c| c > 0).count();
        assert!(seen2 > 120, "composite keys: only {seen2}/128 seen");
    }

    /// Functions as a real map hasher: every inserted key is retrievable and
    /// distinct keys do not clobber each other.
    #[test]
    fn works_as_map_hasher() {
        let mut m: U64Map<u64> = U64Map::default();
        for i in 0..50_000u64 {
            let key = (i.wrapping_mul(2_654_435_761)) ^ (i << 32);
            m.insert(key, i);
        }
        assert_eq!(m.len(), 50_000);
        for i in 0..50_000u64 {
            let key = (i.wrapping_mul(2_654_435_761)) ^ (i << 32);
            assert_eq!(m.get(&key), Some(&i));
        }
    }
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
    Pos(Box<dyn Fn(u32, usize) -> usize + 'a>),
}
