/*
 * Copyright (c) 2020-2026 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Optional per-chunk compression for RAD files.
//!
//! When a producer compresses chunk payloads, it advertises the codec via a
//! file-level tag named [`CHUNK_CODEC_TAG`] (a `u8` holding [`ChunkCodec::as_u8`]).
//! **Absence of the tag means [`ChunkCodec::None`]** — every RAD file written
//! before this feature, and any producer that does not opt in, reads unchanged.
//!
//! On disk a compressed chunk keeps the usual `[u32 nbytes][u32 nrec]` header,
//! but `nbytes` is the *compressed* framing size (header + compressed payload)
//! and the records following the header are the compressed bytes. The
//! uncompressed size travels inside the compressed payload (lz4 via
//! `compress_prepend_size`; zstd frames are self-describing), so a reader can
//! restore the original chunk without any extra header field. Each chunk is
//! independently (de)compressible, preserving streaming and parallel access.
//!
//! `lz4` (codec id 1) is always available through the pure-Rust `lz4_flex`.
//! `zstd` (codec id 2) requires the crate's `zstd` feature; without it a reader
//! errors clearly on a zstd chunk rather than producing garbage.

use anyhow::bail;

/// Well-known file-tag name advertising the chunk compression codec (a `u8`).
pub const CHUNK_CODEC_TAG: &str = "chunk_codec";

/// zstd compression level used when writing zstd-compressed chunks. Level 3 is
/// the measured sweet spot for RAD payloads (good ratio, fast); decoding does
/// not depend on the level, so this can change without a format change.
#[cfg(feature = "zstd")]
const ZSTD_LEVEL: i32 = 3;

/// The compression codec applied to RAD chunk payloads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ChunkCodec {
    /// No compression — payload bytes are the records verbatim (the default and
    /// the meaning of an absent [`CHUNK_CODEC_TAG`]).
    #[default]
    None,
    /// LZ4 (pure-Rust `lz4_flex`, `compress_prepend_size` framing).
    Lz4,
    /// zstd (requires the `zstd` crate feature).
    Zstd,
}

impl ChunkCodec {
    /// Decode a codec id. `0 => None`, `1 => Lz4`, `2 => Zstd`; any other value
    /// is an error (a newer codec this build does not understand) — callers
    /// must treat an *absent* tag as [`ChunkCodec::None`] before calling this.
    pub fn from_u8(v: u8) -> anyhow::Result<Self> {
        Ok(match v {
            0 => ChunkCodec::None,
            1 => ChunkCodec::Lz4,
            2 => ChunkCodec::Zstd,
            x => bail!("unknown RAD chunk codec id {x}; this build cannot read it"),
        })
    }

    /// The codec id written to the [`CHUNK_CODEC_TAG`] file tag.
    pub fn as_u8(self) -> u8 {
        match self {
            ChunkCodec::None => 0,
            ChunkCodec::Lz4 => 1,
            ChunkCodec::Zstd => 2,
        }
    }
}

/// Compress a chunk *payload* (the record bytes, excluding the 8-byte header)
/// with `codec`. For [`ChunkCodec::None`] this clones the payload unchanged.
pub fn compress_payload(codec: ChunkCodec, payload: &[u8]) -> anyhow::Result<Vec<u8>> {
    match codec {
        ChunkCodec::None => Ok(payload.to_vec()),
        ChunkCodec::Lz4 => Ok(lz4_flex::compress_prepend_size(payload)),
        ChunkCodec::Zstd => {
            #[cfg(feature = "zstd")]
            {
                Ok(zstd::encode_all(payload, ZSTD_LEVEL)?)
            }
            #[cfg(not(feature = "zstd"))]
            {
                bail!("writing zstd-compressed chunks requires the libradicl `zstd` feature")
            }
        }
    }
}

/// Decompress a chunk payload produced by [`compress_payload`] with the same
/// `codec`, returning the original record bytes. [`ChunkCodec::None`] returns
/// the input unchanged.
pub fn decompress_payload(codec: ChunkCodec, data: &[u8]) -> anyhow::Result<Vec<u8>> {
    match codec {
        ChunkCodec::None => Ok(data.to_vec()),
        ChunkCodec::Lz4 => lz4_flex::decompress_size_prepended(data)
            .map_err(|e| anyhow::anyhow!("lz4 chunk decompression failed: {e}")),
        ChunkCodec::Zstd => {
            #[cfg(feature = "zstd")]
            {
                Ok(zstd::decode_all(data)?)
            }
            #[cfg(not(feature = "zstd"))]
            {
                bail!(
                    "this RAD file uses zstd-compressed chunks (codec id 2), but this build of \
                     libradicl was compiled without the `zstd` feature"
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lz4_roundtrip() {
        let data: Vec<u8> = (0..10_000u32)
            .flat_map(|i| (i as u16).to_le_bytes())
            .collect();
        let c = compress_payload(ChunkCodec::Lz4, &data).unwrap();
        let d = decompress_payload(ChunkCodec::Lz4, &c).unwrap();
        assert_eq!(d, data);
    }

    #[test]
    fn codec_id_roundtrip() {
        for c in [ChunkCodec::None, ChunkCodec::Lz4, ChunkCodec::Zstd] {
            assert_eq!(ChunkCodec::from_u8(c.as_u8()).unwrap(), c);
        }
        assert!(ChunkCodec::from_u8(7).is_err());
    }

    #[cfg(feature = "zstd")]
    #[test]
    fn zstd_roundtrip() {
        let data: Vec<u8> = (0..10_000u32)
            .flat_map(|i| (i as u16).to_le_bytes())
            .collect();
        let c = compress_payload(ChunkCodec::Zstd, &data).unwrap();
        let d = decompress_payload(ChunkCodec::Zstd, &c).unwrap();
        assert_eq!(d, data);
    }
}
