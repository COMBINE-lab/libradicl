/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! This module contains types for describing hierarchical collation
//! of RAD files, supporting multi-barcode protocols like 10x Flex
//! where reads carry multiple barcodes (e.g., sample + cell).

use serde::{Deserialize, Serialize};
use std::io::{Read, Write};

/// The semantic role of a barcode in the experiment hierarchy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BarcodeRole {
    /// Sample/library-level barcode (outermost collation level)
    Sample,
    /// Cell-level barcode
    Cell,
    /// Feature barcode (e.g., CITE-seq antibody tag)
    Feature,
}

impl std::fmt::Display for BarcodeRole {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BarcodeRole::Sample => write!(f, "sample"),
            BarcodeRole::Cell => write!(f, "cell"),
            BarcodeRole::Feature => write!(f, "feature"),
        }
    }
}

impl std::str::FromStr for BarcodeRole {
    type Err = anyhow::Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "sample" => Ok(BarcodeRole::Sample),
            "cell" => Ok(BarcodeRole::Cell),
            "feature" => Ok(BarcodeRole::Feature),
            _ => anyhow::bail!("unknown barcode role: {}", s),
        }
    }
}

/// Describes a single sample group within a hierarchically-collated RAD file.
/// After collation, chunks belonging to this sample are contiguous in the file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SampleGroup {
    /// The corrected sample barcode value (2-bit packed)
    pub key: u64,
    /// Optional human-readable name for this sample
    pub name: Option<String>,
    /// Index of the first chunk belonging to this sample
    pub chunk_start: u64,
    /// Number of chunks (cells) in this sample
    pub num_chunks: u64,
    /// Total number of records across all chunks in this sample
    pub num_records: u64,
}

/// Describes hierarchical chunk organization in a collated RAD file.
/// Serialized as a sidecar file (`collation_manifest.bin`) alongside
/// the collated RAD file.
///
/// For standard single-barcode collation, no manifest is produced.
/// For multi-barcode protocols (e.g., 10x Flex), the manifest describes
/// how chunks are grouped: first by sample barcode, then by cell barcode
/// within each sample.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollationManifest {
    /// The collation levels in order from outermost to innermost.
    /// e.g., ["sample", "cell"] for 10x Flex.
    pub levels: Vec<String>,
    /// The sample groups, ordered by their position in the RAD file.
    pub sample_groups: Vec<SampleGroup>,
}

impl CollationManifest {
    /// Create a new empty manifest with the given collation level names.
    pub fn new(levels: Vec<String>) -> Self {
        Self {
            levels,
            sample_groups: Vec::new(),
        }
    }

    /// Add a sample group to the manifest.
    pub fn add_sample_group(&mut self, group: SampleGroup) {
        self.sample_groups.push(group);
    }

    /// Total number of chunks across all samples.
    pub fn total_chunks(&self) -> u64 {
        self.sample_groups.iter().map(|g| g.num_chunks).sum()
    }

    /// Total number of records across all samples.
    pub fn total_records(&self) -> u64 {
        self.sample_groups.iter().map(|g| g.num_records).sum()
    }

    /// Write the manifest to a writer in bincode format.
    pub fn write_to<W: Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        let encoded = bincode::serialize(self)
            .map_err(|e| anyhow::anyhow!("failed to serialize collation manifest: {}", e))?;
        writer.write_all(&encoded)?;
        Ok(())
    }

    /// Read a manifest from a reader in bincode format.
    pub fn read_from<R: Read>(reader: &mut R) -> anyhow::Result<Self> {
        let mut buf = Vec::new();
        reader.read_to_end(&mut buf)?;
        let manifest: Self = bincode::deserialize(&buf)
            .map_err(|e| anyhow::anyhow!("failed to deserialize collation manifest: {}", e))?;
        Ok(manifest)
    }

    /// Write the manifest to a file path.
    pub fn write_to_file(&self, path: &std::path::Path) -> anyhow::Result<()> {
        let mut file = std::fs::File::create(path)?;
        self.write_to(&mut file)
    }

    /// Read a manifest from a file path.
    pub fn read_from_file(path: &std::path::Path) -> anyhow::Result<Self> {
        let mut file = std::fs::File::open(path)?;
        Self::read_from(&mut file)
    }
}

// TODO: In the future, support frequency-based sample barcode discovery
// (similar to knee-finding for cell barcodes). For now, a known sample
// barcode list is always required.
//
// pub fn discover_samples(...) -> ... { ... }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collation_manifest_roundtrip() {
        let mut manifest = CollationManifest::new(vec!["sample".to_string(), "cell".to_string()]);
        manifest.add_sample_group(SampleGroup {
            key: 0x1234,
            name: Some("sample_A".to_string()),
            chunk_start: 0,
            num_chunks: 500,
            num_records: 1_000_000,
        });
        manifest.add_sample_group(SampleGroup {
            key: 0x5678,
            name: Some("sample_B".to_string()),
            chunk_start: 500,
            num_chunks: 400,
            num_records: 800_000,
        });

        assert_eq!(manifest.total_chunks(), 900);
        assert_eq!(manifest.total_records(), 1_800_000);

        // Round-trip through bincode
        let mut buf: Vec<u8> = Vec::new();
        manifest.write_to(&mut buf).unwrap();

        let mut cursor = std::io::Cursor::new(buf);
        let restored = CollationManifest::read_from(&mut cursor).unwrap();

        assert_eq!(restored.levels, manifest.levels);
        assert_eq!(restored.sample_groups.len(), 2);
        assert_eq!(restored.sample_groups[0].key, 0x1234);
        assert_eq!(restored.sample_groups[0].name, Some("sample_A".to_string()));
        assert_eq!(restored.sample_groups[1].num_chunks, 400);
    }

    #[test]
    fn barcode_role_display_and_parse() {
        assert_eq!(BarcodeRole::Sample.to_string(), "sample");
        assert_eq!(BarcodeRole::Cell.to_string(), "cell");
        assert_eq!(BarcodeRole::Feature.to_string(), "feature");

        assert_eq!(
            "sample".parse::<BarcodeRole>().unwrap(),
            BarcodeRole::Sample
        );
        assert_eq!("cell".parse::<BarcodeRole>().unwrap(), BarcodeRole::Cell);
        assert_eq!(
            "feature".parse::<BarcodeRole>().unwrap(),
            BarcodeRole::Feature
        );
        assert!("unknown".parse::<BarcodeRole>().is_err());
    }
}
