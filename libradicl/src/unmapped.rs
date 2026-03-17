/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Self-describing file format for unmapped barcode counts.
//!
//! Supports arbitrary numbers of barcode fields with per-field widths
//! matching `RadIntId`. Both single-barcode (standard 10x) and
//! multi-barcode (10x Flex) protocols are handled.
//!
//! ## File format
//!
//! ```text
//! [Header]
//!   version: u8           (currently 1)
//!   num_fields: u8        (number of barcode fields per record)
//!   field_types: [u8; N]  (RadIntId discriminant for each field)
//!
//! [Records] (repeated until EOF)
//!   barcode_0: [width_0 bytes]
//!   barcode_1: [width_1 bytes]  (if num_fields > 1)
//!   ...
//!   count: u32
//! ```

use crate::rad_types::RadIntId;
use std::io::{Read, Write};

/// Version marker for the self-describing format.
pub const UNMAPPED_BC_FORMAT_VERSION: u8 = 1;

/// Describes the record layout of an unmapped barcode count file.
#[derive(Debug, Clone)]
pub struct UnmappedBcFormat {
    /// The RadIntId type for each barcode field.
    pub field_types: Vec<RadIntId>,
}

impl UnmappedBcFormat {
    /// Create a format for a single barcode field.
    pub fn single(bc_type: RadIntId) -> Self {
        Self {
            field_types: vec![bc_type],
        }
    }

    /// Create a format for multiple barcode fields.
    pub fn multi(field_types: Vec<RadIntId>) -> Self {
        Self { field_types }
    }

    /// Number of barcode fields per record.
    pub fn num_fields(&self) -> usize {
        self.field_types.len()
    }

    /// Total bytes per record (all barcode fields + u32 count).
    pub fn record_bytes(&self) -> usize {
        self.field_types.iter().map(|t| t.size_of()).sum::<usize>() + std::mem::size_of::<u32>()
    }

    /// Write the header to a writer.
    pub fn write_header<W: Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        writer.write_all(&[UNMAPPED_BC_FORMAT_VERSION])?;
        writer.write_all(&[self.field_types.len() as u8])?;
        for ft in &self.field_types {
            let id: u8 = (*ft).into();
            writer.write_all(&[id])?;
        }
        Ok(())
    }

    /// Read a header from a reader. Returns None if the file is empty.
    pub fn read_header<R: Read>(reader: &mut R) -> anyhow::Result<Option<Self>> {
        let mut version_buf = [0u8; 1];
        match reader.read_exact(&mut version_buf) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(e.into()),
        }

        let version = version_buf[0];
        if version != UNMAPPED_BC_FORMAT_VERSION {
            anyhow::bail!(
                "Unsupported unmapped BC format version: {} (expected {})",
                version,
                UNMAPPED_BC_FORMAT_VERSION,
            );
        }

        let mut num_fields_buf = [0u8; 1];
        reader.read_exact(&mut num_fields_buf)?;
        let num_fields = num_fields_buf[0] as usize;

        let mut field_types = Vec::with_capacity(num_fields);
        for _ in 0..num_fields {
            let mut type_buf = [0u8; 1];
            reader.read_exact(&mut type_buf)?;
            field_types.push(RadIntId::from(type_buf[0]));
        }

        Ok(Some(Self { field_types }))
    }
}

/// Writer for unmapped barcode count records.
///
/// Accumulates records in memory, then flushes to a writer.
/// Thread-safe: each thread creates its own `UnmappedBcRecordWriter`,
/// then flushes to a shared file under a lock.
pub struct UnmappedBcRecordWriter {
    format: UnmappedBcFormat,
    buf: Vec<u8>,
}

impl UnmappedBcRecordWriter {
    /// Create a new writer with the given format.
    /// Does NOT write the header — the caller is responsible for writing
    /// the header once to the shared output file before any thread flushes.
    pub fn new(format: UnmappedBcFormat) -> Self {
        Self {
            format,
            buf: Vec::with_capacity(4096),
        }
    }

    /// Write a record with barcode values (as u64s, truncated to field width) and a count.
    pub fn write_record(&mut self, barcodes: &[u64], count: u32) {
        debug_assert_eq!(barcodes.len(), self.format.num_fields());
        for (bc, ft) in barcodes.iter().zip(self.format.field_types.iter()) {
            match ft {
                RadIntId::U8 => self.buf.extend_from_slice(&(*bc as u8).to_le_bytes()),
                RadIntId::U16 => self.buf.extend_from_slice(&(*bc as u16).to_le_bytes()),
                RadIntId::U32 => self.buf.extend_from_slice(&(*bc as u32).to_le_bytes()),
                RadIntId::U64 => self.buf.extend_from_slice(&bc.to_le_bytes()),
                _ => panic!("Unsupported RadIntId for unmapped BC: {:?}", ft),
            }
        }
        self.buf.extend_from_slice(&count.to_le_bytes());
    }

    /// Flush accumulated records to a writer.
    pub fn flush_to<W: Write>(&mut self, writer: &mut W) -> anyhow::Result<()> {
        if !self.buf.is_empty() {
            writer.write_all(&self.buf)?;
            self.buf.clear();
        }
        Ok(())
    }

    /// Whether any records have been accumulated.
    pub fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }
}

/// Reader for unmapped barcode count records.
///
/// Reads records one at a time, returning barcode values as u64s.
pub struct UnmappedBcRecordReader {
    format: UnmappedBcFormat,
    record_buf: Vec<u8>,
}

impl UnmappedBcRecordReader {
    /// Create a reader with the given format (from a parsed header).
    pub fn new(format: UnmappedBcFormat) -> Self {
        let record_bytes = format.record_bytes();
        Self {
            format,
            record_buf: vec![0u8; record_bytes],
        }
    }

    /// Read the next record. Returns None at EOF.
    /// On success, returns (barcodes_as_u64, count).
    pub fn read_record<R: Read>(&mut self, reader: &mut R) -> anyhow::Result<Option<(Vec<u64>, u32)>> {
        match reader.read_exact(&mut self.record_buf) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(e.into()),
        }

        let mut offset = 0usize;
        let mut barcodes = Vec::with_capacity(self.format.num_fields());
        for ft in &self.format.field_types {
            let val: u64 = match ft {
                RadIntId::U8 => self.record_buf[offset] as u64,
                RadIntId::U16 => {
                    u16::from_le_bytes(self.record_buf[offset..offset + 2].try_into().unwrap())
                        as u64
                }
                RadIntId::U32 => {
                    u32::from_le_bytes(self.record_buf[offset..offset + 4].try_into().unwrap())
                        as u64
                }
                RadIntId::U64 => {
                    u64::from_le_bytes(self.record_buf[offset..offset + 8].try_into().unwrap())
                }
                _ => panic!("Unsupported RadIntId for unmapped BC: {:?}", ft),
            };
            barcodes.push(val);
            offset += ft.size_of();
        }

        let count = u32::from_le_bytes(
            self.record_buf[offset..offset + 4].try_into().unwrap(),
        );

        Ok(Some((barcodes, count)))
    }

    /// Get the underlying format.
    pub fn format(&self) -> &UnmappedBcFormat {
        &self.format
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn single_barcode_roundtrip() {
        let fmt = UnmappedBcFormat::single(RadIntId::U32);
        assert_eq!(fmt.num_fields(), 1);
        assert_eq!(fmt.record_bytes(), 8); // u32 + u32

        let mut buf = Vec::new();
        fmt.write_header(&mut buf).unwrap();

        let mut writer = UnmappedBcRecordWriter::new(fmt.clone());
        writer.write_record(&[12345], 42);
        writer.write_record(&[67890], 7);
        writer.flush_to(&mut buf).unwrap();

        // Read back
        let mut cursor = Cursor::new(&buf);
        let read_fmt = UnmappedBcFormat::read_header(&mut cursor).unwrap().unwrap();
        assert_eq!(read_fmt.num_fields(), 1);

        let mut reader = UnmappedBcRecordReader::new(read_fmt);
        let (bcs, count) = reader.read_record(&mut cursor).unwrap().unwrap();
        assert_eq!(bcs, vec![12345]);
        assert_eq!(count, 42);

        let (bcs, count) = reader.read_record(&mut cursor).unwrap().unwrap();
        assert_eq!(bcs, vec![67890]);
        assert_eq!(count, 7);

        assert!(reader.read_record(&mut cursor).unwrap().is_none());
    }

    #[test]
    fn multi_barcode_roundtrip() {
        let fmt = UnmappedBcFormat::multi(vec![RadIntId::U16, RadIntId::U32]);
        assert_eq!(fmt.num_fields(), 2);
        assert_eq!(fmt.record_bytes(), 10); // u16 + u32 + u32

        let mut buf = Vec::new();
        fmt.write_header(&mut buf).unwrap();

        let mut writer = UnmappedBcRecordWriter::new(fmt.clone());
        writer.write_record(&[0xABCD, 0x12345678], 100);
        writer.flush_to(&mut buf).unwrap();

        let mut cursor = Cursor::new(&buf);
        let read_fmt = UnmappedBcFormat::read_header(&mut cursor).unwrap().unwrap();
        assert_eq!(read_fmt.num_fields(), 2);

        let mut reader = UnmappedBcRecordReader::new(read_fmt);
        let (bcs, count) = reader.read_record(&mut cursor).unwrap().unwrap();
        assert_eq!(bcs, vec![0xABCD, 0x12345678]);
        assert_eq!(count, 100);
    }

    #[test]
    fn empty_file() {
        let cursor = Cursor::new(Vec::<u8>::new());
        let result = UnmappedBcFormat::read_header(&mut cursor.clone()).unwrap();
        assert!(result.is_none());
    }
}
