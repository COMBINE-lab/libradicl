/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Types and functions that primarily deal with the reading and writing of
//! data [Chunk]s in the RAD file.

use crate::{self as libradicl};
use anyhow::{self, Context};
use libradicl::record::MappedRecord;
use scroll::Pread;
use std::io::{Cursor, Read};
use std::io::{Seek, SeekFrom, Write};

/// Represents a chunk of recrords in a RAD file. The record chunks constitute the
/// bulk of the RAD file, and each has an associated number of bytes and number of
/// records (encoded in the header).  This structure represents the parsed chunk and
/// it holds the associated records in its `reads` field.
#[derive(Debug, PartialEq)]
pub struct Chunk<T: MappedRecord> {
    pub nbytes: u32,
    pub nrec: u32,
    pub reads: Vec<T>,
}

/// A [CorrectedCbChunk] represents a [Chunk] of RAD records
/// that share the same underlying corrected cell barcode
/// `corrected_bc`.
#[deprecated(
    since = "0.9.1",
    note = "This type is not actually used, and its existence in the library may therefore be \
            confusing. Therefore it is being deprecated and is likelty to be removed in a future \
            release."
)]
#[derive(Debug)]
#[allow(dead_code)]
pub struct CorrectedCbChunk {
    pub(crate) remaining_records: u32,
    pub(crate) corrected_bc: u64,
    pub(crate) nrec: u32,
    pub(crate) data: Cursor<Vec<u8>>,
}

impl CorrectedCbChunk {
    pub fn from_label_and_counter(corrected_bc_in: u64, num_remain: u32) -> CorrectedCbChunk {
        let mut cc = CorrectedCbChunk {
            remaining_records: num_remain,
            corrected_bc: corrected_bc_in,
            nrec: 0u32,
            data: Cursor::new(Vec::<u8>::with_capacity((num_remain * 24) as usize)),
        };
        let dummy = 0u32;
        cc.data.write_all(&dummy.to_le_bytes()).unwrap();
        cc.data.write_all(&dummy.to_le_bytes()).unwrap();
        cc
    }
}

#[deprecated(
    since = "0.9.0",
    note = "This type is deprecated as it's name implies it is general, but it is specalized for the single-cell context. \
            This is replaced more generally by the ChunkContext trait and individual structures implementing this trait \
            For specific RAD file types."
)]
pub struct ChunkConfig {
    pub num_chunks: u64,
    pub bc_type: u8,
    pub umi_type: u8,
}

pub struct ChunkConfigAtac {
    pub num_chunks: u64,
    pub bc_type: u8,
}

pub trait ChunkContext {}

pub struct AlevinFryChunkContext {
    pub num_chunks: u64,
    pub bc_type: u8,
    pub umi_type: u8,
}

impl ChunkContext for AlevinFryChunkContext {}

impl<R: MappedRecord> Chunk<R> {
    /// Read the header of the next [Chunk] from the provided `reader`. This
    /// function returns a tuple representing the number of bytes and number of
    /// records, respectively, in the chunk.
    #[inline]
    pub fn read_header<T: Read>(reader: &mut T) -> (u32, u32) {
        let mut buf = [0u8; 8];
        reader.read_exact(&mut buf).unwrap();
        let nbytes = buf.pread::<u32>(0).unwrap();
        let nrec = buf.pread::<u32>(4).unwrap();
        (nbytes, nrec)
    }

    /// Write this chunk to the provided `writer`, which must implement [std::io::Seek].
    /// This is because in order to write the number of bytes in the chunk, we need to know
    /// the size of the final encoding.  Returns Ok(()) on sucess, or propagates any errors
    /// otherwise.
    pub fn write<W: Write + Seek>(
        &self,
        writer: &mut W,
        ctx: &R::ParsingContext,
    ) -> anyhow::Result<()> {
        let dummy_num_bytes = 0_u32;
        let start_pos = writer
            .stream_position()
            .context("couldn't get stream position at start")?;

        writer
            .write_all(&dummy_num_bytes.to_le_bytes())
            .context("couldn't write dummy bytes for chunk")?;

        let nrec = self.reads.len() as u32;
        writer
            .write_all(&nrec.to_le_bytes())
            .context("couldn't write num records for chunk")?;

        for r in &self.reads {
            r.write(writer, ctx).context("couldn't write record")?;
        }
        let end_pos = writer
            .stream_position()
            .context("couldn't get stream position at end")?;
        let nbytes: u32 = (end_pos - start_pos) as u32;
        writer
            .seek(SeekFrom::Current(-(nbytes as i64)))
            .context("couldn't seek to start of chunk")?;
        writer
            .write_all(&nbytes.to_le_bytes())
            .context("couldn't write bytes for chunk")?;

        let seek_fwd = (nbytes as usize) - std::mem::size_of_val(&nbytes);
        writer
            .seek(SeekFrom::Current(seek_fwd as i64))
            .context("couldn't seek to end of chunk")?;
        Ok(())
    }

    /// Read the next [Chunk] from the provided reader and return it.
    #[inline]
    pub fn from_bytes_with_tags<T: Read>(_reader: &mut T, _ctx: &R::ParsingContext) -> Self {
        // think about how best to implement this, and where to store the tags
        // (a) should the tags be part of the record, or stored externally (e.g. in a parallel
        // Vec)?
        // (b) should the tags be read into an "unparsed" structure (e.g. a binary blob) and
        // then parsed on demand, or parsed as they are read here?
        // (c) What's the best mechanism to allow the user to access the tags?
        todo!("Should read and store the optional tags associated with each record.");
    }

    /// Read the next [Chunk] from the provided reader and return it.
    #[inline]
    pub fn from_bytes<T: Read>(reader: &mut T, ctx: &R::ParsingContext) -> Self {
        let (nbytes, nrec) = Self::read_header(reader);
        //println!("parsed chunk header :: nbytes {} {}", nbytes, nrec);
        let mut c = Self {
            nbytes,
            nrec,
            reads: Vec::<R>::with_capacity(nrec as usize),
        };

        for _i in 0..(nrec as usize) {
            c.reads.push(R::from_bytes_with_context(reader, ctx));
        }
        c
    }

    /// Peeks to the first [libradicl::record::AlevinFryReadRecord] in the buffer `buf`, and returns
    /// the barcode and umi associated with this record.  It is assumed
    /// that there is at least one [libradicl::record::AlevinFryReadRecord] present in the buffer.
    #[inline]
    pub fn peek_record(buf: &[u8], ctx: &R::ParsingContext) -> R::PeekResult {
        R::peek_record(buf, ctx)
    }
}

#[cfg(test)]
mod tests {
    use crate::chunk::Chunk;
    use crate::header::{RadHeader, RadPrelude};
    use crate::rad_types::{RadIntId, TagMap, TagSection, TagSectionLabel, TagValue};
    use crate::rad_types::{RadType, TagDesc};
    use crate::record::{AlevinFryReadRecord, AlevinFryRecordContext, RecordContext};
    use std::io::Cursor;

    #[test]
    fn can_write_af_chunk() {
        let rec = AlevinFryReadRecord {
            bc: 12345_u64,
            umi: 6789_u64,
            dirs: vec![true, true, true, false],
            refs: vec![123, 456, 78, 910],
        };

        let ft = TagSection::new_with_label(TagSectionLabel::FileTags);
        let mut rt = TagSection::new_with_label(TagSectionLabel::ReadTags);
        rt.add_tag_desc(TagDesc {
            name: "b".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        rt.add_tag_desc(TagDesc {
            name: "u".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        let at = TagSection::new_with_label(TagSectionLabel::AlignmentTags);

        let ctx = AlevinFryRecordContext::get_context_from_tag_section(&ft, &rt, &at).unwrap();

        let chunk = Chunk::<AlevinFryReadRecord> {
            nbytes: 148_u32,
            nrec: 5_u32,
            reads: vec![rec; 5],
        };

        let buf: Vec<u8> = Vec::new();
        let mut cursor = Cursor::new(buf);
        chunk
            .write(&mut cursor, &ctx)
            .expect("couldn't write chunk");
        chunk
            .write(&mut cursor, &ctx)
            .expect("couldn't write chunk");

        cursor.set_position(0);
        let new_chunk = Chunk::<AlevinFryReadRecord>::from_bytes(&mut cursor, &ctx);
        let new_chunk2 = Chunk::<AlevinFryReadRecord>::from_bytes(&mut cursor, &ctx);

        assert_eq!(chunk, new_chunk);
        assert_eq!(chunk, new_chunk2);
    }

    #[test]
    fn can_write_af_file() {
        // mock the header
        let hdr = RadHeader {
            is_paired: 0,
            ref_count: 3,
            ref_names: vec!["tgt1".to_string(), "tgt2".to_string(), "tgt3".to_string()],
            num_chunks: 2,
        };

        // describe the barcode and UMI length tags
        let bc_desc = TagDesc {
            name: "bclen".to_string(),
            typeid: RadType::Int(RadIntId::U16),
        };
        let umi_desc = TagDesc {
            name: "umilen".to_string(),
            typeid: RadType::Int(RadIntId::U16),
        };
        let mut file_tags = TagSection::new_with_label(TagSectionLabel::FileTags);
        file_tags.add_tag_desc(bc_desc);
        file_tags.add_tag_desc(umi_desc);

        // per-read barcode and umi encoding
        let rd_bc = TagDesc {
            name: "b".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let rd_umi = TagDesc {
            name: "u".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let mut read_tags = TagSection::new_with_label(TagSectionLabel::ReadTags);
        read_tags.add_tag_desc(rd_bc);
        read_tags.add_tag_desc(rd_umi);

        // per alignment information
        let aln_ent = TagDesc {
            name: "compressed_ori_refid".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let mut aln_tags = TagSection::new_with_label(TagSectionLabel::AlignmentTags);
        aln_tags.add_tag_desc(aln_ent);

        // create the whole prelude
        let prelude = RadPrelude {
            hdr,
            file_tags,
            read_tags,
            aln_tags,
        };

        // create the buffer we will write into
        let buf: Vec<u8> = Vec::new();
        let mut cursor = Cursor::new(buf);

        // write the prelude
        let _ = prelude
            .write(&mut cursor)
            .expect("cannot write prelude to buffer");

        // create and write the file tag map
        // barcode length 16, umi length 12
        let mut file_tag_map = TagMap::with_keyset(&prelude.file_tags.tags);
        file_tag_map.add(TagValue::U16(16));
        file_tag_map.add(TagValue::U16(12));
        let _ = file_tag_map
            .write_values(&mut cursor)
            .expect("cannot write file tag map");

        // the record that will comprise our chunks
        let rec = AlevinFryReadRecord {
            bc: 12345_u64,
            umi: 6789_u64,
            dirs: vec![true, true, true, false],
            refs: vec![123, 456, 78, 910],
        };

        let ctx = AlevinFryRecordContext::get_context_from_tag_section(
            &prelude.file_tags,
            &prelude.read_tags,
            &prelude.aln_tags,
        )
        .unwrap();
        let chunk = Chunk::<AlevinFryReadRecord> {
            nbytes: 148_u32,
            nrec: 5_u32,
            reads: vec![rec; 5],
        };

        // write the same chunk twice to ensure we're computing the
        // chunk number of bytes and offsets correctly
        chunk
            .write(&mut cursor, &ctx)
            .expect("couldn't write chunk");
        chunk
            .write(&mut cursor, &ctx)
            .expect("couldn't write chunk");

        // set to the start of the buffer
        cursor.set_position(0);

        // read in the prelude, the tag map and the chunks
        let new_prelude =
            RadPrelude::from_bytes(&mut cursor).expect("cannot read prelude from buffer");

        let new_file_tag_map = &prelude
            .file_tags
            .try_parse_tags_from_bytes(&mut cursor)
            .expect("cannot read file TagMap");

        println!("new_prelude = {}", new_prelude.summary(None).unwrap());
        println!("new_file_tag_map = {:?}", new_file_tag_map);

        assert_eq!(prelude, new_prelude);
        assert_eq!(&file_tag_map, new_file_tag_map);

        let new_chunk = Chunk::<AlevinFryReadRecord>::from_bytes(&mut cursor, &ctx);
        let new_chunk2 = Chunk::<AlevinFryReadRecord>::from_bytes(&mut cursor, &ctx);

        assert_eq!(chunk, new_chunk);
        assert_eq!(chunk, new_chunk2);
    }
}
