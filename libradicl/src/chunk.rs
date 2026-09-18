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
use libradicl::rad_types::{RadType, TagSection};
use libradicl::record::MappedRecord;
use scroll::Pread;
use std::io::{Cursor, Read};
use std::io::{Seek, SeekFrom, Write};

/// Best-effort field-completeness self-check on the next chunk: verify its
/// `nrec` records exactly fill the chunk payload under the layout *declared by the
/// tag sections* (each record = `na:u32` + read-level tags + `na ×` alignment-level
/// tags). `reader` must be positioned at a chunk header (`[nbytes:u32][nrec:u32]`).
///
/// This catches on-disk records that are larger (or smaller) than their tags
/// describe — e.g. an undeclared per-record field — at first read, with a clear
/// error, rather than as a truncated-buffer panic deep in a pipeline (the failure
/// mode that made a divergent long-read RAD unreadable, COMBINE-lab/libradicl#64).
///
/// It is arithmetic and cheap, but only applies when every read/alignment tag is a
/// fixed-width integer; if any tag is variable-width (e.g. a `String`/`Array`) the
/// per-record size can't be computed this way and the check is skipped (`Ok`).
/// An empty reader (no chunk) is also `Ok`.
pub fn validate_first_chunk_layout<T: Read>(
    reader: &mut T,
    read_tags: &TagSection,
    aln_tags: &TagSection,
) -> anyhow::Result<()> {
    // Fixed read-header (na + read tags) and per-alignment stride from the tags;
    // bail out to `Ok` (skip) if any field is variable-width.
    let mut read_bytes = 0usize;
    for td in &read_tags.tags {
        match td.typeid {
            RadType::Int(i) => read_bytes += i.bytes_for_type(),
            _ => return Ok(()),
        }
    }
    let mut aln_stride = 0usize;
    for td in &aln_tags.tags {
        match td.typeid {
            RadType::Int(i) => aln_stride += i.bytes_for_type(),
            _ => return Ok(()),
        }
    }
    let rec_hdr = std::mem::size_of::<u32>() + read_bytes; // na + read tags

    let mut hb = [0u8; 8];
    if reader.read_exact(&mut hb).is_err() {
        return Ok(()); // no chunk to check
    }
    let nbytes = u32::from_le_bytes(hb[0..4].try_into().unwrap()) as usize;
    let nrec = u32::from_le_bytes(hb[4..8].try_into().unwrap()) as usize;
    anyhow::ensure!(nbytes >= 8, "chunk header claims nbytes={nbytes} (< 8)");
    let payload = nbytes - 8;

    // Stream the walk: read each record's small fixed header, then skip its
    // alignment block in bounded chunks — never allocate the whole (up to 4 GiB)
    // payload.
    let mut hdr_buf = vec![0u8; rec_hdr];
    let mut sink = [0u8; 8192];
    let mut consumed = 0usize;
    for i in 0..nrec {
        anyhow::ensure!(
            consumed + rec_hdr <= payload,
            "record {i} header overruns the chunk payload; on-disk records do not match \
             the declared tag layout (undeclared field?)"
        );
        reader
            .read_exact(&mut hdr_buf)
            .context("first chunk is truncated relative to its declared nbytes")?;
        let na = u32::from_le_bytes(hdr_buf[0..4].try_into().unwrap()) as usize;
        let aln_bytes = na * aln_stride;
        anyhow::ensure!(
            consumed + rec_hdr + aln_bytes <= payload,
            "record {i} ({} B) overruns the chunk payload; on-disk records are larger \
             than the declared tags describe (undeclared field?)",
            rec_hdr + aln_bytes
        );
        let mut remaining = aln_bytes;
        while remaining > 0 {
            let n = remaining.min(sink.len());
            reader
                .read_exact(&mut sink[..n])
                .context("first chunk is truncated relative to its declared nbytes")?;
            remaining -= n;
        }
        consumed += rec_hdr + aln_bytes;
    }
    anyhow::ensure!(
        consumed == payload,
        "the first chunk has {} byte(s) beyond its {nrec} declared records; on-disk records \
         do not match the declared tag layout (undeclared field?)",
        payload - consumed
    );
    Ok(())
}

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

/*
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
*/

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

/// An in-memory buffer for accumulating the records of a single RAD chunk,
/// typically in a worker thread. Call [ChunkBuf::write_record] for each record,
/// then [ChunkBuf::into_bytes] to obtain a self-contained byte sequence
/// (chunk header + records) that can be appended to a RAD file via
/// [crate::writers::RadFileWriter::write_chunk_bytes] without any seeking.
pub struct ChunkBuf {
    buf: Vec<u8>,
    nrec: u32,
}

impl Default for ChunkBuf {
    fn default() -> Self {
        Self::new()
    }
}

impl ChunkBuf {
    /// Create a new empty [ChunkBuf].
    pub fn new() -> Self {
        Self {
            buf: Vec::new(),
            nrec: 0,
        }
    }

    /// Create a new [ChunkBuf] with the given initial byte capacity.
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            buf: Vec::with_capacity(cap),
            nrec: 0,
        }
    }

    /// Serialize `rec` into the buffer using `ctx`. Increments the internal record count.
    pub fn write_record<R: MappedRecord>(
        &mut self,
        rec: &R,
        ctx: &R::ParsingContext,
    ) -> anyhow::Result<()> {
        rec.write(&mut self.buf, ctx)?;
        self.nrec += 1;
        Ok(())
    }

    /// Return the number of records accumulated so far.
    pub fn nrec(&self) -> u32 {
        self.nrec
    }

    /// Return the number of record bytes accumulated so far (excluding the chunk header).
    pub fn byte_len(&self) -> usize {
        self.buf.len()
    }

    /// Reset the buffer for reuse without reallocating.
    pub fn clear(&mut self) {
        self.buf.clear();
        self.nrec = 0;
    }

    /// Finalise the chunk: prepend the 4-byte `nbytes` and 4-byte `nrec` header and
    /// return the complete chunk byte sequence.  `nbytes` includes the header itself,
    /// matching the value produced by [Chunk::write].
    pub fn into_bytes(self) -> Vec<u8> {
        let nrec = self.nrec;
        let body = self.buf;
        // nbytes covers the 4-byte nbytes field, the 4-byte nrec field, and all records.
        let nbytes: u32 = (body.len() as u32) + 8;
        let mut result = Vec::with_capacity(body.len() + 8);
        result.extend_from_slice(&nbytes.to_le_bytes());
        result.extend_from_slice(&nrec.to_le_bytes());
        result.extend_from_slice(&body);
        result
    }

    /// Like [`Self::into_bytes`], but the payload is compressed with `codec`.
    /// The returned chunk keeps the `[u32 nbytes][u32 nrec]` header, with
    /// `nbytes` set to the *compressed* framing size (header + compressed
    /// payload). A reader restores it via [`crate::codec::decompress_payload`].
    /// [`crate::codec::ChunkCodec::None`] is identical to [`Self::into_bytes`].
    pub fn into_bytes_with_codec(self, codec: crate::codec::ChunkCodec) -> anyhow::Result<Vec<u8>> {
        use crate::codec::ChunkCodec;
        if codec == ChunkCodec::None {
            return Ok(self.into_bytes());
        }
        let nrec = self.nrec;
        let comp = crate::codec::compress_payload(codec, &self.buf)?;
        let nbytes: u32 = (comp.len() as u32) + 8;
        let mut result = Vec::with_capacity(comp.len() + 8);
        result.extend_from_slice(&nbytes.to_le_bytes());
        result.extend_from_slice(&nrec.to_le_bytes());
        result.extend_from_slice(&comp);
        Ok(result)
    }
}

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
            role: crate::rad_types::TagRole::None,
            name: "b".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        rt.add_tag_desc(TagDesc {
            role: crate::rad_types::TagRole::None,
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

    // Build read/alignment tag sections describing an AlevinFry-like layout:
    // read tags b:u32,u:u32 (8 B) and one alignment tag refid:u32 (stride 4).
    fn af_like_tag_sections() -> (TagSection, TagSection) {
        let mut rt = TagSection::new_with_label(TagSectionLabel::ReadTags);
        rt.add_tag_desc(TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "b".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        rt.add_tag_desc(TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "u".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        let mut at = TagSection::new_with_label(TagSectionLabel::AlignmentTags);
        at.add_tag_desc(TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "refid".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        (rt, at)
    }

    // One chunk with `na` counts per record: each record is 4 (na) + 8 (read) + na*4.
    fn make_chunk(nas: &[u32]) -> Vec<u8> {
        let mut payload: Vec<u8> = Vec::new();
        for &na in nas {
            payload.extend_from_slice(&na.to_le_bytes());
            payload.extend_from_slice(&0u32.to_le_bytes()); // b
            payload.extend_from_slice(&0u32.to_le_bytes()); // u
            for _ in 0..na {
                payload.extend_from_slice(&0u32.to_le_bytes()); // refid
            }
        }
        let nbytes = (payload.len() + 8) as u32;
        let mut buf = Vec::new();
        buf.extend_from_slice(&nbytes.to_le_bytes());
        buf.extend_from_slice(&(nas.len() as u32).to_le_bytes());
        buf.extend_from_slice(&payload);
        buf
    }

    #[test]
    fn field_completeness_accepts_well_formed_chunk() {
        let (rt, at) = af_like_tag_sections();
        let buf = make_chunk(&[2, 1, 3]);
        let mut cur = Cursor::new(buf);
        crate::chunk::validate_first_chunk_layout(&mut cur, &rt, &at)
            .expect("well-formed chunk should validate");
    }

    #[test]
    fn field_completeness_accepts_empty_chunk() {
        // nrec == 0 (payload == 0) is well-formed.
        let (rt, at) = af_like_tag_sections();
        let buf = make_chunk(&[]);
        let mut cur = Cursor::new(buf);
        crate::chunk::validate_first_chunk_layout(&mut cur, &rt, &at)
            .expect("empty chunk should validate");
    }

    #[test]
    fn field_completeness_rejects_record_overrunning_payload() {
        // A record whose declared `na` implies more alignment bytes than the chunk
        // payload holds must be rejected (not read past the end).
        let (rt, at) = af_like_tag_sections();
        // Hand-build a chunk: nbytes covers exactly one na=0 record (4 + 8), but the
        // record claims na = 100.
        let rec_hdr = 4 + 8; // na + b + u
        let nbytes = (8 + rec_hdr) as u32;
        let mut buf = Vec::new();
        buf.extend_from_slice(&nbytes.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes()); // nrec = 1
        buf.extend_from_slice(&100u32.to_le_bytes()); // na = 100 (overruns)
        buf.extend_from_slice(&0u32.to_le_bytes()); // b
        buf.extend_from_slice(&0u32.to_le_bytes()); // u
        let mut cur = Cursor::new(buf);
        let err = crate::chunk::validate_first_chunk_layout(&mut cur, &rt, &at)
            .expect_err("a record overrunning the payload should be rejected");
        assert!(format!("{err}").contains("overruns"));
    }

    #[test]
    fn field_completeness_rejects_undeclared_trailing_field() {
        let (rt, at) = af_like_tag_sections();
        // A well-formed chunk, but bump the declared nbytes so the payload has
        // extra bytes the declared records don't account for (undeclared field).
        let mut buf = make_chunk(&[2, 1]);
        let nbytes = u32::from_le_bytes(buf[0..4].try_into().unwrap()) + 4;
        buf[0..4].copy_from_slice(&nbytes.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes()); // 4 stray trailing bytes
        let mut cur = Cursor::new(buf);
        let err = crate::chunk::validate_first_chunk_layout(&mut cur, &rt, &at)
            .expect_err("trailing undeclared bytes should be rejected");
        assert!(format!("{err}").contains("undeclared field"));
    }

    #[test]
    fn field_completeness_skips_variable_width_layout() {
        // A String read tag makes per-record size non-arithmetic -> skip (Ok).
        let mut rt = TagSection::new_with_label(TagSectionLabel::ReadTags);
        rt.add_tag_desc(TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "name".to_string(),
            typeid: RadType::String,
        });
        let (_r, at) = af_like_tag_sections();
        // Even a bogus buffer must be accepted, because the check is skipped.
        let mut cur = Cursor::new(vec![0u8; 3]);
        crate::chunk::validate_first_chunk_layout(&mut cur, &rt, &at)
            .expect("variable-width layout should skip the check");
    }

    #[test]
    fn can_write_af_file() {
        // mock the header
        let hdr = RadHeader {
            version: crate::header::SpecVersion::Legacy,
            is_paired: 0,
            ref_count: 3,
            ref_names: vec!["tgt1".to_string(), "tgt2".to_string(), "tgt3".to_string()],
            num_chunks: 2,
        };

        // describe the barcode and UMI length tags
        let bc_desc = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "bclen".to_string(),
            typeid: RadType::Int(RadIntId::U16),
        };
        let umi_desc = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "umilen".to_string(),
            typeid: RadType::Int(RadIntId::U16),
        };
        let mut file_tags = TagSection::new_with_label(TagSectionLabel::FileTags);
        file_tags.add_tag_desc(bc_desc);
        file_tags.add_tag_desc(umi_desc);

        // per-read barcode and umi encoding
        let rd_bc = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "b".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let rd_umi = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "u".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let mut read_tags = TagSection::new_with_label(TagSectionLabel::ReadTags);
        read_tags.add_tag_desc(rd_bc);
        read_tags.add_tag_desc(rd_umi);

        // per alignment information
        let aln_ent = TagDesc {
            role: crate::rad_types::TagRole::None,
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
        prelude
            .write(&mut cursor)
            .expect("cannot write prelude to buffer");

        // create and write the file tag map
        // barcode length 16, umi length 12
        let mut file_tag_map = TagMap::with_keyset(&prelude.file_tags.tags);
        file_tag_map.add(TagValue::U16(16));
        file_tag_map.add(TagValue::U16(12));
        file_tag_map
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
