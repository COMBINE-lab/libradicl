/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Types for writing complete RAD files ergonomically and efficiently.
//!
//! # Overview
//!
//! A RAD file is written in three phases:
//!
//! 1. **Header + file-level tags** — construct a [`RadPrelude`] (schema) and a
//!    [`TagMap`] of file-level values, then create a [`RadFileWriter`].
//! 2. **Chunks** — call [`RadFileWriter::write_chunk`] for typed chunks, or
//!    [`RadFileWriter::write_chunk_bytes`] for raw bytes produced by [`ChunkBuf`]
//!    in a worker thread.
//! 3. **Finalize** — call [`RadFileWriter::finalize`] to backpatch the `num_chunks`
//!    field in the header and flush the output.
//!
//! # Multi-threaded writing
//!
//! Worker threads should each own a [`ChunkBuf`], call
//! [`ChunkBuf::write_record`] for every record, then hand the bytes produced by
//! [`ChunkBuf::into_bytes`] to a [`ConcurrentChunkWriter`]:
//!
//! ```no_run
//! use std::sync::{Arc, Mutex};
//! use libradicl::{ChunkBuf, writers::{ConcurrentChunkWriter, RadFileWriter}};
//! // ... build prelude and file_tag_map, then:
//! // let fw = RadFileWriter::new(file, &prelude, &file_tag_map).unwrap();
//! // let ccw = ConcurrentChunkWriter::new(fw);
//! // let writer_ref: Arc<Mutex<RadFileWriter<_>>> = ccw.get_writer_ref();
//! // // in each thread:
//! // let bytes = chunk_buf.into_bytes();
//! // writer_ref.lock().unwrap().write_chunk_bytes(&bytes).unwrap();
//! // // after all threads finish:
//! // ccw.finalize().unwrap();
//! ```

use crate::chunk::Chunk;
use crate::header::RadPrelude;
use crate::rad_types::{TagMap, TagValue};
use crate::record::MappedRecord;
use anyhow::Context;
use std::collections::HashMap;
use std::io::{BufWriter, Seek, SeekFrom, Write};
use std::sync::{Arc, Mutex};

/// A writer for a complete RAD file.
///
/// Constructed via [`RadFileWriter::new`], which immediately writes the prelude
/// schema and file-level tag values and records the byte offset of the
/// `num_chunks` field for later backpatching.
///
/// Use [`RadFileWriter::write_chunk`] or [`RadFileWriter::write_chunk_bytes`] to
/// append chunks, then [`RadFileWriter::finalize`] to backpatch and flush.
pub struct RadFileWriter<W: Write + Seek> {
    inner: BufWriter<W>,
    num_chunks_offset: u64,
    num_chunks: u64,
    /// `file_tag_name -> (byte_offset, byte_len)` for each file-tag value, so a
    /// fixed-size reserved value (written as a placeholder in [`Self::new`]) can be
    /// overwritten later via [`Self::backpatch_file_tag_value`].
    file_tag_slots: HashMap<String, (u64, u64)>,
}

impl<W: Write + Seek> RadFileWriter<W> {
    /// Create a new [`RadFileWriter`].
    ///
    /// Writes the prelude schema (header + three tag-section descriptions) and
    /// the file-level tag values to `writer`, then records the byte offset of
    /// the `num_chunks` field so it can be backpatched in [`Self::finalize`].
    pub fn new(writer: W, prelude: &RadPrelude, file_tag_values: &TagMap) -> anyhow::Result<Self> {
        let mut inner = BufWriter::new(writer);

        // Compute the byte offset of the num_chunks field *before* writing.
        // Header layout:
        //   1 byte  — is_paired
        //   8 bytes — ref_count
        //   for each ref_name: 2 bytes (length) + name bytes
        //   8 bytes — num_chunks   <-- backpatch target
        let start = inner
            .stream_position()
            .context("couldn't get stream position before writing prelude")?;
        let ref_names_size: u64 = prelude
            .hdr
            .ref_names
            .iter()
            .map(|n| 2u64 + n.len() as u64)
            .sum();
        let num_chunks_offset = start + 1 + 8 + ref_names_size;

        prelude
            .write(&mut inner)
            .context("couldn't write prelude to RAD file")?;

        // Write each file-tag value individually, recording the byte offset and
        // length of each so a fixed-size reserved value can be backpatched after
        // the chunks are written (e.g. a fragment-length distribution computed
        // during the streaming pass). Equivalent to `file_tag_values.write_values`,
        // but tracking offsets. `stream_position` flushes the buffered prelude
        // once; offsets thereafter are tracked arithmetically (no per-tag flush).
        let mut file_tag_slots: HashMap<String, (u64, u64)> = HashMap::new();
        let mut off = inner
            .stream_position()
            .context("couldn't get stream position before file-tag values")?;
        for (desc, val) in file_tag_values.entries() {
            let mut scratch = Vec::new();
            val.write_with_type(&desc.typeid, &mut scratch)
                .context("couldn't serialize file-level tag value")?;
            inner
                .write_all(&scratch)
                .context("couldn't write file-level tag value to RAD file")?;
            let len = scratch.len() as u64;
            file_tag_slots.insert(desc.name.clone(), (off, len));
            off += len;
        }

        Ok(Self {
            inner,
            num_chunks_offset,
            num_chunks: 0,
            file_tag_slots,
        })
    }

    /// Overwrite a previously-written file-tag value in place. The new `value`
    /// must serialize to exactly the same number of bytes as the placeholder
    /// written by [`Self::new`] (true for fixed-length arrays / fixed-width
    /// scalars). Intended for values that are only known after the chunks have
    /// streamed — e.g. a fragment-length distribution or abundance estimates
    /// computed during the pass. Seeks are absolute, so this composes with the
    /// `num_chunks` backpatch in [`Self::finalize`]; call it before `finalize`.
    pub fn backpatch_file_tag_value(&mut self, name: &str, value: &TagValue) -> anyhow::Result<()> {
        let &(offset, len) = self
            .file_tag_slots
            .get(name)
            .with_context(|| format!("no reserved file-tag slot named '{name}'"))?;
        let mut scratch = Vec::new();
        value
            .write_with_type(&value.rad_type(), &mut scratch)
            .context("couldn't serialize backpatch file-tag value")?;
        anyhow::ensure!(
            scratch.len() as u64 == len,
            "backpatch size mismatch for file tag '{name}': {} bytes vs reserved {len}",
            scratch.len()
        );
        self.inner
            .seek(SeekFrom::Start(offset))
            .with_context(|| format!("couldn't seek to file-tag '{name}' for backpatch"))?;
        self.inner
            .write_all(&scratch)
            .with_context(|| format!("couldn't backpatch file tag '{name}'"))?;
        Ok(())
    }

    /// Write a fully-typed [`Chunk`] to the file.
    ///
    /// Internally delegates to [`Chunk::write`], which uses seeking to backpatch
    /// the per-chunk `nbytes` field.
    pub fn write_chunk<R: MappedRecord>(
        &mut self,
        chunk: &Chunk<R>,
        ctx: &R::ParsingContext,
    ) -> anyhow::Result<()> {
        chunk
            .write(&mut self.inner, ctx)
            .context("couldn't write chunk to RAD file")?;
        self.num_chunks += 1;
        Ok(())
    }

    /// Append raw chunk bytes produced by [`ChunkBuf::into_bytes`].
    ///
    /// The bytes must already contain the complete chunk header (`nbytes` + `nrec`)
    /// followed by all record bytes. This is the low-overhead path for multi-threaded
    /// writing where worker threads build chunks in local [`ChunkBuf`]s.
    pub fn write_chunk_bytes(&mut self, bytes: &[u8]) -> anyhow::Result<()> {
        self.inner
            .write_all(bytes)
            .context("couldn't write chunk bytes to RAD file")?;
        self.num_chunks += 1;
        Ok(())
    }

    /// Backpatch the `num_chunks` field in the header, flush the writer, and
    /// return the inner `W`.
    ///
    /// This must be called after all chunks have been written.  Any outstanding
    /// [`Arc`] clones of the inner writer (e.g. held by a [`ConcurrentChunkWriter`])
    /// must be dropped before calling this.
    pub fn finalize(mut self) -> anyhow::Result<W> {
        // BufWriter::seek flushes the internal buffer before seeking, ensuring
        // all chunk data is on the underlying writer before we backpatch.
        self.inner
            .seek(SeekFrom::Start(self.num_chunks_offset))
            .context("couldn't seek to num_chunks field for backpatch")?;
        self.inner
            .write_all(&self.num_chunks.to_le_bytes())
            .context("couldn't backpatch num_chunks")?;
        self.inner
            .flush()
            .context("couldn't flush writer during finalize")?;
        self.inner
            .into_inner()
            .map_err(|e| anyhow::anyhow!("couldn't unwrap BufWriter: {}", e.error()))
    }
}

/// A thread-safe wrapper around a [`RadFileWriter`] for parallel chunk writing.
///
/// Multiple threads each build a [`ChunkBuf`], then call
/// [`ConcurrentChunkWriter::append_chunk_bytes`] (or lock `get_writer_ref()` directly)
/// to atomically append their chunk to the output file.
///
/// Call [`ConcurrentChunkWriter::finalize`] once all worker threads have finished
/// and all [`Arc`] clones returned by [`Self::get_writer_ref`] have been dropped.
pub struct ConcurrentChunkWriter<W: Write + Seek + Send> {
    inner: Arc<Mutex<RadFileWriter<W>>>,
}

impl<W: Write + Seek + Send> ConcurrentChunkWriter<W> {
    /// Wrap a [`RadFileWriter`] for concurrent use.
    pub fn new(writer: RadFileWriter<W>) -> Self {
        Self {
            inner: Arc::new(Mutex::new(writer)),
        }
    }

    /// Clone the inner [`Arc`] so worker threads can call
    /// `lock().unwrap().write_chunk_bytes(&bytes)` directly.
    ///
    /// All clones **must** be dropped before [`Self::finalize`] is called.
    pub fn get_writer_ref(&self) -> Arc<Mutex<RadFileWriter<W>>> {
        Arc::clone(&self.inner)
    }

    /// Convenience method: lock, append raw chunk bytes, and release.
    pub fn append_chunk_bytes(&self, bytes: &[u8]) -> anyhow::Result<()> {
        self.inner
            .lock()
            .expect("ConcurrentChunkWriter mutex was poisoned")
            .write_chunk_bytes(bytes)
    }

    /// Unwrap the [`Arc`] (requires all clones to have been dropped), then
    /// call [`RadFileWriter::finalize`] to backpatch and flush.
    pub fn finalize(self) -> anyhow::Result<W> {
        self.into_writer()?.finalize()
    }

    /// Unwrap back into the inner [`RadFileWriter`] (requires all clones returned
    /// by [`Self::get_writer_ref`] to have been dropped). Use this to apply
    /// [`RadFileWriter::backpatch_file_tag_value`] before calling
    /// [`RadFileWriter::finalize`].
    pub fn into_writer(self) -> anyhow::Result<RadFileWriter<W>> {
        let inner = Arc::try_unwrap(self.inner).map_err(|_| {
            anyhow::anyhow!(
                "ConcurrentChunkWriter::into_writer called while Arc clones are still alive"
            )
        })?;
        Ok(inner
            .into_inner()
            .expect("ConcurrentChunkWriter mutex was poisoned"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chunk::{Chunk, ChunkBuf};
    use crate::header::{RadHeader, RadPrelude};
    use crate::rad_types::{
        RadAtomicId, RadFloatId, RadIntId, RadType, TagDesc, TagMap, TagSection, TagSectionLabel,
        TagValue,
    };
    use crate::record::{AlevinFryReadRecord, AlevinFryRecordContext, RecordContext};
    use std::io::Cursor;

    /// Build a minimal AlevinFry prelude and matching file-tag values for tests.
    fn make_af_prelude() -> (RadPrelude, TagMap) {
        let hdr = RadHeader {
            is_paired: 0,
            ref_count: 3,
            ref_names: vec!["tgt1".to_string(), "tgt2".to_string(), "tgt3".to_string()],
            num_chunks: 0, // will be backpatched
        };

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

        let mut read_tags = TagSection::new_with_label(TagSectionLabel::ReadTags);
        read_tags.add_tag_desc(TagDesc {
            name: "b".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        read_tags.add_tag_desc(TagDesc {
            name: "u".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });

        let mut aln_tags = TagSection::new_with_label(TagSectionLabel::AlignmentTags);
        aln_tags.add_tag_desc(TagDesc {
            name: "compressed_ori_refid".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });

        let prelude = RadPrelude {
            hdr,
            file_tags,
            read_tags,
            aln_tags,
        };

        let mut file_tag_map = TagMap::with_keyset(&prelude.file_tags.tags);
        file_tag_map.add(TagValue::U16(16)); // bclen
        file_tag_map.add(TagValue::U16(12)); // umilen

        (prelude, file_tag_map)
    }

    fn make_af_record() -> AlevinFryReadRecord {
        AlevinFryReadRecord {
            bc: 12345_u64,
            umi: 6789_u64,
            dirs: vec![true, false, true],
            refs: vec![0, 1, 2],
        }
    }

    #[test]
    fn rad_file_writer_roundtrip() {
        let (prelude, file_tag_map) = make_af_prelude();
        let rec = make_af_record();
        let ctx = AlevinFryRecordContext::get_context_from_tag_section(
            &prelude.file_tags,
            &prelude.read_tags,
            &prelude.aln_tags,
        )
        .unwrap();

        let chunk = Chunk::<AlevinFryReadRecord> {
            nbytes: 0,
            nrec: 3,
            reads: vec![rec.clone(), rec.clone(), rec.clone()],
        };

        // --- write ---
        let buf: Vec<u8> = Vec::new();
        let cursor = Cursor::new(buf);
        let mut fw = RadFileWriter::new(cursor, &prelude, &file_tag_map).unwrap();
        fw.write_chunk(&chunk, &ctx).unwrap();
        fw.write_chunk(&chunk, &ctx).unwrap();
        let cursor = fw.finalize().unwrap();

        // --- read back ---
        let mut cursor = Cursor::new(cursor.into_inner());
        let read_prelude = RadPrelude::from_bytes(&mut cursor).expect("read prelude");
        let read_file_tags = read_prelude
            .file_tags
            .parse_tags_from_bytes(&mut cursor)
            .expect("read file tag map");

        assert_eq!(read_prelude.hdr.num_chunks, 2);
        assert_eq!(read_file_tags.get("bclen"), Some(&TagValue::U16(16)));
        assert_eq!(read_file_tags.get("umilen"), Some(&TagValue::U16(12)));

        let read_chunk1 = Chunk::<AlevinFryReadRecord>::from_bytes(&mut cursor, &ctx);
        let read_chunk2 = Chunk::<AlevinFryReadRecord>::from_bytes(&mut cursor, &ctx);
        assert_eq!(read_chunk1.nrec, 3);
        assert_eq!(read_chunk2.nrec, 3);
        assert_eq!(read_chunk1.reads[0], rec);
    }

    #[test]
    fn backpatch_file_tag_value_roundtrip() {
        // Prelude with a reserved fixed-length ArrayF64 file tag (placeholder),
        // plus a scalar tag before it to exercise non-zero offsets.
        let hdr = RadHeader {
            is_paired: 0,
            ref_count: 2,
            ref_names: vec!["t0".to_string(), "t1".to_string()],
            num_chunks: 0,
        };
        let mut file_tags = TagSection::new_with_label(TagSectionLabel::FileTags);
        file_tags.add_tag_desc(TagDesc {
            name: "bclen".to_string(),
            typeid: RadType::Int(RadIntId::U16),
        });
        file_tags.add_tag_desc(TagDesc {
            name: "frag_length_dist".to_string(),
            typeid: RadType::Array(RadIntId::U32, RadAtomicId::Float(RadFloatId::F64)),
        });
        let mut read_tags = TagSection::new_with_label(TagSectionLabel::ReadTags);
        read_tags.add_tag_desc(TagDesc {
            name: "b".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        read_tags.add_tag_desc(TagDesc {
            name: "u".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        let mut aln_tags = TagSection::new_with_label(TagSectionLabel::AlignmentTags);
        aln_tags.add_tag_desc(TagDesc {
            name: "compressed_ori_refid".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        });
        let prelude = RadPrelude {
            hdr,
            file_tags,
            read_tags,
            aln_tags,
        };
        let mut file_tag_map = TagMap::with_keyset(&prelude.file_tags.tags);
        file_tag_map.add(TagValue::U16(16)); // bclen
        file_tag_map.add(TagValue::ArrayF64(vec![0.0; 4])); // reserved FLD placeholder

        let rec = AlevinFryReadRecord {
            bc: 1,
            umi: 2,
            dirs: vec![true, false],
            refs: vec![0, 1],
        };
        let ctx = AlevinFryRecordContext::get_context_from_tag_section(
            &prelude.file_tags,
            &prelude.read_tags,
            &prelude.aln_tags,
        )
        .unwrap();
        let chunk = Chunk::<AlevinFryReadRecord> {
            nbytes: 0,
            nrec: 1,
            reads: vec![rec.clone()],
        };

        let cursor = Cursor::new(Vec::<u8>::new());
        let mut fw = RadFileWriter::new(cursor, &prelude, &file_tag_map).unwrap();
        fw.write_chunk(&chunk, &ctx).unwrap();
        // backpatch the reserved slot with real values (same length ⇒ same size)
        fw.backpatch_file_tag_value(
            "frag_length_dist",
            &TagValue::ArrayF64(vec![0.1, 0.2, 0.3, 0.4]),
        )
        .unwrap();
        // a differently-sized value must be rejected, not silently corrupt the file
        assert!(
            fw.backpatch_file_tag_value("frag_length_dist", &TagValue::ArrayF64(vec![1.0]))
                .is_err()
        );
        // an unknown tag name must error
        assert!(
            fw.backpatch_file_tag_value("nope", &TagValue::U16(0))
                .is_err()
        );
        let cursor = fw.finalize().unwrap();

        let mut cursor = Cursor::new(cursor.into_inner());
        let read_prelude = RadPrelude::from_bytes(&mut cursor).unwrap();
        let read_file_tags = read_prelude
            .file_tags
            .parse_tags_from_bytes(&mut cursor)
            .unwrap();
        assert_eq!(read_prelude.hdr.num_chunks, 1);
        assert_eq!(read_file_tags.get("bclen"), Some(&TagValue::U16(16)));
        assert_eq!(
            read_file_tags.get("frag_length_dist"),
            Some(&TagValue::ArrayF64(vec![0.1, 0.2, 0.3, 0.4]))
        );
        // the chunk still parses correctly after the backpatch
        let read_chunk = Chunk::<AlevinFryReadRecord>::from_bytes(&mut cursor, &ctx);
        assert_eq!(read_chunk.nrec, 1);
        assert_eq!(read_chunk.reads[0], rec);
    }

    #[test]
    fn chunk_buf_roundtrip() {
        let (prelude, _) = make_af_prelude();
        let rec = make_af_record();
        let ctx = AlevinFryRecordContext::get_context_from_tag_section(
            &prelude.file_tags,
            &prelude.read_tags,
            &prelude.aln_tags,
        )
        .unwrap();

        let mut cbuf = ChunkBuf::with_capacity(256);
        cbuf.write_record(&rec, &ctx).unwrap();
        cbuf.write_record(&rec, &ctx).unwrap();
        assert_eq!(cbuf.nrec(), 2);

        let bytes = cbuf.into_bytes();

        // Parse back as a Chunk
        let mut cursor = Cursor::new(bytes);
        let chunk = Chunk::<AlevinFryReadRecord>::from_bytes(&mut cursor, &ctx);
        assert_eq!(chunk.nrec, 2);
        assert_eq!(chunk.reads[0], rec);
        assert_eq!(chunk.reads[1], rec);
    }

    #[test]
    fn write_chunk_bytes_backpatch() {
        let (prelude, file_tag_map) = make_af_prelude();
        let rec = make_af_record();
        let ctx = AlevinFryRecordContext::get_context_from_tag_section(
            &prelude.file_tags,
            &prelude.read_tags,
            &prelude.aln_tags,
        )
        .unwrap();

        // Build three chunks via ChunkBuf
        let mut chunks_bytes: Vec<Vec<u8>> = Vec::new();
        for _ in 0..3 {
            let mut cbuf = ChunkBuf::new();
            cbuf.write_record(&rec, &ctx).unwrap();
            chunks_bytes.push(cbuf.into_bytes());
        }

        // Write using write_chunk_bytes
        let buf: Vec<u8> = Vec::new();
        let mut fw = RadFileWriter::new(Cursor::new(buf), &prelude, &file_tag_map).unwrap();
        for bytes in &chunks_bytes {
            fw.write_chunk_bytes(bytes).unwrap();
        }
        let cursor = fw.finalize().unwrap();

        // Verify num_chunks was backpatched to 3
        let mut cursor = Cursor::new(cursor.into_inner());
        let read_prelude = RadPrelude::from_bytes(&mut cursor).unwrap();
        assert_eq!(read_prelude.hdr.num_chunks, 3);
    }

    #[test]
    fn concurrent_chunk_writer_roundtrip() {
        use std::thread;

        let (prelude, file_tag_map) = make_af_prelude();
        let rec = make_af_record();
        let ctx = AlevinFryRecordContext::get_context_from_tag_section(
            &prelude.file_tags,
            &prelude.read_tags,
            &prelude.aln_tags,
        )
        .unwrap();

        let fw =
            RadFileWriter::new(Cursor::new(Vec::<u8>::new()), &prelude, &file_tag_map).unwrap();
        let ccw = ConcurrentChunkWriter::new(fw);

        // Spawn 4 threads, each writing 1 chunk of 2 records
        let mut handles = Vec::new();
        for _ in 0..4 {
            let writer_ref = ccw.get_writer_ref();
            let rec_clone = rec.clone();
            let ctx_clone = ctx.clone();
            handles.push(thread::spawn(move || {
                let mut cbuf = ChunkBuf::with_capacity(256);
                cbuf.write_record(&rec_clone, &ctx_clone).unwrap();
                cbuf.write_record(&rec_clone, &ctx_clone).unwrap();
                let bytes = cbuf.into_bytes();
                writer_ref
                    .lock()
                    .unwrap()
                    .write_chunk_bytes(&bytes)
                    .unwrap();
            }));
        }
        for h in handles {
            h.join().unwrap();
        }

        let cursor = ccw.finalize().unwrap();
        let mut cursor = Cursor::new(cursor.into_inner());
        let read_prelude = RadPrelude::from_bytes(&mut cursor).unwrap();
        assert_eq!(read_prelude.hdr.num_chunks, 4);
    }
}
