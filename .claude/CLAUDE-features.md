# CLAUDE-features.md

This file tracks features implemented in libradicl.

## Writing API (implemented on `develop`, session 2026-02-19)

### `ChunkBuf` (`libradicl/src/chunk.rs`)

In-memory accumulation buffer for building a single RAD chunk in a worker thread.
- `write_record<R: MappedRecord>()` — serializes one record
- `into_bytes()` — prepends `[nbytes(u32)][nrec(u32)]` and returns a complete chunk byte sequence

### `RadFileWriter<W: Write + Seek>` (`libradicl/src/writers.rs`)

Primary single-threaded file writer.
- `new(writer, prelude, file_tag_values)` — writes prelude schema + file-level tag values; records backpatch offset for `num_chunks`
- `write_chunk()` — writes a typed `Chunk<R>`
- `write_chunk_bytes()` — appends raw bytes (e.g. from `ChunkBuf::into_bytes()`)
- `finalize()` — backpatches `num_chunks` in the header, flushes, and returns the inner writer

### `ConcurrentChunkWriter<W: Write + Seek + Send>` (`libradicl/src/writers.rs`)

`Arc<Mutex<RadFileWriter<W>>>` wrapper for multi-threaded chunk appending.
- `get_writer_ref()` — clones the `Arc` for distribution to worker threads
- `append_chunk_bytes()` — convenience method for the owning thread
- `finalize()` — requires all `Arc` clones to be dropped first, then finalizes

### Aggregate / key-value tag helpers (`libradicl/src/rad_types.rs`)

- `TagValue::rad_type() -> RadType` — infers the `RadType` for a value
- `TagSection::from_tag_values(label, &[(&str, TagValue)])` — builds schema + `TagMap` together
- `TagSection::add_map_tags(name, key_type, val_type)` — declares `{name}.keys` and `{name}.values` array tags
- `TagMap::insert_map_tags(name, keys, vals)` — writes both arrays sequentially
- `TagMap::get_map_tag_arrays(name)` — returns `(&TagValue, &TagValue)` for zero-copy read-back

### `AtacSeqReadRecord::write()` (`libradicl/src/record.rs`)

Implemented (was previously `todo!()`). Encodes: `naln (u32)`, `bc (RadIntId)`, then per-alignment: `ref_id (u32)`, `map_type (u8)`, `start_pos (u32)`, `frag_length (u16)`.

### Bug fix: `TagValue::PartialEq` infinite recursion

Pre-existing bug in the wildcard match arm `(x, y) => { x == y }` which recursively called itself. Fixed by expanding to explicit per-variant match arms.
