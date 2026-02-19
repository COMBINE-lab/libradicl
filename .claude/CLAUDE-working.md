# Plan: RAD File Writing API for libradicl

## Context

libradicl has solid reading infrastructure but lacks a unified, ergonomic API for *writing* RAD files. `piscem-rs` currently has its own bespoke RAD writer (`src/io/rad.rs`) that we want to replace with direct use of libradicl. The four requirements are:
1. Idiomatic, structured Rust API
2. Multi-threaded chunk writing (workers write to local buffers; buffers get safely appended to the output file)
3. Backpatching: after writing all chunks, seek back to fill in `num_chunks` in the header
4. Ergonomic encoding of aggregate/key-value types (e.g., file-level metadata → HashMap)

**What already exists (do not recreate):**
- `RadHeader::write<W: Write>()` / `RadPrelude::write<W: Write>()` — write the schema (not values)
- `TagSection::new_with_label()` + `add_tag_desc()` — builder for tag schemas
- `TagMap::with_keyset()` + `try_add()` + `write_values<W>()` — key-value value writing
- `Chunk<T>::write<W: Write + Seek>()` — writes a typed chunk with internal backpatch of `nbytes`
- `MappedRecord::write()` for most record types (missing: `AtacSeqReadRecord`)

**Critical format detail:** `RadPrelude::write()` writes the schema (header + 3 TagSections) but NOT the file-level tag values. Callers must write those separately via `TagMap::write_values()`.

---

## Implementation Plan

### 1. `ChunkBuf` in `libradicl/src/chunk.rs`

An in-memory accumulation buffer for building one chunk in a worker thread. Produces a complete, self-contained chunk byte sequence (header + records) that can be appended to the output file without seeking.

```rust
pub struct ChunkBuf {
    buf: Vec<u8>,   // accumulates serialized record bytes
    nrec: u32,
}

impl ChunkBuf {
    pub fn new() -> Self
    pub fn with_capacity(cap: usize) -> Self
    pub fn write_record<R: MappedRecord>(&mut self, rec: &R, ctx: &R::ParsingContext) -> anyhow::Result<()>
    pub fn nrec(&self) -> u32
    pub fn byte_len(&self) -> usize
    pub fn clear(&mut self)   // reset for reuse without reallocation

    /// Finalizes the chunk: prepends `nbytes` (u32) + `nrec` (u32) and returns
    /// a complete chunk byte sequence ready to write. Consumes self.
    pub fn into_bytes(self) -> Vec<u8>
}
```

`into_bytes()` formula: `nbytes = 8 + body.len()` (matching Chunk::write()'s `end - start` calculation, which includes the header fields themselves).

---

### 2. New file `libradicl/src/writers.rs` — `RadFileWriter` and `ConcurrentChunkWriter`

#### `RadFileWriter<W: Write + Seek>`

The primary single-threaded writer. Constructor writes the prelude + file-level tag values and records the `num_chunks` backpatch offset. `finalize()` seeks back to write the final count.

```rust
pub struct RadFileWriter<W: Write + Seek> {
    inner: BufWriter<W>,
    num_chunks_offset: u64,
    num_chunks: u64,
}

impl<W: Write + Seek> RadFileWriter<W> {
    /// Writes prelude schema + file-level tag values; records backpatch offset.
    pub fn new(writer: W, prelude: &RadPrelude, file_tag_values: &TagMap) -> anyhow::Result<Self>

    /// Write a fully-typed chunk (uses existing Chunk::write internally).
    pub fn write_chunk<R: MappedRecord>(
        &mut self, chunk: &Chunk<R>, ctx: &R::ParsingContext,
    ) -> anyhow::Result<()>

    /// Append raw chunk bytes produced by ChunkBuf::into_bytes().
    pub fn write_chunk_bytes(&mut self, bytes: &[u8]) -> anyhow::Result<()>

    /// Backpatch num_chunks, flush, and return the inner writer.
    pub fn finalize(mut self) -> anyhow::Result<W>
}
```

**Backpatch offset calculation** (done in `new()`, using `stream_position()` before writing):
```rust
// The num_chunks field is the last 8 bytes of the RadHeader, before tag sections.
let ref_names_size: u64 = prelude.hdr.ref_names.iter()
    .map(|n| 2u64 + n.len() as u64)
    .sum();
let num_chunks_offset = start + 1 + 8 + ref_names_size;
// (1 byte is_paired, 8 bytes ref_count, variable ref_names, then num_chunks)
```

#### `ConcurrentChunkWriter<W: Write + Seek + Send>`

A thin `Arc<Mutex<>>` wrapper that lets multiple threads safely append chunk bytes to the same file writer.

```rust
pub struct ConcurrentChunkWriter<W: Write + Seek + Send> {
    inner: Arc<Mutex<RadFileWriter<W>>>,
}

impl<W: Write + Seek + Send> ConcurrentChunkWriter<W> {
    pub fn new(writer: RadFileWriter<W>) -> Self
    /// Clone the Arc for distribution to worker threads.
    pub fn get_writer_ref(&self) -> Arc<Mutex<RadFileWriter<W>>>
    /// Convenience: lock and append bytes (for use on the owning thread).
    pub fn append_chunk_bytes(&self, bytes: &[u8]) -> anyhow::Result<()>
    /// Unwrap Arc (requires all clones dropped), then finalize.
    pub fn finalize(self) -> anyhow::Result<W>
}
```

Worker threads receive `Arc<Mutex<RadFileWriter<W>>>` from `get_writer_ref()` and call `lock().unwrap().write_chunk_bytes(&bytes)` directly.

---

### 3. Aggregate / key-value type helpers in `libradicl/src/rad_types.rs`

Two related capabilities:

#### 3a. `TagSection::from_tag_values()` — convenience multi-tag constructor

Infers the schema from a slice of `(name, TagValue)` pairs, eliminating the need to declare schema and values separately. Requires a `TagValue::rad_type() -> RadType` helper method to infer the RadType from a value.

```rust
impl TagValue {
    /// Infer the RadType for this value (used for schema construction).
    pub fn rad_type(&self) -> RadType
}

impl TagSection {
    /// Build a TagSection schema + TagMap from a list of (name, value) pairs.
    pub fn from_tag_values(
        label: TagSectionLabel,
        entries: &[(&str, TagValue)],
    ) -> (TagSection, TagMap)
}
```

Usage:
```rust
let (file_tag_section, file_tag_map) = TagSection::from_tag_values(
    TagSectionLabel::FileTags,
    &[("sample_id", TagValue::String("HEK293".into())),
      ("bc_len", TagValue::U32(16))],
);
```

#### 3b. Homogeneous map encoding via parallel array tags

For efficiently encoding a `HashMap<K, V>` (or any homogeneous map) where all keys share one primitive type and all values share another. Stored as two array tags using the naming convention `"{name}.keys"` and `"{name}.values"` (the `.` separator sets these apart from ordinary user-defined tag names; `.values` mirrors Rust's standard iterator naming).

```rust
impl TagSection {
    /// Declare a homogeneous map as two parallel array tags:
    ///   "{name}.keys"   → Array of key_type
    ///   "{name}.values" → Array of val_type
    pub fn add_map_tags(&mut self, name: &str, key_type: RadIntId, val_type: RadIntId)
}

impl TagMap {
    /// Write a homogeneous map as parallel arrays under "{name}.keys" / "{name}.values".
    pub fn insert_map_tags(&mut self, name: &str, keys: &TagValue, vals: &TagValue) -> anyhow::Result<()>

    /// Return an iterator of (key: &TagValue, val: &TagValue) pairs by zipping the two arrays.
    /// Callers can collect into any map type (std HashMap, ahash HashMap, BTreeMap, etc.).
    pub fn get_key_value_iter(&self, name: &str) -> anyhow::Result<impl Iterator<Item = (&TagValue, &TagValue)>>
}
```

Usage pattern:
```rust
// Writing
section.add_map_tags("ref_lengths", RadIntId::U32, RadIntId::U32);
tag_map.insert_map_tags(
    "ref_lengths",
    &TagValue::ArrayU32(keys),
    &TagValue::ArrayU32(vals),
)?;

// Reading back — caller chooses their own map type/hasher
let hmap: HashMap<u32, u32, ahash::RandomState> = tag_map
    .get_key_value_iter("ref_lengths")?
    .map(|(k, v)| (k.as_u32()?, v.as_u32()?))   // or appropriate cast helpers
    .collect();
```

---

### Future work: `TAG_MAP` format type (Option B)

*Record for future consideration — not in scope for this implementation.*

A first-class `TAG_MAP = 9` type in the RAD format would make the map self-describing to any tool reading the file (not just libradicl). The serialization layout would still use SoA parallel arrays, but the tag descriptor would encode both the key type and value type directly.

A key motivation for a dedicated type is variable-length value types (e.g. `HashMap<String, u32>`). With Option A's parallel arrays, the `.keys` and `.values` arrays have the same *count*, but because String elements are variable-width, a reader cannot seek directly to the start of the `.values` array without scanning the entire `.keys` array first. A dedicated `TAG_MAP` descriptor could include a `value_offset: u64` field recording the byte offset from the start of the serialized map data to where the `.values` array begins, enabling O(1) random access to either array.

---

### 4. Complete `AtacSeqReadRecord::write()` in `libradicl/src/record.rs`

The `AtacSeqReadRecord::write()` method currently returns a `not yet implemented` error. Implement it following the same pattern as `PiscemBulkReadRecord::write()`, encoding: `naln (u32)`, `barcode (RadIntId)`, and per-alignment `ref (u32)`, `type (u8)`, `start_pos (u32)`, `frag_len (u16)`.

---

### 5. Update `libradicl/src/lib.rs`

- Add `pub mod writers;`
- Re-export `ChunkBuf`, `RadFileWriter`, `ConcurrentChunkWriter` at the crate root

---

### 6. Tests and Examples

**Tests** (in `writers.rs` and `chunk.rs`):
- `ChunkBuf` round-trip: write records, finalize, parse bytes back as a `Chunk` and verify contents
- `RadFileWriter` round-trip: write a complete file (prelude + file tags + chunks), read back with `ParallelRadReader` and verify
- Backpatch correctness: verify `num_chunks` in written file matches actual chunk count
- Concurrent write: spawn N threads each calling `write_chunk_bytes`, verify final file

**Example** (`libradicl/examples/write_chunk_single_cell.rs`):
- Demonstrates the complete workflow: build prelude, construct `RadFileWriter`, use `ChunkBuf` in threads, finalize

---

## File Summary

| File | Action |
|------|--------|
| `libradicl/src/chunk.rs` | Add `ChunkBuf` struct |
| `libradicl/src/writers.rs` | **New** — `RadFileWriter`, `ConcurrentChunkWriter` |
| `libradicl/src/rad_types.rs` | Add `TagSection::from_tag_values()` + `TagValue::rad_type()` |
| `libradicl/src/record.rs` | Implement `AtacSeqReadRecord::write()` |
| `libradicl/src/lib.rs` | Add `pub mod writers`, re-exports |
| `libradicl/examples/write_chunk_single_cell.rs` | **New** — end-to-end write example |

---

## Verification

```bash
cargo test --all                          # all unit tests pass
cargo clippy --all                        # no warnings
cargo run --example write_chunk_single_cell -- /tmp/test.rad
# then read it back:
cargo run --example read_chunk_single_cell -- /tmp/test.rad
```
