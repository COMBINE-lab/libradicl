# RAD prelude versioning (magic + spec version)

This documents the versioned RAD prelude introduced in libradicl for
COMBINE-lab/libradicl#64. It is the authoritative in-repo description; the shared
RAD format spec should be updated to match.

## Motivation

Historically a RAD prelude began directly with the header's `is_paired` byte —
there was **no version or magic field**, so the format could not evolve
back-compatibly (any change to the prelude/tag layout would desync existing
readers with no way to detect it). This adds a magic signature + spec version so
future changes (starting with per-tag collation roles, #64) can be gated.

## On-disk layout

A **versioned** prelude begins with:

```
[ magic : 8 bytes = "RAD_FILE" ][ major : u8 ][ minor : u8 ][ ...header... ]
```

followed by the existing header (`is_paired : u8`, `ref_count : u64`, ref names,
`num_chunks : u64`) and the three tag sections, exactly as before.

A **legacy** prelude has **no** prefix — it begins directly with `is_paired`.

### Detecting versioned vs legacy

A reader sniffs the first 8 bytes:

- If they equal the magic `RAD_FILE`, the file is versioned; the next two bytes
  are `major`, `minor`.
- Otherwise the file is legacy (reported as major 0, minor 0), and those 8 bytes
  are the start of the legacy header (spliced back before the reader).

This is unambiguous because the magic's first byte (`'R'` = 0x52) can never begin
a legacy prelude, whose first byte is `is_paired ∈ {0, 1}`.

## Version semantics

`major`/`minor` (`u8` each):

- **major** — *breaking* prelude/layout changes. A reader **must reject** a file
  whose `major` is greater than it supports (rather than misparse), and reject a
  magic-bearing file with `major` below the first versioned major (0/1 are not
  valid versioned majors).
- **minor** — *additive* changes (e.g. new optional tags/roles). Within a
  supported major, a reader **accepts a higher minor best-effort**, ignoring
  fields it does not recognize.

Reserved values:

| major | meaning |
|------:|---------|
| 0 | legacy (no magic); minor is 0 |
| 1 | reserved (treat a magic-bearing major-1 file as malformed) |
| 2 | first versioned spec — introduces per-tag collation roles (#64) |

This build writes/understands **major 2, minor 0**
(`constants::RAD_SPEC_MAJOR` / `RAD_SPEC_MINOR`).

## Compatibility notes

- **Reading** old files is unchanged: legacy preludes parse exactly as before.
- **Writing** is unchanged until a producer opts in: `RadHeader::write` emits the
  prefix only when `major_version >= RAD_FIRST_VERSIONED_MAJOR`; a default
  (`major_version == 0`) header writes byte-for-byte as a legacy prelude.
- A **versioned** file is not readable by a pre-magic reader (it would try to read
  the magic as `is_paired`/`ref_count`). Producers (piscem, salmon) and all RAD
  readers must therefore adopt the magic before versioned files are emitted;
  until then their files stay legacy and interoperate normally.
- The `unmapped_bc_count.bin` sidecar has its **own** independent format version
  and is unrelated to the prelude spec version.

## Related

- `constants::RAD_MAGIC`, `RAD_SPEC_MAJOR`, `RAD_SPEC_MINOR`,
  `RAD_FIRST_VERSIONED_MAJOR`
- `RadHeader::{from_bytes, write, get_size}` (`libradicl/src/header.rs`)
- COMBINE-lab/libradicl#64 (roles), #65 (roles design)
