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
[ magic : 8 bytes = "RAD_FILE" ][ major : u8 ][ minor : u8 ]
[ ext_len : u32 ][ ext_len bytes ][ ...header... ]
```

followed by the existing header (`is_paired : u8`, `ref_count : u64`, ref names,
`num_chunks : u64`) and the three tag sections. Tag *descriptors* in a versioned
prelude additionally carry a role suffix (see **Tag roles** below).

A **legacy** prelude has **no** prefix — it begins directly with `is_paired` — and
its tag descriptors carry no role suffix.

### Prelude extension block

Immediately after `[major][minor]`, a versioned prelude carries a length-prefixed
extension block: `[ext_len : u32]` followed by `ext_len` opaque bytes. It is
**empty (`ext_len == 0`) today**. It exists so a future *minor* can add
file-level metadata that older readers skip wholesale (`ext_len` bytes) rather
than desyncing — the mechanism that makes "minor is additive" real for the
prelude itself. A reader reads `ext_len` and discards that many bytes.

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

## Tag roles (per-`TagDesc`)

In a versioned prelude (major ≥ 2) **every** tag descriptor — in all three tag
sections — carries a semantic role suffix after its existing `[name][type]`
encoding:

```
[ role_code : u8 ][ plen : u8 ][ plen payload bytes ]
```

`plen` is the length of the role's parameter payload, so a reader can skip a role
code it does not recognize (a newer *minor*'s addition) by `plen` bytes, and can
read a known role whose payload *grew* in a newer minor by taking the fields it
knows and advancing to `plen`. Neither desyncs the descriptor stream — this is
what makes new/extended roles a *minor* (not major) change. A payload cannot
exceed 255 bytes.

| code | role | payload (`plen`) |
|-----:|------|------------------|
| 0 | `None` (unannotated; default) | — (`plen` = 0) |
| 1 | `Barcode` | `[level : u8][len : u8]` (`plen` = 2) — collation level (0 = outermost/sample) and barcode nucleotide length (`0` = unspecified) |
| 2 | `Umi` | `[len : u8]` (`plen` = 1) — UMI nucleotide length (`0` = unspecified) |
| 3 | `Reference` | — (`plen` = 0) |
| 4 | `Orientation` | — (`plen` = 0) |
| 5 | `MappingPosition` | — (`plen` = 0) — an alignment's mapping start coordinate (e.g. scATAC `start_pos`, long-read `starts`) |
| 6 | `FragmentLength` | — (`plen` = 0) — the fragment/template length of an alignment (e.g. scATAC `frag_lengths`, long-read `tlens`) |
| 7 | `MappingType` | — (`plen` = 0) — the mapping-category flag for an alignment (e.g. scATAC `map_type`) |

An unknown code decodes to `None` (its `plen` bytes skipped). Legacy (major 0)
preludes carry **no** role bytes and always read/write `None`.

Codes 3–7 are **reserved semantic markers**: their integer widths come from the
`TagDesc`, so they carry no payload, and this build writes/reads them but does not
yet *consume* them (records are still built by position, not by these roles). They
exist so a producer can self-describe the alignment fields — notably the scATAC
`start_pos`/`frag_lengths`/`map_type` — and a future reader can build the record
layout from roles rather than by convention, without a major bump. New roles are
always added by allocating the next code (an additive *minor*); a reader that
predates one skips it by `plen`.

Because `Barcode`/`Umi` carry the barcode/UMI nucleotide lengths, a fully
role-annotated RAD needs no `cblen`/`ulen`/`bNlen` file tags; readers prefer the
role length and fall back to those file tags for un-annotated files.

## Compatibility notes

- **Reading** old files is unchanged: legacy preludes parse exactly as before.
- **Writing** is unchanged until a producer opts in: the header's version is a
  `SpecVersion` (`Legacy` | `Versioned { major, minor }`), and `RadHeader::write`
  emits the prefix + extension block + role suffixes only for `Versioned`; a
  `Legacy` header writes byte-for-byte as a pre-versioning prelude.
- A **versioned** file is not readable by a pre-magic reader (it would try to read
  the magic as `is_paired`/`ref_count`). Producers (piscem, salmon) and all RAD
  readers must therefore adopt the magic before versioned files are emitted;
  until then their files stay legacy and interoperate normally.
- The `unmapped_bc_count.bin` sidecar has its **own** independent format version
  and is unrelated to the prelude spec version.

## Related

- `constants::RAD_MAGIC`, `RAD_SPEC_MAJOR`, `RAD_SPEC_MINOR`,
  `RAD_FIRST_VERSIONED_MAJOR`
- `header::SpecVersion`, `RadHeader::{from_bytes, write, get_size}`
  (`libradicl/src/header.rs`)
- `rad_types::TagRole` + `TagRole::{write, read}` (the role wire format above),
  `TagDesc::{new, with_role}` (`libradicl/src/rad_types.rs`)
- COMBINE-lab/libradicl#64 (roles), #65 (roles design)
