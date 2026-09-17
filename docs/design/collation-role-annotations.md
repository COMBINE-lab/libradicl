# Self-describing collation: barcode/UMI/orientation role annotations in the RAD

**Status:** design proposal · **Component:** libradicl (RAD format + record layer) · **Follows:** the collation-engine unification (#62), specifically `CollationKeySpec` + the tag-driven `GenericReadRecord` gather.

## Problem

The unified collation gather (`collate_generic::collate_bucket`) is record-type-agnostic: it groups by a `u128` key produced by `CollationScan`. For the built-in fast records the key location is baked in at compile time; for the tag-driven `GenericReadRecord` it comes from a runtime `CollationKeySpec` built from the read-level `TagSection`.

But a `TagSection` only declares each field's **name and type** — not its **meaning**. So today the collate layer must be *told* which read-level tags are the barcode levels (and their sample/cell hierarchy), which tag is the UMI, and which alignment field carries orientation. We currently supply that from the `do_collate` dispatch as a hardcoded per-record-type hint (the "bridge"): `["b"]` for single-barcode, `["b0","b1"]` for multi, etc.

That bridge is fine as an interim, but it has three drawbacks:
1. **Not self-describing.** A RAD produced by a new tool / future record type can't be collated unless alevin-fry's dispatch already knows its tag names — the file can't declare its own collatability.
2. **Convention-fragile.** It leans on tag-name conventions (`b`, `b0/b1`, `u`) that aren't part of the format contract.
3. **Semantics split across repos.** The meaning of a field lives in alevin-fry's dispatch, not in the RAD that libradicl owns — exactly the kind of drift that produced the divergent long-read format we hit during #62 (an undeclared read-name field).

## Proposal: per-tag semantic roles on `TagDesc`

Make the RAD **self-describing** by attaching an optional semantic **role** to each tag descriptor, written in the tag section alongside the existing name + type.

```rust
/// Optional semantic role of a tag, so a reader can locate the collation key,
/// UMI, and orientation without out-of-band knowledge of field names.
pub enum TagRole {
    None,                 // default; unannotated (back-compat)
    Barcode { level: u8 },// collation key level; outer→inner by `level` (0 = outermost/sample)
    Umi,
    Reference,            // the alignment's target reference id
    Orientation,          // orientation flag (or the field packing it, e.g. ori+ref_id)
    // room to grow: MateReference, Position, Score, ...
}

pub struct TagDesc {
    pub name: String,
    pub typeid: RadType,
    pub role: TagRole,    // NEW
}
```

- **Collation key** = the `Barcode { level }` tags, ordered by `level` (outer→inner); a single `Barcode { level: 0 }` is the single-barcode case, `{0}=sample,{1}=cell` reproduces the current multi-barcode composite. `CollationKeySpec::from_tags` builds directly from these — no caller-supplied names.
- **Scatter** reads the barcode-for-correction and the `Orientation` field via the same roles (no hardcoded bit position per record type).
- **Quant** finds the UMI via the `Umi` role.

### Wire format + versioning

`TagDesc` on disk currently is `[name_len:u16][name][type_enc:u8](+array subtypes)`. Add a trailing role suffix — a `[role_code:u8]`, plus a `[level:u8]` for `Barcode`. This is a **format change** that needs a version to gate on — but implementation surfaced that **the RAD prelude had no version or magic field at all** (it began directly at the header's `is_paired` byte). So versioning is introduced first, as a foundation:

- **Magic + `major.minor` prefix.** A versioned prelude begins with `RAD_MAGIC` (`"RAD_FILE"`, 8 bytes) followed by `[major:u8][minor:u8]`; the header + tag sections follow unchanged. A reader sniffs the magic — unambiguous because its first byte (`'R'`) can never be a legacy `is_paired` (∈{0,1}) — and on a legacy file the sniffed bytes are the start of the header, spliced back via `Read::chain` (no `Seek` needed). Legacy files report major 0; major 1 is reserved; versioned files start at **2.0**. (Details: `docs/rad-prelude-versioning.md`.)
- **Version semantics.** `major` bumps are breaking: a reader **rejects** a file whose major exceeds what it supports (rather than misparse). `minor` bumps are additive: a higher minor within a supported major is read best-effort.
- **Role gating.** The role suffix is written/read **only when the spec major is versioned (≥ 2)**; the major is known before any tag descriptor is parsed, so it cleanly gates descriptor parsing. Legacy files carry no role bytes and are byte-identical.
- **Back-compat:** a legacy tag parses as `TagRole::None`; when no relevant tag has a role the collate layer falls back to the interim bridge (caller-supplied names), so old files keep working unchanged.
- **Forward-compat:** unknown role codes parse as `None`; parameter-bearing roles are reserved to a **major** bump, so a param-less unknown code never desyncs the descriptor stream.

### Validation the format then enables

With roles declared, libradicl can enforce (at read time, cheaply) the invariants #62 surfaced the hard way:
- **Field completeness:** the sum of declared fixed field widths × counts matches the record span — catches undeclared fields (the exact bug behind the unreadable long-read RADs) at first read, not 8 GB into a pipeline.
- **Collatability:** `CollationKeySpec::from_tags` succeeds iff ≥1 `Barcode` role exists and the composite fits `u128` — the collate entry point fails fast and clearly for a keyless layout, while plain reading is unaffected.

## Why per-tag role (vs. a file-level `collation_roles` tag)

An alternative is a single file-level tag mapping roles→tag-names (needs `RadType::String`/`Array`, which is only partly implemented). Per-tag roles are preferable because: the annotation lives with the field it describes (no name-matching indirection), it naturally covers alignment-level fields (orientation/reference) too, and it doesn't depend on completing the string/array tag machinery. The file-level approach could layer on later for record-level (non-per-tag) metadata.

## Rollout

1. ✅ **Magic + `major.minor` version foundation** (`RAD_MAGIC`, `RadHeader.{major,minor}_version`, sniff + `Read::chain` back-compat, too-new-major guard, `get_size`). Spec: `docs/rad-prelude-versioning.md`.
2. ✅ **`TagRole` + `TagDesc.role`** (default `None`), version threaded through `TagSection`/`TagDesc` read+write, gated on major ≥ 2. Legacy files byte-identical.
3. ✅ **`CollationKeySpec::from_roles`** (+ `GenericCollateCtx::from_roles`) alongside the interim `from_read_tags(names)` bridge; the collate dispatch prefers roles, falls back to the bridge. `Umi`/`Orientation` roles are consumed — the generic path filters alignments by the declared orientation field (dropping the earlier `--expected-ori both` limitation).
4. ⏳ Producers (piscem/salmon, alevin-fry writers) stamp roles on the records they emit; auto-route unknown record types to the generic path when roles are present (currently an env-gated preview).
5. ⏳ Field-completeness self-check; once producers stamp roles, promote it from warning to error behind the version gate.

**Status:** items 1–3 are implemented and validated on `feat/unified-collate-step1` (COMBINE-lab/libradicl#64): a legacy RAD stamped to spec 2.0 with `Barcode` + `Orientation` roles collates through the role-driven generic path to output canonically identical to the fast engine, both unfiltered and strand-filtered. Known record types keep taking their specialized fast path; roles there are optional validation only. Composite/hierarchical generic keys are #66.

## Non-goals

- Changing record *encodings* or chunk framing (only the tag descriptor gains a byte).
- Removing the interim bridge (it remains the fallback for un-annotated/old files).
- Inferring roles from names (the point is to stop relying on names).

## Relationship to #62

#62 delivered the runtime `CollationKeySpec` + tag-driven gather and the interim bridge. This proposal is the permanent source of the spec's inputs: the RAD declaring its own roles, so collatability (and the scatter/quant field locations) come from the file rather than from alevin-fry's dispatch.
