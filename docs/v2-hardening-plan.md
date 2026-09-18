# libradicl/alevin-fry v2 hardening plan

Turns the fable review of `feat/unified-collate-step1` (libradicl `e524622..HEAD`) +
`feat/generic-gather-position` (alevin-fry `ad05742..HEAD`) into an actionable plan.
Every review finding below has **either a concrete change or an explicit decision**.

Legend: [FIX] code change · [DEC] decision (no code, or "do X not Y") · [NEW] my
addition beyond the review. Fable refs in (parens).

---

## Cross-cutting decisions

- **DEC-A — No forbidden/reserved arbitrary tag names.** Producers may name a tag
  anything (incl. `cblen`). Length metadata source of truth in v2 = the *roles*
  (`Barcode{len}`/`Umi{len}`). File tags `cblen`/`ulen`/`bNlen` are consulted only
  as a **fallback** when no role length is present. Both present → prefer the role,
  **warn** on mismatch, never error, never forbid. (Overrides Fable C2's "deprecate
  cblen/ulen".)
- **DEC-B — Overflow guard now, u128 later (C5).** Reject `>2` barcode levels and
  `cell_bits >= 64` in the role/context constructors with clear errors; move the
  multi group key to u128 only when real data needs it.
- **DEC-C — Role wire encoding = uniform inline `[code:u8][plen:u8][payload]`;
  `None = [0x00][0x00]`.** One unconditional read loop, unknown codes skipped by
  `plen`, known codes parsed then advanced by `plen` (additive-minor safe). ~2
  bytes/tag overhead in v2 is negligible. (Chosen over a sparse trailing block.)
- **DEC-D — Atomic format landing.** All P0 wire-format items ship as one change
  set; never commit a half-migrated wire format. The role format we already
  committed (Barcode{level,len}/Umi{len} without plen) is *replaced*, not layered.

---

## P0 — on-disk format, before ANY non-test producer emits v2

- **P0-1 [FIX] (C1)** Role encoding → `[code][plen][payload]` (DEC-C). Writer emits
  `plen` for every role incl. `None`([0][0]). Reader: read code+plen; known code →
  parse its fields then seek to `start+plen`; unknown → skip `plen`. Document the
  exact byte layout in `docs/rad-prelude-versioning.md` (make it normative).
- **P0-2 [FIX] (C1)** Prelude extension block after `[major][minor]`:
  `[ext_len:u32][ext_len bytes]`, written `0` today, reader skips it. This is what
  makes a *minor* bump able to add file-level metadata without desync.
- **P0-3 [FIX] (D1)** `CollationKeySpec::extract` (`collate_generic.rs:155`): guard
  the 128-bit shift (`if p.bits >= 128 { v } else { (key<<p.bits)|(v&mask) }`).
  Add a single-`U128`-key test. (Confirmed debug panic.)
- **P0-4 [DEC/FIX] (D2,D10)** u128 on the tag-driven scatter: **reject** `U128` key
  parts in `GenericCollateCtx::new` with `Err` now (aligns with DEC-B); implement a
  u128 scatter only when needed. Add `debug_assert!(bytes<=8)` / explicit guard in
  `le_u64` and where multi/ATAC keys are read.
- **P0-5 [FIX] (C3)** Validate single-barcode physical layout. Make
  `bct_umit_from_roles` (`record.rs:751`) require barcode@idx0, umi@idx1, exactly
  two read tags — mirroring the multi validation — else `Err`. See NEW-2 for the
  unified form. Add misordered / extra-tag / swapped tests.
- **P0-6 [FIX] (D3)** Implement `GenericReadRecord::peek_collatable_header`
  (`record.rs:1614`) (Cursor over `&[u8]` + `from_bytes_collatable_header`), or
  return `Err`. Never a reachable `unimplemented!()`.
- **P0-7 [DEC] (D7)** Barcode-role-without-Umi-role policy: **single-barcode →
  fall back to the name bridge with a warning** (don't hard-fail a partially
  stamped file); **multi → strict error** (already the case). Encode this in the
  constructors.

## P1 — before merge   ✅ DONE (except P1-7's SpecVersion/#[non_exhaustive], moved to P2)

Status: P1-1..P1-6, P1-8..P1-11 landed. P1-7 split: `TagDesc::new`/`with_role`
added now; the `SpecVersion` enum (C4) and `#[non_exhaustive]` on `TagDesc` (C6
breaking half) are folded into P2 release prep, where all struct literals get
converted once alongside the rename (landing them now churns ~20 sites twice).


- **P1-1 [FIX] (D5)** `get_record_type_from_prelude -> anyhow::Result` (drop the 8
  panics); move the role-based multi check *after* the long-read/pos/ATAC checks;
  use role length in the non-multi arms so a role-only single-barcode RAD reaches
  the auto-route instead of `expect("cblen")`.
- **P1-2 [FIX] (C2 + DEC-A)** One libradicl `barcode_lengths(prelude, file_tag_map)`
  (+ umi length) helper: role-preferred, file-tag fallback, **prefer-role + warn on
  mismatch**, never forbid. Replace the four hand-rolled chains (`utils.rs`,
  `cellfilter.rs`, `quant.rs`, `convert.rs`). Represent `len` in memory as
  `Option<NonZeroU8>`; encode `0`=unspecified only on the wire.
- **P1-3 [FIX] (D6,D16)** Propagate errors: reader filler context
  (`readers.rs:303,491`) and gather worker threads (`collate.rs`, `atac/collate.rs`)
  return `Result` and are joined with `?` — no `unwrap`/`expect` in spawned threads.
- **P1-4 [FIX] (D4)** `u32::try_from(...).context(...)` for chunk `nbytes`
  (`collate_generic.rs:665`) and `allocated_records` (`collate.rs:1073,1088`).
- **P1-5 [FIX] (C9,D8)** `validate_first_chunk_layout`: stream instead of allocating
  the whole chunk; **skip when `CHUNK_CODEC_TAG` is present** (false-positive on
  compressed payloads); wire it into `atac/collate.rs`. Test the overrun and
  `nrec==0` branches.
- **P1-6 [FIX] (C5, DEC-B)** Reject `>2` barcode levels and `cell_bits>=64` in
  `MultiBarcodeRecordContext::from_roles` (and the generic key spec) with clear
  errors.
- **P1-7 [FIX] (C4,C6)** `RadHeader` version → `enum SpecVersion { Legacy,
  Versioned{major,minor} }` with a validating constructor; `TagSection::write/from_bytes`
  take it (or become `pub(crate)` with `RadPrelude::write` the only public path);
  `TagDesc::new(name,typeid)` + `with_role(...)` + `#[non_exhaustive]`;
  `TagSection::add_tag(name,typeid)` defaults role None.
- **P1-8 [FIX] (C7,D9)** Collapse the fixed-layout opt-in to one
  `fixed_layout() -> Option<FixedLayout{hdr_bytes,stride,key_fn}>` (removes the
  `unreachable!()` default). Fix the stale `collate_bucket` memory comments; if we
  want the "one bucket" claim true under codec, compress `tmp`→`out` per chunk.
- **P1-9 [FIX] (D11)** Replace `AF_FORCE_GENERIC_COLLATE` env var with a hidden CLI
  flag `--collate-engine {auto,fast,generic}` (or a `dev-tools` feature).
- **P1-10 [FIX] (D15)** `atac/deduplicate`: detect a stray legacy `map.collated.rad.sz`
  and emit a "collated format changed; re-run collate" error.
- **P1-11 [FIX] (D17)** Tests: unknown-role-code stays in sync; v2 input + codec via
  `write_collated_output_header`; truncated bucket → `Err` not panic; header sniff on
  a <8-byte stream; direct assertion of the ATAC backpatched `num_chunks`.

## P2 — release / cleanup

Status: **Phase A (code) + Phase B (docs) DONE.** P1-7 remainder (SpecVersion
enum + `#[non_exhaustive]` TagDesc), P2-5 (dead `umi_tag_idx` removed, doc strings
fixed, `Reference` kept), P2-6 (fast-path contexts through `prefer_roles`; atac
positional read documented), P2-4 (`collate_generic`→`bucket_gather`,
`Generic*`→`TagDriven*`), P2-3 (dev examples gated behind `dev-tools`), and P2-7
(rad-prelude-versioning.md normative for roles + ext block; #65 design doc
updated) are landed. **Remaining: Phase C release mechanics (P2-1, P2-2) — the
crates.io publish boundary, to be run with the maintainer.**


- **P2-1 [FIX] (D18)** libradicl → `0.20.0` + CHANGELOG (removed fns, changed
  TagSection/TagDesc signatures, new role field + v2 prelude/role wire format).
  Publish to crates.io.
- **P2-2 [FIX] (D18)** alevin-fry: remove `[patch.crates-io]`, set
  `libradicl = "0.20.0"`, regenerate `Cargo.lock` (restore registry source/checksum),
  bump AF (ATAC collated `.sz`→per-chunk format change) + changelog.
- **P2-3 [DEC] (D18)** Examples: keep `probe_rad`, `check_layout`, one `dump_collated*`
  in `examples/`; move stamp/gen/rename/subset/convert_sclong to a `dev-tools`
  feature or `src/bin/`. Commit `dump_collated_generic.rs`/`gen_atac_rad.rs`
  deliberately (into that set) rather than leaving untracked.
- **P2-4 [FIX] (C8)** Rename `collate_generic`→`bucket_gather`; tag-driven
  `Generic*`→`TagDriven*`. **Do this dead-last** (large diff, rebase churn).
- **P2-5 [DEC/FIX] (D13)** Remove dead `umi_tag_idx`; **keep `TagRole::Reference`**
  as a reserved-but-unconsumed code (free under plen-prefix); fix the copy-pasted
  "file-level tags" doc strings (`header.rs:331-336`).
- **P2-6 [DEC] (D14)** Route the remaining name-bridge consumers (long/pos/short
  fast drivers, atac `tags[0]`) through `prefer_roles` where feasible; document the
  ones that stay name-bridge-by-design.
- **P2-7 [FIX] (D18)** Update the #65 design doc to the shipped wire format; make
  `docs/rad-prelude-versioning.md` the normative reference for the prelude prefix,
  the extension block, and the role bytes.

## NEW — additions beyond the review

- **NEW-1 [NEW]** Proptest/fuzz the role + tag-section round-trip (random tags,
  random/unknown role codes, grown payloads) → assert round-trip + forward-skip
  stays in sync. Commit a **frozen v2 conformance RAD fixture** and a test that
  reads it, so future wire drift is caught. (Pairs with P0-1.)
- **NEW-2 [NEW]** `expected_read_layout() -> &'static [TagRole]` (or equivalent) on
  each fixed record context; check it in *both* the context builder (P0-5) and
  `validate_first_chunk_layout` (P1-5) — one layout-truth, not two partial checks.
- **NEW-3 [NEW]** Legacy (major-0) regression test: read a real pbmc + Flex legacy
  RAD through the new reader and assert unchanged classification/collation
  (codifies the manual no-regression check).
- **NEW-4 [NEW]** (folded into P1-2) reconciliation prefers role + warns on
  mismatch; never errors/forbids — matches DEC-A.
- **NEW-5 [NEW]** (folded into DEC-D) P0 format items land atomically; C8 rename last.
</content>
