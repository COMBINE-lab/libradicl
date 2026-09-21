# Changelog

All notable changes to this project are documented here. The format follows
[conventional commits](https://www.conventionalcommits.org); entries are
generated from commit messages by [git-cliff](https://git-cliff.org).

## [0.21.0](https://github.com/COMBINE-lab/libradicl/compare/v0.20.0...v0.21.0) (2026-09-21)


### Features

* Role-aware bulk & scATAC record readers ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([aa7c33a](https://github.com/COMBINE-lab/libradicl/commit/aa7c33a105e8f5d773442215f2dbc2f25db7a423))

### Refactor

* Drop the noodles dependency; RadHeader::from_ref_names ([8918d73](https://github.com/COMBINE-lab/libradicl/commit/8918d730147b6b168132374459b7bfbe3c5f0974))

## [0.20.0](https://github.com/COMBINE-lab/libradicl/compare/v0.19.1...v0.20.0) (2026-09-18)


### Bug Fixes

* Include magic+version prefix in RadHeader::get_size for versioned headers ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([b4eb70a](https://github.com/COMBINE-lab/libradicl/commit/b4eb70a06a8ac67d8e5bc219d56ba4a99481f3a8))
* P0 correctness/robustness for the role-driven collation paths (#64/#66) ([36414fb](https://github.com/COMBINE-lab/libradicl/commit/36414fb49c9307f40b21689f7892b7da70a353f3))

### Documentation

* Make the cell-index u32 invariant explicit + note the opt-in axis ([#62](https://github.com/COMBINE-lab/libradicl/issues/62)) ([290d0d3](https://github.com/COMBINE-lab/libradicl/commit/290d0d324e94808b71296f9a0eee1cd432d58900))
* V2 hardening plan (review dispositions + P0/P1/P2) ([6940ee8](https://github.com/COMBINE-lab/libradicl/commit/6940ee8ffa1358f99b0ebf90c2c763fa3253bb0d))
* Mark P1 done in the v2 hardening plan (SpecVersion/non_exhaustive -> P2) ([cfc22fe](https://github.com/COMBINE-lab/libradicl/commit/cfc22fe8bf2e527eabf98f86757f87f90a210bc2))
* Make rad-prelude-versioning normative for roles + extension block (P2/P2-7) ([e6eebe6](https://github.com/COMBINE-lab/libradicl/commit/e6eebe6db7347e7db1b354406c9ecaefacd8d7a8))
* Mark P2 Phase A+B done in the hardening plan (Phase C = publish, remains) ([2c41b2a](https://github.com/COMBINE-lab/libradicl/commit/2c41b2a0de966bf802fad7f79b277bb90a790301))
* Add Astro/Starlight RAD format specification site ([b0c4013](https://github.com/COMBINE-lab/libradicl/commit/b0c40135d5adeb874bd4eb0a6638e2bb046e37e5))
* Fix broken/private intra-doc links (rustdoc -D warnings) ([dee7a0c](https://github.com/COMBINE-lab/libradicl/commit/dee7a0c6eba109c572f65b2c6db9018c40a0592e))

### Features

* Parse-based generic collation core + ScatterProbe (step 1 of #62) ([68b8e6f](https://github.com/COMBINE-lab/libradicl/commit/68b8e6f9bcbb0355e91ff5bb743a2de7754f52dd))
* Wire built-in records into the generic core via ScatterProbe ([#62](https://github.com/COMBINE-lab/libradicl/issues/62)) ([427dc7f](https://github.com/COMBINE-lab/libradicl/commit/427dc7fb8eb2b202179098d7154feb2d7f39379e))
* Record chunk offsets in the streaming generic two-pass ([#62](https://github.com/COMBINE-lab/libradicl/issues/62)) ([cfd171b](https://github.com/COMBINE-lab/libradicl/commit/cfd171bb6991855f143ec914f682d74aa4e24542))
* Wire single-barcode gather onto the unified collate_bucket ([#62](https://github.com/COMBINE-lab/libradicl/issues/62)) ([b80d2ae](https://github.com/COMBINE-lab/libradicl/commit/b80d2ae8f1f05dd94a280b46f21dfe04956402e8))
* Wire multi-barcode (Flex) gather onto the unified collate_bucket; re-scan pass 2 ([#62](https://github.com/COMBINE-lab/libradicl/issues/62)) ([5465d15](https://github.com/COMBINE-lab/libradicl/commit/5465d156c3cc6203dda51c82c21f52bd9b9517ed))
* CollationKeySpec + tag-driven generic-record gather ([#62](https://github.com/COMBINE-lab/libradicl/issues/62)) ([dc65715](https://github.com/COMBINE-lab/libradicl/commit/dc6571502d8d0cee061ee4117a02ebf2a519d06e))
* Make GenericReadRecord collatable (scatter/gather) for single-barcode ([#62](https://github.com/COMBINE-lab/libradicl/issues/62)) ([3ab3b46](https://github.com/COMBINE-lab/libradicl/commit/3ab3b4679ebc4d7bf7a94a61e232174f74db733c))
* RAD magic + spec-version prefix with legacy back-compat ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([e02cf1b](https://github.com/COMBINE-lab/libradicl/commit/e02cf1b86cd3767e5c1f482f1bed8bbebf92190d))
* RAD spec version as major.minor + too-new guard + versioning spec ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([944e977](https://github.com/COMBINE-lab/libradicl/commit/944e977c4d404af69ab9d496b13e4582bfb1daa2))
* Per-TagDesc semantic roles, gated on spec version ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([fe4051f](https://github.com/COMBINE-lab/libradicl/commit/fe4051fef0d4721e6b410b8a20f0dbfbb502ac3c))
* Derive the collation key from declared roles; dispatch prefers roles ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([fb988d3](https://github.com/COMBINE-lab/libradicl/commit/fb988d3f713bb5ae2e0d44446d3f77d247b0ad94))
* Consume Umi/Orientation roles — generic path filters by strand ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([80c0a8a](https://github.com/COMBINE-lab/libradicl/commit/80c0a8a6edd6aeba0d2d415477ee51a293008601))
* Add first-chunk field-completeness self-check ([14e3ee5](https://github.com/COMBINE-lab/libradicl/commit/14e3ee534cb1deaf4b9d133afd7f172d96a24042))
* Role-driven MultiBarcodeRecordContext for composite collation ([#66](https://github.com/COMBINE-lab/libradicl/issues/66)) ([aaaa0e9](https://github.com/COMBINE-lab/libradicl/commit/aaaa0e9d7751a52fed913f805057e7e3e59f1112))
* Unify scATAC collation onto collate_bucket; retire twopass_atac ([2a03e14](https://github.com/COMBINE-lab/libradicl/commit/2a03e144296eec224347f7ce3bb246ccc2a0bdd7))
* Role-aware record contexts for the read path ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([ac4371a](https://github.com/COMBINE-lab/libradicl/commit/ac4371a458867fc7a48e550b19b8f43f1e023b2d))
* Barcode role carries nucleotide length; fix v2 writer num_chunks (#64/#66) ([e801b53](https://github.com/COMBINE-lab/libradicl/commit/e801b53c1766da813ad5a83e4a6e82b6baaaf677))
* UMI role carries nucleotide length (Umi{len}), matching Barcode ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([b65c0c7](https://github.com/COMBINE-lab/libradicl/commit/b65c0c7e5298434719dee09a4d4eb71508df0c21))
* Forward-compatible v2 role encoding + prelude extension block (P0, #64) ([8076188](https://github.com/COMBINE-lab/libradicl/commit/8076188930e84793ff5744d6828982fecc1b0d6e))
* TagDesc::new / with_role constructors (P1 partial, C6) ([491c25d](https://github.com/COMBINE-lab/libradicl/commit/491c25d619d743e57ea062f70691a1a5a1c2c360))
* Reserve MappingPosition/FragmentLength/MappingType roles (5,6,7) ([e1c9b86](https://github.com/COMBINE-lab/libradicl/commit/e1c9b86f0c34d72273191e1b2b0b5c413586b680))

### Performance

* Bounded-memory collate_bucket (build-in-out, len-only pass-1) ([86ea742](https://github.com/COMBINE-lab/libradicl/commit/86ea74297f489a2e2d06018501437ef73f5c1479))
* Pass-2 reads each record straight into its slot (match two-pass) ([ae90c6d](https://github.com/COMBINE-lab/libradicl/commit/ae90c6de2230e3f05f454d42bb501e14532983b0))
* Fixed-layout fast pass-2 for the gather (fix Flex wall regression) ([#62](https://github.com/COMBINE-lab/libradicl/issues/62)) ([e29caba](https://github.com/COMBINE-lab/libradicl/commit/e29caba34acc4358ef67b3b045e1c5f402d7e93a))

### Refactor

* Collate_bucket emits chunks only; caller records the index ([1c5b6a2](https://github.com/COMBINE-lab/libradicl/commit/1c5b6a267a7d1f48e2f6b9e604443dd24140421c))
* Streaming bounded-memory generic gather + rename to CollationScan ([a4e58d1](https://github.com/COMBINE-lab/libradicl/commit/a4e58d12e671fc9dfa0cf70de82d6e09eea3f210))
* Retire collate_temporary_bucket_twopass_generic ([#62](https://github.com/COMBINE-lab/libradicl/issues/62)) ([30f3522](https://github.com/COMBINE-lab/libradicl/commit/30f352264a4c41fdef99fa346224c3f33cf9d0e0))
* P1 collation-engine robustness (#62/#64/#66) ([a447695](https://github.com/COMBINE-lab/libradicl/commit/a4476957fb9b74cb91d0bd3853c248e3c5387ea8))
* SpecVersion enum + non_exhaustive TagDesc (P2/C4/C6) ([f29fa49](https://github.com/COMBINE-lab/libradicl/commit/f29fa494c10c4387fbf156a61e5f4ef84f997dd0))
* Drop dead umi_tag_idx; fix copy-pasted prelude-write context (P2/D13) ([e84a546](https://github.com/COMBINE-lab/libradicl/commit/e84a5466deaef7bd7d460a83f11b50662d8a7bdc))
* Rename module collate_generic -> bucket_gather (P2/C8) ([c0cb573](https://github.com/COMBINE-lab/libradicl/commit/c0cb57313595f576c08318d266bc6b535d5cb472))
* Rename tag-driven Generic* -> TagDriven* (P2/C8) ([fc486f7](https://github.com/COMBINE-lab/libradicl/commit/fc486f7d6fbaef0623d89a707fc300936c0286db))
* Finish Generic->TagDriven rename in read_chunk example ([a660da1](https://github.com/COMBINE-lab/libradicl/commit/a660da1d2643b695d68f0a05901132f6353fc66b))

### Testing

* From-scratch v2 prelude with roles round-trips (writer capability) ([#64](https://github.com/COMBINE-lab/libradicl/issues/64)) ([406613b](https://github.com/COMBINE-lab/libradicl/commit/406613baa1e74af27521c644f11f5dce2cf47c4c))

### Style

* Apply cargo fmt (rustfmt) across the crate ([457e507](https://github.com/COMBINE-lab/libradicl/commit/457e50737ba025c82210a6ad9c7fece4dd563672))

## [0.19.1](https://github.com/COMBINE-lab/libradicl/compare/v0.19.0...v0.19.1) (2026-09-13)


### Features

* Record chunk offsets during gather (chunk index without a re-scan) ([2c512b8](https://github.com/COMBINE-lab/libradicl/commit/2c512b8f5ca38f752225a7fe658510188edaf916))

## [0.19.0](https://github.com/COMBINE-lab/libradicl/compare/v0.18.1...v0.19.0) (2026-09-13)


### Features

* Per-chunk chunk codecs for collated RAD (lz4 default, zstd opt-in) ([7c55979](https://github.com/COMBINE-lab/libradicl/commit/7c55979d5c2c77fdbe31e052800763b54780acb8))

## [0.18.1](https://github.com/COMBINE-lab/libradicl/compare/v0.18.0...v0.18.1) (2026-08-31)


### Performance

* Fast fixed u64 hasher for the collation maps ([ddf02c6](https://github.com/COMBINE-lab/libradicl/commit/ddf02c68c38240cf442f7d15db4aebf96dda7780))

## [0.18.0](https://github.com/COMBINE-lab/libradicl/compare/v0.17.0...v0.18.0) (2026-08-15)


### Bug Fixes

* Clamp collation resource minima ([34e37f5](https://github.com/COMBINE-lab/libradicl/commit/34e37f57195b41fff1e78af2b78926b4646e2d8c))
* Clamp single-collator resources ([194d127](https://github.com/COMBINE-lab/libradicl/commit/194d127105f22acbc1d9731c68022d610cc5ca86))

### Features

* Apply caller-compiled barcode corrections ([1065aa3](https://github.com/COMBINE-lab/libradicl/commit/1065aa3bba70ab3b14c1121b09ce83415a0e16bb))

### Performance

* Add bounded multi-barcode collator ([08ae416](https://github.com/COMBINE-lab/libradicl/commit/08ae41640a4da089ec33ad31a4bf927434e2557b))
* Add bounded single-barcode collator ([acd5cec](https://github.com/COMBINE-lab/libradicl/commit/acd5cec61cbd10fa5d42f23fda991b1ac432c0af))

### Style

* Satisfy current rustfmt ([8c17f4a](https://github.com/COMBINE-lab/libradicl/commit/8c17f4a7a9724c085e657b14dca83e407286a6bd))

## [0.17.0](https://github.com/COMBINE-lab/libradicl/compare/v0.16.0...v0.17.0) (2026-08-08)


### Bug Fixes

* Release consumers when the producer stops early ([2302191](https://github.com/COMBINE-lab/libradicl/commit/23021916749d055fd17acad87032b6bc6e3f7be1))
* Bound oversized tag values instead of wrapping their length ([3cf3e32](https://github.com/COMBINE-lab/libradicl/commit/3cf3e3243e1b1a11b684913a0808cbfc8e3e1de9))
* Report the length actually written, not the bound ([9ce8426](https://github.com/COMBINE-lab/libradicl/commit/9ce8426808de13ae0998e5c00ad5f9a8d5b1bce3))

### Build & CI

* Replace release-please with git-cliff ([3f20ed9](https://github.com/COMBINE-lab/libradicl/commit/3f20ed945da3f731801e3dd4e89efb0247f86af6))
* Create the GitHub Release from a pushed tag ([144d5b8](https://github.com/COMBINE-lab/libradicl/commit/144d5b8d5dae4b43994a71fc48681ef41f072bf6))
* Fall back to the default-branch changelog for old tags ([8ec81e4](https://github.com/COMBINE-lab/libradicl/commit/8ec81e4d63872200d4cde52908d47be29cd3addf))

### Documentation

* Tighten the DoneOnDrop and next_chunk_header comments ([3974e35](https://github.com/COMBINE-lab/libradicl/commit/3974e352338a19ad624bb9f0103c644f6c3499f9))
* Note cargo publish --workspace as a possible simplification ([7d526b2](https://github.com/COMBINE-lab/libradicl/commit/7d526b21c99be651b802151188eda7d952a60344))

### Features

* Add checked tag writers that report a shortened value ([6aef88c](https://github.com/COMBINE-lab/libradicl/commit/6aef88c3e9084cc5c46e9a497db6b6a86a3a4f51))

### Refactor

* Keep the plain writers free of reporting machinery ([c70bb38](https://github.com/COMBINE-lab/libradicl/commit/c70bb3844de968d7f986d3c71f05c046b40065b3))
* Have the checked writers defer for the bytes ([0a1645d](https://github.com/COMBINE-lab/libradicl/commit/0a1645dffd4a1b9f7de150263eea848ebb36ec5d))
* Make fits answer for the writer, and rename to _reporting ([b99ee88](https://github.com/COMBINE-lab/libradicl/commit/b99ee88d90647487e7cf633fba861eb6aa83f443))

## [0.16.0](https://github.com/COMBINE-lab/libradicl/compare/v0.15.0...v0.16.0) (2026-08-04)


### Bug Fixes

* Restore MetaChunkIterator; add fallible constructors ([151df8d](https://github.com/COMBINE-lab/libradicl/commit/151df8ddd57c7d9c28ef655ce34833d985f0be63))
* Bound the speculative ref_names reservation ([47e7c27](https://github.com/COMBINE-lab/libradicl/commit/47e7c27aeb3cb844eb44cb2c378cb71c3857ff18))

### Documentation

* Rewrite the libradicl README ([c57b15d](https://github.com/COMBINE-lab/libradicl/commit/c57b15d5c930ff7fc6e31077aea0f5e154ad2b1e))
* Add a module-level overview of the parallel reader API ([02e1913](https://github.com/COMBINE-lab/libradicl/commit/02e1913d0a2c66d9f7128001d0b2d9b8291638f4))
* Fix ten broken intra-doc links ([2bbe2cc](https://github.com/COMBINE-lab/libradicl/commit/2bbe2cc6cd5b0e03cfe28e9e23587056bbf48b93))

### Features

* Add drain-safe consumer APIs for the parallel readers ([9eefcfa](https://github.com/COMBINE-lab/libradicl/commit/9eefcfa0ee03f0f5d3ecddec5764237dd571c2d1))

### Performance

* Bound the consumer spin before yielding ([8150c62](https://github.com/COMBINE-lab/libradicl/commit/8150c6273721260fa89e258bb7d227b0f4686a89))
* Use a proper backoff policy, escalating to sleep when idle ([43aa382](https://github.com/COMBINE-lab/libradicl/commit/43aa3824a96648a1c1b3887fed83a6350396fa5d))

## [0.15.0](https://github.com/COMBINE-lab/libradicl/compare/v0.14.3...v0.15.0) (2026-07-29)


### Build & CI

* Add build/lint/test/audit workflow ([5b51c0a](https://github.com/COMBINE-lab/libradicl/commit/5b51c0abc94649acd7d2f2721ff22c769b31de41))

## [0.14.3](https://github.com/COMBINE-lab/libradicl/compare/v0.14.2...v0.14.3) (2026-07-09)


### Bug Fixes

* Accept "b" as well as "barcode" for the scATAC read-level tag ([60b42ed](https://github.com/COMBINE-lab/libradicl/commit/60b42ed1c82baeb02af46b078df4884ff9d4e855))

## [0.14.2](https://github.com/COMBINE-lab/libradicl/compare/v0.14.0...v0.14.2) (2026-07-02)


### Bug Fixes

* Bump lz4_flex 0.10 -> 0.13 (GHSA-vvp9-7p8x-rfvv); release 0.14.1 ([e7d348d](https://github.com/COMBINE-lab/libradicl/commit/e7d348d97f6c2440ed681b79b3458c2a4c72a678))

## [0.14.0](https://github.com/COMBINE-lab/libradicl/compare/v0.13.0...v0.14.0) (2026-06-27)


### Bug Fixes

* Decode U128 (type id 9) tag descriptors ([3d901ea](https://github.com/COMBINE-lab/libradicl/commit/3d901ea7f1987fa1cb9cd7e4f6adf18f8c7f7e0c))

### Features

* Backpatchable reserved file tags ([4b7803c](https://github.com/COMBINE-lab/libradicl/commit/4b7803c80db7c6ea131500a7ebeb9c0ad9635e4b))
* Optional per-chunk LZ4/zstd compression ([96fae41](https://github.com/COMBINE-lab/libradicl/commit/96fae4110773eeda316ce56659cbf42babfb9f13))

## [0.10.0](https://github.com/COMBINE-lab/libradicl/compare/v0.9.0...v0.10.0) (2024-12-06)


### Miscellaneous

* Release 0.10.0 ([c14759b](https://github.com/COMBINE-lab/libradicl/commit/c14759b45bedc0c8e69606d9fd3a6f6670e3183a))

## [0.9.0](https://github.com/COMBINE-lab/libradicl/compare/v0.8.2...v0.9.0) (2024-07-12)


### Bug Fixes

* Removed some unused code, adding filter version of rad and chunk reader ([7bfc668](https://github.com/COMBINE-lab/libradicl/commit/7bfc668ff8ea1408e77f472782beb2aca7f12cf8))
* Make some fields public ([6f15db7](https://github.com/COMBINE-lab/libradicl/commit/6f15db72760fe41646caa0233cabd4165e506006))

### Features

* Deprecated some types, made parallel readers more generic ([5dd74da](https://github.com/COMBINE-lab/libradicl/commit/5dd74da16309409ed75287f611d54f2398b85ae5))
* Add atac-seq-support ([8704b54](https://github.com/COMBINE-lab/libradicl/commit/8704b54215d0adef6183631dbf61170254101767))

### Miscellaneous

* Release 0.9.0 ([9a4f94a](https://github.com/COMBINE-lab/libradicl/commit/9a4f94ac052b15f62fbfd6f197c97191542ff1ee))

## [0.8.2](https://github.com/COMBINE-lab/libradicl/compare/v0.8.1...v0.8.2) (2024-03-08)


### Bug Fixes

* Add functions for compatibility with alevin-fry changes ([a9df1fa](https://github.com/COMBINE-lab/libradicl/commit/a9df1fa6815cb84d8a350bc72b4212bae47e3d5e))

### Miscellaneous

* Release 0.8.2 ([4f0f514](https://github.com/COMBINE-lab/libradicl/commit/4f0f514859ecbb9a296b091bf6a4a75515482fdc))

## [0.8.1](https://github.com/COMBINE-lab/libradicl/compare/v0.8.0...v0.8.1) (2024-03-03)


### Bug Fixes

* Umi type tag is u not b ([67f3e28](https://github.com/COMBINE-lab/libradicl/commit/67f3e280f91571417c895dfece83c30605d2106f))
* Add new function ([87dbbd1](https://github.com/COMBINE-lab/libradicl/commit/87dbbd15c8a4fec34bbdba549a488effc583bc78))

### Miscellaneous

* Release 0.8.1 ([1c9ca49](https://github.com/COMBINE-lab/libradicl/commit/1c9ca49b8ef1615f86303012cd8bce1fdd067e0c))

## [0.8.0](https://github.com/COMBINE-lab/libradicl/compare/v0.7.0...v0.8.0) (2024-02-26)


### Bug Fixes

* Add examples to Cargo.toml ([a163b99](https://github.com/COMBINE-lab/libradicl/commit/a163b99824050bb1a7ac0501745ac97046060d18))

### Features

* Add record_context function to prelude ([aa85018](https://github.com/COMBINE-lab/libradicl/commit/aa850182902460bfe2d08f398cbfb818d4fa43a6))

### Miscellaneous

* Release 0.8.0 ([50fb643](https://github.com/COMBINE-lab/libradicl/commit/50fb6436c5e12210be147b06fbccda51cbad95e7))

## [0.7.0](https://github.com/COMBINE-lab/libradicl/compare/v0.6.0...v0.7.0) (2024-02-16)


### Features

* Drop htslib dependency, update deps ([ff4940f](https://github.com/COMBINE-lab/libradicl/commit/ff4940f4f778c3527c0099a7055b79c9c303d10d))

### Miscellaneous

* Release 0.7.0 ([7a8a369](https://github.com/COMBINE-lab/libradicl/commit/7a8a3697aadf2dd69d98415b29d77a1d3fcf1a09))

## [0.6.0](https://github.com/COMBINE-lab/libradicl/compare/v0.5.1...v0.6.0) (2023-06-29)


### Features

* Update dependencies ([ea255cc](https://github.com/COMBINE-lab/libradicl/commit/ea255cc40219192feb328d75e485886341853f0b))

### Miscellaneous

* Release 0.6.0 ([d845ba4](https://github.com/COMBINE-lab/libradicl/commit/d845ba4a4bd98018d1156601c7066eb5c18da750))

## [0.5.1](https://github.com/COMBINE-lab/libradicl/compare/v0.5.0...v0.5.1) (2023-01-12)


### Features

* Bump dependencies ([dd477dc](https://github.com/COMBINE-lab/libradicl/commit/dd477dc38485dbfec2385df85cf9724976cc5ffb))

### Miscellaneous

* Release 0.6.0 ([68a44f6](https://github.com/COMBINE-lab/libradicl/commit/68a44f6b3f826b75aad578b86d7aaf8b8c149bee))

## [0.5.0](https://github.com/COMBINE-lab/libradicl/compare/v0.4.6...v0.5.0) (2022-11-08)


### Documentation

* Update README.md ([1e90379](https://github.com/COMBINE-lab/libradicl/commit/1e9037967ff82ba45532608359e3306c3646c8de))
* Add CODE_OF_CONDUCT.md ([cb86eef](https://github.com/COMBINE-lab/libradicl/commit/cb86eef68dbdc8ddca49abad66a5776c3b3fc388))
* Add CONTRIBUTING.md ([ea6faf3](https://github.com/COMBINE-lab/libradicl/commit/ea6faf3011d00e7756e0bc2272d2e28fa87e0972))

### Features

* Update dependencies ([d0b9641](https://github.com/COMBINE-lab/libradicl/commit/d0b964171cbee53b2209e385140a6c51375d9cc2))

### Miscellaneous

* Release 0.5.0 ([b7824ab](https://github.com/COMBINE-lab/libradicl/commit/b7824aba4675ee7cb6187c323b65b039b539ae2e))

## [0.4.6](https://github.com/COMBINE-lab/libradicl/releases/tag/v0.4.6) (2022-06-01)


### Features

* Add release-please ([9b9eb99](https://github.com/COMBINE-lab/libradicl/commit/9b9eb9980d74c0f9e9958bb5d1ac7d679e434ac4))

### Miscellaneous

* Release 0.1.0 ([99d10ef](https://github.com/COMBINE-lab/libradicl/commit/99d10ef1900d052274ae3c53cdee676a744f60f5))
* Release 0.4.6 ([a442420](https://github.com/COMBINE-lab/libradicl/commit/a442420e92650d614ca16401214842735e0b2a51))
* Release 0.4.6 ([773bef2](https://github.com/COMBINE-lab/libradicl/commit/773bef20330c91f87acea49a48c2e15d9e8e3319))
* Release 0.4.6 ([d1377eb](https://github.com/COMBINE-lab/libradicl/commit/d1377ebc3c19d26bbc78f3bfef19c35004693c73))
* Release 0.4.6 ([3c9ffb7](https://github.com/COMBINE-lab/libradicl/commit/3c9ffb769ff7fe72ce96df1ad680d94cffd1f29a))
* Release 0.4.6 ([8299238](https://github.com/COMBINE-lab/libradicl/commit/8299238d1ac2e6dbd71482f7b7c28a3d33c28762))
* Release 0.4.6 ([4f572c2](https://github.com/COMBINE-lab/libradicl/commit/4f572c2507ddb71478d68d10bd7443aed1ff43b7))


