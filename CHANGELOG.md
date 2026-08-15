# Changelog

All notable changes to this project are documented here. The format follows
[conventional commits](https://www.conventionalcommits.org); entries are
generated from commit messages by [git-cliff](https://git-cliff.org).

## [0.18.0](https://github.com/COMBINE-lab/libradicl/compare/v0.17.0...v0.18.0) (2026-08-15)


### Bug Fixes

* Clamp collation resource minima ([34e37f5](https://github.com/COMBINE-lab/libradicl/commit/34e37f57195b41fff1e78af2b78926b4646e2d8c))
* Clamp single-collator resources ([194d127](https://github.com/COMBINE-lab/libradicl/commit/194d127105f22acbc1d9731c68022d610cc5ca86))
* Validate compiled multi-barcode correction targets before collation ([195cd1d](https://github.com/COMBINE-lab/libradicl/commit/195cd1d81b87bc291e677103aa5ebe84984782cf))

### Features

* Apply caller-compiled barcode corrections ([1065aa3](https://github.com/COMBINE-lab/libradicl/commit/1065aa3bba70ab3b14c1121b09ce83415a0e16bb))

### Performance

* Add bounded multi-barcode collator ([08ae416](https://github.com/COMBINE-lab/libradicl/commit/08ae41640a4da089ec33ad31a4bf927434e2557b))
* Add bounded single-barcode collator ([acd5cec](https://github.com/COMBINE-lab/libradicl/commit/acd5cec61cbd10fa5d42f23fda991b1ac432c0af))
* Reduce compiled-correction lookup memory and release those indexes before gather ([364aaaf](https://github.com/COMBINE-lab/libradicl/commit/364aaaf0e29efe8602fb90fa0fbb0b18c1ccb65f), [56ff5fc](https://github.com/COMBINE-lab/libradicl/commit/56ff5fcbe74adc0e9af5ab3a0392b574e0367d6d))
* Adapt compiled barcode prefix indexes to the observed barcode distribution ([c2476e1](https://github.com/COMBINE-lab/libradicl/commit/c2476e1bba8ba204410528b9d2a67d59bf4baa39))
* Generalize legacy collation lookups over caller-selected hashers ([f2c5c89](https://github.com/COMBINE-lab/libradicl/commit/f2c5c899bf21bbc7d9437e4e2b3c1a7d1f7ff563))

### Documentation

* Document bounded collation, caller-compiled correction plans, and the
  two-thread and memory floors; add strict rustdoc and package dry-runs to CI.

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
