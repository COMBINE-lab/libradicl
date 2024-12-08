# libradicl - A library for reading parsing and writing RAD files for high-throughput genomic data

The working spec for the RAD format can be found [here](https://hackmd.io/@PI7Og0l1ReeBZu_pjQGUQQ/HkbVOHXUR).

Libradicl is a [Rust](https://www.rust-lang.org/) library for reading (and eventually writing and manipulating) 
Reduced Alignment Data (RAD) format files.  These files are produced by [`piscem`](https://github.com/COMBINE-lab/piscem) and [`salmon`](https://github.com/COMBINE-lab/salmon) when preparing sc/snRNA-seq or scATAC-seq data for single-cell quantification with [`alevin-fry`](https://github.com/COMBINE-lab/alevin-fry).

Currently, `libradicl` has primarily been developed in support of `alevin-fry`, though we aim for it to be a general library with a useful API for reading, writing and parsing RAD files.
