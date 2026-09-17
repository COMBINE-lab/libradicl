/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! This module contains types, functions and traits to deal with RAD
//! file headers, and also top-level functionality to encapsulate a RAD
//! prelude (which consists of the header, and the initial [TagSection]s;
//! basically everything up to the first chunk).

use crate::{self as libradicl, constants};
use anyhow::{self, Context};
use libradicl::codec::{CHUNK_CODEC_TAG, ChunkCodec};
use libradicl::rad_types::{
    RadIntId, RadType, TagDesc, TagMap, TagSection, TagSectionLabel, TagValue,
};
use libradicl::record::RecordContext;
use noodles::sam;
use scroll::Pread;
use std::cmp::{Eq, PartialEq};
use std::io::{Read, Write};

use educe::Educe;

/// The [RadPrelude] groups together the [RadHeader]
/// as well as the relevant top-level [TagSection]s of the file.
/// It constitutes everything in the initial file prior to the
/// start of the first [libradicl::chunk::Chunk].
#[derive(Debug, PartialEq, Eq)]
pub struct RadPrelude {
    pub hdr: RadHeader,
    pub file_tags: TagSection,
    pub read_tags: TagSection,
    pub aln_tags: TagSection,
}

/// The [RadHeader] contains the relevant information about the
/// references against which the reads in this file were mapped and
/// information about the way in which mapping was performed.
#[derive(Educe)]
#[educe(Debug, PartialEq, Eq)]
pub struct RadHeader {
    /// RAD spec **major** version: 0 for a legacy (magic-less) prelude, >= 2 for a
    /// versioned one (see [`constants::RAD_MAGIC`] / [`constants::RAD_SPEC_MAJOR`]).
    /// Major bumps are breaking; minor bumps are additive.
    pub major_version: u8,
    /// RAD spec **minor** version (0 for legacy).
    pub minor_version: u8,
    pub is_paired: u8,
    pub ref_count: u64,
    pub ref_names: Vec<String>,
    #[educe(PartialEq(ignore))]
    pub num_chunks: u64,
}

impl Default for RadHeader {
    fn default() -> Self {
        Self::new()
    }
}

impl RadHeader {
    /// Create a new empty [RadHeader]
    pub fn new() -> Self {
        Self {
            // Default to legacy (major 0) so existing construction + write paths
            // are byte-for-byte unchanged; a writer opts in by setting
            // `major_version = constants::RAD_SPEC_MAJOR`.
            major_version: 0,
            minor_version: 0,
            is_paired: 0,
            ref_count: 0,
            ref_names: vec![],
            num_chunks: 0,
        }
    }

    /// If the number of chunks is known, then it returns
    /// Some(num_chunks), if not, then it returns None.
    pub fn num_chunks(&self) -> Option<std::num::NonZeroUsize> {
        std::num::NonZeroUsize::new(self.num_chunks as usize)
    }

    /// Create and return a new [RadHeader] by reading the contents of the
    /// `reader`. If the reader is positioned such that a valid [RadHeader] comes
    /// next, then this function returns [Ok(RadHeader)], otherwise, it returns
    /// an [anyhow::Error] explaining the failure to parse the [RadHeader].
    pub fn from_bytes<T: Read>(reader: &mut T) -> anyhow::Result<RadHeader> {
        // Sniff the optional magic. Its first byte (`b'R'`) can't begin a legacy
        // prelude (whose first byte is `is_paired` in {0,1}), so this is
        // unambiguous. On a legacy file the sniffed bytes ARE the start of the
        // header, so we splice them back in front of the reader via `Read::chain`
        // (no `Seek` needed -- works for `Cursor` and `BufReader` alike).
        let mut magic = [0u8; constants::RAD_MAGIC.len()];
        reader.read_exact(&mut magic)?;
        if magic == constants::RAD_MAGIC {
            let mut vbuf = [0u8; 2];
            reader.read_exact(&mut vbuf)?;
            let (major, minor) = (vbuf[0], vbuf[1]);
            // Too-new guard: a higher *major* is a breaking layout this build does
            // not understand, so refuse rather than silently misparse. A higher
            // *minor* within the supported major is additive and read best-effort.
            if major > constants::RAD_SPEC_MAJOR {
                anyhow::bail!(
                    "RAD spec major version {major} is newer than supported ({}); please update this tool",
                    constants::RAD_SPEC_MAJOR
                );
            }
            if major < constants::RAD_FIRST_VERSIONED_MAJOR {
                anyhow::bail!(
                    "RAD prelude carries the magic but a reserved/legacy major version {major}; file is malformed"
                );
            }
            Self::read_fields(reader, major, minor)
        } else {
            let mut chained = std::io::Cursor::new(magic).chain(reader);
            Self::read_fields(&mut chained, 0, 0)
        }
    }

    /// Read the header fields (everything after the optional magic + version) from
    /// `reader`, tagging the result with the spec `major`/`minor`.
    fn read_fields<T: Read>(reader: &mut T, major: u8, minor: u8) -> anyhow::Result<RadHeader> {
        let mut rh = RadHeader {
            major_version: major,
            minor_version: minor,
            ..RadHeader::new()
        };

        // size of the longest allowable string.
        let mut buf = [0u8; constants::MAX_REF_NAME_LEN];
        // reader.read_exact(&mut buf[0..1])?;
        reader.read_exact(&mut buf[0..9])?;

        rh.is_paired = buf.pread(0)?;
        rh.ref_count = buf.pread::<u64>(1)?;
        // We know how many names we will read in, so reserve up front — but
        // `ref_count` comes straight off the wire and is not yet corroborated by
        // anything. Reserving it verbatim lets a malformed or truncated file
        // request an arbitrary allocation, which aborts the process (capacity
        // overflow / OOM) instead of surfacing as the parse error it is. Cap the
        // speculative part; a genuine header just grows past it, and a bogus one
        // fails at the first `read_exact` below.
        const MAX_SPECULATIVE_REFS: usize = 64 * 1024;
        rh.ref_names
            .reserve_exact((rh.ref_count as usize).min(MAX_SPECULATIVE_REFS));

        let mut num_read = 0u64;
        while num_read < rh.ref_count {
            // the length of the string
            reader.read_exact(&mut buf[0..2])?;
            let l: usize = buf.pread::<u16>(0)? as usize;
            // the string itself
            reader.read_exact(&mut buf[0..l])?;
            rh.ref_names
                .push(std::str::from_utf8(&buf[0..l])?.to_string());
            num_read += 1;
        }

        reader.read_exact(&mut buf[0..8])?;
        rh.num_chunks = buf.pread::<u64>(0)?;
        Ok(rh)
    }

    /// Create and return a [RadHeader] from the provided BAM/SAM header
    /// (represented by the noodles [sam::Header] `header`).  
    /// **Note**: The returned [RadHeader] will *not* have a value for the `num_chunks`
    /// field, which will remain set at 0, nor will it set a meaningful value for the
    /// `is_paried` flag, since the SAM/BAM header itself doesn't encode this information.
    pub fn from_bam_header(header: &sam::Header) -> RadHeader {
        let mut rh = RadHeader {
            major_version: 0,
            minor_version: 0,
            is_paired: 0,
            ref_count: 0,
            ref_names: vec![],
            num_chunks: 0,
        };

        let ref_seqs = header.reference_sequences();
        rh.ref_count = ref_seqs.len() as u64;
        // we know how many names we will read in.
        rh.ref_names.reserve_exact(rh.ref_count as usize);
        for (k, _v) in ref_seqs.iter() {
            rh.ref_names.push(k.to_string());
        }
        rh
    }

    /// Returns the size, in bytes, that this [RadHeader] will take
    /// if written to an output stream.
    pub fn get_size(&self) -> usize {
        let mut tot_size = 0usize;
        // versioned headers (major >= first-versioned) are prefixed by the magic
        // + [major:u8][minor:u8]
        if self.major_version >= constants::RAD_FIRST_VERSIONED_MAJOR {
            tot_size += constants::RAD_MAGIC.len() + 2;
        }
        tot_size += std::mem::size_of_val(&self.is_paired) + std::mem::size_of_val(&self.ref_count);
        // each name takes 2 bytes for the length, plus the actual
        // number of bytes required by the string itself.
        for t in self.ref_names.iter().map(|a| a.len()) {
            tot_size += std::mem::size_of::<u16>() + t;
        }
        tot_size += std::mem::size_of_val(&self.num_chunks);
        tot_size
    }

    /// Write a summary of the current [RadHeader] to a [String]. This
    /// produces an [Ok(String)] if successful. The `num_refs` argument
    /// can be provided to control the number of reference names printed.
    /// The default (if `None` is provided to this option) is 10.
    pub fn summary(&self, num_refs: Option<usize>) -> anyhow::Result<String> {
        use std::fmt::Write as _;
        let mut s = String::new();
        writeln!(&mut s, "RadHeader {{")?;
        writeln!(&mut s, "is_paired: {}", self.is_paired)?;
        writeln!(&mut s, "ref_count: {}", self.ref_count)?;

        let refs_to_print = match num_refs {
            Some(rcount) => rcount.min(self.ref_count as usize),
            None => (self.ref_count as usize).min(10_usize),
        };

        for rn in self.ref_names.iter().take(refs_to_print) {
            writeln!(&mut s, "  ref: {}", rn)?;
        }
        if refs_to_print < self.ref_count as usize {
            writeln!(&mut s, "  ...")?;
        }

        writeln!(&mut s, "num_chunks: {}", self.num_chunks)?;
        writeln!(&mut s, "}}")?;
        Ok(s)
    }

    /// Write this [RadHeader] to the provided writer `w`, propagating
    /// any error that occurs or returing `Ok(())` on success.
    pub fn write<W: Write>(&self, w: &mut W) -> anyhow::Result<()> {
        // NOTE: If this RadHeader was created from a SAM
        // header, this information is not meanginful because
        // it's not contained in the SAM header.  Think about if
        // and how to address that.
        // Versioned files (major >= first-versioned) get the magic + [major][minor]
        // prefix; legacy headers (major 0) write exactly as before.
        if self.major_version >= constants::RAD_FIRST_VERSIONED_MAJOR {
            w.write_all(&constants::RAD_MAGIC)?;
            w.write_all(&[self.major_version, self.minor_version])?;
        }

        w.write_all(&self.is_paired.to_le_bytes())?;

        let ref_count = self.ref_count;
        w.write_all(&ref_count.to_le_bytes())?;

        // create longest buffer
        for k in self.ref_names.iter() {
            let name_size = k.len() as u16;
            w.write_all(&name_size.to_le_bytes())?;
            w.write_all(k.as_bytes())?;
        }

        let initial_num_chunks = self.num_chunks;
        w.write_all(&initial_num_chunks.to_le_bytes())?;
        Ok(())
    }
}

impl RadPrelude {
    /// Build a [RadPrelude] from the provided [RadHeader] and the
    /// [TagSection]s for the file, read, and alignment tags. The header
    /// and tag sections are moved, and so are no long valid after the
    /// construction of the prelude. However, those fields are public
    /// so they can be accessed after the prelude is returned. Unlike
    /// the `from_bytes` constructor, this construction is assumed not
    /// to be failable.
    pub fn from_header_and_tag_sections(
        hdr: RadHeader,
        file_tags: TagSection,
        read_tags: TagSection,
        aln_tags: TagSection,
    ) -> Self {
        Self {
            hdr,
            file_tags,
            read_tags,
            aln_tags,
        }
    }

    /// Read a [RadPrelude] from the provided `reader`, which includes the
    /// [RadHeader] as well as the relevant [TagSection]s.  This function returns
    /// an `std::Ok(`[RadPrelude]`)` if the prelude is parsed succesfully and an
    /// [anyhow::Error] otherwise.
    pub fn from_bytes<T: Read>(reader: &mut T) -> anyhow::Result<Self> {
        let hdr = RadHeader::from_bytes(reader)?;
        // Tag descriptors carry per-tag roles only in versioned files; the major
        // version (just parsed) tells the tag reader whether to expect them.
        let m = hdr.major_version;
        let file_tags = TagSection::from_bytes_with_label(reader, TagSectionLabel::FileTags, m)?;
        let read_tags = TagSection::from_bytes_with_label(reader, TagSectionLabel::ReadTags, m)?;
        let aln_tags =
            TagSection::from_bytes_with_label(reader, TagSectionLabel::AlignmentTags, m)?;

        //let file_tag_vals = file_tags.parse_tags_from_bytes(reader)?;
        //println!("file-level tag values: {:?}", file_tag_vals);

        Ok(Self {
            hdr,
            file_tags,
            read_tags,
            aln_tags,
        })
    }

    /// Writes this [RadPrelude] to the provided writer. Returns an
    /// [anyhow::Result] that records any error that occured during writing or
    /// Ok(()) if successful
    pub fn write<W: Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        let m = self.hdr.major_version;
        self.hdr
            .write(writer)
            .context("could not write the header of the prelude")?;
        self.file_tags
            .write(writer, m)
            .context("could not write the file-level tags of the prelude")?;
        self.read_tags
            .write(writer, m)
            .context("could not write the file-level tags of the prelude")?;
        self.aln_tags
            .write(writer, m)
            .context("could not write the file-level tags of the prelude")?;
        Ok(())
    }

    /// Write a collated-output header derived from this prelude: the header
    /// with `num_chunks` patched to the collated chunk count and, when
    /// `codec != `[`ChunkCodec::None`], an added [`CHUNK_CODEC_TAG`] file-tag
    /// descriptor. It is followed by `original_file_tag_values` (the file-tag
    /// value bytes copied verbatim from the source RAD, i.e. the bytes that
    /// immediately follow the source prelude) and, for a non-`None` codec, the
    /// codec tag's `u8` value appended last so it aligns with the appended
    /// descriptor. The `original_file_tag_values` slice is obtained by the
    /// caller as `source_header[self.write(..).len()..]`.
    ///
    /// This lets a collation writer record which per-chunk codec was applied to
    /// the gathered chunks; readers recover it via the same file tag (see
    /// [`crate::codec`]). An absent tag means [`ChunkCodec::None`], so an
    /// uncompressed collated header need not be rebuilt through this path.
    pub fn write_with_chunk_codec<W: Write>(
        &self,
        writer: &mut W,
        original_file_tag_values: &[u8],
        num_chunks: u64,
        codec: ChunkCodec,
    ) -> anyhow::Result<()> {
        // Header with num_chunks (the final u64 of the header) patched.
        let mut hdr_bytes = Vec::new();
        self.hdr
            .write(&mut hdr_bytes)
            .context("could not serialize the collated header")?;
        let nc_off = hdr_bytes.len() - std::mem::size_of::<u64>();
        hdr_bytes[nc_off..].copy_from_slice(&num_chunks.to_le_bytes());
        writer.write_all(&hdr_bytes)?;

        // File-tag section descriptors, adding the codec tag when compressing.
        let m = self.hdr.major_version;
        if codec == ChunkCodec::None {
            self.file_tags.write(writer, m)?;
        } else {
            let mut file_tags = self.file_tags.clone();
            file_tags.add_tag_desc(TagDesc {
                name: CHUNK_CODEC_TAG.to_string(),
                typeid: RadType::Int(RadIntId::U8),
                role: crate::rad_types::TagRole::None,
            });
            file_tags.write(writer, m)?;
        }
        self.read_tags.write(writer, m)?;
        self.aln_tags.write(writer, m)?;

        // The source file-tag values (unchanged), then the codec value last so
        // it lines up with the descriptor appended above.
        writer.write_all(original_file_tag_values)?;
        if codec != ChunkCodec::None {
            let codec_desc = TagDesc {
                name: CHUNK_CODEC_TAG.to_string(),
                typeid: RadType::Int(RadIntId::U8),
                role: crate::rad_types::TagRole::None,
            };
            let mut values = TagMap::with_keyset(std::slice::from_ref(&codec_desc));
            values.add(TagValue::U8(codec.as_u8()));
            values.write_values(writer)?;
        }
        Ok(())
    }

    /// Returns a textual summary of this as an `std::Ok(`[String]`)` if successful
    /// and an [anyhow::Error] otherwise.
    pub fn summary(&self, num_refs: Option<usize>) -> anyhow::Result<String> {
        use std::fmt::Write as _;
        let mut s = self.hdr.summary(num_refs)?;
        writeln!(&mut s, "[[{:?}]]", self.file_tags)?;
        writeln!(&mut s, "[[{:?}]]", self.read_tags)?;
        writeln!(&mut s, "[[{:?}]]", self.aln_tags)?;
        Ok(s)
    }

    /// Obtain a [RecordContext] for a record of type `R` from this prelude, by
    /// using the associated [TagSection]s.  **Note**: Since this function
    /// constructs the resulting `R` itself, and doesn't take any `R` parameter,
    /// then it must always be invoked with the proper
    /// [turbofish](https://doc.rust-lang.org/1.75.0/book/2018-edition/appendix-02-operators.html?highlight=turbofish#non-operator-symbols)
    /// notation.
    pub fn get_record_context<R: RecordContext>(&self) -> anyhow::Result<R> {
        R::get_context_from_tag_section(&self.file_tags, &self.read_tags, &self.aln_tags)
    }
}

#[cfg(test)]
mod tests {
    use super::{RadHeader, RadPrelude};
    use crate::rad_types::{RadAtomicId, RadIntId, TagMap, TagSection, TagSectionLabel, TagValue};
    use crate::rad_types::{RadType, TagDesc};

    /// A versioned header (spec >= 2) writes the magic + version prefix and reads
    /// back with the same version; a legacy header writes no prefix and reads back
    /// as version 0; and raw legacy bytes (no magic, as produced before versioning)
    /// still parse as version 0 with the correct fields.
    #[test]
    fn magic_version_roundtrip_and_legacy_backcompat() {
        let mk = |major: u8, minor: u8| RadHeader {
            major_version: major,
            minor_version: minor,
            is_paired: 1,
            ref_count: 2,
            ref_names: vec!["a".to_string(), "bb".to_string()],
            num_chunks: 5,
        };

        // versioned round-trip
        let v = mk(
            crate::constants::RAD_SPEC_MAJOR,
            crate::constants::RAD_SPEC_MINOR,
        );
        let mut vb: Vec<u8> = Vec::new();
        v.write(&mut vb).unwrap();
        assert_eq!(
            &vb[..crate::constants::RAD_MAGIC.len()],
            &crate::constants::RAD_MAGIC
        );
        let vr = RadHeader::from_bytes(&mut std::io::Cursor::new(&vb)).unwrap();
        assert_eq!(vr.major_version, crate::constants::RAD_SPEC_MAJOR);
        assert_eq!(vr.minor_version, crate::constants::RAD_SPEC_MINOR);
        assert_eq!(vr.ref_names, v.ref_names);
        assert_eq!(vr.num_chunks, 5);

        // legacy round-trip: no magic prefix, version reads back as 0
        let l = mk(0, 0);
        let mut lb: Vec<u8> = Vec::new();
        l.write(&mut lb).unwrap();
        assert_ne!(
            &lb[..crate::constants::RAD_MAGIC.len()],
            &crate::constants::RAD_MAGIC
        );
        let lr = RadHeader::from_bytes(&mut std::io::Cursor::new(&lb)).unwrap();
        assert_eq!(lr.major_version, 0);
        assert_eq!(lr.minor_version, 0);
        assert_eq!(lr.ref_names, l.ref_names);

        // a versioned file is byte-longer than the legacy one by exactly the prefix
        assert_eq!(vb.len() - lb.len(), crate::constants::RAD_MAGIC.len() + 2);
    }

    /// A writer can produce a versioned prelude *from scratch* (magic + version +
    /// per-tag roles) that reads back intact — not just by copying a v2 source.
    #[test]
    fn prelude_v2_with_roles_roundtrips() {
        use crate::rad_types::{RadIntId, RadType, TagDesc, TagRole};
        let int = |n: &str, i: RadIntId, role: TagRole| TagDesc {
            name: n.to_string(),
            typeid: RadType::Int(i),
            role,
        };
        let hdr = RadHeader {
            major_version: crate::constants::RAD_SPEC_MAJOR,
            minor_version: crate::constants::RAD_SPEC_MINOR,
            is_paired: 0,
            ref_count: 1,
            ref_names: vec!["r0".to_string()],
            num_chunks: 3,
        };
        let file_tags = TagSection {
            label: TagSectionLabel::FileTags,
            tags: vec![int("cblen", RadIntId::U16, TagRole::None)],
        };
        let read_tags = TagSection {
            label: TagSectionLabel::ReadTags,
            tags: vec![
                int("b", RadIntId::U32, TagRole::Barcode { level: 0 }),
                int("u", RadIntId::U32, TagRole::Umi),
            ],
        };
        let aln_tags = TagSection {
            label: TagSectionLabel::AlignmentTags,
            tags: vec![int("cor", RadIntId::U32, TagRole::Orientation)],
        };
        let prelude = RadPrelude::from_header_and_tag_sections(hdr, file_tags, read_tags, aln_tags);

        let mut buf = Vec::new();
        prelude.write(&mut buf).unwrap();
        assert_eq!(
            &buf[..crate::constants::RAD_MAGIC.len()],
            &crate::constants::RAD_MAGIC
        );

        let rp = RadPrelude::from_bytes(&mut buf.as_slice()).unwrap();
        assert_eq!(rp.hdr.major_version, crate::constants::RAD_SPEC_MAJOR);
        assert_eq!(rp.hdr.minor_version, crate::constants::RAD_SPEC_MINOR);
        assert_eq!(rp.hdr.ref_names, vec!["r0".to_string()]);
        assert_eq!(rp.read_tags.tags[0].role, TagRole::Barcode { level: 0 });
        assert_eq!(rp.read_tags.tags[1].role, TagRole::Umi);
        assert_eq!(rp.aln_tags.tags[0].role, TagRole::Orientation);
        assert_eq!(rp.file_tags.tags[0].role, TagRole::None);
    }

    /// A file whose major version exceeds what this build supports must be
    /// refused (not silently misparsed); a higher minor within the supported
    /// major is accepted.
    #[test]
    fn rejects_too_new_major_accepts_higher_minor() {
        let mk_bytes = |major: u8, minor: u8| {
            let mut b = Vec::new();
            b.extend_from_slice(&crate::constants::RAD_MAGIC);
            b.extend_from_slice(&[major, minor]);
            b.push(0); // is_paired
            b.extend_from_slice(&0u64.to_le_bytes()); // ref_count = 0
            b.extend_from_slice(&0u64.to_le_bytes()); // num_chunks = 0
            b
        };
        let too_new = mk_bytes(crate::constants::RAD_SPEC_MAJOR + 1, 0);
        assert!(RadHeader::from_bytes(&mut std::io::Cursor::new(too_new)).is_err());

        let higher_minor = mk_bytes(crate::constants::RAD_SPEC_MAJOR, 200);
        let h = RadHeader::from_bytes(&mut std::io::Cursor::new(higher_minor))
            .expect("higher minor within a supported major must be accepted");
        assert_eq!(h.major_version, crate::constants::RAD_SPEC_MAJOR);
        assert_eq!(h.minor_version, 200);
    }

    /// The speculative-reservation cap must not limit real headers. A human
    /// transcriptome has a few hundred thousand references, well past the cap,
    /// so the `Vec` has to keep growing past it.
    #[test]
    fn header_roundtrips_more_refs_than_the_prealloc_cap() {
        const NREFS: usize = 70_000; // > MAX_SPECULATIVE_REFS
        let names: Vec<String> = (0..NREFS).map(|i| format!("tx{i}")).collect();
        let hdr = RadHeader {
            major_version: 0,
            minor_version: 0,
            is_paired: 0,
            ref_count: NREFS as u64,
            ref_names: names.clone(),
            num_chunks: 7,
        };

        let mut buf: Vec<u8> = Vec::new();
        hdr.write(&mut buf).expect("write header");

        let read_back =
            RadHeader::from_bytes(&mut std::io::Cursor::new(buf)).expect("parse header");
        assert_eq!(read_back.ref_count, NREFS as u64);
        assert_eq!(read_back.ref_names.len(), NREFS);
        assert_eq!(read_back.ref_names[0], names[0]);
        assert_eq!(read_back.ref_names[NREFS - 1], names[NREFS - 1]);
        assert_eq!(read_back.num_chunks, 7);
    }

    /// A `ref_count` that is not corroborated by the rest of the stream must be
    /// a parse error, not an aborting allocation.
    #[test]
    fn absurd_ref_count_is_an_error_not_an_abort() {
        let mut buf: Vec<u8> = Vec::new();
        buf.push(0); // is_paired
        buf.extend_from_slice(&u64::MAX.to_le_bytes()); // ref_count: absurd
        // ...and then nothing, as a truncated file would have.
        let res = RadHeader::from_bytes(&mut std::io::Cursor::new(buf));
        assert!(res.is_err(), "an absurd ref_count was not rejected");
    }

    #[test]
    fn can_write_prelude() {
        let hdr = RadHeader {
            major_version: 0,
            minor_version: 0,
            is_paired: 0,
            ref_count: 3,
            ref_names: vec!["tgt1".to_string(), "tgt2".to_string(), "tgt3".to_string()],
            num_chunks: 1,
        };

        let ft_desc = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "ref_lengths".to_string(),
            typeid: RadType::Array(RadIntId::U32, RadAtomicId::Int(RadIntId::U32)),
        };
        let mut file_tags = TagSection::new_with_label(TagSectionLabel::FileTags);
        file_tags.add_tag_desc(ft_desc);

        let rd_desc = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "frag_map_type".to_string(),
            typeid: RadType::Int(RadIntId::U8),
        };
        let mut read_tags = TagSection::new_with_label(TagSectionLabel::ReadTags);
        read_tags.add_tag_desc(rd_desc);

        let aln_coi = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "compressed_ori_ref".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let aln_mt = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "frag_map_type".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let aln_fl = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "frag_len".to_string(),
            typeid: RadType::Int(RadIntId::U16),
        };
        let mut aln_tags = TagSection::new_with_label(TagSectionLabel::AlignmentTags);
        aln_tags.add_tag_desc(aln_coi);
        aln_tags.add_tag_desc(aln_mt);
        aln_tags.add_tag_desc(aln_fl);

        let prelude = RadPrelude {
            hdr,
            file_tags,
            read_tags,
            aln_tags,
        };

        let mut buf: Vec<u8> = Vec::new();

        prelude
            .write(&mut buf)
            .expect("cannot write prelude to buffer");

        let mut file_tag_map = TagMap::with_keyset(&prelude.file_tags.tags);
        file_tag_map.add(TagValue::ArrayU32(vec![1, 2, 3]));
        file_tag_map
            .write_values(&mut buf)
            .expect("cannot write file tag map");

        let mut cursor = std::io::Cursor::new(buf);
        let new_prelude =
            RadPrelude::from_bytes(&mut cursor).expect("cannot read prelude from buffer");
        let new_file_tag_map = &prelude
            .file_tags
            .try_parse_tags_from_bytes(&mut cursor)
            .expect("cannot read file TagMap");

        println!("new_prelude = {}", new_prelude.summary(None).unwrap());
        println!("new_file_tag_map = {:?}", new_file_tag_map);

        assert_eq!(prelude, new_prelude);
        assert_eq!(&file_tag_map, new_file_tag_map);
    }

    #[test]
    fn preludes_equal_with_different_chunks() {
        let hdr = RadHeader {
            major_version: 0,
            minor_version: 0,
            is_paired: 0,
            ref_count: 3,
            ref_names: vec!["tgt1".to_string(), "tgt2".to_string(), "tgt3".to_string()],
            num_chunks: 1,
        };

        let ft_desc = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "ref_lengths".to_string(),
            typeid: RadType::Array(RadIntId::U32, RadAtomicId::Int(RadIntId::U32)),
        };
        let mut file_tags = TagSection::new_with_label(TagSectionLabel::FileTags);
        file_tags.add_tag_desc(ft_desc);

        let rd_desc = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "frag_map_type".to_string(),
            typeid: RadType::Int(RadIntId::U8),
        };
        let mut read_tags = TagSection::new_with_label(TagSectionLabel::ReadTags);
        read_tags.add_tag_desc(rd_desc);

        let aln_coi = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "compressed_ori_ref".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let aln_mt = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "frag_map_type".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let aln_fl = TagDesc {
            role: crate::rad_types::TagRole::None,
            name: "frag_len".to_string(),
            typeid: RadType::Int(RadIntId::U16),
        };
        let mut aln_tags = TagSection::new_with_label(TagSectionLabel::AlignmentTags);
        aln_tags.add_tag_desc(aln_coi);
        aln_tags.add_tag_desc(aln_mt);
        aln_tags.add_tag_desc(aln_fl);

        let prelude = RadPrelude {
            hdr,
            file_tags,
            read_tags,
            aln_tags,
        };

        let mut buf: Vec<u8> = Vec::new();

        prelude
            .write(&mut buf)
            .expect("cannot write prelude to buffer");

        let mut file_tag_map = TagMap::with_keyset(&prelude.file_tags.tags);
        file_tag_map.add(TagValue::ArrayU32(vec![1, 2, 3]));
        file_tag_map
            .write_values(&mut buf)
            .expect("cannot write file tag map");

        let mut cursor = std::io::Cursor::new(buf);
        let mut new_prelude =
            RadPrelude::from_bytes(&mut cursor).expect("cannot read prelude from buffer");
        let new_file_tag_map = &prelude
            .file_tags
            .try_parse_tags_from_bytes(&mut cursor)
            .expect("cannot read file TagMap");

        new_prelude.hdr.num_chunks = 4;
        println!("new_prelude = {}", new_prelude.summary(None).unwrap());
        println!("new_file_tag_map = {:?}", new_file_tag_map);

        assert_eq!(prelude, new_prelude);
        assert_eq!(&file_tag_map, new_file_tag_map);
    }
}
