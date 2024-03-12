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
use libradicl::rad_types::{TagSection, TagSectionLabel};
use libradicl::record::RecordContext;
use noodles_sam as sam;
use scroll::Pread;
use std::io::{Read, Write};

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
#[derive(Debug, PartialEq, Eq)]
pub struct RadHeader {
    pub is_paired: u8,
    pub ref_count: u64,
    pub ref_names: Vec<String>,
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
            is_paired: 0,
            ref_count: 0,
            ref_names: vec![],
            num_chunks: 0,
        }
    }

    /// Create and return a new [RadHeader] by reading the contents of the
    /// `reader`. If the reader is positioned such that a valid [RadHeader] comes
    /// next, then this function returns [Ok(RadHeader)], otherwise, it returns
    /// an [anyhow::Error] explaining the failure to parse the [RadHeader].
    pub fn from_bytes<T: Read>(reader: &mut T) -> anyhow::Result<RadHeader> {
        let mut rh = RadHeader::new();

        // size of the longest allowable string.
        let mut buf = [0u8; constants::MAX_REF_NAME_LEN];
        reader.read_exact(&mut buf[0..9])?;
        rh.is_paired = buf.pread(0)?;
        rh.ref_count = buf.pread::<u64>(1)?;

        // we know how many names we will read in.
        rh.ref_names.reserve_exact(rh.ref_count as usize);

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
        writeln!(&mut s, "  ...")?;

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
        let file_tags = TagSection::from_bytes_with_label(reader, TagSectionLabel::FileTags)?;
        let read_tags = TagSection::from_bytes_with_label(reader, TagSectionLabel::ReadTags)?;
        let aln_tags = TagSection::from_bytes_with_label(reader, TagSectionLabel::AlignmentTags)?;

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
        self.hdr
            .write(writer)
            .context("could not write the header of the prelude")?;
        self.file_tags
            .write(writer)
            .context("could not write the file-level tags of the prelude")?;
        self.read_tags
            .write(writer)
            .context("could not write the file-level tags of the prelude")?;
        self.aln_tags
            .write(writer)
            .context("could not write the file-level tags of the prelude")?;
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

    #[test]
    fn can_write_prelude() {
        let hdr = RadHeader {
            is_paired: 0,
            ref_count: 3,
            ref_names: vec!["tgt1".to_string(), "tgt2".to_string(), "tgt3".to_string()],
            num_chunks: 1,
        };

        let ft_desc = TagDesc {
            name: "ref_lengths".to_string(),
            typeid: RadType::Array(RadIntId::U32, RadAtomicId::Int(RadIntId::U32)),
        };
        let mut file_tags = TagSection::new_with_label(TagSectionLabel::FileTags);
        file_tags.add_tag_desc(ft_desc);

        let rd_desc = TagDesc {
            name: "frag_map_type".to_string(),
            typeid: RadType::Int(RadIntId::U8),
        };
        let mut read_tags = TagSection::new_with_label(TagSectionLabel::ReadTags);
        read_tags.add_tag_desc(rd_desc);

        let aln_coi = TagDesc {
            name: "compressed_ori_ref".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let aln_mt = TagDesc {
            name: "frag_map_type".to_string(),
            typeid: RadType::Int(RadIntId::U32),
        };
        let aln_fl = TagDesc {
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

        let _ = prelude
            .write(&mut buf)
            .expect("cannot write prelude to buffer");

        let mut file_tag_map = TagMap::with_keyset(&prelude.file_tags.tags);
        file_tag_map.add(TagValue::ArrayU32(vec![1, 2, 3]));
        let _ = file_tag_map
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
}
