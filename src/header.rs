use crate::{self as libradicl, constants};
use libradicl::rad_types::{TagSection, TagSectionLabel};
use libradicl::record::RecordContext;
use noodles_sam as sam;
use scroll::Pread;
use std::io::Read;

/// The [RadPrelude] groups together the [RadHeader]
/// as well as the relevant top-level [TagSection]s of the file.
/// It constitutes everything in the initial file prior to the
/// start of the first [libradicl::chunk::Chunk].
pub struct RadPrelude {
    pub hdr: RadHeader,
    pub file_tags: TagSection,
    pub read_tags: TagSection,
    pub aln_tags: TagSection,
}

/// The [RadHeader] contains the relevant information about the
/// references against which the reads in this file were mapped and
/// information about the way in which mapping was performed.
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
}

impl RadPrelude {
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
