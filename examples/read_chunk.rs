use anyhow;
use libradicl::rad_types::{self, RecordContext};
use std::io::BufReader;

fn main() -> anyhow::Result<()> {
    let fname = std::env::args().nth(1).expect("input filename");
    let f = std::fs::File::open(&fname)?;
    let mut ifile = BufReader::new(f);
    let p = rad_types::RadPrelude::from_bytes(&mut ifile)?;
    if let Ok(summary) = p.summary(None) {
        println!("{}", summary);
    }

    let tag_map = p.file_tags.parse_tags_from_bytes_checked(&mut ifile)?;
    println!("tag map {:?}", tag_map);
    // Any extra context we may need to parse the records. In this case, it's the
    // size of the barcode and the umi.
    let tag_context = rad_types::AlevinFryRecordContext::get_context_from_tag_section(
        &p.file_tags,
        &p.read_tags,
        &p.aln_tags,
    )?;
    let first_chunk =
        rad_types::Chunk::<rad_types::AlevinFryReadRecord>::from_bytes(&mut ifile, &tag_context);
    println!(
        "nbytes = {}, nrecs = {}",
        first_chunk.nbytes, first_chunk.nrec
    );

    Ok(())
}
