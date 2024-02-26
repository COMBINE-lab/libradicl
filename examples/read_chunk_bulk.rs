use anyhow;
use libradicl;
use libradicl::chunk::Chunk;
use libradicl::rad_types;
use libradicl::record::{PiscemBulkReadRecord, PiscemBulkRecordContext, RecordContext};
use std::io::BufReader;

fn main() -> anyhow::Result<()> {
    let fname = std::env::args().nth(1).expect("input filename");
    let f = std::fs::File::open(&fname)?;
    let mut ifile = BufReader::new(f);
    let p = libradicl::header::RadPrelude::from_bytes(&mut ifile)?;
    if let Ok(summary) = p.summary(None) {
        println!("{}", summary);
    }

    let _tag_map = p.file_tags.parse_tags_from_bytes_checked(&mut ifile)?;

    // Any extra context we may need to parse the records. In this case, it's the
    // size of the barcode and the umi.
    let tag_context = PiscemBulkRecordContext::get_context_from_tag_section(
        &p.file_tags,
        &p.read_tags,
        &p.aln_tags,
    )?;
    let first_chunk = Chunk::<PiscemBulkReadRecord>::from_bytes(&mut ifile, &tag_context);
    println!(
        "Chunk :: nbytes: {}, nrecs: {}",
        first_chunk.nbytes, first_chunk.nrec
    );
    assert_eq!(first_chunk.nrec as usize, first_chunk.reads.len());
    for (i, r) in first_chunk.reads.iter().take(10).enumerate() {
        println!("record {i}: {:?}", r);
    }

    Ok(())
}
