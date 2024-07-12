use anyhow::{self, Context};
use libradicl;
use libradicl::chunk::Chunk;
use libradicl::record::{PiscemBulkReadRecord, PiscemBulkRecordContext};
use std::io::BufReader;

fn main() -> anyhow::Result<()> {
    let fname = std::env::args().nth(1).context("missing input filename")?;
    let f = std::fs::File::open(&fname)?;
    let mut ifile = BufReader::new(f);

    let p = libradicl::header::RadPrelude::from_bytes(&mut ifile)?;
    if let Ok(summary) = p.summary(None) {
        println!("{}", summary);
    }

    let _tag_map = p.file_tags.try_parse_tags_from_bytes(&mut ifile)?;

    // Any extra context we may need to parse the records. In this case, it's the
    // size of the barcode and the umi.
    let tag_context = p.get_record_context::<PiscemBulkRecordContext>()?;
    let first_chunk = Chunk::<PiscemBulkReadRecord>::from_bytes(&mut ifile, &tag_context);
    println!(
        "Chunk :: nbytes: {}, nrecs: {}",
        first_chunk.nbytes, first_chunk.nrec
    );
    assert_eq!(first_chunk.nrec as usize, first_chunk.reads.len());
    for (i, r) in first_chunk.reads.iter().take(10).enumerate() {
        println!("record {i}: {:?}", r);
    }
    println!("printed 10 records of {} in chunk", first_chunk.nrec);

    let mut total_rec = first_chunk.nrec as usize;
    let mut total_bytes = first_chunk.nbytes as usize;
    let mut total_chunks = 1;

    while total_chunks < p.hdr.num_chunks {
        let chunk = Chunk::<PiscemBulkReadRecord>::from_bytes(&mut ifile, &tag_context);
        total_rec += chunk.nrec as usize;
        total_bytes += chunk.nbytes as usize;
        total_chunks += 1;
        if total_chunks % 500 == 0 {
            println!(r"read {total_chunks} chunks");
        }
    }

    println!(
        r"read a total of {total_chunks} chunks, comprising {total_rec} records and {total_bytes} bytes."
    );

    Ok(())
}
