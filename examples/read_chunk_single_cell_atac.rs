use crossbeam_queue::ArrayQueue;
use libradicl::chunk::Chunk;
use libradicl::{
    header::RadPrelude,
    readers::{MetaChunk, ParallelRadReader},
    record::{AtacSeqReadRecord, AtacSeqRecordContext},
    utils,
};
use std::fs::File;
use std::io::BufReader;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

fn main() {
    let f = File::open("../piscem_atac_data/map.rad");
    let mut ifile = BufReader::new(f.unwrap());
    let p = RadPrelude::from_bytes(&mut ifile).unwrap();
    if let Ok(summary) = p.summary(None) {
        println!("{}", summary);
    }
    let tag_map = p.file_tags.parse_tags_from_bytes(&mut ifile).unwrap();
    println!("tag map {:?}\n", tag_map);
    println!("num chunks = {:?}\n", p.hdr.num_chunks());

    let q = Arc::new(ArrayQueue::<MetaChunk<AtacSeqReadRecord>>::new(1));

    let mut reader = ParallelRadReader::<AtacSeqReadRecord> {
        prelude: &p,
        meta_chunk_queue: q.clone(),
        header_incl_in_bytes: false,
    };

    let reading_done = Arc::new(AtomicBool::new(false));

    let rd = reading_done.clone();
    let handle = std::thread::spawn(move || {
        let mut q = q.clone();
        while !rd.load(Ordering::SeqCst) {
            while let Some(meta_chunk) = q.pop() {
                for c in meta_chunk.iter() {
                    println!("Chunk :: nbytes: {}, nrecs: {}", c.nbytes, c.nrec);
                    assert_eq!(c.nrec as usize, c.reads.len());
                    for (i, r) in c.reads.iter().take(10).enumerate() {
                        println!("record {i}: {:?}", r);
                    }
                }
            }
        }
    });

    reader.fill_work_queue(reading_done, &mut ifile);
    handle.join().expect("The parsing thread panicked");
    /*
    // Any extra context we may need to parse the records. In this case, it's the
    // size of the barcode and the umi.
    let tag_context = p.get_record_context::<AtacSeqRecordContext>().unwrap();
    println!("tag context = {:?}", tag_context);

    while utils::has_data_left(&mut ifile).expect("encountered error reading input file") {
        let next_chunk = Chunk::<AtacSeqReadRecord>::from_bytes(&mut ifile, &tag_context);
        println!(
            "Chunk :: nbytes: {}, nrecs: {}",
            next_chunk.nbytes, next_chunk.nrec
        );
        assert_eq!(next_chunk.nrec as usize, next_chunk.reads.len());
        for (i, r) in next_chunk.reads.iter().take(10).enumerate() {
            println!("record {i}: {:?}", r);
        }
    }
    */
}
