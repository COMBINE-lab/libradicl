use libradicl::{
    //header::RadPrelude,
    //readers::ParallelChunkReader,
    readers::ParallelRadReader,
    record::AtacSeqReadRecord,
};
use std::fs::File;
use std::io::BufReader;
use std::num::NonZeroUsize;
use std::sync::atomic::Ordering;

fn main() {
    let f = File::open("../piscem_atac_data/map.rad");
    let ifile = BufReader::new(f.unwrap());

    const NWORKERS: usize = 4;
    let mut rad_reader = ParallelRadReader::<AtacSeqReadRecord, BufReader<File>>::new(
        ifile,
        NonZeroUsize::new(NWORKERS).unwrap(),
        false,
    );

    if let Ok(summary) = rad_reader.prelude.summary(None) {
        println!("{}", summary);
    }
    println!("tag map {:?}\n", rad_reader.file_tag_map);
    println!("num chunks = {:?}\n", rad_reader.prelude.hdr.num_chunks());

    let mut handles = Vec::<std::thread::JoinHandle<_>>::new();
    for _ in 0..NWORKERS {
        let rd = rad_reader.is_done();
        let q = rad_reader.get_queue();
        let handle = std::thread::spawn(move || {
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
        handles.push(handle);
    }

    let _ = rad_reader.start_chunk_parsing();
    for handle in handles {
        handle.join().expect("The parsing thread panicked");
    }
}
