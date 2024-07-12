use indicatif::{ProgressBar, ProgressDrawTarget, ProgressStyle};
use libradicl::{
    //header::RadPrelude,
    //readers::ParallelChunkReader,
    readers::ParallelRadReader,
    record::AlevinFryReadRecord,
};
use std::fs::File;
use std::io::BufReader;
use std::num::NonZeroUsize;
use std::sync::atomic::Ordering;

fn main() -> anyhow::Result<()> {
    let f = File::open("../piscem_atac_data/map.rad")?;
    let metadata = f.metadata()?;
    let file_len = metadata.len();
    let ifile = BufReader::new(f);

    const NWORKERS: usize = 12;
    let mut rad_reader = ParallelRadReader::<AlevinFryReadRecord, BufReader<File>>::new(
        ifile,
        NonZeroUsize::new(NWORKERS).unwrap(),
    );

    if let Ok(summary) = rad_reader.prelude.summary(None) {
        println!("{}", summary);
    }
    println!("tag map {:?}\n", rad_reader.file_tag_map);
    println!("num chunks = {:?}\n", rad_reader.prelude.hdr.num_chunks());

    let mut handles = Vec::<std::thread::JoinHandle<usize>>::new();
    for _ in 0..NWORKERS {
        let rd = rad_reader.is_done();
        let q = rad_reader.get_queue();
        let handle = std::thread::spawn(move || {
            let mut nrec_processed = 0_usize;
            while !rd.load(Ordering::SeqCst) {
                while let Some(meta_chunk) = q.pop() {
                    for c in meta_chunk.iter() {
                        nrec_processed += c.nrec as usize;
                        /*
                        println!("Chunk :: nbytes: {}, nrecs: {}", c.nbytes, c.nrec);
                        assert_eq!(c.nrec as usize, c.reads.len());
                        for (i, r) in c.reads.iter().take(10).enumerate() {
                            println!("record {i}: {:?}", r);
                        }
                        */
                    }
                }
            }
            nrec_processed
        });
        handles.push(handle);
    }

    // simple callback if we want to test one
    let header_offset = rad_reader.get_byte_offset();
    let pbar = ProgressBar::new(file_len - header_offset);
    pbar.set_style(
        ProgressStyle::with_template(
            "[{elapsed_precise}] {bar:40.cyan/blue} {pos:>7}/{len:7} {msg}",
        )
        .unwrap()
        .progress_chars("##-"),
    );
    pbar.set_draw_target(ProgressDrawTarget::stderr_with_hz(5));
    let cb = |new_bytes: u64, _new_rec: u64| {
        pbar.inc(new_bytes);
    };

    let _ = rad_reader.start_chunk_parsing(Some(cb)); //libradicl::readers::EMPTY_METACHUNK_CALLBACK);
    let mut total_processed = 0;
    for handle in handles {
        total_processed += handle.join().expect("The parsing thread panicked");
    }
    pbar.finish_with_message(format!(
        "finished parsing RAD file; processed {} total records\n",
        total_processed
    ));
    Ok(())
}
