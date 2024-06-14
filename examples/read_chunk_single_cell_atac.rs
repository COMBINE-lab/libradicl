use std::fs::File;
use std::io::BufReader;
use libradicl::{
    utils,
    header::{RadPrelude},
    record::{AtacSeqReadRecord, AtacSeqRecordContext},
};
use libradicl::chunk::Chunk;

fn main() {
    let f = File::open("/fs/nexus-projects/scATAC-seq/chromap/peaks_chromap_analysis/piscem_output/10k_entire_k23_psc_off=true_ps_skip=false_thr=0.7/map.rad");
    let mut ifile = BufReader::new(f.unwrap());
    let p = RadPrelude::from_bytes(&mut ifile).unwrap();
    if let Ok(summary) = p.summary(None) {
        println!("{}", summary);
    }
    let tag_map = p.file_tags.parse_tags_from_bytes(&mut ifile).unwrap();
    println!("tag map {:?}\n", tag_map);
    println!("num chunks = {:?}\n", p.hdr.num_chunks());
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

}
