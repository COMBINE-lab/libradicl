use anyhow;
use libradicl::rad_types;
use std::io::BufReader;

fn main() -> anyhow::Result<()> {
    let fname = std::env::args().nth(1).expect("input filename");
    {
        let f = std::fs::File::open(&fname)?;
        let mut ifile = BufReader::new(f);
        let h = rad_types::RadHeader::from_bytes(&mut ifile)?;

        if let Ok(summary) = h.summary(None) {
            println!("{}", summary);
        }

        let ts = rad_types::TagSection::from_bytes(&mut ifile)?;
        println!("File-level tags: {ts:?}");

        let ts = rad_types::TagSection::from_bytes(&mut ifile)?;
        println!("Read-level tags: {ts:?}");

        let ts = rad_types::TagSection::from_bytes(&mut ifile)?;
        println!("Alignment-level tags: {ts:?}");
    }

    println!("\n");

    {
        let f = std::fs::File::open(&fname)?;
        let mut ifile = BufReader::new(f);
        let p = rad_types::RadPrelude::from_bytes(&mut ifile)?;
        if let Ok(summary) = p.summary(None) {
            println!("{}", summary);
        }
    }
    Ok(())
}
