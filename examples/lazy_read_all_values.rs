use ion_rs::lazy::lazy_reader::LazyReader;
use ion_rs::lazy::lazy_system_reader::{LazySequence, LazyStruct, LazyValue};
use ion_rs::lazy::value_ref::ValueRef;
use ion_rs::IonResult;
use memmap::MmapOptions;
use std::fs::File;
use std::process::exit;

fn main() -> IonResult<()> {
    let args: Vec<String> = std::env::args().collect();
    let path = args.get(1).unwrap_or_else(|| {
        eprintln!("USAGE:\n\n    {} [Binary Ion file]\n", args.get(0).unwrap());
        eprintln!("No mode was specified.");
        exit(1);
    });

    let file = File::open(path).unwrap();

    // This example uses `mmap` so we can use either the blocking reader (which reads from an
    // io::BufRead) or the non-blocking reader (which reads from an AsRef<[u8]>).
    let mmap = unsafe { MmapOptions::new().map(&file).unwrap() };

    // Treat the mmap as a byte array.
    let ion_data: &[u8] = &mmap[..];

    let mut reader = LazyReader::new(ion_data);
    let mut count = 0;
    while let Some(lazy_value) = reader.next()? {
        count += read_value(&lazy_value)?;
    }
    println!("Read {} values.", count);
    Ok(())
}

fn read_value(lazy_value: &LazyValue) -> IonResult<usize> {
    use ValueRef::*;
    let child_count = match lazy_value.read()? {
        List(s) | SExp(s) => read_sequence(&s)?,
        Struct(s) => read_struct(&s)?,
        _ => 0,
    };
    Ok(1 + child_count)
}

fn read_sequence(lazy_sequence: &LazySequence) -> IonResult<usize> {
    let mut count = 0;
    for value in lazy_sequence {
        count += read_value(&value?)?;
    }
    Ok(count)
}

fn read_struct(lazy_struct: &LazyStruct) -> IonResult<usize> {
    let mut count = 0;
    for field in lazy_struct {
        count += read_value(&field?.value())?;
    }
    Ok(count)
}
