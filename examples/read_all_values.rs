use ion_rs::binary::non_blocking::raw_binary_reader::RawBinaryReader;
use ion_rs::raw_reader::RawStreamItem;
use ion_rs::result::IonResult;
use ion_rs::{BlockingRawBinaryReader, IonType, RawReader};
use memmap::MmapOptions;
use std::fs::File;
use std::process::exit;

fn main() -> IonResult<()> {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).unwrap_or_else(|| {
        eprintln!("USAGE:\n\n    {} [Binary Ion file]\n", args.get(0).unwrap());
        eprintln!("No mode was specified.");
        exit(1);
    });
    let path = args.get(2).unwrap_or_else(|| {
        eprintln!("USAGE:\n\n    {} [Binary Ion file]\n", args.get(0).unwrap());
        eprintln!("No input file was specified.");
        exit(2);
    });
    let file = File::open(path).unwrap();

    // This example uses `mmap` so we can use either the blocking reader (which reads from an
    // io::BufRead) or the non-blocking reader (which reads from an AsRef<[u8]>).
    let mmap = unsafe { MmapOptions::new().map(&file).unwrap() };

    // Treat the mmap as a byte array.
    let ion_data: &[u8] = &mmap[..];

    if mode == "blocking" {
        let mut reader = BlockingRawBinaryReader::new(ion_data)?;
        let number_of_values = read_all_values(&mut reader)?;
        println!("Blocking: read {} values", number_of_values);
    } else if mode == "nonblocking" {
        let mut reader = RawBinaryReader::new(ion_data);
        let number_of_values = read_all_values(&mut reader)?;
        println!("Non-blocking: read {} values", number_of_values);
    } else {
        eprintln!("Unsupported `mode`: {}.", mode);
        exit(3);
    }

    Ok(())
}

// Visits each value in the stream recursively, reading each scalar into a native Rust type.
// Prints the total number of values read upon completion.
fn read_all_values<R: RawReader>(reader: &mut R) -> IonResult<usize> {
    use IonType::*;
    use RawStreamItem::{Nothing, Null as NullValue, Value, VersionMarker};
    let mut count: usize = 0;
    loop {
        match reader.next()? {
            VersionMarker(_major, _minor) => {}
            NullValue(_ion_type) => {
                count += 1;
                continue;
            }
            Value(ion_type) => {
                count += 1;
                match ion_type {
                    Struct | List | SExp => reader.step_in()?,
                    String => {
                        let _string = reader.read_str()?;
                    }
                    Symbol => {
                        let _symbol_id = reader.read_symbol()?;
                    }
                    Int => {
                        let _int = reader.read_i64()?;
                    }
                    Float => {
                        let _float = reader.read_f64()?;
                    }
                    Decimal => {
                        let _decimal = reader.read_decimal()?;
                    }
                    Timestamp => {
                        let _timestamp = reader.read_timestamp()?;
                    }
                    Bool => {
                        let _boolean = reader.read_bool()?;
                    }
                    Blob => {
                        let _blob = reader.read_blob()?;
                    }
                    Clob => {
                        let _clob = reader.read_clob()?;
                    }
                    Null => {}
                }
            }
            Nothing if reader.depth() > 0 => {
                reader.step_out()?;
            }
            _ => break,
        }
    }
    Ok(count)
}
