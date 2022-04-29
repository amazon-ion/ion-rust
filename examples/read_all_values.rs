use ion_rs::raw_reader::RawStreamItem;
use ion_rs::result::IonResult;
use ion_rs::StreamReader;
use ion_rs::{IonDataSource, IonType, RawBinaryReader};
use std::fs::File;
use std::process::exit;

fn main() -> IonResult<()> {
    let args: Vec<String> = std::env::args().collect();
    let path = args.get(1).unwrap_or_else(|| {
        eprintln!("USAGE:\n\n    {} [Binary Ion file]\n", args.get(0).unwrap());
        eprintln!("No input file was specified.");
        exit(1);
    });

    let file = File::open(path)?;
    let buf_reader = std::io::BufReader::new(file);
    let mut cursor = RawBinaryReader::new(buf_reader);
    let number_of_values = read_all_values(&mut cursor)?;
    println!("Read {} values", number_of_values);
    Ok(())
}

// Visits each value in the stream recursively, reading each scalar into a native Rust type.
// Prints the total number of values read upon completion.
fn read_all_values<R: IonDataSource>(cursor: &mut RawBinaryReader<R>) -> IonResult<usize> {
    use IonType::*;
    use RawStreamItem::{Nothing, Null as NullValue, Value, VersionMarker};
    let mut count: usize = 0;
    loop {
        match cursor.next()? {
            VersionMarker(_major, _minor) => {}
            NullValue(_ion_type) => {
                count += 1;
                continue;
            }
            Value(ion_type) => {
                count += 1;
                match ion_type {
                    Struct | List | SExpression => cursor.step_in()?,
                    String => {
                        let _text = cursor.map_string(|_s| ())?;
                    }
                    Symbol => {
                        let _symbol_id = cursor.read_symbol()?;
                    }
                    Integer => {
                        let _int = cursor.read_i64()?;
                    }
                    Float => {
                        let _float = cursor.read_f64()?;
                    }
                    Decimal => {
                        let _decimal = cursor.read_decimal()?;
                    }
                    Timestamp => {
                        let _timestamp = cursor.read_timestamp()?;
                    }
                    Boolean => {
                        let _boolean = cursor.read_bool()?;
                    }
                    Blob => {
                        let _blob = cursor.map_blob(|_b| ())?;
                    }
                    Clob => {
                        let _clob = cursor.map_clob(|_c| ())?;
                    }
                    Null => {}
                }
            }
            Nothing if cursor.depth() > 0 => {
                cursor.step_out()?;
            }
            _ => break,
        }
    }
    Ok(count)
}
