#[cfg(not(feature = "experimental-lazy-reader"))]
fn main() {
    println!("This example requires the 'experimental-lazy-reader' feature to work.");
}

#[cfg(feature = "experimental-lazy-reader")]
use ion_rs::IonResult;

#[cfg(feature = "experimental-lazy-reader")]
fn main() -> IonResult<()> {
    lazy_reader_example::read_all_values()
}

#[cfg(feature = "experimental-lazy-reader")]
mod lazy_reader_example {

    use ion_rs::lazy::binary::lazy_reader::LazyReader;
    use ion_rs::lazy::binary::system::lazy_sequence::LazySequence;
    use ion_rs::lazy::binary::system::lazy_struct::LazyStruct;
    use ion_rs::lazy::binary::system::lazy_value::LazyValue;
    use ion_rs::lazy::value_ref::ValueRef;
    use ion_rs::IonResult;
    use memmap::MmapOptions;
    use std::fs::File;
    use std::process::exit;

    pub fn read_all_values() -> IonResult<()> {
        let args: Vec<String> = std::env::args().collect();
        let path = args.get(1).unwrap_or_else(|| {
            eprintln!("USAGE:\n\n    {} [Binary Ion file]\n", args.get(0).unwrap());
            eprintln!("No mode was specified.");
            exit(1);
        });

        let file = File::open(path).unwrap();

        // This example uses `mmap` so we can view the entire input file as a `&[u8]`.
        let mmap = unsafe { MmapOptions::new().map(&file).unwrap() };
        let ion_data: &[u8] = &mmap[..];

        // We're going to recursively visit and read every value in the input stream, counting
        // them as we go.
        let mut count = 0;
        let mut reader = LazyReader::new(ion_data)?;
        while let Some(lazy_value) = reader.next()? {
            count += count_value_and_children(&lazy_value)?;
        }
        println!("Read {} values.", count);
        Ok(())
    }

    // Counts scalar values as 1 and container values as (the number of children) + 1.
    fn count_value_and_children(lazy_value: &LazyValue) -> IonResult<usize> {
        use ValueRef::*;
        let child_count = match lazy_value.read()? {
            List(s) | SExp(s) => count_sequence_children(&s)?,
            Struct(s) => count_struct_children(&s)?,
            _ => 0,
        };
        Ok(1 + child_count)
    }

    fn count_sequence_children(lazy_sequence: &LazySequence) -> IonResult<usize> {
        let mut count = 0;
        for value in lazy_sequence {
            count += count_value_and_children(&value?)?;
        }
        Ok(count)
    }

    fn count_struct_children(lazy_struct: &LazyStruct) -> IonResult<usize> {
        let mut count = 0;
        for field in lazy_struct {
            count += count_value_and_children(field?.value())?;
        }
        Ok(count)
    }
}
