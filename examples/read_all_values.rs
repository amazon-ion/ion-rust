#[cfg(feature = "experimental")]
use ion_rs::IonResult;

#[cfg(not(feature = "experimental"))]
fn main() {
    println!("This example requires the 'experimental' feature to work; try again with `--features experimental`");
}

#[cfg(feature = "experimental")]
fn main() -> IonResult<()> {
    lazy_reader_example::read_all_values()
}

#[cfg(feature = "experimental")]
mod lazy_reader_example {
    use std::fs::File;
    use std::process::exit;

    use ion_rs::{AnyEncoding, Decoder, IonResult, LazyStruct, LazyValue, Reader, ValueRef};

    pub fn read_all_values() -> IonResult<()> {
        let args: Vec<String> = std::env::args().collect();
        let path = args.get(1).unwrap_or_else(|| {
            eprintln!(
                "USAGE:\n\n    {} [Binary Ion file]\n",
                args.first().unwrap()
            );
            eprintln!("No mode was specified.");
            exit(1);
        });

        let file = File::open(path).unwrap();
        let mut reader = Reader::new(AnyEncoding, file)?;
        // We're going to recursively visit and read every value in the input stream, counting
        // them as we go.
        let mut count = 0;
        while let Some(lazy_value) = reader.next()? {
            count += count_value_and_children(&lazy_value)?;
        }
        println!("Read {count} values.");
        Ok(())
    }

    // Counts scalar values as 1 and container values as (the number of children) + 1.
    fn count_value_and_children<D: Decoder>(lazy_value: &LazyValue<D>) -> IonResult<usize> {
        use ValueRef::*;
        let child_count = match lazy_value.read()? {
            List(s) => count_sequence_children(s.iter())?,
            SExp(s) => count_sequence_children(s.iter())?,
            Struct(s) => count_struct_children(&s)?,
            _ => 0,
        };
        Ok(1 + child_count)
    }

    fn count_sequence_children<'a, D: Decoder>(
        lazy_sequence: impl Iterator<Item = IonResult<LazyValue<'a, D>>>,
    ) -> IonResult<usize> {
        let mut count = 0;
        for value in lazy_sequence {
            count += count_value_and_children(&value?)?;
        }
        Ok(count)
    }

    fn count_struct_children<D: Decoder>(lazy_struct: &LazyStruct<D>) -> IonResult<usize> {
        let mut count = 0;
        for field in lazy_struct {
            count += count_value_and_children(&field?.value())?;
        }
        Ok(count)
    }
}
