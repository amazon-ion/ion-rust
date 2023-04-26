use crate::lazy::lazy_system_reader::{LazySystemReader, LazyValue};
use crate::IonResult;

pub struct LazyReader<'data> {
    system_reader: LazySystemReader<'data>,
}

impl<'data> LazyReader<'data> {
    pub fn new(ion_data: &'data [u8]) -> LazyReader<'data> {
        let system_reader = LazySystemReader::new(ion_data);
        LazyReader { system_reader }
    }

    pub fn next<'top>(&'top mut self) -> IonResult<Option<LazyValue<'top, 'data>>> {
        self.system_reader.next_user_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::element::writer::ElementWriter;
    use crate::element::Element;
    use crate::lazy::value_ref::ValueRef;
    use crate::{BinaryWriterBuilder, Int, IonResult, IonWriter};

    fn to_10n(text_ion: &str) -> IonResult<Vec<u8>> {
        let mut buffer = Vec::new();
        let mut writer = BinaryWriterBuilder::default().build(&mut buffer)?;
        let elements = Element::read_all(text_ion)?;
        writer.write_elements(&elements)?;
        writer.flush()?;
        drop(writer);
        Ok(buffer)
    }

    #[test]
    fn sequence_iter() -> IonResult<()> {
        let ion_data = to_10n(
            r#"
                (foo baz baz)
                (1 2 3)
                (a b c)
        "#,
        )?;
        let mut reader = LazyReader::new(&ion_data);
        // For each top-level value...
        while let Some(top_level_value) = reader.next()? {
            // ...see if it's an S-expression...
            if let ValueRef::SExp(sexp) = top_level_value.read()? {
                //...and if it is, print its child values.
                for lazy_value in &sexp {
                    println!("{:?}", lazy_value?.read()?)
                }
            }
        }
        Ok(())
    }

    #[test]
    fn test_rewind() -> IonResult<()> {
        let data = &to_10n(
            r#"
            [
                "yo",
                77,
                true,
                {name:"hi", name: "hello"},
            ]
        "#,
        )?;
        let mut reader = LazyReader::new(data);

        let first_value = reader.next()?.expect("one top level value");
        let list = first_value.read()?.expect_list()?;
        let lazy_values = list.iter().collect::<IonResult<Vec<_>>>()?;

        assert_eq!(lazy_values[1].read()?.expect_int()?, Int::from(77));
        assert_eq!(lazy_values[2].read()?.expect_bool()?, true);
        Ok(())
    }
}
