use crate::lazy_reader::lazy_system_reader::{LazySystemReader, LazyValue};
use crate::lazy_reader::system_stream_item::SystemStreamItem;
use crate::IonResult;

pub struct LazyReader<'a> {
    system_reader: LazySystemReader<'a>,
}

impl<'a> LazyReader<'a> {
    pub fn new(ion_data: &'a [u8]) -> LazyReader<'a> {
        let system_reader = LazySystemReader::new(ion_data);
        LazyReader { system_reader }
    }

    pub fn next(&mut self) -> IonResult<Option<LazyValue<'a>>> {
        let value: Option<LazyValue> = loop {
            match self.system_reader.next()? {
                SystemStreamItem::VersionMarker(_, _) | SystemStreamItem::SymbolTable(_) => {}
                SystemStreamItem::Value(value) => break Some(value),
                SystemStreamItem::Nothing => break None,
            }
        };
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::element::writer::ElementWriter;
    use crate::element::Element;
    use crate::lazy_reader::value_ref::ValueRef;
    use crate::{BinaryWriterBuilder, IonResult, IonWriter};

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
        let list = reader
            .next()?
            .expect("one top level value")
            .read()?
            .expect_list()?;

        let values = list.iter().collect::<IonResult<Vec<_>>>()?;

        println!("=== Replay second and third values ===");
        println!("{:?}", values[1].read()?);
        println!("{:?}", values[2].read()?);
        Ok(())
    }
}
