use crate::element::reader::ElementReader;
use crate::element::Element;
use crate::lazy::binary::lazy_system_reader::{LazySystemReader, LazyValue};
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

pub struct LazyElementIterator<'iter, 'data> {
    lazy_reader: &'iter mut LazyReader<'data>,
}

impl<'iter, 'data> Iterator for LazyElementIterator<'iter, 'data> {
    type Item = IonResult<Element>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.lazy_reader.next() {
            Ok(None) => None,
            Ok(Some(lazy_value)) => Some(lazy_value.try_into()),
            Err(e) => Some(Err(e)),
        }
    }
}

impl<'data> ElementReader for LazyReader<'data> {
    type ElementIterator<'a> = LazyElementIterator<'a, 'data> where Self: 'a,;

    fn read_next_element(&mut self) -> IonResult<Option<Element>> {
        let lazy_value = match self.next()? {
            None => return Ok(None),
            Some(lazy_value) => lazy_value,
        };
        let element: Element = lazy_value.try_into()?;
        Ok(Some(element))
    }

    fn elements(&mut self) -> Self::ElementIterator<'_> {
        LazyElementIterator { lazy_reader: self }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::element::writer::ElementWriter;
    use crate::element::Element;
    use crate::lazy::value_ref::ValueRef;
    use crate::{
        ion_list, ion_sexp, ion_struct, BinaryWriterBuilder, Int, IonResult, IonType, IonWriter,
    };

    fn to_binary_ion(text_ion: &str) -> IonResult<Vec<u8>> {
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
        let ion_data = to_binary_ion(
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
        let data = &to_binary_ion(
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

    #[test]
    fn materialize() -> IonResult<()> {
        let data = &to_binary_ion(
            r#"
            [
                "yo",
                77,
                true,
                {name:"hi", name: "hello"},
            ]
            null.int
            (null null.string)
        "#,
        )?;
        let mut reader = LazyReader::new(data);
        let list: Element = ion_list![
            "yo",
            77,
            true,
            ion_struct! {
                "name": "hi",
                "name": "hello"
            }
        ]
        .into();
        assert_eq!(reader.read_next_element()?, Some(list));
        assert_eq!(
            reader.read_next_element()?,
            Some(Element::null(IonType::Int))
        );
        let sexp: Element = ion_sexp!(IonType::Null IonType::String).into();
        assert_eq!(reader.read_next_element()?, Some(sexp));
        assert_eq!(reader.read_next_element()?, None);
        Ok(())
    }
}
