use crate::binary::constants::v1_0::IVM;
use crate::element::reader::ElementReader;
use crate::element::Element;
use crate::lazy::binary::system::lazy_system_reader::LazySystemReader;
use crate::lazy::binary::system::lazy_value::LazyValue;
use crate::result::{decoding_error, decoding_error_raw};
use crate::IonResult;

/// A binary reader that only reads each value that it visits upon request (that is: lazily).
///
/// Each time [`LazyReader::next`] is called, the reader will advance to the next top-level value
/// in the input stream. Once positioned on a top-level value, users may visit nested values by
/// calling [`LazyValue::read`] and working with the resulting [`crate::lazy::value_ref::ValueRef`],
/// which may contain either a scalar value or a lazy container that may itself be traversed.
///
/// The values that the reader yields ([`LazyValue`],
/// [`LazySequence`](crate::lazy::binary::system::lazy_sequence::LazySequence), and
/// [`LazyStruct`](crate::lazy::binary::system::lazy_struct::LazyStruct)) are
/// immutable references to the data stream, and remain valid until [`LazyReader::next`] is called
/// again to advance the reader to the next top level value. This means that these references can
/// be stored, read, and re-read as long as the reader remains on the same top-level value.
/// ```
///# use ion_rs::IonResult;
///# fn main() -> IonResult<()> {
///
/// // Construct an Element and serialize it as binary Ion.
/// use ion_rs::element::Element;
/// use ion_rs::ion_list;
/// use ion_rs::lazy::binary::lazy_reader::LazyReader;
///
/// let element: Element = ion_list! [10, 20, 30].into();
/// let binary_ion = element.to_binary()?;
///
/// let mut lazy_reader = LazyReader::new(&binary_ion)?;
///
/// // Get the first value from the stream and confirm that it's a list.
/// let lazy_list = lazy_reader.expect_next()?.read()?.expect_list()?;
///
/// // Visit the values in the list
/// let mut sum = 0;
/// for lazy_value in &lazy_list {
///     // Read each lazy value in the lazy list as an int (i64) and
///     // add it to the running total
///     sum += lazy_value?.read()?.expect_i64()?;
/// }
///
/// assert_eq!(sum, 60);
///
/// // Note that we can re-read any of the lazy values. Here we'll step into the list again and
/// // read the first child value.
/// let first_int = lazy_list.iter().next().unwrap()?.read()?.expect_i64()?;
/// assert_eq!(first_int, 10);
///
///# Ok(())
///# }
/// ```
pub struct LazyReader<'data> {
    system_reader: LazySystemReader<'data>,
}

impl<'data> LazyReader<'data> {
    pub fn new(ion_data: &'data [u8]) -> IonResult<LazyReader<'data>> {
        if ion_data.len() < IVM.len() {
            return decoding_error("input is too short to be recognized as Ion");
        } else if ion_data[..IVM.len()] != IVM {
            return decoding_error("input does not begin with an Ion version marker");
        }

        let system_reader = LazySystemReader::new(ion_data);
        Ok(LazyReader { system_reader })
    }

    /// Returns the next top-level value in the input stream as `Ok(Some(lazy_value))`.
    /// If there are no more top-level values in the stream, returns `Ok(None)`.
    /// If the next value is incomplete (that is: only part of it is in the input buffer) or if the
    /// input buffer contains invalid data, returns `Err(ion_error)`.
    pub fn next<'top>(&'top mut self) -> IonResult<Option<LazyValue<'top, 'data>>> {
        self.system_reader.next_value()
    }

    /// Like [`Self::next`], but returns an `IonError` if there are no more values in the stream.
    pub fn expect_next<'top>(&'top mut self) -> IonResult<LazyValue<'top, 'data>> {
        self.next()?
            .ok_or_else(|| decoding_error_raw("expected another top-level value"))
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
        let mut reader = LazyReader::new(&ion_data)?;
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
        let mut reader = LazyReader::new(data)?;

        let first_value = reader.expect_next()?;
        let list = first_value.read()?.expect_list()?;
        let lazy_values = list.iter().collect::<IonResult<Vec<_>>>()?;

        assert_eq!(lazy_values[1].read()?.expect_int()?, Int::from(77));
        assert!(lazy_values[2].read()?.expect_bool()?);
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
        let mut reader = LazyReader::new(data)?;
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
