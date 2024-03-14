#![allow(non_camel_case_types)]

use crate::element::reader::ElementReader;
use crate::element::Element;
use crate::lazy::any_encoding::AnyEncoding;
use crate::lazy::decoder::LazyDecoder;
use crate::lazy::encoding::{BinaryEncoding_1_0, TextEncoding_1_0, TextEncoding_1_1};
use crate::lazy::streaming_raw_reader::IonInput;
use crate::lazy::system_reader::{
    LazySystemAnyReader, LazySystemBinaryReader, LazySystemReader, LazySystemTextReader_1_1,
};
use crate::lazy::text::raw::v1_1::reader::MacroAddress;
use crate::lazy::value::LazyValue;
use crate::result::IonFailure;
use crate::{IonError, IonResult};

/// A binary reader that only reads each value that it visits upon request (that is: lazily).
///
/// Each time [`LazyApplicationReader::next`] is called, the reader will advance to the next top-level value
/// in the input stream. Once positioned on a top-level value, users may visit nested values by
/// calling [`LazyValue::read`] and working with the resulting [`crate::lazy::value_ref::ValueRef`],
/// which may contain either a scalar value or a lazy container that may itself be traversed.
///
/// The values that the reader yields ([`LazyValue`],
/// [`LazyList`](crate::lazy::sequence::LazyList), [`LazySExp`](crate::lazy::sequence::LazySExp),
/// and [`LazyStruct`](crate::lazy::struct::LazyStruct)) are immutable references to the data
/// stream, and remain valid until [`LazyApplicationReader::next`] is called again to advance the
/// reader to the next top level value. This means that these references can be stored, read, and
/// re-read as long as the reader remains on the same top-level value.
/// ```
///# use ion_rs::IonResult;
///# fn main() -> IonResult<()> {
///
/// // Construct an Element and serialize it as binary Ion.
/// use ion_rs::{Element, ion_list};
/// use ion_rs::lazy::reader::LazyBinaryReader;;
///
/// let element: Element = ion_list! [10, 20, 30].into();
/// let binary_ion = element.to_binary()?;
///
/// let mut lazy_reader = LazyBinaryReader::new(binary_ion)?;
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
pub struct LazyApplicationReader<Encoding: LazyDecoder, Input: IonInput> {
    system_reader: LazySystemReader<Encoding, Input>,
}

pub(crate) enum NextApplicationValue<'top, D: LazyDecoder> {
    ApplicationValue(LazyValue<'top, D>),
    SystemValue,
    EndOfStream,
}

impl<Encoding: LazyDecoder, Input: IonInput> LazyApplicationReader<Encoding, Input> {
    /// Returns the next top-level value in the input stream as `Ok(Some(lazy_value))`.
    /// If there are no more top-level values in the stream, returns `Ok(None)`.
    /// If the next value is incomplete (that is: only part of it is in the input buffer) or if the
    /// input buffer contains invalid data, returns `Err(ion_error)`.
    ///
    /// <div class="warning">A warning when reading from growing input streams</div>
    ///
    /// If reader's [`IonInput`] indicates that the stream is complete, the reader will
    /// also consider any remaining available data to be complete. In select circumstances--namely,
    /// when reading top-level text Ion scalars or keywords from an input stream that continues
    /// to grow over time--this can lead to unexpected results.
    ///
    /// For example: consider the case of following a growing file (as `tail -f` would do).
    /// When the reader encounters the (temporary!) end of the file and a [`std::io::Read::read`]
    /// operation returns `Ok(0)`, the reader would consider its input buffer's contents to be final.
    /// This has the potential to result in **incorrect data** when the data that was available
    /// happened to be legal Ion data. Here are some examples:
    ///
    /// | On `Ok(0)`, `next()` returns... | A later call to `next()` returns... |
    /// | ------------------------------- | ------------------------------------|
    /// | `false`                         | `_teeth`                            |
    /// | `123`                           | `456`                               |
    /// | `null`                          | `.struct`                           |
    /// | `$ion`                          | `_1_0`                              |
    /// | `2024-03-14T`                   | `12:00:30.000Z`                     |
    /// | `// Discarded start of comment` | ` with words treated as symbols`    |
    ///
    /// This is not an issue in binary Ion as incomplete items can always be detected. When following
    /// a text Ion data source, it is recommended that you only trust values returned after an
    /// `Ok(container_value)`, as incomplete containers can be detected reliably. This should only
    /// be attempted when you have control over the format of the data being read.
    #[allow(clippy::should_implement_trait)]
    // ^-- Clippy objects that the method name `next` will be confused for `Iterator::next()`
    pub fn next(&mut self) -> IonResult<Option<LazyValue<Encoding>>> {
        self.system_reader.next_value()
    }

    /// Like [`Self::next`], but returns an `IonError` if there are no more values in the stream.
    pub fn expect_next(&mut self) -> IonResult<LazyValue<Encoding>> {
        self.next()?
            .ok_or_else(|| IonError::decoding_error("expected another top-level value"))
    }
}

pub type LazyBinaryReader<Input> = LazyApplicationReader<BinaryEncoding_1_0, Input>;
pub type LazyTextReader_1_0<Input> = LazyApplicationReader<TextEncoding_1_0, Input>;
pub type LazyTextReader_1_1<Input> = LazyApplicationReader<TextEncoding_1_1, Input>;
pub type LazyReader<Input> = LazyApplicationReader<AnyEncoding, Input>;

impl<Input: IonInput> LazyReader<Input> {
    pub fn new(ion_data: Input) -> LazyReader<Input> {
        let system_reader = LazySystemAnyReader::new(ion_data);
        LazyApplicationReader { system_reader }
    }
}

impl<Input: IonInput> LazyBinaryReader<Input> {
    pub fn new(ion_data: Input) -> IonResult<LazyBinaryReader<Input>> {
        let system_reader = LazySystemBinaryReader::new(ion_data);
        Ok(LazyApplicationReader { system_reader })
    }
}

impl<Input: IonInput> LazyTextReader_1_1<Input> {
    pub fn new(ion_data: Input) -> IonResult<LazyTextReader_1_1<Input>> {
        let system_reader = LazySystemTextReader_1_1::new(ion_data);
        Ok(LazyApplicationReader { system_reader })
    }

    // Temporary method for defining/testing templates.
    // TODO: Remove this when the reader can understand 1.1 encoding directives.
    pub fn register_template(&mut self, template_definition: &str) -> IonResult<MacroAddress> {
        self.system_reader
            .expanding_reader
            .register_template(template_definition)
    }
}

pub struct LazyElementIterator<'iter, Encoding: LazyDecoder, Input: IonInput> {
    lazy_reader: &'iter mut LazyApplicationReader<Encoding, Input>,
}

impl<'iter, Encoding: LazyDecoder, Input: IonInput> Iterator
    for LazyElementIterator<'iter, Encoding, Input>
{
    type Item = IonResult<Element>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.lazy_reader.next() {
            Ok(None) => None,
            Ok(Some(lazy_value)) => Some(lazy_value.try_into()),
            Err(e) => Some(Err(e)),
        }
    }
}

impl<Encoding: LazyDecoder, Input: IonInput> ElementReader
    for LazyApplicationReader<Encoding, Input>
{
    type ElementIterator<'a> = LazyElementIterator<'a, Encoding, Input> where Self: 'a,;

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
    use crate::element::writer::ElementWriter;
    use crate::element::Element;
    use crate::lazy::value_ref::ValueRef;
    use crate::{
        ion_list, ion_sexp, ion_struct, BinaryWriterBuilder, Int, IonResult, IonType, IonWriter,
    };

    use super::*;

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
        let mut reader = LazyBinaryReader::new(ion_data)?;
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
        let data = to_binary_ion(
            r#"
            [
                "yo",
                77,
                true,
                {name:"hi", name: "hello"},
            ]
        "#,
        )?;
        let mut reader = LazyBinaryReader::new(data)?;

        let first_value = reader.expect_next()?;
        let list = first_value.read()?.expect_list()?;
        let lazy_values = list.iter().collect::<IonResult<Vec<_>>>()?;

        assert_eq!(lazy_values[1].read()?.expect_int()?, Int::from(77));
        assert!(lazy_values[2].read()?.expect_bool()?);
        Ok(())
    }

    #[test]
    fn materialize() -> IonResult<()> {
        let data = to_binary_ion(
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
        let mut reader = LazyBinaryReader::new(data)?;
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
