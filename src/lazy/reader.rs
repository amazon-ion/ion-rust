#![allow(non_camel_case_types)]

use crate::element::reader::ElementReader;
use crate::element::Element;
use crate::lazy::decoder::Decoder;
use crate::lazy::streaming_raw_reader::IonInput;
use crate::lazy::system_reader::SystemReader;
use crate::lazy::value::LazyValue;
use crate::read_config::ReadConfig;
use crate::result::IonFailure;
use crate::{try_or_some_err, IonError, IonResult};

/// An Ion reader that only reads each value that it visits upon request (that is: lazily).
///
/// Each time [`Reader::next`] is called, the reader will advance to the next top-level value
/// in the input stream. Once positioned on a top-level value, users may visit nested values by
/// calling [`LazyValue::read`] and working with the resulting [`crate::lazy::value_ref::ValueRef`],
/// which may contain either a scalar value or a lazy container that may itself be traversed.
///
/// The values that the reader yields ([`LazyValue`],
/// [`LazyList`](crate::lazy::sequence::LazyList), [`LazySExp`](crate::lazy::sequence::LazySExp),
/// and [`LazyStruct`](crate::lazy::r#struct::LazyStruct)) are immutable references to the data
/// stream, and remain valid until [`Reader::next`] is called again to advance the
/// reader to the next top level value. This means that these references can be stored, read, and
/// re-read as long as the reader remains on the same top-level value.
/// ```
///# use ion_rs::IonResult;
///# #[cfg(feature = "experimental-reader-writer")]
///# fn main() -> IonResult<()> {
///
/// // Construct an Element and serialize it as binary Ion.
/// use ion_rs::{Element, ion_list, Reader};
/// use ion_rs::v1_0::Binary;
///
/// let element: Element = ion_list! [10, 20, 30].into();
/// let binary_ion = element.encode_as(Binary)?;
///
/// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
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
///# #[cfg(not(feature = "experimental-reader-writer"))]
///# fn main() -> IonResult<()> { Ok(()) }
/// ```
pub struct Reader<Encoding: Decoder, Input: IonInput> {
    system_reader: SystemReader<Encoding, Input>,
}

impl<Encoding: Decoder, Input: IonInput> Reader<Encoding, Input> {
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
    pub fn next(&mut self) -> IonResult<Option<LazyValue<'_, Encoding>>> {
        self.system_reader.next_value()
    }

    /// Like [`Self::next`], but returns an `IonError` if there are no more values in the stream.
    pub fn expect_next(&mut self) -> IonResult<LazyValue<'_, Encoding>> {
        self.next()?
            .ok_or_else(|| IonError::decoding_error("expected another top-level value"))
    }
}

impl<Encoding: Decoder, Input: IonInput> Reader<Encoding, Input> {
    pub fn new(
        config: impl Into<ReadConfig<Encoding>>,
        ion_data: Input,
    ) -> IonResult<Reader<Encoding, Input>> {
        let system_reader = SystemReader::new(config, ion_data);
        Ok(Reader { system_reader })
    }
}

use crate::lazy::expanded::lazy_element::LazyElement;
use crate::lazy::{expanded::template::TemplateMacro, text::raw::v1_1::reader::MacroAddress};

impl<Encoding: Decoder, Input: IonInput> Reader<Encoding, Input> {
    // TODO: Remove this when the reader can understand 1.1 encoding directives.
    pub fn register_template_src(&mut self, template_definition: &str) -> IonResult<MacroAddress> {
        self.system_reader
            .expanding_reader
            .register_template_src(template_definition)
    }

    pub fn register_template(&mut self, template_macro: TemplateMacro) -> IonResult<MacroAddress> {
        self.system_reader
            .expanding_reader
            .register_template(template_macro)
    }
}

impl<Encoding: Decoder, Input: IonInput> Iterator for Reader<Encoding, Input> {
    type Item = IonResult<LazyElement<Encoding>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next() {
            Ok(None) => None,
            Ok(Some(lazy_value)) => Some(Ok(lazy_value.to_owned())),
            Err(e) => Some(Err(e)),
        }
    }
}

pub struct LazyElementIterator<'iter, Encoding: Decoder, Input: IonInput> {
    lazy_reader: &'iter mut Reader<Encoding, Input>,
}

impl<Encoding: Decoder, Input: IonInput> Iterator for LazyElementIterator<'_, Encoding, Input> {
    type Item = IonResult<LazyElement<Encoding>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.lazy_reader.next() {
            Ok(None) => None,
            Ok(Some(lazy_value)) => Some(Ok(lazy_value.to_owned())),
            Err(e) => Some(Err(e)),
        }
    }
}

/// Extension methods for iterators that return an `IonResult`.
///
/// These methods are analogous to methods that already exist on `Iterator`,
/// but automatically handle situations where the input `IonResult` is an `Err`
/// sparing the user from writing more boilerplate.
pub trait IonResultIterExt<Item>: Iterator<Item = IonResult<Item>> {
    /// Filters a stream of `IonResult` values.
    ///
    /// If the current value is an `Err`, it is passed through as that error.
    /// If the current value is `Ok` but the predicate does not approve its contents,
    /// the value is discarded.
    /// Otherwise, passes the value through without modification.
    fn try_filter<FalliblePredicate>(
        &mut self,
        mut predicate: FalliblePredicate,
    ) -> impl Iterator<Item = IonResult<Item>>
    where
        FalliblePredicate: FnMut(&Item) -> IonResult<bool>,
    {
        self.filter_map(move |result| {
            let element = match result {
                Ok(element) => element,
                Err(e) => return Some(Err(e)),
            };

            match predicate(&element) {
                Ok(true) => Some(Ok(element)),
                Ok(false) => None,
                Err(e) => Some(Err(e)),
            }
        })
    }

    /// Maps a stream of `IonResult<Item>` values to `IonResult<Output>` items.
    ///
    /// If the current value is an `Err`, it is passed through as that error.
    /// If the current value is `Ok`, applies the `map_fn` and passes its result through.
    fn try_map<MapFn, Output>(
        &mut self,
        mut map_fn: MapFn,
    ) -> impl Iterator<Item = IonResult<Output>>
    where
        MapFn: FnMut(&Item) -> IonResult<Output>,
    {
        self.map(move |result| {
            let element = result?;
            Ok(map_fn(&element)?)
        })
    }

    /// Similar to [`try_filter`] and [`try_map`] above, but performs both operations in a single step.
    fn try_filter_map<'a, MappingPredicate, Output>(
        &'a mut self,
        mut mapping_predicate: MappingPredicate,
    ) -> impl Iterator<Item = IonResult<Output>>
    where
        MappingPredicate: FnMut(&Item) -> IonResult<Option<Output>> + 'a,
    {
        self.filter_map(move |item_result| {
            let item = try_or_some_err!(item_result);
            mapping_predicate(&item).transpose()
        })
    }
}

impl<Item, T> IonResultIterExt<Item> for T
where
    T: Iterator<Item = IonResult<Item>>,
{
    // Uses default implementations
}

pub struct ElementIterator<'iter, Encoding: Decoder, Input: IonInput> {
    lazy_reader: &'iter mut Reader<Encoding, Input>,
}

impl<Encoding: Decoder, Input: IonInput> Iterator for ElementIterator<'_, Encoding, Input> {
    type Item = IonResult<Element>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.lazy_reader.next() {
            Ok(None) => None,
            Ok(Some(lazy_value)) => Some(lazy_value.try_into()),
            Err(e) => Some(Err(e)),
        }
    }
}

impl<Encoding: Decoder, Input: IonInput> ElementReader for Reader<Encoding, Input> {
    type ElementIterator<'a>
        = ElementIterator<'a, Encoding, Input>
    where
        Self: 'a;

    fn read_next_element(&mut self) -> IonResult<Option<Element>> {
        let lazy_value = match self.next()? {
            None => return Ok(None),
            Some(lazy_value) => lazy_value,
        };
        let element: Element = lazy_value.try_into()?;
        Ok(Some(element))
    }

    fn elements(&mut self) -> Self::ElementIterator<'_> {
        ElementIterator { lazy_reader: self }
    }
}

#[cfg(test)]
mod tests {
    use crate::element::element_writer::ElementWriter;
    use crate::element::Element;
    use crate::lazy::encoder::writer::Writer;
    use crate::lazy::encoding::BinaryEncoding_1_0;
    use crate::lazy::text::raw::v1_1::reader::MacroAddress;
    use crate::lazy::value_ref::ValueRef;
    use crate::write_config::WriteConfig;
    use crate::{ion_list, ion_sexp, ion_struct, v1_0, v1_1, Int, IonResult, IonType, MacroTable};

    use super::*;

    fn to_binary_ion(text_ion: &str) -> IonResult<Vec<u8>> {
        let buffer = Vec::new();
        let config = WriteConfig::<BinaryEncoding_1_0>::new();
        let mut writer = Writer::new(config, buffer)?;
        let elements = Element::read_all(text_ion)?;
        writer.write_elements(&elements)?;
        writer.flush()?;
        writer.close()
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
        let mut reader = Reader::new(v1_0::Binary, ion_data)?;
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
        let mut reader = Reader::new(v1_0::Binary, data)?;

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
        let mut reader = Reader::new(v1_0::Binary, data)?;
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

    fn expand_macro_test(
        macro_source: &str,
        encode_macro_fn: impl FnOnce(MacroAddress) -> Vec<u8>,
        test_fn: impl FnOnce(Reader<v1_1::Binary, &[u8]>) -> IonResult<()>,
    ) -> IonResult<()> {
        // Because readers do not yet understand encoding directives, we'll pre-calculate the
        // macro ID that will be assigned.
        let macro_address = MacroTable::FIRST_USER_MACRO_ID;
        let opcode_byte = u8::try_from(macro_address).unwrap();
        // Using that ID, encode a binary stream containing an invocation of the new macro.
        // This function must add an IVM and the encoded e-expression ID, followed by any number
        // of arguments that matches the provided signature.
        let binary_ion = encode_macro_fn(opcode_byte as usize);
        // Construct a reader for the encoded data.
        let mut reader = Reader::new(v1_1::Binary, binary_ion.as_slice())?;
        // Register the template definition, getting the same ID we used earlier.
        let actual_address = reader.register_template_src(macro_source)?;
        assert_eq!(
            macro_address, actual_address,
            "Assigned macro address did not match expected address."
        );
        // Use the provided test function to confirm that the data expands to the expected stream.
        test_fn(reader)
    }

    #[cfg(feature = "experimental-ion-1-1")]
    #[test]
    fn expand_binary_template_macro() -> IonResult<()> {
        let macro_source = "(macro seventeen () 17)";
        let encode_macro_fn = |address| vec![address as u8];
        expand_macro_test(macro_source, encode_macro_fn, |mut reader| {
            assert_eq!(reader.expect_next()?.read()?.expect_i64()?, 17);
            Ok(())
        })
    }

    #[cfg(feature = "experimental-ion-1-1")]
    #[test]
    fn expand_binary_template_macro_with_one_arg() -> IonResult<()> {
        let macro_source = r#"
            (macro greet (name)
                (.make_string "Hello, " (%name) "!")
            )
        "#;
        #[rustfmt::skip]
        let encode_macro_fn = |address| vec![
            // === Macro ID ===
            address as u8,
            // === Arg 1 ===
            // 8-byte string
            0x98,
            // M     i     c     h     e     l     l     e
            0x4D, 0x69, 0x63, 0x68, 0x65, 0x6C, 0x6C, 0x65,
        ];
        expand_macro_test(macro_source, encode_macro_fn, |mut reader| {
            assert_eq!(
                reader.expect_next()?.read()?.expect_string()?,
                "Hello, Michelle!"
            );
            Ok(())
        })
    }

    #[cfg(feature = "experimental-ion-1-1")]
    #[test]
    fn expand_binary_template_macro_with_multiple_outputs() -> IonResult<()> {
        let macro_source = r#"
            (macro questions (food)
                (.values
                    (.make_string "What color is a " (%food) "?")
                    (.make_string "How much potassium is in a " (%food) "?")
                    (.make_string "What wine should I pair with a " (%food) "?")))
        "#;
        #[rustfmt::skip]
            let encode_macro_fn = |address| vec![
            // === Macro ID ===
            address as u8,
            // === Arg 1 ===
            // 6-byte string
            0x96,
            // b     a     n     a     n     a
            0x62, 0x61, 0x6E, 0x61, 0x6E, 0x61
        ];
        expand_macro_test(macro_source, encode_macro_fn, |mut reader| {
            assert_eq!(
                reader.expect_next()?.read()?.expect_string()?,
                "What color is a banana?"
            );
            assert_eq!(
                reader.expect_next()?.read()?.expect_string()?,
                "How much potassium is in a banana?"
            );
            assert_eq!(
                reader.expect_next()?.read()?.expect_string()?,
                "What wine should I pair with a banana?"
            );
            Ok(())
        })
    }
}
