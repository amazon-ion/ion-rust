use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::streaming_raw_reader::IoBuffer;
use crate::lazy::value::AnnotationsIterator;
use crate::{
    AnyEncoding, Decoder, Element, EncodingContext, ExpandedValueSource, IonError, IonResult,
    IonType, LazyExpandedValue, LazyValue, ValueRef,
};
use std::ops::Deref;

/// A (`LazyValue`, `Resource`) pair, in which the `Resource` is a value that depends on
/// the `LazyValue`.
///
/// `LazyElement` implements many of its methods by first converting itself to a `LazyValue`
/// with a fixed lifetime and then delegating the method call to the `LazyValue`. However,
/// this means that the result of that method call may be borrowed from the `LazyValue`.
///
/// In order to offer an ergonomic API that does not require callers to manually convert the
/// `LazyElement` to a `LazyValue`, `LazyElement` methods return a `LazyResource`.
///
/// `LazyResource` implements `Deref`, allowing the inner `Resource`'s methods to be invoked
/// directly.
///
/// See [`LazyElement::read`] for an example.
pub struct LazyResource<'a, Encoding: Decoder, Resource> {
    // This field is never read from, so the compiler considers it dead code.
    // However, it is necessary to keep the `LazyValue` alive while the `Resource` is borrowed.
    #[allow(dead_code)]
    value: LazyValue<'a, Encoding>,
    resource: Resource,
}

impl<Encoding: Decoder, Resource> Deref for LazyResource<'_, Encoding, Resource> {
    type Target = Resource;

    fn deref(&self) -> &Self::Target {
        &self.resource
    }
}

/// A (potentially annotated) value in an Ion data stream.
///
/// Unlike an [`Element`], a `LazyElement` does not eagerly read the value's contents or materialize
/// its data, making it comparatively lightweight.
///
/// Unlike a [`LazyValue`], a `LazyElement` shares ownership of its backing resources with the `Reader`.
/// This requires a small amount of bookkeeping overhead, but eliminates the need for lifetimes.
/// `LazyElement` instances can be stored indefinitely and read any number of times.
///
/// Storing one keeps those resources (input bytes, symbol table, bump arena) alive, and each read
/// rebuilds the value in the arena without reclaiming it, so reading the *same* element many times
/// accumulates memory; convert it to an owned [`Element`] instead.
pub struct LazyElement<Encoding: Decoder = AnyEncoding> {
    // Cloned from the reader's context; keeps its symbol table and arena alive.
    context: EncodingContext,
    // A second handle to the same input bytes `context` captured.
    io_buffer: IoBuffer,
    // What `Encoding::Value<'_>` is re-derived from, and the only record of which bytes this value
    // occupies; see `as_lazy_value`.
    detached_value: Encoding::DetachedValue,
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    /// `io_buffer` must hold the same input bytes as `context`, which must be a clone of the
    /// reader's.
    pub(crate) fn new(
        context: EncodingContext,
        io_buffer: IoBuffer,
        detached_value: Encoding::DetachedValue,
    ) -> Self {
        Self {
            context,
            io_buffer,
            detached_value,
        }
    }

    pub(crate) fn as_lazy_value<'top>(&'top self) -> LazyValue<'top, Encoding> {
        let context = self.context.get_ref();
        // Rebuild a value that borrows from this `LazyElement` rather than from the reader; nothing
        // is re-parsed, only the backing byte slice. This happens per call rather than once at
        // construction because the rebuilt value borrows `self.context`, which lives inline in this
        // struct; a `LazyElement` that was moved (into a `Vec`, say) would leave a cached value
        // pointing at the old address.
        //
        // The bytes come from the range the detached value itself reports, so the two cannot
        // disagree; a disagreement would decode unrelated bytes as this value.
        let span = self
            .io_buffer
            .span_for_stream_range(Encoding::detached_range(&self.detached_value));
        let value = Encoding::reattach_value(&self.detached_value, context, span);
        let expanded: LazyExpandedValue<'top, Encoding> = LazyExpandedValue {
            context,
            source: ExpandedValueSource::ValueLiteral(value),
        };
        LazyValue::new(expanded)
    }
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    // These five deliberately do NOT go through `as_lazy_value()`: rebuilding a binary value
    // allocates in an arena the `LazyElement` never reclaims, so delegating would grow memory
    // without bound. Each must still agree with `LazyValue`'s equivalent method.

    pub fn ion_type(&self) -> IonType {
        Encoding::detached_ion_type(&self.detached_value)
    }

    pub fn is_null(&self) -> bool {
        Encoding::detached_is_null(&self.detached_value)
    }

    pub fn is_container(&self) -> bool {
        matches!(
            self.ion_type(),
            IonType::List | IonType::SExp | IonType::Struct
        )
    }

    pub fn is_scalar(&self) -> bool {
        !self.is_container()
    }

    pub fn has_annotations(&self) -> bool {
        Encoding::detached_has_annotations(&self.detached_value)
    }

    // The methods below return values with a lifetime. As such, we need to wrap the
    // return value in a `LazyResource`. This allows the (otherwise temporary) `LazyValue` that
    // the return value depends on to continue living for the same duration as the return value itself.

    /// Reads the value portion of this `LazyElement`.
    pub fn read(&self) -> IonResult<LazyResource<'_, Encoding, ValueRef<'_, Encoding>>> {
        let value = self.as_lazy_value();
        let resource = value.read()?;

        Ok(LazyResource { value, resource })
    }

    /// Returns an iterator over the annotations on this `LazyElement`.
    pub fn annotations(
        &self,
    ) -> IonResult<LazyResource<'_, Encoding, AnnotationsIterator<'_, Encoding>>> {
        let value = self.as_lazy_value();
        let resource = value.annotations();

        Ok(LazyResource { value, resource })
    }

    /// Returns the encoding context that this `LazyElement` uses to read its data.
    #[allow(dead_code)]
    pub(crate) fn context(&self) -> LazyResource<'_, Encoding, EncodingContextRef<'_>> {
        let value = self.as_lazy_value();
        let resource = value.context();

        LazyResource { value, resource }
    }
}

impl<'top, Encoding: Decoder> From<LazyValue<'top, Encoding>> for LazyElement<Encoding> {
    fn from(value: LazyValue<'top, Encoding>) -> Self {
        value.to_owned()
    }
}

impl<Encoding: Decoder> TryFrom<LazyElement<Encoding>> for Element {
    type Error = IonError;

    fn try_from(lazy_element: LazyElement<Encoding>) -> Result<Self, Self::Error> {
        lazy_element.as_lazy_value().try_into()
    }
}

impl<Encoding: Decoder> TryFrom<&LazyElement<Encoding>> for Element {
    type Error = IonError;

    fn try_from(lazy_element: &LazyElement<Encoding>) -> Result<Self, Self::Error> {
        lazy_element.as_lazy_value().try_into()
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::expanded::lazy_element::LazyElement;
    use crate::{AnyEncoding, Element, IonResult, Reader, Sequence};

    fn test_data() -> String {
        let test_data = r#"
            // === Values backed by `ExpandedValueSource::ValueLiteral` ===
            foo
            true
            baz::5
            [(), {}, ()]
            2025T
            "Hello"
         "#;
        test_data.to_owned()
    }

    /// Reads the output of `test_data()` twice, once using the `Element` API and again using
    /// the `LazyElement` API. The output is passed to `TestFn` to make assertions.
    fn lazy_element_test<TestFn>(test: TestFn) -> IonResult<()>
    where
        TestFn: FnOnce(Sequence, &mut dyn Iterator<Item = IonResult<LazyElement>>) -> IonResult<()>,
    {
        let test_data = test_data();
        let expected = Element::read_all(&test_data)?;
        let mut reader = Reader::new(AnyEncoding, &test_data)?;
        test(expected, &mut reader)
    }

    #[test]
    fn equivalent_to_lazy_value_when_reading_forward() -> IonResult<()> {
        lazy_element_test(|expected, reader| {
            // Fully read each LazyElement as it's encountered and compare it to the corresponding
            // expected element. Only one LazyElement exists at a time.
            let actual = reader
                .map(|result| result.and_then(Element::try_from))
                .collect::<IonResult<Vec<Element>>>()?;
            assert!(expected.iter().eq(&actual));
            Ok(())
        })
    }

    #[test]
    fn equivalent_to_lazy_value_when_read_backward() -> IonResult<()> {
        lazy_element_test(|expected, reader| {
            // Store the LazyElements in a Vec without reading them.
            let lazy_elements_vec = reader.collect::<IonResult<Vec<LazyElement>>>()?;
            // Read the collected LazyElements in reverse order and store them in another Vec,
            // demonstrating that it's safe/correct to read them in an order that differs from their
            // order in the input stream.
            let actual = lazy_elements_vec
                .iter()
                .rev()
                .map(Element::try_from)
                .collect::<IonResult<Vec<Element>>>()?;
            assert!(expected.into_iter().rev().eq(actual));
            Ok(())
        })
    }

    #[test]
    fn values_survive_after_reader_drops() -> IonResult<()> {
        let mut reader = Reader::new(AnyEncoding, "foo")?;
        let lazy_element = reader.expect_next()?.to_owned();
        // Even though we have a `LazyElement`, we can safely drop the `Reader`.
        drop(reader);
        // The `LazyElement` is still valid/usable.
        assert_eq!(Element::symbol("foo"), Element::try_from(lazy_element)?);
        Ok(())
    }

    // ===== Binary =====
    //
    // The binary path erases no lifetimes, so these are expected to be Miri-clean under both
    // aliasing models; the text tests above stay out because text still erases lifetimes. Keep this
    // module's name in sync with `MIRI_TEST_SELECTION` in `.github/workflows/miri.yml`, which selects
    // these tests by module path.
    mod binary_soundness_tests {
        use super::test_data;
        use crate::lazy::binary::test_utilities::to_binary_ion;
        use crate::lazy::encoding::BinaryEncoding_1_0;
        use crate::lazy::expanded::lazy_element::LazyElement;
        use crate::read_config::ReadConfig;
        use crate::{
            AnyEncoding, Decoder, Element, IonResult, IonType, LazyValue, Reader, ValueRef,
        };
        use rstest::rstest;
        use std::io::{BufReader, Cursor};

        /// Containers with children of their own, including one of each type and an annotated one.
        fn container_test_data() -> String {
            let test_data = r#"
                [1, two, "three", [4, 5]]
                {a: 1, b: [2, 3], c: {d: four}, e: (5)}
                (six (7 8) {nine: 10})
                annotated::[11]
            "#;
            test_data.to_owned()
        }

        /// Every value in `container_test_data()` and its descendants, in depth-first order.
        fn expected_container_ion_types() -> Vec<IonType> {
            use IonType::*;
            vec![
                // [1, two, "three", [4, 5]]
                List, Int, Symbol, String, List, Int, Int,
                // {a: 1, b: [2, 3], c: {d: four}, e: (5)}
                Struct, Int, List, Int, Int, Struct, Symbol, SExp, Int,
                // (six (7 8) {nine: 10})
                SExp, Symbol, SExp, Int, Int, Struct, Int, // annotated::[11]
                List, Int,
            ]
        }

        fn store_elements_then_drop_reader<E: Decoder + Into<ReadConfig<E>>>(
            encoding: E,
            ion_data: Vec<u8>,
        ) -> IonResult<Vec<LazyElement<E>>> {
            let mut reader = Reader::new(encoding, ion_data)?;
            let elements = (&mut reader).collect::<IonResult<Vec<LazyElement<E>>>>()?;
            drop(reader);
            Ok(elements)
        }

        /// Appends the `IonType` of `value` and its descendants to `types`, exercising stored
        /// containers' lazy child iterators directly.
        fn collect_ion_types<E: Decoder>(
            value: LazyValue<'_, E>,
            types: &mut Vec<IonType>,
        ) -> IonResult<()> {
            types.push(value.ion_type());
            match value.read()? {
                ValueRef::List(list) => {
                    for child in list.iter() {
                        collect_ion_types(child?, types)?;
                    }
                }
                ValueRef::SExp(sexp) => {
                    for child in sexp.iter() {
                        collect_ion_types(child?, types)?;
                    }
                }
                ValueRef::Struct(fields) => {
                    for field in fields.iter() {
                        collect_ion_types(field?.value(), types)?;
                    }
                }
                _ => {}
            }
            Ok(())
        }

        fn assert_elements_match_text(
            text: &str,
            elements: &[LazyElement<impl Decoder>],
        ) -> IonResult<()> {
            let expected = Element::read_all(text)?;
            assert_eq!(
                expected.len(),
                elements.len(),
                "stored a different number of values than `Element::read_all` found"
            );
            let actual = elements
                .iter()
                .map(Element::try_from)
                .collect::<IonResult<Vec<Element>>>()?;
            assert!(expected.iter().eq(&actual));
            Ok(())
        }

        /// Checks the materialized values and the header accessors of one equivalence class against
        /// `Element`. `encoding` appears in the failure messages because the caller runs both.
        fn assert_class_survives_reader<E: Decoder + Into<ReadConfig<E>>>(
            encoding: E,
            text: &str,
        ) -> IonResult<()> {
            let label = format!("{encoding:?}");
            let elements = store_elements_then_drop_reader(encoding, to_binary_ion(text)?)?;
            assert_elements_match_text(text, &elements)?;

            let expected = Element::read_all(text)?;
            for (index, (element, expected)) in elements.iter().zip(expected.iter()).enumerate() {
                assert_eq!(
                    expected.ion_type(),
                    element.ion_type(),
                    "ion_type: value #{index} ({label})"
                );
                assert_eq!(
                    expected.is_null(),
                    element.is_null(),
                    "is_null: value #{index} ({label})"
                );
                assert_eq!(
                    !expected.annotations().is_empty(),
                    element.has_annotations(),
                    "has_annotations: value #{index} ({label})"
                );
            }
            Ok(())
        }

        #[rstest]
        fn values_survive_after_reader_drops<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, BinaryEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let text = test_data();
            let elements = store_elements_then_drop_reader(encoding, to_binary_ion(&text)?)?;
            assert_elements_match_text(&text, &elements)
        }

        #[rstest]
        fn container_children_survive_after_reader_drops<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, BinaryEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let text = container_test_data();
            let elements = store_elements_then_drop_reader(encoding, to_binary_ion(&text)?)?;

            let mut actual = Vec::new();
            for element in &elements {
                collect_ion_types(element.as_lazy_value(), &mut actual)?;
            }
            assert_eq!(expected_container_ion_types(), actual);

            // Reading a stored value is not one-shot; a second traversal sees the same data.
            let mut actual_again = Vec::new();
            for element in &elements {
                collect_ion_types(element.as_lazy_value(), &mut actual_again)?;
            }
            assert_eq!(actual, actual_again);

            // The children are also correct, not merely well-typed.
            assert_elements_match_text(&text, &elements)
        }

        #[rstest]
        #[case::null_forms(
            "null null.null null.bool null.int null.float null.decimal null.timestamp \
             null.symbol null.string null.clob null.blob null.list null.sexp null.struct"
        )]
        #[case::long_form_length("\"a string whose length does not fit in its type descriptor\"")]
        #[case::multi_annotation("one::two::three::four::5")]
        #[case::empty_container("[] () {}")]
        #[case::clob("{{ \"a clob\" }}")]
        #[case::blob("{{ dGhpcyBpcyBhIGJsb2I= }}")]
        #[case::float("1.5e0")]
        #[case::decimal("-7.25")]
        #[case::negative_int("-42")]
        #[case::min_i64("-9223372036854775808")]
        #[case::timestamp("2024-06-01T12:34:56Z")]
        fn equivalence_classes_survive_reader(#[case] text: &str) -> IonResult<()> {
            assert_class_survives_reader(AnyEncoding, text)?;
            assert_class_survives_reader(BinaryEncoding_1_0, text)
        }

        #[test]
        fn child_values_can_be_stored_after_reader_drops() -> IonResult<()> {
            let binary_ion = to_binary_ion("[1, two, {a: three}]")?;
            let elements = store_elements_then_drop_reader(AnyEncoding, binary_ion)?;
            let [list] = elements.as_slice() else {
                panic!(
                    "expected exactly one top-level value, found {}",
                    elements.len()
                );
            };
            let children: Vec<LazyElement> = list
                .read()?
                .clone()
                .expect_list()?
                .iter()
                .map(|child| child.map(LazyValue::to_owned))
                .collect::<IonResult<_>>()?;
            drop(elements);

            assert_elements_match_text("1 two {a: three}", &children)
        }

        /// An annotated child's stored range begins before its opcode
        /// (`header_offset - annotations_total_length`) -- a reattach boundary nothing else reaches.
        #[test]
        fn annotated_child_values_can_be_stored_after_reader_drops() -> IonResult<()> {
            let binary_ion = to_binary_ion("[a::1, {b: c::three}]")?;
            let elements = store_elements_then_drop_reader(BinaryEncoding_1_0, binary_ion)?;
            let [list] = elements.as_slice() else {
                panic!(
                    "expected exactly one top-level value, found {}",
                    elements.len()
                );
            };
            let children: Vec<LazyElement<BinaryEncoding_1_0>> = list
                .read()?
                .clone()
                .expect_list()?
                .iter()
                .map(|child| child.map(LazyValue::to_owned))
                .collect::<IonResult<_>>()?;
            drop(elements);

            let [annotated_int, unannotated_struct] = children.as_slice() else {
                panic!("expected exactly two children, found {}", children.len());
            };
            assert!(annotated_int.has_annotations());
            assert!(!unannotated_struct.has_annotations());
            // Materializing resolves the annotation text, which lives in those leading bytes.
            assert_elements_match_text("a::1 {b: c::three}", &children)
        }

        /// Values stored from a streaming (`Read`) input, whose window slides--and, pinned by a
        /// stored element, copies itself--as the reader advances. The only test where
        /// `bytes_for_stream_range` subtracts a non-zero offset; the rest read from a `Vec<u8>`.
        #[test]
        fn values_survive_a_shifting_stream_window() -> IonResult<()> {
            // Exceed `IonStream`'s 4 KiB window so the reader must shift while elements are stored.
            const VALUE_COUNT: usize = 10;
            let text = (0..VALUE_COUNT)
                .map(|index| format!("{{index: {index}, filler: \"{}\"}}", "x".repeat(500)))
                .collect::<Vec<String>>()
                .join("\n");
            let binary_ion = to_binary_ion(&text)?;
            assert!(
                binary_ion.len() > 4 * 1024,
                "test data ({} bytes) is too small to force a window shift",
                binary_ion.len()
            );

            // A `BufReader` goes through `IonStream`; a `Vec<u8>` would be borrowed in place instead.
            let mut reader = Reader::new(
                BinaryEncoding_1_0,
                BufReader::new(Cursor::new(binary_ion.clone())),
            )?;
            let elements =
                (&mut reader).collect::<IonResult<Vec<LazyElement<BinaryEncoding_1_0>>>>()?;
            drop(reader);

            // Confirm the window really did slide; a larger `IonStream` buffer would stop it.
            let max_stream_offset = elements
                .iter()
                .map(|element| element.io_buffer.stream_offset())
                .max()
                .unwrap_or(0);
            assert!(
                max_stream_offset > 0,
                "no stored element saw a shifted window, so this test proves nothing"
            );

            assert_elements_match_text(&text, &elements)
        }

        /// Stays readable after moving and after its reader advances -- why `as_lazy_value()`
        /// rebuilds per call instead of caching.
        #[test]
        fn stored_values_survive_moves_and_reader_advances() -> IonResult<()> {
            let binary_ion = to_binary_ion("first::1 [2, 3] \"four\"")?;
            let mut reader = Reader::new(BinaryEncoding_1_0, binary_ion)?;

            let first = reader.expect_next()?.to_owned();
            // Read it once while the reader is still parked on it.
            assert_eq!(Element::read_one("first::1")?, Element::try_from(&first)?);

            // Move `first` into a `Vec` and grow it, then keep reading from it. We don't assert the
            // backing address changed: `Vec`'s realloc may grow in place, so the pointer is not a
            // portable proof of relocation. A cached borrow into a moved element would instead be
            // caught by Miri.
            let mut stored = vec![first];
            stored.push(reader.expect_next()?.to_owned());

            // Advancing again allocates in the shared arena while both stored elements are alive.
            let third = reader.expect_next()?;
            assert_eq!(Element::string("four"), Element::try_from(third)?);

            assert_elements_match_text("first::1 [2, 3]", &stored)?;
            drop(reader);
            assert_elements_match_text("first::1 [2, 3]", &stored)
        }

        /// Keeps resolving its symbol IDs against the table active when it was created, even after
        /// the reader reads one that redefines them.
        #[test]
        fn stored_values_keep_their_symbol_table_after_an_lst_change() -> IonResult<()> {
            // Two complete binary streams, each with its own symbol table, so `alpha` and `beta` are
            // both the first local symbol--the same symbol ID--in theirs.
            let mut binary_ion = to_binary_ion("alpha")?;
            binary_ion.extend_from_slice(&to_binary_ion("beta")?);

            let mut reader = Reader::new(BinaryEncoding_1_0, binary_ion)?;
            let alpha = reader.expect_next()?.to_owned();
            // Reading on passes the second segment's IVM and LST, redefining the ID `alpha` uses.
            assert_eq!(
                Element::symbol("beta"),
                Element::try_from(reader.expect_next()?)?
            );
            // `alpha` is unaffected: the update copied the shared table instead of overwriting it.
            assert_eq!(Element::symbol("alpha"), Element::try_from(&alpha)?);
            drop(reader);
            assert_eq!(Element::symbol("alpha"), Element::try_from(&alpha)?);
            Ok(())
        }

        /// One of each header fact the accessors report, including a container of each type.
        fn header_test_data() -> &'static str {
            "null.string 5 annotated::foo [1] (2) {a: 3}"
        }

        /// The header accessors bypass `as_lazy_value()`, so check them against `LazyValue`'s.
        #[rstest]
        fn header_accessors_match_lazy_value<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, BinaryEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let elements =
                store_elements_then_drop_reader(encoding, to_binary_ion(header_test_data())?)?;
            assert_eq!(6, elements.len(), "unexpected number of top-level values");
            for (index, element) in elements.iter().enumerate() {
                let value = element.as_lazy_value();
                let context = format!("value #{index} ({:?})", value.ion_type());
                assert_eq!(value.ion_type(), element.ion_type(), "ion_type: {context}");
                assert_eq!(value.is_null(), element.is_null(), "is_null: {context}");
                assert_eq!(
                    value.is_container(),
                    element.is_container(),
                    "is_container: {context}"
                );
                assert_eq!(
                    value.is_scalar(),
                    element.is_scalar(),
                    "is_scalar: {context}"
                );
                assert_eq!(
                    value.has_annotations(),
                    element.has_annotations(),
                    "has_annotations: {context}"
                );
            }
            Ok(())
        }

        /// The header accessors must not rebuild the value in the arena: a `LazyElement` never
        /// reclaims it, so allocating per call would grow memory without bound.
        #[test]
        fn header_accessors_do_not_grow_the_arena() -> IonResult<()> {
            let elements = store_elements_then_drop_reader(
                BinaryEncoding_1_0,
                to_binary_ion("ann::[1, 2, 3]")?,
            )?;
            let [element] = elements.as_slice() else {
                panic!(
                    "expected exactly one top-level value, found {}",
                    elements.len()
                );
            };

            // `allocated_bytes()` reports chunk capacity, so it only moves when the arena acquires
            // one; tens of kilobytes' worth of iterations makes that certain.
            const ITERATIONS: usize = 1_000;
            let allocated_bytes = || element.context.get_ref().allocator().allocated_bytes();

            let bytes_before = allocated_bytes();
            for _ in 0..ITERATIONS {
                assert_eq!(IonType::List, element.ion_type());
                assert!(!element.is_null());
                assert!(element.is_container());
                assert!(!element.is_scalar());
                assert!(element.has_annotations());
            }
            assert_eq!(
                bytes_before,
                allocated_bytes(),
                "the header accessors grew the arena"
            );

            // Confirm the measurement is sensitive: that many `as_lazy_value()` calls do grow it.
            for _ in 0..ITERATIONS {
                let _ = element.as_lazy_value();
            }
            assert!(
                allocated_bytes() > bytes_before,
                "rebuilding the value {ITERATIONS} times did not grow the arena, so this test \
                 could not have detected an allocation in the accessors"
            );
            Ok(())
        }
    }
}
