use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, ExpandedAnnotationsSource,
};
use crate::lazy::span::Span;
use crate::lazy::streaming_raw_reader::IoBuffer;
use crate::lazy::value::AnnotationsIterator;
use crate::{
    AnyEncoding, Decoder, Element, EncodingContext, ExpandedValueSource, IonError, IonResult,
    IonType, LazyExpandedValue, LazyValue, ValueRef,
};
use std::marker::PhantomData;
use std::ops::Deref;

/// A `Resource` that borrows from a [`LazyElement`], such as the [`ValueRef`] returned by
/// [`LazyElement::read`].
///
/// `LazyResource` implements `Deref`, allowing the inner `Resource`'s methods to be invoked
/// directly.
pub struct LazyResource<'a, Encoding: Decoder, Resource> {
    // Gives `'a` and `Encoding` the variance and auto traits of a `LazyValue<'a, Encoding>`; the
    // resource itself borrows the `LazyElement` for `'a`.
    spooky: PhantomData<LazyValue<'a, Encoding>>,
    resource: Resource,
}

impl<Encoding: Decoder, Resource> LazyResource<'_, Encoding, Resource> {
    fn new(resource: Resource) -> Self {
        Self {
            spooky: PhantomData,
            resource,
        }
    }
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
/// Storing one keeps those resources (input bytes, symbol table, bump arena) alive. Storing or
/// reading it allocates in that arena, which reclaims nothing until it is dropped:
///
/// * Binary Ion rebuilds the value on every read.
/// * Text Ion re-parses a container's subtree once, on its first read. A container stored from a
///   stored container's parsed subtree shares that parse instead; storing it copies its raw value
///   (at most 72 bytes on 64-bit targets) into the arena.
/// * Text Ion also allocates on every read that decodes an escaped or multi-segment string, an
///   escaped symbol, a blob, or a clob.
///
/// To read the *same* element many times, convert it to an owned [`Element`] instead.
pub struct LazyElement<Encoding: Decoder = AnyEncoding> {
    // Cloned from the reader's context; keeps its symbol table and arena alive.
    context: EncodingContext,
    // A second handle to the same input bytes `context` captured.
    io_buffer: IoBuffer,
    // What `Encoding::Value<'_>` is re-derived from, and the only record of which bytes this value
    // occupies; see `span`.
    detached_value: Encoding::DetachedValue,
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    /// `context` must be a clone of the reader's, and `io_buffer` a handle to that clone's own
    /// `IoBuffer` (`context.save_io_buffer()`), so that both hold the same bytes.
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

    /// The bytes this value occupies. They come from the range the detached value itself reports,
    /// so the two cannot disagree; a disagreement would decode unrelated bytes as this value.
    fn span(&self) -> Span<'_> {
        let range = Encoding::detached_range(&self.detached_value);
        let span = self.io_buffer.span_for_stream_range(range.clone());
        debug_assert_eq!(range, span.range());
        span
    }

    pub(crate) fn as_lazy_value<'top>(&'top self) -> IonResult<LazyValue<'top, Encoding>> {
        let context = self.context.get_ref();
        // Rebuild a value that borrows from this `LazyElement` rather than from the reader. This
        // happens per call rather than once at construction because the rebuilt value borrows
        // `self.context`, which lives inline in this struct; a `LazyElement` that was moved (into a
        // `Vec`, say) would leave a cached value pointing at the old address. Scalars are not
        // re-parsed. A text container is parsed at most once, into a cache in `detached_value`
        // whose storage is on the heap and so survives moves.
        //
        // For binary, `reattach_value` allocates the rebuilt value in `self.context`'s arena on
        // every call, regardless of the value's type, and that allocation lives as long as the
        // arena does. Methods that only need header information or annotations should use the
        // `detached_*` accessors or `reattach_annotations` instead of calling this.
        let value = Encoding::reattach_value(&self.detached_value, context, self.span())?;
        let expanded: LazyExpandedValue<'top, Encoding> = LazyExpandedValue {
            context,
            source: ExpandedValueSource::ValueLiteral(value),
        };
        Ok(LazyValue::new(expanded))
    }
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    // These five, and `annotations()` below, deliberately do NOT go through `as_lazy_value()`:
    // rebuilding a binary value allocates in an arena the `LazyElement` never reclaims, so
    // delegating would grow memory without bound. Each must still agree with `LazyValue`'s equivalent method.

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

    // The methods below return values that borrow this `LazyElement`, wrapped in a `LazyResource`.

    /// Reads the value portion of this `LazyElement`.
    ///
    /// For binary Ion, each call allocates in this element's arena, as does iterating a container's
    /// children. For text Ion, the first call to this method or conversion to an [`Element`] on a
    /// container re-parses it into the arena, unless the container was stored from a stored
    /// container's parsed subtree. Reading an escaped or multi-segment string, an escaped symbol, a
    /// blob, or a clob also allocates. That memory is not reclaimed until the arena is dropped, so
    /// reading the same element repeatedly can grow memory; see [`LazyElement`].
    pub fn read(&self) -> IonResult<LazyResource<'_, Encoding, ValueRef<'_, Encoding>>> {
        let value = self.as_lazy_value()?;
        let resource = value.read()?;

        Ok(LazyResource::new(resource))
    }

    /// Returns an iterator over the annotations on this `LazyElement`.
    ///
    /// For text Ion, the annotations are read from the bytes that precede the value without
    /// re-parsing it, though iterating escaped annotations allocates. To check whether annotations
    /// are present without allocating, use [`has_annotations`](Self::has_annotations).
    pub fn annotations(
        &self,
    ) -> IonResult<LazyResource<'_, Encoding, AnnotationsIterator<'_, Encoding>>> {
        let context = self.context.get_ref();
        let raw_annotations =
            Encoding::reattach_annotations(&self.detached_value, context, self.span())?;
        let resource = AnnotationsIterator {
            expanded_annotations: ExpandedAnnotationsIterator::new(
                ExpandedAnnotationsSource::ValueLiteral(raw_annotations),
            ),
            context,
        };

        Ok(LazyResource::new(resource))
    }

    /// Returns the encoding context that this `LazyElement` uses to read its data.
    #[allow(dead_code)]
    pub(crate) fn context(&self) -> IonResult<LazyResource<'_, Encoding, EncodingContextRef<'_>>> {
        let value = self.as_lazy_value()?;
        let resource = value.context();

        Ok(LazyResource::new(resource))
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
        lazy_element.as_lazy_value()?.try_into()
    }
}

impl<Encoding: Decoder> TryFrom<&LazyElement<Encoding>> for Element {
    type Error = IonError;

    fn try_from(lazy_element: &LazyElement<Encoding>) -> Result<Self, Self::Error> {
        lazy_element.as_lazy_value()?.try_into()
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::expanded::lazy_element::LazyElement;
    use crate::read_config::ReadConfig;
    use crate::{
        AnyEncoding, Decoder, Element, IonResult, IonType, LazyValue, Reader, Sequence, ValueRef,
    };

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

    // ===== Helpers for the soundness tests =====

    /// The reader owns its input, so dropping it frees the bytes it parsed from.
    fn store_elements_then_drop_reader<E: Decoder + Into<ReadConfig<E>>>(
        encoding: E,
        ion_data: impl Into<Vec<u8>>,
    ) -> IonResult<Vec<LazyElement<E>>> {
        let mut reader = Reader::new(encoding, ion_data.into())?;
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

    /// The `IonType`s of `elements` and their descendants, in depth-first order.
    fn traverse_all<E: Decoder>(elements: &[LazyElement<E>]) -> IonResult<Vec<IonType>> {
        let mut types = Vec::new();
        for element in elements {
            collect_ion_types(element.as_lazy_value()?, &mut types)?;
        }
        Ok(types)
    }

    /// Annotations on scalars and on each container type, including quoted, escaped,
    /// comment-separated, and symbol ID ones (`$4` is `name`; `$0` has no text), alongside
    /// unannotated values.
    const ANNOTATED: &str = r#"
        a::1
        'b c'::'d\'e':: /* comment */ "f"
        g:: /* comment */ h::[1, 2]
        i::(j k)
        'l\nm'::{n: o::p}
        [q]
        r::null.struct
        s
        $4::5
        $0::t
        $4::$0::[u]
    "#;

    fn annotation_texts<E: Decoder>(element: &LazyElement<E>) -> IonResult<Vec<Option<String>>> {
        // `LazyResource` only derefs, so take the iterator out of it to consume it.
        element
            .annotations()?
            .resource
            .map(|annotation| Ok(annotation?.text().map(str::to_owned)))
            .collect()
    }

    /// Checks each stored element's annotations against `Element::read_all(text)`'s.
    fn assert_annotations_match_text(
        text: &str,
        elements: &[LazyElement<impl Decoder>],
    ) -> IonResult<()> {
        let expected: Vec<Vec<Option<String>>> = Element::read_all(text)?
            .iter()
            .map(|element| {
                element
                    .annotations()
                    .iter()
                    .map(|annotation| annotation.text().map(str::to_owned))
                    .collect()
            })
            .collect();
        let actual = elements
            .iter()
            .map(annotation_texts)
            .collect::<IonResult<Vec<_>>>()?;
        assert_eq!(expected, actual);
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

    /// Checks each element's header accessors against those of its `LazyValue`.
    fn assert_header_accessors_match_lazy_value(
        elements: &[LazyElement<impl Decoder>],
    ) -> IonResult<()> {
        for (index, element) in elements.iter().enumerate() {
            let value = element.as_lazy_value()?;
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

    // ===== Binary =====
    //
    // Keep this module's name in sync with `MIRI_TEST_SELECTION` in `.github/workflows/miri.yml`,
    // which selects these tests by module path.
    mod binary_soundness_tests {
        use super::{
            assert_annotations_match_text, assert_elements_match_text,
            assert_header_accessors_match_lazy_value, collect_ion_types,
            store_elements_then_drop_reader, test_data, ANNOTATED,
        };
        use crate::lazy::binary::test_utilities::to_binary_ion;
        use crate::lazy::encoding::BinaryEncoding_1_0;
        use crate::lazy::expanded::lazy_element::LazyElement;
        use crate::read_config::ReadConfig;
        use crate::{AnyEncoding, Decoder, Element, IonResult, IonType, LazyValue, Reader};
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
        fn stored_annotations_match_elements<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, BinaryEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let elements = store_elements_then_drop_reader(encoding, to_binary_ion(ANNOTATED)?)?;
            assert_annotations_match_text(ANNOTATED, &elements)
        }

        #[rstest]
        fn container_children_survive_after_reader_drops<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, BinaryEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let text = container_test_data();
            let elements = store_elements_then_drop_reader(encoding, to_binary_ion(&text)?)?;

            let mut actual = Vec::new();
            for element in &elements {
                collect_ion_types(element.as_lazy_value()?, &mut actual)?;
            }
            assert_eq!(expected_container_ion_types(), actual);

            // Reading a stored value is not one-shot; a second traversal sees the same data.
            let mut actual_again = Vec::new();
            for element in &elements {
                collect_ion_types(element.as_lazy_value()?, &mut actual_again)?;
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
            assert_elements_match_text("a::1 {b: c::three}", &children)?;
            assert_annotations_match_text("a::1 {b: c::three}", &children)
        }

        /// Values stored from a streaming (`Read`) input, whose window slides--and, pinned by a
        /// stored element, copies itself--as the reader advances. With its text twin, one of the
        /// two tests where `bytes_for_stream_range` subtracts a non-zero offset; the rest read
        /// from a `Vec<u8>`.
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
            assert_header_accessors_match_lazy_value(&elements)
        }

        /// The header accessors and `annotations()` must not rebuild the value in the arena: a
        /// `LazyElement` never reclaims it, so allocating per call would grow memory without bound.
        #[rstest]
        fn header_accessors_do_not_grow_the_arena<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, BinaryEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let elements =
                store_elements_then_drop_reader(encoding, to_binary_ion("ann::[1, 2, 3]")?)?;
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
                assert_eq!(1, element.annotations()?.resource.count());
            }
            assert_eq!(
                bytes_before,
                allocated_bytes(),
                "the header accessors or `annotations()` grew the arena"
            );

            // Confirm the measurement is sensitive: that many `as_lazy_value()` calls do grow it.
            for _ in 0..ITERATIONS {
                let _ = element.as_lazy_value()?;
            }
            assert!(
                allocated_bytes() > bytes_before,
                "rebuilding the value {ITERATIONS} times did not grow the arena, so this test \
                 could not have detected an allocation in the accessors"
            );
            Ok(())
        }
    }
    // ===== Text =====
    //
    // A stored text container is re-parsed once, on first read, into a cache that owns the storage
    // it borrows from; one stored from another container's cache shares it. These exercise that
    // cache, and the scalar path, under Miri. Keep this module's name in sync with
    // `MIRI_TEST_SELECTION` in `.github/workflows/miri.yml`.
    mod text_soundness_tests {
        use super::{
            annotation_texts, assert_annotations_match_text, assert_elements_match_text,
            assert_header_accessors_match_lazy_value, store_elements_then_drop_reader,
            traverse_all, ANNOTATED,
        };
        use crate::lazy::decoder::private::DetachableValue;
        use crate::lazy::encoding::TextEncoding_1_0;
        use crate::lazy::expanded::lazy_element::LazyElement;
        use crate::read_config::ReadConfig;
        use crate::{AnyEncoding, Decoder, Element, IonResult, LazyValue, Reader, ValueRef};
        use rstest::rstest;
        use std::io::{BufReader, Cursor};

        /// Scalars and containers of each type: nested, annotated with interstitial comments,
        /// holding escapes (decoded into the arena), and holding s-expression operators.
        const TEXT: &str = r#"
            foo
            ann:: /* comment */ 5
            null.list
            [1, two, "th\nree", [4, 5]]
            {a: 1, b: [2, 3], c: {d: four}, 'e\'s': (5 + 6)}
            outer:: /* comment */ inner::(six (7 8) {nine: 10})
            []
        "#;

        #[rstest]
        fn values_survive_after_reader_drops<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, TextEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let elements = store_elements_then_drop_reader(encoding, TEXT)?;
            assert_elements_match_text(TEXT, &elements)
        }

        #[rstest]
        fn stored_annotations_match_elements<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, TextEncoding_1_0)] encoding: E,
            #[values(false, true)] populate_first: bool,
        ) -> IonResult<()> {
            let elements = store_elements_then_drop_reader(encoding, ANNOTATED)?;
            if populate_first {
                traverse_all(&elements)?;
            }
            assert_annotations_match_text(ANNOTATED, &elements)
        }

        /// Symbol ID annotations resolve against the symbol table active when each value was
        /// stored, even after a later one redefines the same ID.
        #[rstest]
        fn stored_annotations_keep_their_symbol_table<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, TextEncoding_1_0)] encoding: E,
            #[values(false, true)] populate_first: bool,
        ) -> IonResult<()> {
            const REDEFINED: &str = r#"
                $ion_symbol_table::{symbols: ["x"]}
                $10::[1]
                $10::2
                $ion_symbol_table::{symbols: ["y"]}
                $10::[3]
                $10::4
            "#;
            let elements = store_elements_then_drop_reader(encoding, REDEFINED)?;
            if populate_first {
                traverse_all(&elements)?;
            }
            assert_annotations_match_text(REDEFINED, &elements)
        }

        /// The stored children of a container: its field values, or its child values.
        fn store_children<E: Decoder>(parent: LazyValue<'_, E>) -> IonResult<Vec<LazyElement<E>>> {
            match parent.read()? {
                ValueRef::List(list) => list.iter().map(|c| c.map(LazyValue::to_owned)).collect(),
                ValueRef::SExp(sexp) => sexp.iter().map(|c| c.map(LazyValue::to_owned)).collect(),
                ValueRef::Struct(fields) => fields
                    .iter()
                    .map(|field| field.map(|field| field.value().to_owned()))
                    .collect(),
                _ => panic!("expected a container, found {:?}", parent.ion_type()),
            }
        }

        /// A stored child's range excludes its field name and separators, whether the child was
        /// stored from the reader's parse or from a stored parent's re-parse.
        #[rstest]
        #[case::struct_fields(
            r#"{a: x:: /*c*/ y::1, 'b': 'e\nf'::[2], c: (z::3), d: 4}"#,
            r#"x::y::1 'e\nf'::[2] (z::3) 4"#
        )]
        #[case::list_children(
            r#"[x:: /*c*/ y::1, 'e\nf'::[2], w::(z::3), 4]"#,
            r#"x::y::1 'e\nf'::[2] w::(z::3) 4"#
        )]
        #[case::sexp_children(
            r#"(x:: /*c*/ y::1 'e\nf'::{g: 2} + 4)"#,
            r#"x::y::1 'e\nf'::{g: 2} '+' 4"#
        )]
        fn stored_child_annotations_match_elements(
            #[case] parent_text: &str,
            #[case] children_text: &str,
            #[values(false, true)] from_stored_parent: bool,
        ) -> IonResult<()> {
            let children = if from_stored_parent {
                let elements = store_elements_then_drop_reader(TextEncoding_1_0, parent_text)?;
                let [parent] = elements.as_slice() else {
                    panic!("expected one top-level value, found {}", elements.len());
                };
                store_children(parent.as_lazy_value()?)?
            } else {
                let mut reader = Reader::new(TextEncoding_1_0, parent_text.as_bytes().to_vec())?;
                store_children(reader.expect_next()?)?
            };
            assert_elements_match_text(children_text, &children)?;
            assert_annotations_match_text(children_text, &children)
        }

        /// A stored container's annotations are read from its leading bytes, leaving its cache empty.
        #[rstest]
        fn annotations_do_not_parse_a_stored_container<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, TextEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let elements =
                store_elements_then_drop_reader(encoding, "g:: /* comment */ h::[1, 2]")?;
            let [element] = elements.as_slice() else {
                panic!("expected one top-level value, found {}", elements.len());
            };
            assert_eq!(
                vec![Some("g".to_owned()), Some("h".to_owned())],
                annotation_texts(element)?
            );
            assert!(
                !E::detached_is_parsed(&element.detached_value),
                "reading the annotations re-parsed the container"
            );
            // Confirm the probe sees the cache once it is filled.
            element.as_lazy_value()?;
            assert!(E::detached_is_parsed(&element.detached_value));
            Ok(())
        }

        #[rstest]
        fn cached_containers_survive_repeat_reads<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, TextEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let elements = store_elements_then_drop_reader(encoding, TEXT)?;
            let first = traverse_all(&elements)?;
            let second = traverse_all(&elements)?;
            assert_eq!(first, second);
            assert_elements_match_text(TEXT, &elements)
        }

        /// `TryFrom<LazyElement>` takes the element by value and drops it inside the call, with
        /// the cache populated either beforehand or inside that same call.
        #[rstest]
        fn consuming_conversion_drops_the_element_inside_the_call<
            E: Decoder + Into<ReadConfig<E>>,
        >(
            #[values(AnyEncoding, TextEncoding_1_0)] encoding: E,
            #[values(true, false)] populate_first: bool,
        ) -> IonResult<()> {
            let elements = store_elements_then_drop_reader(encoding, TEXT)?;
            if populate_first {
                traverse_all(&elements)?;
            }
            let actual = elements
                .into_iter()
                .map(Element::try_from)
                .collect::<IonResult<Vec<Element>>>()?;
            let expected: Vec<Element> = Element::read_all(TEXT)?.into_iter().collect();
            assert_eq!(expected, actual);
            Ok(())
        }

        #[test]
        fn cached_containers_survive_moves() -> IonResult<()> {
            let elements = store_elements_then_drop_reader(TextEncoding_1_0, TEXT)?;
            let before = traverse_all(&elements)?;
            // Push one at a time so each element moves into `moved`'s buffer and the original
            // buffer is freed; `collect` could reuse the original allocation in place.
            let mut moved = Vec::new();
            for element in elements {
                moved.push(element);
            }
            assert_eq!(before, traverse_all(&moved)?);
            assert_elements_match_text(TEXT, &moved)
        }

        /// The cache is populated in the arena the reader is still using; advancing the reader
        /// must swap in a new arena instead of resetting that one. The later values allocate in
        /// the arena (container children, an escaped string), so a reset would overwrite the
        /// cached tree.
        #[test]
        fn cached_containers_survive_the_reader_advancing() -> IonResult<()> {
            let mut reader = Reader::new(
                TextEncoding_1_0,
                br#"[1, [2, "x"]] [3, [4, "y"]] "a\nb" [5, {c: 6}]"#.to_vec(),
            )?;
            let first = reader.expect_next()?.to_owned();
            let expected = Element::read_one(r#"[1, [2, "x"]]"#)?;
            assert_eq!(expected, Element::try_from(&first)?);
            for _ in 0..3 {
                Element::try_from(reader.expect_next()?)?;
            }
            assert_eq!(expected, Element::try_from(&first)?);
            drop(reader);
            assert_eq!(expected, Element::try_from(first)?);
            Ok(())
        }

        /// Operators only match inside an s-expression, so a stored operator must not be
        /// re-parsed on its own.
        #[test]
        fn stored_operators_survive_after_reader_drops() -> IonResult<()> {
            let mut reader = Reader::new(TextEncoding_1_0, b"(+ 1 -)".to_vec())?;
            let children = reader
                .expect_next()?
                .read()?
                .expect_sexp()?
                .iter()
                .map(|child| child.map(LazyValue::to_owned))
                .collect::<IonResult<Vec<_>>>()?;
            drop(reader);
            let actual = children
                .into_iter()
                .map(Element::try_from)
                .collect::<IonResult<Vec<Element>>>()?;
            let expected = vec![Element::symbol("+"), Element::from(1), Element::symbol("-")];
            assert_eq!(expected, actual);
            Ok(())
        }

        /// A container stored from a cached container shares that cache's parse, at every level,
        /// and it outlives every ancestor. A container stored straight from the reader is not
        /// parsed until it is read. Each case's second child holds only `z::[3, d::4]`.
        #[rstest]
        #[case::struct_parent(
            "{a: x:: /*c*/ [1, (2 +)], b: y::{c: z::[3, d::4]}}",
            "x::[1, (2 +)] y::{c: z::[3, d::4]}"
        )]
        #[case::list_parent(
            "[x:: /*c*/ [1, (2 +)], y::[z::[3, d::4]]]",
            "x::[1, (2 +)] y::[z::[3, d::4]]"
        )]
        #[case::sexp_parent("(x:: /*c*/ (2 +) y::(z::[3, d::4]))", "x::(2 +) y::(z::[3, d::4])")]
        fn containers_stored_from_a_cache_share_it<E: Decoder + Into<ReadConfig<E>>>(
            #[case] text: &str,
            #[case] children_text: &str,
            #[values(AnyEncoding, TextEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let elements = store_elements_then_drop_reader(encoding, text)?;
            let [parent] = elements.as_slice() else {
                panic!("expected one top-level value, found {}", elements.len());
            };
            assert!(
                !E::detached_is_parsed(&parent.detached_value),
                "a container stored from the reader was parsed before it was read"
            );

            let children = store_children(parent.as_lazy_value()?)?;
            let Some(owner) = E::detached_parse_owner(&parent.detached_value) else {
                panic!("reading the parent did not fill its cache");
            };
            let [_, second] = children.as_slice() else {
                panic!("expected two children, found {}", children.len());
            };
            for child in &children {
                assert_eq!(
                    Some(owner),
                    E::detached_parse_owner(&child.detached_value),
                    "a container stored from a cached parent does not share the parent's parse"
                );
            }

            let grandchildren = store_children(second.as_lazy_value()?)?;
            let [grandchild] = grandchildren.as_slice() else {
                panic!("expected one grandchild, found {}", grandchildren.len());
            };
            assert_eq!(
                Some(owner),
                E::detached_parse_owner(&grandchild.detached_value),
                "a container stored from a shared cache does not share that parse"
            );
            drop(elements);
            assert_elements_match_text(children_text, &children)?;
            drop(children);
            // The grandchild now holds the last `Rc` to the parse, which the consuming conversion
            // drops inside the call.
            let actual = grandchildren
                .into_iter()
                .map(Element::try_from)
                .collect::<IonResult<Vec<Element>>>()?;
            let expected: Vec<Element> = Element::read_all("z::[3, d::4]")?.into_iter().collect();
            assert_eq!(expected, actual);
            Ok(())
        }

        /// Every child stored from a cached container outlives the parent.
        #[test]
        fn children_of_a_cached_container_outlive_it() -> IonResult<()> {
            let elements =
                store_elements_then_drop_reader(TextEncoding_1_0, "{a: [1, (2 +)], b: x}")?;
            let [parent] = elements.as_slice() else {
                panic!("expected one top-level value, found {}", elements.len());
            };
            let children = store_children(parent.as_lazy_value()?)?;
            drop(elements);
            assert_elements_match_text("[1, (2 +)] x", &children)
        }

        /// Values stored from a streaming input whose window slides as the reader advances. With
        /// `read_while_live`, each element's cache is populated as soon as it is stored, so the
        /// window then shifts (copying the bytes the cache borrows) under populated caches, and
        /// each element's children are stored sharing that cache.
        #[rstest]
        fn values_survive_a_shifting_stream_window(
            #[values(false, true)] read_while_live: bool,
        ) -> IonResult<()> {
            const VALUE_COUNT: usize = 10;
            let filler = "x".repeat(500);
            let text = (0..VALUE_COUNT)
                .map(|index| format!("{{index: {index}, inner: ann::{{filler: \"{filler}\"}}}}"))
                .collect::<Vec<String>>()
                .join("\n");
            assert!(
                text.len() > 4 * 1024,
                "test data is too small to shift the window"
            );

            let mut reader = Reader::new(
                TextEncoding_1_0,
                BufReader::new(Cursor::new(text.clone().into_bytes())),
            )?;
            let mut elements = Vec::new();
            let mut children = Vec::new();
            for element in &mut reader {
                let element: LazyElement<TextEncoding_1_0> = element?;
                if read_while_live {
                    let stored = store_children(element.as_lazy_value()?)?;
                    let [_, inner] = stored.as_slice() else {
                        panic!("expected two fields, found {}", stored.len());
                    };
                    let owner = TextEncoding_1_0::detached_parse_owner(&element.detached_value);
                    assert!(owner.is_some(), "reading a record did not fill its cache");
                    assert_eq!(
                        owner,
                        TextEncoding_1_0::detached_parse_owner(&inner.detached_value),
                        "a container stored from a cached record does not share its parse"
                    );
                    children.extend(stored);
                }
                elements.push(element);
            }

            let max_stream_offset = elements
                .iter()
                .map(|element| element.io_buffer.stream_offset())
                .max()
                .unwrap_or(0);
            assert!(
                max_stream_offset > 0,
                "no stored element saw a shifted window"
            );
            if read_while_live {
                assert_elements_match_text(&text, &elements)?;
            }
            drop(reader);
            traverse_all(&elements)?;
            assert_elements_match_text(&text, &elements)?;
            drop(elements);
            if read_while_live {
                let children_text = (0..VALUE_COUNT)
                    .map(|index| format!("{index} ann::{{filler: \"{filler}\"}}"))
                    .collect::<Vec<String>>()
                    .join("\n");
                assert_elements_match_text(&children_text, &children)?;
                assert_annotations_match_text(&children_text, &children)?;
            }
            Ok(())
        }

        /// One of each header fact the accessors report, including a container of each type, a
        /// null container, and annotated containers.
        const HEADER_TEST_DATA: &str =
            "null.string 5 annotated::foo [1] (2) {a: 3} null.list ann::[4] ann:: /*c*/ (5)";

        /// The header accessors bypass `as_lazy_value()`, so check them against `LazyValue`'s.
        #[rstest]
        fn header_accessors_match_lazy_value<E: Decoder + Into<ReadConfig<E>>>(
            #[values(AnyEncoding, TextEncoding_1_0)] encoding: E,
        ) -> IonResult<()> {
            let elements = store_elements_then_drop_reader(encoding, HEADER_TEST_DATA)?;
            assert_eq!(9, elements.len(), "unexpected number of top-level values");
            assert_header_accessors_match_lazy_value(&elements)
        }

        /// After the first call, `as_lazy_value` on a stored container is served from its cache;
        /// calling it again neither re-parses nor allocates.
        #[test]
        fn repeated_reads_of_a_cached_container_do_not_grow_the_arena() -> IonResult<()> {
            let elements =
                store_elements_then_drop_reader(TextEncoding_1_0, "[1, [2, \"three\"], {a: 4}]")?;
            let [element] = elements.as_slice() else {
                panic!("expected one top-level value, found {}", elements.len());
            };
            // Populates the cache.
            element.as_lazy_value()?;

            // `allocated_bytes()` reports chunk capacity, so it only moves when the arena acquires
            // one; `binary_soundness_tests::header_accessors_do_not_grow_the_arena` shows this many
            // allocating calls is enough to move it.
            let allocated_bytes = || element.context.get_ref().allocator().allocated_bytes();
            let bytes_before = allocated_bytes();
            for _ in 0..1_000 {
                element.as_lazy_value()?;
            }
            assert_eq!(
                bytes_before,
                allocated_bytes(),
                "re-reading a cached container grew the arena"
            );
            Ok(())
        }
    }
}
