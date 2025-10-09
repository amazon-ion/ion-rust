use crate::lazy::decoder::Decoder;
use crate::lazy::expanded::lazy_element::LazyElement;
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, IoBufferSource, LazyExpandedValue,
};
use crate::lazy::value_ref::ValueRef;
use crate::location::SourceLocation;
use crate::result::IonFailure;
use crate::symbol_ref::AsSymbolRef;
use crate::{
    try_or_some_err, Annotations, Element, ExpandedValueSource, HasSpan, IntoAnnotatedElement,
    IonError, IonResult, IonType, LazyRawValue, Span, SymbolRef, SymbolTable, Value,
};

/// A value in a binary Ion stream whose header has been parsed but whose body (i.e. its data) has
/// not. A `LazyValue` is immutable; its data can be read any number of times.
///
/// Note that `LazyValue` does not memoize the result of a read. Each time that [`LazyValue::read()`]
/// is called, the serialized body of the value is parsed again.
///
/// ```
///# use ion_rs::IonResult;
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
/// ```
#[derive(Debug, Copy, Clone)]
pub struct LazyValue<'top, D: Decoder> {
    pub(crate) expanded_value: LazyExpandedValue<'top, D>,
}

impl<'top, D: Decoder> LazyValue<'top, D> {
    pub(crate) fn new(expanded_value: LazyExpandedValue<'top, D>) -> LazyValue<'top, D> {
        LazyValue { expanded_value }
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        self.expanded_value.context.symbol_table()
    }

    /// Returns the [`IonType`] of this value.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{Element, IonType, Reader};
    /// use ion_rs::v1_0::Binary;
    ///
    /// let element: Element = "hello".into();
    /// let binary_ion = element.encode_as(Binary)?;
    ///
    /// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
    ///
    /// // Get the first lazy value from the stream.
    /// let lazy_value = lazy_reader.expect_next()?;
    ///
    /// // Check its type
    /// assert_eq!(lazy_value.ion_type(), IonType::String);
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn ion_type(&self) -> IonType {
        self.expanded_value.ion_type()
    }

    pub fn is_container(&self) -> bool {
        matches!(
            self.expanded_value.ion_type(),
            IonType::List | IonType::SExp | IonType::Struct
        )
    }

    pub fn is_scalar(&self) -> bool {
        !self.is_container()
    }

    /// Returns the `LazyExpandedValue` backing this `LazyValue`. The expanded value can be used to
    /// determine whether this value was part of the data stream, part of a template, or constructed
    /// by a macro invocation.
    pub fn expanded(&self) -> LazyExpandedValue<'top, D> {
        self.expanded_value
    }

    /// If this value came from a raw value literal encoded in the data stream (that is: it was not
    /// an ephemeral value resulting from macro expansion), returns that encoding's representation
    /// of the raw value. Otherwise, returns `None`.
    pub fn raw(&self) -> Option<D::Value<'top>> {
        if let ExpandedValueSource::ValueLiteral(raw_value) = self.expanded().source() {
            Some(raw_value)
        } else {
            None
        }
    }

    /// Returns `true` if this value is any form of `null`, including
    /// `null`, `null.string`, `null.int`, etc. Otherwise, returns `false`.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{Element, IonType, Reader};
    /// use ion_rs::v1_0::Binary;
    ///
    /// let element = Element::string("hello");
    /// let binary_ion = element.encode_as(Binary)?;
    /// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
    /// let lazy_value = lazy_reader.expect_next()?;
    /// assert!(!lazy_value.is_null());
    ///
    /// let element: Element = Element::null(IonType::String);
    /// let binary_ion = element.encode_as(Binary)?;
    /// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
    /// let lazy_value = lazy_reader.expect_next()?;
    /// assert!(lazy_value.is_null());
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn is_null(&self) -> bool {
        self.expanded_value.is_null()
    }

    /// Returns an iterator over the annotations on this value. If this value has no annotations,
    /// the resulting iterator will be empty.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{Element, IntoAnnotatedElement, Reader};
    /// use ion_rs::v1_0::Binary;
    ///
    /// let element: Element = "hello".with_annotations(["foo", "bar", "baz"]);
    /// let binary_ion = element.encode_as(Binary)?;
    ///
    /// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
    ///
    /// // Get the first lazy value from the stream.
    /// let lazy_value = lazy_reader.expect_next()?;
    ///
    /// // Inspect its annotations.
    /// let mut annotations = lazy_value.annotations();
    /// assert_eq!(annotations.next().unwrap()?, "foo");
    /// assert_eq!(annotations.next().unwrap()?, "bar");
    /// assert_eq!(annotations.next().unwrap()?, "baz");
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn annotations(&self) -> AnnotationsIterator<'top, D> {
        AnnotationsIterator {
            expanded_annotations: self.expanded_value.annotations(),
            context: self.expanded_value.context,
        }
    }

    pub fn has_annotations(&self) -> bool {
        self.expanded_value.has_annotations()
    }

    /// Reads the body of this value (that is: its data) and returns it as a [`ValueRef`].
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{Element, IntoAnnotatedElement, Reader};
    /// use ion_rs::v1_0::Binary;
    /// use ion_rs::ValueRef;
    ///
    /// let element: Element = "hello".with_annotations(["foo", "bar", "baz"]);
    /// let binary_ion = element.encode_as(Binary)?;
    ///
    /// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
    ///
    /// // Get the first lazy value from the stream.
    /// let lazy_value = lazy_reader.expect_next()?;
    ///
    /// if let ValueRef::String(text) = lazy_value.read()? {
    ///     assert_eq!(text, "hello");
    /// } else {
    ///     panic!("Expected a string.");
    /// }
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn read(&self) -> IonResult<ValueRef<'top, D>> {
        self.expanded_value.read_resolved()
    }

    pub(crate) fn context(&self) -> EncodingContextRef<'top> {
        self.expanded_value.context()
    }

    pub fn location(&self) -> SourceLocation {
        if let Some(raw) = self.raw() {
            if raw.encoding().is_text() {
                self.expanded_value
                    .context()
                    .location_for_span(self.expanded_value.span())
                    .unwrap_or_default()
            } else {
                // No row/column for binary Ion
                SourceLocation::empty()
            }
        } else {
            SourceLocation::empty()
        }
    }

    pub fn to_owned(self) -> LazyElement<D> {
        // Clone the `EncodingContext`, which will also bump the reference counts for the resources
        // it owns.
        let context = self.context().context.clone();

        let source = if let ExpandedValueSource::ValueLiteral(raw_value) =
            self.expanded_value.source
        {
            // If the value's source is a `ValueLiteral`, then it may hold references to bytes in the input buffer.
            // We need to modify the source to point to heap data that is owned by `context`.
            // First, get the `IoBufferSource` and ask it for a shared copy of the IoBuffer.
            // SAFETY: `io_buffer_source` is an `UnsafeCell` to allow us to set it from the `StreamingRawReader`
            //         after each top-level value. Unfortunately, that means we need to use `unsafe` to access it here.
            let IoBufferSource::IoBuffer(ref io_buffer) =
                (unsafe { &*context.io_buffer_source.get() })
            else {
                unreachable!("tried to access cloned EncodingContext IoBuffer but it didn't exist");
            };
            // Take note of all the ValueLiteral's recorded offsets.
            let value_span = raw_value.span();
            let value_offset = value_span.offset();
            let value_length = value_span.len();
            // Now, swap out the backing data for a slice of the `IoBuffer`.
            // The value begins at stream position `value_offset`.
            // The buffer begins at `io_buffer.stream_offset()`.
            // To find the serialized value within the buffer,
            // subtract the buffer's offset from the value's.
            let local_offset = value_offset - io_buffer.stream_offset();
            let value_bytes = &io_buffer.all_bytes()[local_offset..local_offset + value_length];
            // Construct a new span that is backed by the IoBuffer.
            let backing_span = Span::with_offset(value_offset, value_bytes);
            let raw_value = raw_value.with_backing_data(backing_span);
            ExpandedValueSource::ValueLiteral(raw_value)
        } else {
            // If the value is not a literal, then it lives in the bump allocator.
            // That is to say, it is already heap data that is owned by `context`.
            self.expanded_value.source
        };
        // Now that we have upheld the invariants required by `LazyElement::new`, we can safely call it.
        unsafe { LazyElement::new(context, source) }
    }
}

impl<'top, D: Decoder> TryFrom<LazyValue<'top, D>> for Element {
    type Error = IonError;

    fn try_from(lazy_value: LazyValue<'top, D>) -> Result<Self, Self::Error> {
        let value: Value = lazy_value.read()?.try_into()?;
        if lazy_value.has_annotations() {
            let annotations: Annotations = lazy_value.annotations().try_into()?;
            Ok(value
                .with_annotations(annotations)
                .with_location(lazy_value.location()))
        } else {
            Ok(<Value as Into<Element>>::into(value).with_location(lazy_value.location()))
        }
    }
}

/// Iterates over a slice of bytes, lazily reading them as a sequence of symbol tokens encoded
/// using the format described by generic type parameter `D`.
pub struct AnnotationsIterator<'top, D: Decoder> {
    pub(crate) expanded_annotations: ExpandedAnnotationsIterator<'top, D>,
    pub(crate) context: EncodingContextRef<'top>,
}

impl<D: Decoder> AnnotationsIterator<'_, D> {
    /// Returns `Ok(true)` if this annotations iterator matches the provided sequence exactly, or
    /// `Ok(false)` if not. If a decoding error occurs while visiting and resolving each annotation,
    /// returns an `Err(IonError)`.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{Element, Reader};
    /// use ion_rs::v1_0::Binary;
    ///
    /// let element = Element::read_one("foo::bar::baz::99")?;
    /// let binary_ion = element.encode_as(Binary)?;
    /// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
    ///
    /// // Get the first value from the stream
    /// let lazy_value = lazy_reader.expect_next()?;
    ///
    /// assert!(lazy_value.annotations().are(["foo", "bar", "baz"])?);
    ///
    /// assert!(!lazy_value.annotations().are(["foo", "bar", "baz", "quux"])?);
    /// assert!(!lazy_value.annotations().are(["baz", "bar", "foo"])?);
    /// assert!(!lazy_value.annotations().are(["foo", "bar"])?);
    /// assert!(!lazy_value.annotations().are(["foo"])?);
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn are<A: AsSymbolRef, I: IntoIterator<Item = A>>(
        mut self,
        annotations_to_match: I,
    ) -> IonResult<bool> {
        // We've exhausted `annotations_to_match`, now make sure `self` is empty
        Ok(self.starts_with(annotations_to_match)? && self.next().is_none())
    }

    /// Returns `Ok(true)` if this annotations iterator's first elements match the provided sequence
    /// or `Ok(false)` if not. If a decoding error occurs while visiting and resolving each annotation,
    /// returns an `Err(IonError)`.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{Element, Reader};
    /// use ion_rs::v1_0::Binary;
    ///
    /// let element = Element::read_one("foo::bar::baz::99")?;
    /// let binary_ion = element.encode_as(Binary)?;
    /// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
    ///
    /// // Get the first value from the stream
    /// let lazy_value = lazy_reader.expect_next()?;
    ///
    /// assert!(lazy_value.annotations().starts_with(["foo"])?);
    /// assert!(lazy_value.annotations().starts_with(["foo", "bar"])?);
    /// assert!(lazy_value.annotations().starts_with(["foo", "bar", "baz"])?);
    ///
    /// assert!(!lazy_value.annotations().starts_with(["foo", "bar", "baz", "quux"])?);
    /// assert!(!lazy_value.annotations().starts_with(["baz", "bar", "foo"])?);
    /// assert!(!lazy_value.annotations().starts_with(["bar", "foo"])?);
    /// assert!(!lazy_value.annotations().starts_with(["bar"])?);
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn starts_with<A: AsSymbolRef, I: IntoIterator<Item = A>>(
        &mut self,
        annotations_to_match: I,
    ) -> IonResult<bool> {
        for to_match in annotations_to_match {
            match self.next() {
                Some(Ok(actual)) if actual == to_match => {}
                Some(Err(e)) => return Err(e),
                Some(_) | None => return Ok(false),
            }
        }
        Ok(true)
    }

    /// Like [`Self::are`], but returns an [`IonError::Decoding`] if the iterator's annotations
    /// don't match the provided sequence exactly.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{Element, Reader};
    /// use ion_rs::v1_0::Binary;
    ///
    /// let element = Element::read_one("foo::bar::baz::99")?;
    /// let binary_ion = element.encode_as(Binary)?;
    /// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
    ///
    /// // Get the first value from the stream
    /// let lazy_value = lazy_reader.expect_next()?;
    ///
    /// assert!(lazy_value.annotations().expect(["foo", "bar", "baz"]).is_ok());
    ///
    /// assert!(lazy_value.annotations().expect(["foo", "bar", "baz", "quux"]).is_err());
    /// assert!(lazy_value.annotations().expect(["baz", "bar", "foo"]).is_err());
    /// assert!(lazy_value.annotations().expect(["foo", "bar"]).is_err());
    /// assert!(lazy_value.annotations().expect(["foo"]).is_err());
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn expect<A: AsSymbolRef, I: IntoIterator<Item = A>>(
        self,
        annotations_to_match: I,
    ) -> IonResult<()> {
        if self.are(annotations_to_match)? {
            Ok(())
        } else {
            IonResult::decoding_error("value annotations did not match expected sequence")
        }
    }
}

impl<'top, D: Decoder> Iterator for AnnotationsIterator<'top, D> {
    type Item = IonResult<SymbolRef<'top>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_annotation = try_or_some_err!(self.expanded_annotations.next()?);
        Some(Ok(try_or_some_err!(
            raw_annotation.resolve("an annotation", self.context)
        )))
    }
}

impl<'top, D: Decoder> TryFrom<AnnotationsIterator<'top, D>> for Annotations {
    type Error = IonError;

    fn try_from(iter: AnnotationsIterator<'top, D>) -> Result<Self, Self::Error> {
        let annotations = iter
            .map(|symbol_ref| match symbol_ref {
                Ok(symbol_ref) => Ok(symbol_ref.to_owned()),
                Err(e) => Err(e),
            })
            .collect::<IonResult<Vec<_>>>()?;
        Ok(Annotations::from(annotations))
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Float;
    use rstest::*;
    use std::io;
    use std::io::{Cursor, Read};

    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::expanded::lazy_element::LazyElement;
    use crate::location::SourceLocation;
    use crate::{
        ion_list, ion_sexp, ion_struct, v1_0, AnyEncoding, Decimal, Decoder, IonResult, IonType,
        LazyValue, Reader, Symbol, Timestamp,
    };
    use crate::{Element, IntoAnnotatedElement};

    #[test]
    fn annotations_are() -> IonResult<()> {
        let ion_data = to_binary_ion("foo::bar::baz::5")?;
        let mut reader = Reader::new(v1_0::Binary, ion_data)?;
        let first = reader.expect_next()?;
        assert!(first.annotations().are(["foo", "bar", "baz"])?);

        // No similarity
        assert!(!first.annotations().are(["quux", "quuz"])?);

        // Prefix subset
        assert!(!first.annotations().are(["foo", "bar"])?);
        assert!(!first.annotations().are(["foo"])?);

        // Superset
        assert!(!first.annotations().are(["foo", "bar", "baz", "quux"])?);

        Ok(())
    }

    fn lazy_value_equals(ion_text: &str, expected: impl Into<Element>) -> IonResult<()> {
        let binary_ion = to_binary_ion(ion_text)?;
        let mut reader = Reader::new(v1_0::Binary, binary_ion)?;
        let value = reader.expect_next()?;
        let actual: Element = value.try_into()?;
        let expected = expected.into();
        assert_eq!(actual, expected);
        Ok(())
    }

    #[rstest]
    #[case::null("null", IonType::Null)]
    #[case::typed_null("null.list", IonType::List)]
    #[case::annotated_typed_null("foo::null.list", IonType::List.with_annotations(["foo"]))]
    #[case::boolean("false", false)]
    #[case::negative_int("-1", -1)]
    #[case::int_zero("0", 0)]
    #[case::positive_int("1", 1)]
    #[case::float_zero("0e0", 0f64)]
    #[case::float("2.5e0", 2.5f64)]
    #[case::special_float("-inf", f64::neg_infinity())]
    #[case::decimal("3.14159", Decimal::new(314159, -5))]
    #[case::timestamp("2023-04-29T", Timestamp::with_ymd(2023, 4, 29).build()?)]
    #[case::symbol("foo", Symbol::owned("foo"))]
    #[case::string("\"hello\"", "hello")]
    #[case::blob("{{Blob}}", Element::blob([0x06, 0x5A, 0x1B]))]
    #[case::clob("{{\"Clob\"}}", Element::clob("Clob".as_bytes()))]
    #[case::list("[1, 2, 3]", ion_list![1, 2, 3])]
    #[case::sexp("(1 2 3)", ion_sexp!(1 2 3))]
    #[case::struct_("{foo: 1, bar: 2}", ion_struct! {"foo": 1, "bar": 2})]
    fn try_into_element(
        #[case] ion_text: &str,
        #[case] expected: impl Into<Element>,
    ) -> IonResult<()> {
        lazy_value_equals(ion_text, expected)?;
        Ok(())
    }

    #[test]
    fn try_into_element_error() -> IonResult<()> {
        #[rustfmt::skip]
            let binary_ion: &[u8] = &[
            // IVM
            0xE0, 0x01, 0x00, 0xEA,
            // Opcode for a 4-byte list
            0xB4,
            // There are 4 bytes here, so reading the list (not yet reading its contents) will
            // succeed. However, the 4 bytes are another IVM in value position, which is illegal.
            // When the reader goes to materialize the contents of the list, it will produce
            // an error.
            0xE0, 0x01, 0x00, 0xEA,
        ];
        let mut reader = Reader::new(v1_0::Binary, binary_ion)?;
        let list = reader.expect_next()?.read()?.expect_list()?;
        let result: IonResult<Element> = list.try_into();
        assert!(result.is_err());
        Ok(())
    }

    #[rstest]
    #[case::negative_int("-1")]
    #[case::positive_int("1")]
    #[case::float("2.5e0")]
    #[case::special_float("-inf")]
    #[case::decimal("3.14159")]
    #[case::timestamp("2023-04-29T")]
    #[case::symbol("foo")]
    #[case::string("\"hello\"")]
    #[case::blob("{{Blob}}")]
    #[case::clob("{{\"Clob\"}}")]
    #[case::list("[1, 2, 3]")]
    #[case::sexp("(1 2 3)")]
    #[case::struct_("{foo: 1, bar: 2}")]
    fn try_into_element_incomplete(#[case] ion_text: &str) -> IonResult<()> {
        let mut binary_ion = to_binary_ion(ion_text)?;
        let _oops_i_lost_a_byte = binary_ion.pop().unwrap();
        let mut reader = Reader::new(v1_0::Binary, binary_ion)?;
        let result = reader.expect_next();
        assert!(matches!(result, Err(crate::IonError::Incomplete(_))));
        Ok(())
    }

    #[rstest]
    #[case::no_crlf( "{}\"hello\"",       [(1, 1), (1, 3)])]
    #[case::cr_lf_lf("{}\r\n\n\"hello\"", [(1, 1), (3, 1)] )]
    #[case::lf_lf_cr("{}\n\n\r\"hello\"", [(1, 1), (3, 2)] )]
    #[case::lf_cr_cr("{}\n\r\r\"hello\"", [(1, 1), (2, 3)] )]
    #[case::lf_cr_lf("{}\n\r\n\"hello\"", [(1, 1), (3, 1)] )]
    #[case::cr_lf_lf("{}\r\n\n\"hello\"", [(1, 1), (3, 1)] )]
    #[case::cr_lf_cr("{}\r\n\r\"hello\"", [(1, 1), (2, 2)] )]
    #[case::cr_cr_lf("{}\r\r\n\"hello\"", [(1, 1), (2, 1)] )]
    #[case::cr_cr_cr("{}\r\r\r\"hello\"", [(1, 1), (1, 6)] )]
    #[case::nl_after("{}\"hello\"\n\n",   [(1, 1), (1, 3)])]
    #[case::tabs(    "{}\n\t\t\"hello\"", [(1, 1), (2, 3)] )]
    #[case::tabs_after("{}\"hello\"\t\t", [(1, 1), (1, 3)])]
    #[case::mix_tabs_and_newlines("{}\n\t\n\"hello\"",[(1, 1), (3, 1)])]
    #[case::long_string("{}\n\n'''long \n\r\n\t hello'''", [(1, 1), (3, 1)])]
    #[case::comment("{}\n\n /*multiline \n comment*/'''long \n\r\n\t hello'''", [(1, 1), (4, 11)])]
    #[case::on_same_line_as_preceding_multiline_value("{\n}\"hello\"", [(1, 1), (2, 2)])]
    #[case::values_in_struct("{foo:1,bar:2}", [(1, 1), (1, 6), (1, 12)])]
    #[case::values_in_multiline_struct("{\n  foo:1,\n  bar:2,\n}", [(1, 1), (2, 7), (3, 7)])]
    #[case::values_in_lists("[1,2,3,4]", [(1, 1), (1, 2), (1, 4), (1, 6), (1, 8)])]
    #[case::values_in_multiline_lists(
        "[\n  1,\n  2,\n  3,\n  4\n]",
        [(1, 1), (2, 3), (3, 3), (4, 3), (5, 3)],
    )]
    #[case::values_in_sexps("(1 2 3 4)", [(1, 1), (1, 2), (1, 4), (1, 6), (1, 8)])]
    #[case::values_in_multiline_sexps(
        "(foo (bar 123)\n     (bar 456)\n     (bar 789))",
        // (      foo     (       bar     123   )
        [(1, 1), (1, 2), (1, 6), (1, 7), (1, 11),
        //                (       bar     456   )
                         (2, 6), (2, 7), (2, 11),
        //                (       bar     789   )  )
                         (3, 6), (3, 7), (3, 11)],
    )]
    #[case::deeply_nested_containers(
        "{\n  foo:{a:1,b:2},\n  bar:[a,b,c],\n  baz:(foo (bar)\n           (quux)),\n}",
        // {
        [(1, 1),
        // foo: {       a:1,     b:2    },
               (2, 7), (2, 10), (2, 14),
        // bar: [       a,      b,       c      ],
               (3, 7), (3, 8), (3, 10), (3, 12),
        // baz: (       foo     (        bar    )
               (4, 7), (4, 8), (4, 12), (4, 13),
        //                      (        quux   ) )
                               (5, 12), (5, 13),
        // }
        ],
    )]
    #[case::multiple_top_level_containers(
        "{foo:1,bar:2}\n{\n  foo:1,\n  bar:[a,b,c],\n}\n{foo:1,bar:2}\n{\n  foo:1,\n  bar:[a,b,c],\n}",
        [(1, 1), (1, 6), (1, 12), (2, 1), (3, 7), (4, 7), (4, 8), (4, 10), (4, 12),
        (6, 1), (6, 6), (6, 12), (7, 1), (8, 7), (9, 7), (9, 8), (9, 10), (9, 12)],
    )]
    #[case::multiple_top_level_containers_ion_1_1(
            "$ion_1_1\n{foo:1,bar:2}\n{\n  foo:1,\n  bar:[a,b,c],\n}\n{foo:1,bar:2}\n{\n  foo:1,\n  bar:[a,b,c],\n}",
            [(2, 1), (2, 6), (2, 12), (3, 1), (4, 7), (5, 7), (5, 8), (5, 10), (5, 12),
            (7, 1), (7, 6), (7, 12), (8, 1), (9, 7), (10, 7), (10, 8), (10, 10), (10, 12)],
    )]
    #[case::binary_1_0_data(
        [
            0xE0u8, 0x01, 0x00, 0xEA, // IVM
            0x85, 65, 10, 66, 10, 67, // String: "A\nB\nC"
            0x85, 68, 10, 69, 10, 70, // String: "D\nE\nF"
        ],
        [/* no locations */],
    )]
    #[case::binary_1_1_data(
            [
                0xE0u8, 0x01, 0x01, 0xEA, // IVM
                0x95, 65, 10, 66, 10, 67, // String: "A\nB\nC"
                0x95, 68, 10, 69, 10, 70, // String: "D\nE\nF"
            ],
            [/* no locations */],
    )]
    fn location_test_slice_input<const N: usize, I: AsRef<[u8]>>(
        #[case] ion_input: I,
        #[case] expected_locations: [(usize, usize); N],
    ) -> IonResult<()> {
        let values: Vec<_> =
            Reader::new(AnyEncoding, ion_input.as_ref())?.collect::<IonResult<_>>()?;
        let actual_locations: Vec<_> = get_locations_of_lazy_elements(values)?
            .into_iter()
            // Only collect those where location is Some(...)
            .filter_map(|it| it.row_column())
            .collect();
        assert_eq!(&expected_locations, actual_locations.as_slice());
        Ok(())
    }

    #[rstest]
    #[case::no_crlf( "{}\"hello\"",       [(1, 1), (1, 3)])]
    #[case::lf_lf_lf("{}\n\n\n\"hello\"", [(1, 1), (4, 1)] )]
    #[case::lf_lf_cr("{}\n\n\r\"hello\"", [(1, 1), (3, 2)] )]
    #[case::lf_cr_cr("{}\n\r\r\"hello\"", [(1, 1), (2, 3)] )]
    #[case::lf_cr_lf("{}\n\r\n\"hello\"", [(1, 1), (3, 1)] )]
    #[case::cr_lf_lf("{}\r\n\n\"hello\"", [(1, 1), (3, 1)] )]
    #[case::cr_lf_cr("{}\r\n\r\"hello\"", [(1, 1), (2, 2)] )]
    #[case::cr_cr_lf("{}\r\r\n\"hello\"", [(1, 1), (2, 1)] )]
    #[case::cr_cr_cr("{}\r\r\r\"hello\"", [(1, 1), (1, 6)] )]
    #[case::nl_after("{}\"hello\"\n\n",   [(1, 1), (1, 3)])]
    #[case::tabs(    "{}\n\t\t\"hello\"", [(1, 1), (2, 3)] )]
    #[case::tabs_after("{}\"hello\"\t\t", [(1, 1), (1, 3)])]
    #[case::mix_tabs_and_newlines("{}\n\t\n\"hello\"",[(1, 1), (3, 1)])]
    #[case::long_string("{}\n\n'''long \n\r\n\t hello'''", [(1, 1), (3, 1)])]
    #[case::comment("{}\n\n /*multiline \n comment*/'''long \n\r\n\t hello'''", [(1, 1), (4, 11)])]
    #[case::on_same_line_as_preceding_multiline_value("{\n}\"hello\"", [(1, 1), (2, 2)])]
    #[case::values_in_struct("{foo:1,bar:2}", [(1, 1), (1, 6), (1, 12)])]
    #[case::values_in_multiline_struct("{\n  foo:1,\n  bar:2,\n}", [(1, 1), (2, 7), (3, 7)])]
    #[case::values_in_lists("[1,2,3,4]", [(1, 1), (1, 2), (1, 4), (1, 6), (1, 8)])]
    #[case::values_in_multiline_lists(
        "[\n  1,\n  2,\n  3,\n  4\n]",
        [(1, 1), (2, 3), (3, 3), (4, 3), (5, 3)],
    )]
    #[case::values_in_sexps("(1 2 3 4)", [(1, 1), (1, 2), (1, 4), (1, 6), (1, 8)])]
    #[case::values_in_multiline_sexps(
        "(foo (bar 123)\n     (bar 456)\n     (bar 789))",
        // (      foo     (       bar     123   )
        [(1, 1), (1, 2), (1, 6), (1, 7), (1, 11),
        //                (       bar     456   )
                         (2, 6), (2, 7), (2, 11),
        //                (       bar     789   )  )
                         (3, 6), (3, 7), (3, 11)],
    )]
    #[case::deeply_nested_containers(
        "{\n  foo:{a:1,b:2},\n  bar:[a,b,c],\n  baz:(foo (bar)\n           (quux)),\n}",
        // {
        [(1, 1),
        // foo: {       a:1,     b:2    },
               (2, 7), (2, 10), (2, 14),
        // bar: [       a,      b,       c      ],
               (3, 7), (3, 8), (3, 10), (3, 12),
        // baz: (       foo     (        bar    )
               (4, 7), (4, 8), (4, 12), (4, 13),
        //                      (        quux   ) )
                               (5, 12), (5, 13),
        // }
        ],
    )]
    #[case::multiple_top_level_containers(
        "{foo:1,bar:2}\n{\n  foo:1,\n  bar:[a,b,c],\n}\n{foo:1,bar:2}\n{\n  foo:1,\n  bar:[a,b,c],\n}",
        [(1, 1), (1, 6), (1, 12), (2, 1), (3, 7), (4, 7), (4, 8), (4, 10), (4, 12),
        (6, 1), (6, 6), (6, 12), (7, 1), (8, 7), (9, 7), (9, 8), (9, 10), (9, 12)],
    )]
    #[case::multiple_top_level_containers_ion_1_1(
            "$ion_1_1\n{foo:1,bar:2}\n{\n  foo:1,\n  bar:[a,b,c],\n}\n{foo:1,bar:2}\n{\n  foo:1,\n  bar:[a,b,c],\n}",
            [(2, 1), (2, 6), (2, 12), (3, 1), (4, 7), (5, 7), (5, 8), (5, 10), (5, 12),
            (7, 1), (7, 6), (7, 12), (8, 1), (9, 7), (10, 7), (10, 8), (10, 10), (10, 12)],
    )]
    // FIXME: Currently failing because of https://github.com/amazon-ion/ion-rust/issues/954
    // #[case::binary_1_0_data(
    //     [
    //         0xE0u8, 0x01, 0x00, 0xEA, // IVM
    //         0x85, 65, 10, 66, 10, 67, // String: "A\nB\nC"
    //         0x85, 68, 10, 69, 10, 70, // String: "D\nE\nF"
    //     ],
    //     [/* no locations */],
    // )]
    // #[case::binary_1_1_data(
    //         [
    //             0xE0u8, 0x01, 0x01, 0xEA, // IVM
    //             0x95, 65, 10, 66, 10, 67, // String: "A\nB\nC"
    //             0x95, 68, 10, 69, 10, 70, // String: "D\nE\nF"
    //         ],
    //         [/* no locations */],
    // )]
    fn location_test_stream_input<const N: usize, I: AsRef<[u8]>>(
        #[case] ion_input: I,
        #[case] expected_locations: [(usize, usize); N],
    ) -> IonResult<()> {
        // Wrapping each byte in an `io::Chain`
        let mut input: Box<dyn Read> = Box::new(io::empty());
        for input_byte in ion_input.as_ref().iter().copied() {
            input = Box::new(input.chain(Cursor::new([input_byte])));
        }
        let values: Vec<_> = Reader::new(AnyEncoding, input)?.collect::<IonResult<_>>()?;
        let actual_locations: Vec<_> = get_locations_of_lazy_elements(values)?
            .into_iter()
            // Only collect those where location is Some(...)
            .filter_map(|it| it.row_column())
            .collect();
        assert_eq!(&expected_locations, actual_locations.as_slice());
        Ok(())
    }

    fn get_locations_of_lazy_elements<E: Decoder>(
        values: Vec<LazyElement<E>>,
    ) -> IonResult<Vec<SourceLocation>> {
        let mut locations = vec![];
        for lazy_element in values {
            locations.push(lazy_element.as_lazy_value().location());
            let contained_values = match lazy_element.ion_type() {
                IonType::List => lazy_element
                    .read()?
                    .expect_list()?
                    .iter()
                    .map(Result::unwrap)
                    .map(LazyValue::into)
                    .collect(),
                IonType::SExp => lazy_element
                    .read()?
                    .expect_sexp()?
                    .iter()
                    .map(Result::unwrap)
                    .map(LazyValue::into)
                    .collect(),
                IonType::Struct => lazy_element
                    .read()?
                    .expect_struct()?
                    .iter()
                    .map(|f| f.unwrap().value())
                    .map(LazyValue::into)
                    .collect(),
                _ => vec![],
            };
            locations.extend(get_locations_of_lazy_elements(contained_values)?);
        }
        Ok(locations)
    }
}
