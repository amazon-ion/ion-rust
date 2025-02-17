#![allow(non_camel_case_types)]

use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{Decoder, HasRange, HasSpan, LazyRawValue, RawVersionMarker};
use crate::lazy::encoding::{TextEncoding, TextEncoding_1_0, TextEncoding_1_1};
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::span::Span;
use crate::lazy::text::buffer::TextBuffer;
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::{IonEncoding, IonResult, IonType, RawSymbolRef};
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::ops::Range;

/// A value that has been identified in the text input stream but whose data has not yet been read.
///
/// `LazyRawTextValue`s are "unresolved," which is to say that symbol values, annotations, and
/// struct field names may or may not include a text definition. (This is less common in Ion's text
/// format than in its binary format, but is still possible.) For a resolved lazy value that
/// includes a text definition for these items whenever one exists, see
/// [`crate::lazy::value::LazyValue`].
#[derive(Copy, Clone)]
pub struct LazyRawTextValue<'top, Encoding: TextEncoding> {
    pub(crate) encoded_value: EncodedTextValue<'top, Encoding>,
    pub(crate) input: TextBuffer<'top>,
}

impl<'top, Encoding: TextEncoding> LazyRawTextValue<'top, Encoding> {
    pub(crate) fn new(
        encoded_value: EncodedTextValue<'top, Encoding>,
        input: TextBuffer<'top>,
    ) -> Self {
        Self {
            encoded_value,
            input,
        }
    }
}

impl<'top, Encoding: TextEncoding> LazyRawTextValue<'top, Encoding> {
    pub fn data_range(&self) -> Range<usize> {
        // If the matched value has annotations, the `data_offset` will be the offset beyond
        // the annotations at which the value's data begins.
        let data_offset = self.encoded_value.data_offset();
        let data_length = self.input.len() - data_offset;
        // Add the input buffer's offset to the data offset to get the absolute offset.
        let start = self.input.offset() + data_offset;
        let end = start + data_length;
        start..end
    }

    pub fn has_annotations(&self) -> bool {
        self.encoded_value.data_offset() > 0
    }

    pub fn annotations_range(&self) -> Range<usize> {
        let annotations_length = self.encoded_value.data_offset();
        let start = self.input.offset();
        let end = start + annotations_length;
        start..end
    }

    pub fn annotations_span(&self) -> Span<'top> {
        let local_range = self.annotations_range();
        let bytes = &self.input.bytes()[..local_range.len()];
        Span::with_offset(local_range.start, bytes)
    }

    fn value_span(&self) -> Span<'top> {
        let start = self.encoded_value.data_offset();
        let bytes = &self.input.bytes()[start..];
        Span::with_offset(start, bytes)
    }

    /// Returns the total number of bytes used to represent the current value, including its
    /// annotations (if any) and its value.
    pub fn total_length(&self) -> usize {
        self.input.len()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawTextVersionMarker<'top, E: TextEncoding> {
    major: u8,
    minor: u8,
    input: TextBuffer<'top>,
    // We need distinct version marker types for 1.0 and 1.1 even though the data/logic is the same.
    // This allows us to implement a `From<LazyRawTextVersionMarker_1_x> for LazyRawAnyVersionMarker`
    // unambiguously for the two encodings.
    spooky: PhantomData<E>,
}

impl<'top, E: TextEncoding> LazyRawTextVersionMarker<'top, E> {
    pub fn new(input: TextBuffer<'top>, major: u8, minor: u8) -> LazyRawTextVersionMarker<'top, E> {
        Self {
            major,
            minor,
            input,
            spooky: PhantomData,
        }
    }
}

pub type LazyRawTextVersionMarker_1_0<'top> = LazyRawTextVersionMarker<'top, TextEncoding_1_0>;
pub type LazyRawTextVersionMarker_1_1<'top> = LazyRawTextVersionMarker<'top, TextEncoding_1_1>;

impl<'top, E: TextEncoding> HasSpan<'top> for LazyRawTextVersionMarker<'top, E> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl<'top, E: TextEncoding> HasRange for LazyRawTextVersionMarker<'top, E> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top, E: TextEncoding> RawVersionMarker<'top> for LazyRawTextVersionMarker<'top, E> {
    fn major_minor(&self) -> (u8, u8) {
        (self.major, self.minor)
    }

    fn stream_encoding_before_marker(&self) -> IonEncoding {
        IonEncoding::Text_1_0
    }
}

pub type LazyRawTextValue_1_0<'top> = LazyRawTextValue<'top, TextEncoding_1_0>;
pub type LazyRawTextValue_1_1<'top> = LazyRawTextValue<'top, TextEncoding_1_1>;

impl<'top, Encoding: TextEncoding> Debug for LazyRawTextValue<'top, Encoding> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Encoding::name())?;

        // Try to read the value
        match self.read() {
            // If we can read the value, show it
            Ok(value) => write!(f, " {{{value:?}}}"),
            // Otherwise, write out diagnostic information
            Err(e) => write!(
                f,
                " {{\n  encoded_value={:?}\n  {:?}\n  err={:?}\n}}\n",
                self.encoded_value, self.input, e
            ),
        }
    }
}

// ===== Ion-version-agnostic functionality =====
//
// These trait impls are common to all Ion versions, but require the caller to specify a type
// parameter.

impl<'top, Encoding: TextEncoding> HasRange for LazyRawTextValue<'top, Encoding> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top, Encoding: TextEncoding> HasSpan<'top> for LazyRawTextValue<'top, Encoding> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl<'top, Encoding: TextEncoding> LazyRawValue<'top, Encoding>
    for LazyRawTextValue<'top, Encoding>
{
    fn ion_type(&self) -> IonType {
        self.encoded_value.ion_type()
    }

    fn is_null(&self) -> bool {
        self.encoded_value.is_null()
    }

    fn is_delimited(&self) -> bool {
        false
    }

    fn has_annotations(&self) -> bool {
        self.has_annotations() // Inherent impl
    }

    fn annotations(&self) -> <Encoding as Decoder>::AnnotationsIterator<'top> {
        let range = self
            .encoded_value
            .annotations_range()
            .unwrap_or(self.input.offset()..self.input.offset());
        let annotations_bytes = self.input.slice(0, range.len());
        RawTextAnnotationsIterator::new(annotations_bytes)
    }

    fn read(&self) -> IonResult<RawValueRef<'top, Encoding>> {
        // Get the value's matched input, skipping over any annotations
        let matched_input = self.input.slice_to_end(self.encoded_value.data_offset());
        let allocator = self.input.context.allocator();

        use crate::lazy::text::matched::MatchedValue::*;
        let value_ref = match self.encoded_value.matched() {
            Null(ion_type) => RawValueRef::Null(ion_type),
            Bool(b) => RawValueRef::Bool(b),
            Int(i) => RawValueRef::Int(i.read(matched_input)?),
            Float(f) => RawValueRef::Float(f.read(matched_input)?),
            Decimal(d) => RawValueRef::Decimal(d.read(matched_input)?),
            Timestamp(t) => RawValueRef::Timestamp(t.read(matched_input)?),
            String(s) => RawValueRef::String(s.read(allocator, matched_input)?),
            Symbol(s) => RawValueRef::Symbol(s.read(allocator, matched_input)?),
            Blob(b) => RawValueRef::Blob(b.read(allocator, matched_input)?),
            Clob(c) => RawValueRef::Clob(c.read(allocator, matched_input)?),
            List(_) => RawValueRef::List(Encoding::List::<'top>::from_value(*self)),
            SExp(_) => RawValueRef::SExp(Encoding::SExp::<'top>::from_value(*self)),
            Struct(_) => RawValueRef::Struct(Encoding::Struct::from_value(*self)),
        };
        Ok(value_ref)
    }

    fn annotations_span(&self) -> Span<'top> {
        self.annotations_span() // Inherent impl
    }

    fn value_span(&self) -> Span<'top> {
        self.value_span() // Inherent impl
    }

    fn with_backing_data(&self, span: Span<'top>) -> Self {
        Self {
            input: TextBuffer::from_span(self.input.context(), span, true),
            ..*self
        }
    }
}

pub struct RawTextAnnotationsIterator<'data> {
    input: TextBuffer<'data>,
    has_returned_error: bool,
}

impl<'top> RawTextAnnotationsIterator<'top> {
    pub(crate) fn new(input: TextBuffer<'top>) -> Self {
        debug_assert!(input.is_final_data());
        RawTextAnnotationsIterator {
            input,
            has_returned_error: false,
        }
    }
}

impl<'top> Iterator for RawTextAnnotationsIterator<'top> {
    type Item = IonResult<RawSymbolRef<'top>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error || self.input.is_empty() {
            return None;
        }

        // Match the first annotation in the input. In order for this iterator to be created,
        // the parser already successfully matched this input once before, so we know it will succeed.
        use winnow::Parser;
        let (symbol, matched_input) = TextBuffer::match_annotation
            .parse_next(&mut self.input)
            .expect("annotations were already matched successfully by this parser");
        let text = match symbol.read(self.input.context.allocator(), matched_input) {
            Ok(text) => text,
            Err(e) => {
                self.has_returned_error = true;
                return Some(Err(e));
            }
        };
        Some(Ok(text))
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::text::buffer::TextBuffer;
    use crate::lazy::text::value::RawTextAnnotationsIterator;
    use crate::{IonResult, RawSymbolRef};

    #[test]
    fn iterate_annotations() -> IonResult<()> {
        fn test(input: &str) -> IonResult<()> {
            let encoding_context = EncodingContext::empty();
            let context = encoding_context.get_ref();
            let input = TextBuffer::new(context, input.as_bytes());
            let mut iter = RawTextAnnotationsIterator::new(input);
            assert_eq!(iter.next().unwrap()?, RawSymbolRef::Text("foo"));
            assert_eq!(iter.next().unwrap()?, RawSymbolRef::Text("bar"));
            assert_eq!(iter.next().unwrap()?, RawSymbolRef::Text("baz"));
            Ok(())
        }
        test("foo::bar::baz::")?;
        test("foo         ::     'bar'  ::   baz::")?;
        test("foo /*comment*/ :://comment\nbar\n::'baz'::")?;
        Ok(())
    }
}
