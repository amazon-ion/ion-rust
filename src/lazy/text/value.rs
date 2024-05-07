#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::ops::Range;

use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{HasRange, HasSpan, LazyDecoder, LazyRawValue, RawVersionMarker};
use crate::lazy::encoding::{TextEncoding, TextEncoding_1_0, TextEncoding_1_1};
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::span::Span;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::{IonResult, IonType, RawSymbolTokenRef};

/// A value that has been identified in the text input stream but whose data has not yet been read.
///
/// `LazyRawTextValue`s are "unresolved," which is to say that symbol values, annotations, and
/// struct field names may or may not include a text definition. (This is less common in Ion's text
/// format than in its binary format, but is still possible.) For a resolved lazy value that
/// includes a text definition for these items whenever one exists, see
/// [`crate::lazy::value::LazyValue`].
// This type is version agnostic, and is wrapped by the LazyRawValue implementations for all
// existing encodings.
#[derive(Copy, Clone)]
pub struct MatchedRawTextValue<'top, E: TextEncoding<'top>> {
    pub(crate) encoded_value: EncodedTextValue<'top, E>,
    pub(crate) input: TextBufferView<'top>,
}

impl<'top, E: TextEncoding<'top>> Debug for MatchedRawTextValue<'top, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MatchedRawTextValue {{\n  val={:?},\n  buf={:?}\n}}\n",
            self.encoded_value, self.input
        )
    }
}

// ===== Version-specific wrappers =====
//
// These types provide Ion-version-specific impls of the LazyRawValue trait
#[derive(Copy, Clone)]
pub struct LazyRawTextValue<'top, E: TextEncoding<'top>> {
    pub(crate) matched: MatchedRawTextValue<'top, E>,
}

impl<'top, E: TextEncoding<'top>> LazyRawTextValue<'top, E> {
    pub fn new(matched: MatchedRawTextValue<'top, E>) -> Self {
        Self { matched }
    }

    pub fn data_range(&self) -> Range<usize> {
        // If the matched value has annotations, the `data_offset` will be the offset beyond
        // the annotations at which the value's data begins.
        let data_offset = self.matched.encoded_value.data_offset();
        let data_length = self.matched.input.len() - data_offset;
        // Add the input buffer's offset to the data offset to get the absolute offset.
        let start = self.matched.input.offset() + data_offset;
        let end = start + data_length;
        start..end
    }

    pub fn has_annotations(&self) -> bool {
        self.matched.encoded_value.data_offset() > 0
    }

    pub fn annotations_range(&self) -> Option<Range<usize>> {
        if !self.has_annotations() {
            return None;
        }
        let annotations_length = self.matched.encoded_value.data_offset();
        let start = self.matched.input.offset();
        let end = start + annotations_length;
        Some(start..end)
    }

    pub fn annotations_span(&self) -> Option<Span<'top>> {
        let range = self.annotations_range()?;
        let bytes = &self.matched.input.bytes()[..range.len()];
        Some(Span::with_offset(range.start, bytes))
    }

    /// Returns the total number of bytes used to represent the current value, including its
    /// annotations (if any) and its value.
    pub fn total_length(&self) -> usize {
        self.matched.input.len()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawTextVersionMarker<'top, E: TextEncoding<'top>> {
    major: u8,
    minor: u8,
    input: TextBufferView<'top>,
    // We need distinct version marker types for 1.0 and 1.1 even though the data/logic is the same.
    // This allows us to implement a `From<LazyRawTextVersionMarker_1_x> for LazyRawAnyVersionMarker`
    // unambiguously for the two encodings.
    spooky: PhantomData<E>,
}

impl<'top, E: TextEncoding<'top>> LazyRawTextVersionMarker<'top, E> {
    pub fn new(
        input: TextBufferView<'top>,
        major: u8,
        minor: u8,
    ) -> LazyRawTextVersionMarker<'top, E> {
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

impl<'top, E: TextEncoding<'top>> HasSpan<'top> for LazyRawTextVersionMarker<'top, E> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl<'top, E: TextEncoding<'top>> HasRange for LazyRawTextVersionMarker<'top, E> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top, E: TextEncoding<'top>> RawVersionMarker<'top> for LazyRawTextVersionMarker<'top, E> {
    fn version(&self) -> (u8, u8) {
        (self.major, self.minor)
    }
}

pub type LazyRawTextValue_1_0<'top> = LazyRawTextValue<'top, TextEncoding_1_0>;
pub type LazyRawTextValue_1_1<'top> = LazyRawTextValue<'top, TextEncoding_1_1>;

impl<'top, E: TextEncoding<'top>> Debug for LazyRawTextValue<'top, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", E::name())?;

        // Try to read the value
        match self.read() {
            // If we can read the value, show it
            Ok(value) => write!(f, " {{{value:?}}}"),
            // Otherwise, write out diagnostic information
            Err(e) => write!(f, " {{\n  matched={:?}\n  err={:?}\n}}\n", self.matched, e),
        }
    }
}

impl<'top> From<MatchedRawTextValue<'top, TextEncoding_1_0>> for LazyRawTextValue_1_0<'top> {
    fn from(matched: MatchedRawTextValue<'top, TextEncoding_1_0>) -> Self {
        LazyRawTextValue::new(matched)
    }
}

impl<'top> From<MatchedRawTextValue<'top, TextEncoding_1_1>> for LazyRawTextValue_1_1<'top> {
    fn from(matched: MatchedRawTextValue<'top, TextEncoding_1_1>) -> Self {
        LazyRawTextValue::new(matched)
    }
}

// ===== Ion-version-agnostic functionality =====
//
// These trait impls are common to all Ion versions, but require the caller to specify a type
// parameter.

impl<'top, E: TextEncoding<'top>> HasRange for MatchedRawTextValue<'top, E> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top, E: TextEncoding<'top>> HasSpan<'top> for MatchedRawTextValue<'top, E> {
    fn span(&self) -> Span<'top> {
        let range = self.range();
        let input_offset = self.input.offset();
        let local_range = (range.start - input_offset)..(range.end - input_offset);
        Span::with_offset(range.start, &self.input.bytes()[local_range])
    }
}

impl<'top, E: TextEncoding<'top>> LazyRawValue<'top, E> for MatchedRawTextValue<'top, E> {
    fn ion_type(&self) -> IonType {
        self.encoded_value.ion_type()
    }

    fn is_null(&self) -> bool {
        self.encoded_value.is_null()
    }

    fn annotations(&self) -> <E as LazyDecoder>::AnnotationsIterator<'top> {
        let range = self
            .encoded_value
            .annotations_range()
            .unwrap_or(self.input.offset()..self.input.offset());
        let annotations_bytes = self.input.slice(0, range.len());
        RawTextAnnotationsIterator::new(annotations_bytes)
    }

    fn read(&self) -> IonResult<RawValueRef<'top, E>> {
        // Get the value's matched input, skipping over any annotations
        let matched_input = self.input.slice_to_end(self.encoded_value.data_offset());
        let allocator = self.input.allocator;

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
            List(_) => RawValueRef::List(E::List::<'top>::from_value(E::value_from_matched(*self))),
            SExp(_) => RawValueRef::SExp(E::SExp::<'top>::from_value(E::value_from_matched(*self))),
            Struct(_) => RawValueRef::Struct(E::Struct::from_value(E::value_from_matched(*self))),
        };
        Ok(value_ref)
    }
}

impl<'top, E: TextEncoding<'top>> HasRange for LazyRawTextValue<'top, E> {
    fn range(&self) -> Range<usize> {
        self.matched.range()
    }
}

impl<'top, E: TextEncoding<'top>> HasSpan<'top> for LazyRawTextValue<'top, E> {
    fn span(&self) -> Span<'top> {
        self.matched.span()
    }
}

impl<'top, E: TextEncoding<'top>> LazyRawValue<'top, E> for LazyRawTextValue<'top, E> {
    fn ion_type(&self) -> IonType {
        self.matched.ion_type()
    }

    fn is_null(&self) -> bool {
        self.matched.is_null()
    }

    fn annotations(&self) -> <E as LazyDecoder>::AnnotationsIterator<'top> {
        self.matched.annotations()
    }

    fn read(&self) -> IonResult<RawValueRef<'top, E>> {
        self.matched.read()
    }
}

pub struct RawTextAnnotationsIterator<'data> {
    input: TextBufferView<'data>,
    has_returned_error: bool,
}

impl<'top> RawTextAnnotationsIterator<'top> {
    pub(crate) fn new(input: TextBufferView<'top>) -> Self {
        RawTextAnnotationsIterator {
            input,
            has_returned_error: false,
        }
    }
}

impl<'top> Iterator for RawTextAnnotationsIterator<'top> {
    type Item = IonResult<RawSymbolTokenRef<'top>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error || self.input.is_empty() {
            return None;
        }

        // Match the first annotation in the input. In order for this iterator to be created,
        // the parser already successfully matched this input once before, so we know it will succeed.
        use nom::Parser;
        let (remaining, (symbol, span)) = TextBufferView::match_annotation
            .parse(self.input)
            .expect("annotations were already matched successfully by this parser");
        let matched_input = self
            .input
            .slice(span.start - self.input.offset(), span.len());
        let text = match symbol.read(self.input.allocator, matched_input) {
            Ok(text) => text,
            Err(e) => {
                self.has_returned_error = true;
                return Some(Err(e));
            }
        };
        self.input = remaining;
        Some(Ok(text))
    }
}

#[cfg(test)]
mod tests {
    use bumpalo::Bump as BumpAllocator;

    use crate::lazy::text::buffer::TextBufferView;
    use crate::lazy::text::value::RawTextAnnotationsIterator;
    use crate::{IonResult, RawSymbolTokenRef};

    #[test]
    fn iterate_annotations() -> IonResult<()> {
        fn test(input: &str) -> IonResult<()> {
            let allocator = BumpAllocator::new();
            let input = TextBufferView::new(&allocator, input.as_bytes());
            let mut iter = RawTextAnnotationsIterator::new(input);
            assert_eq!(iter.next().unwrap()?, RawSymbolTokenRef::Text("foo"));
            assert_eq!(iter.next().unwrap()?, RawSymbolTokenRef::Text("bar"));
            assert_eq!(iter.next().unwrap()?, RawSymbolTokenRef::Text("baz"));
            Ok(())
        }
        test("foo::bar::baz::")?;
        test("foo         ::     'bar'  ::   baz::")?;
        test("foo /*comment*/ :://comment\nbar\n::'baz'::")?;
        Ok(())
    }
}
