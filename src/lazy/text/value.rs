#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;

use crate::lazy::decoder::private::{LazyContainerPrivate, LazyRawValuePrivate};
use crate::lazy::decoder::LazyRawValue;
use crate::lazy::encoding::{TextEncoding, TextEncoding_1_0, TextEncoding_1_1};
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::{IonResult, IonType, RawSymbolTokenRef};

/// A value that has been identified in the text input stream but whose data has not yet been read.
///
/// If only part of the value is in the input buffer, calls to [`MatchedRawTextValue::read`] (which examines
/// bytes beyond the value's header) may return [`IonError::Incomplete`](crate::result::IonError::Incomplete).
///
/// `LazyRawTextValue`s are "unresolved," which is to say that symbol values, annotations, and
/// struct field names may or may not include a text definition. (This is less common in Ion's text
/// format than in its binary format, but is still possible.) For a resolved lazy value that
/// includes a text definition for these items whenever one exists, see
/// [`crate::lazy::value::LazyValue`].
#[derive(Copy, Clone)]
pub struct MatchedRawTextValue<'data> {
    pub(crate) encoded_value: EncodedTextValue,
    pub(crate) input: TextBufferView<'data>,
}

impl<'a> Debug for MatchedRawTextValue<'a> {
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
pub struct LazyRawTextValue<'data, E: TextEncoding<'data> + Copy> {
    pub(crate) matched: MatchedRawTextValue<'data>,
    spooky: PhantomData<E>,
}

impl<'data, E: TextEncoding<'data>> LazyRawTextValue<'data, E> {
    pub fn new(matched: MatchedRawTextValue<'data>) -> Self {
        Self {
            matched,
            spooky: PhantomData,
        }
    }
}

pub type LazyRawTextValue_1_0<'data> = LazyRawTextValue<'data, TextEncoding_1_0>;
pub type LazyRawTextValue_1_1<'data> = LazyRawTextValue<'data, TextEncoding_1_1>;

impl<'data, E: TextEncoding<'data>> Debug for LazyRawTextValue<'data, E> {
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

impl<'data> From<MatchedRawTextValue<'data>> for LazyRawTextValue_1_0<'data> {
    fn from(matched: MatchedRawTextValue<'data>) -> Self {
        LazyRawTextValue::new(matched)
    }
}

impl<'data> From<MatchedRawTextValue<'data>> for LazyRawTextValue_1_1<'data> {
    fn from(matched: MatchedRawTextValue<'data>) -> Self {
        LazyRawTextValue::new(matched)
    }
}

impl<'data> LazyRawValuePrivate<'data> for MatchedRawTextValue<'data> {
    // TODO: We likely want to move this functionality to the Ion-version-specific LazyDecoder::Field
    //       implementations. See: https://github.com/amazon-ion/ion-rust/issues/631
    fn field_name(&self) -> IonResult<RawSymbolTokenRef<'data>> {
        self.encoded_value.field_name(self.input)
    }
}

impl<'data> MatchedRawTextValue<'data> {
    /// No-op compiler hint that we want a particular generic flavor of MatchedRawTextValue
    pub(crate) fn as_version<D: TextEncoding<'data>>(&self) -> &impl LazyRawValue<'data, D> {
        self
    }
}
// ===== Ion-version-agnostic functionality =====
//
// These trait impls are common to all Ion versions, but require the caller to specify a type
// parameter.
impl<'data, D: TextEncoding<'data>> LazyRawValue<'data, D> for MatchedRawTextValue<'data> {
    fn ion_type(&self) -> IonType {
        self.encoded_value.ion_type()
    }

    fn is_null(&self) -> bool {
        self.encoded_value.is_null()
    }

    fn annotations(&self) -> D::AnnotationsIterator {
        let span = self
            .encoded_value
            .annotations_range()
            .unwrap_or(self.input.offset()..self.input.offset());
        let annotations_bytes = self
            .input
            .slice(span.start - self.input.offset(), span.len());
        RawTextAnnotationsIterator::new(annotations_bytes)
    }

    fn read(&self) -> IonResult<RawValueRef<'data, D>> {
        let matched_input = self.input.slice(
            self.encoded_value.data_offset() - self.input.offset(),
            self.encoded_value.data_length(),
        );

        use crate::lazy::text::matched::MatchedValue::*;
        let value_ref = match self.encoded_value.matched() {
            Null(ion_type) => RawValueRef::Null(ion_type),
            Bool(b) => RawValueRef::Bool(b),
            Int(i) => RawValueRef::Int(i.read(matched_input)?),
            Float(f) => RawValueRef::Float(f.read(matched_input)?),
            Decimal(d) => RawValueRef::Decimal(d.read(matched_input)?),
            Timestamp(t) => RawValueRef::Timestamp(t.read(matched_input)?),
            String(s) => RawValueRef::String(s.read(matched_input)?),
            Symbol(s) => RawValueRef::Symbol(s.read(matched_input)?),
            Blob(b) => RawValueRef::Blob(b.read(matched_input)?),
            Clob(c) => RawValueRef::Clob(c.read(matched_input)?),
            List => RawValueRef::List(D::List::from_value(D::value_from_matched(*self))),
            SExp => RawValueRef::SExp(D::SExp::from_value(D::value_from_matched(*self))),
            Struct => RawValueRef::Struct(D::Struct::from_value(D::value_from_matched(*self))),
        };
        Ok(value_ref)
    }
}

impl<'data, E: TextEncoding<'data>> LazyRawValuePrivate<'data> for LazyRawTextValue<'data, E> {
    fn field_name(&self) -> IonResult<RawSymbolTokenRef<'data>> {
        self.matched.field_name()
    }
}

impl<'data, E: TextEncoding<'data>> LazyRawValue<'data, E> for LazyRawTextValue<'data, E> {
    fn ion_type(&self) -> IonType {
        self.matched.as_version::<E>().ion_type()
    }

    fn is_null(&self) -> bool {
        self.matched.as_version::<E>().is_null()
    }

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        self.matched.as_version::<E>().annotations()
    }

    fn read(&self) -> IonResult<RawValueRef<'data, E>> {
        self.matched.as_version::<E>().read()
    }
}

pub struct RawTextAnnotationsIterator<'data> {
    input: TextBufferView<'data>,
    has_returned_error: bool,
}

impl<'data> RawTextAnnotationsIterator<'data> {
    pub(crate) fn new(input: TextBufferView<'data>) -> Self {
        RawTextAnnotationsIterator {
            input,
            has_returned_error: false,
        }
    }
}

impl<'data> Iterator for RawTextAnnotationsIterator<'data> {
    type Item = IonResult<RawSymbolTokenRef<'data>>;

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
        let text = match symbol.read(matched_input) {
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
    use crate::lazy::text::buffer::TextBufferView;
    use crate::lazy::text::value::RawTextAnnotationsIterator;
    use crate::{IonResult, RawSymbolTokenRef};

    #[test]
    fn iterate_annotations() -> IonResult<()> {
        fn test(input: &str) -> IonResult<()> {
            let input = TextBufferView::new(input.as_bytes());
            let mut iter = RawTextAnnotationsIterator::new(input);
            assert_eq!(iter.next().unwrap()?, RawSymbolTokenRef::Text("foo".into()));
            assert_eq!(iter.next().unwrap()?, RawSymbolTokenRef::Text("bar".into()));
            assert_eq!(iter.next().unwrap()?, RawSymbolTokenRef::Text("baz".into()));
            Ok(())
        }
        test("foo::bar::baz::")?;
        test("foo         ::     'bar'  ::   baz::")?;
        test("foo /*comment*/ :://comment\nbar\n::'baz'::")?;
        Ok(())
    }
}
