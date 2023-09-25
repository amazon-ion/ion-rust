#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};

use crate::lazy::decoder::private::{LazyContainerPrivate, LazyRawValuePrivate};
use crate::lazy::decoder::LazyRawValue;
use crate::lazy::encoding::TextEncoding_1_0;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::lazy::text::raw::r#struct::LazyRawTextStruct_1_0;
use crate::lazy::text::raw::sequence::{LazyRawTextList_1_0, LazyRawTextSExp_1_0};
use crate::{IonResult, IonType, RawSymbolTokenRef};

/// A value that has been identified in the text input stream but whose data has not yet been read.
///
/// If only part of the value is in the input buffer, calls to [`LazyRawTextValue_1_0::read`] (which examines
/// bytes beyond the value's header) may return [`IonError::Incomplete`](crate::result::IonError::Incomplete).
///
/// `LazyRawTextValue`s are "unresolved," which is to say that symbol values, annotations, and
/// struct field names may or may not include a text definition. (This is less common in Ion's text
/// format than in its binary format, but is still possible.) For a resolved lazy value that
/// includes a text definition for these items whenever one exists, see
/// [`crate::lazy::value::LazyValue`].
#[derive(Copy, Clone)]
pub struct LazyRawTextValue_1_0<'data> {
    pub(crate) encoded_value: EncodedTextValue,
    pub(crate) input: TextBufferView<'data>,
}

impl<'data> LazyRawValuePrivate<'data> for LazyRawTextValue_1_0<'data> {
    fn field_name(&self) -> IonResult<RawSymbolTokenRef<'data>> {
        self.encoded_value.field_name(self.input)
    }
}

impl<'data> LazyRawValue<'data, TextEncoding_1_0> for LazyRawTextValue_1_0<'data> {
    fn ion_type(&self) -> IonType {
        self.encoded_value.ion_type()
    }

    fn is_null(&self) -> bool {
        self.encoded_value.is_null()
    }

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        let span = self
            .encoded_value
            .annotations_range()
            .unwrap_or(self.input.offset()..self.input.offset());
        let annotations_bytes = self
            .input
            .slice(span.start - self.input.offset(), span.len());
        RawTextAnnotationsIterator::new(annotations_bytes)
    }

    fn read(&self) -> IonResult<RawValueRef<'data, TextEncoding_1_0>> {
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
            List => RawValueRef::List(LazyRawTextList_1_0::from_value(*self)),
            SExp => RawValueRef::SExp(LazyRawTextSExp_1_0::from_value(*self)),
            Struct => RawValueRef::Struct(LazyRawTextStruct_1_0::from_value(*self)),
        };
        Ok(value_ref)
    }
}

impl<'a> Debug for LazyRawTextValue_1_0<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "LazyRawTextValue {{\n  val={:?},\n  buf={:?}\n}}\n",
            self.encoded_value, self.input
        )
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
