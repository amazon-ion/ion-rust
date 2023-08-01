use crate::lazy::decoder::private::LazyRawValuePrivate;
use crate::lazy::decoder::{LazyDecoder, LazyRawValue};
use crate::lazy::encoding::TextEncoding;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::lazy::text::matched::MatchedValue;
use crate::{IonResult, IonType, RawSymbolTokenRef};
use std::fmt;
use std::fmt::{Debug, Formatter};

/// A value that has been identified in the text input stream but whose data has not yet been read.
///
/// If only part of the value is in the input buffer, calls to [`LazyRawTextValue::read`] (which examines
/// bytes beyond the value's header) may return [`IonError::Incomplete`](crate::result::IonError::Incomplete).
///
/// `LazyRawTextValue`s are "unresolved," which is to say that symbol values, annotations, and
/// struct field names may or may not include a text definition. (This is less common in Ion's text
/// format than in its binary format, but is still possible.) For a resolved lazy value that
/// includes a text definition for these items whenever one exists, see
/// [`crate::lazy::value::LazyValue`].
#[derive(Clone)]
pub struct LazyRawTextValue<'data> {
    pub(crate) encoded_value: EncodedTextValue,
    pub(crate) input: TextBufferView<'data>,
}

impl<'data> LazyRawValuePrivate<'data> for LazyRawTextValue<'data> {
    fn field_name(&self) -> Option<RawSymbolTokenRef<'data>> {
        todo!()
    }
}

impl<'data> LazyRawValue<'data, TextEncoding> for LazyRawTextValue<'data> {
    fn ion_type(&self) -> IonType {
        self.encoded_value.ion_type()
    }

    fn is_null(&self) -> bool {
        self.encoded_value.is_null()
    }

    fn annotations(&self) -> <TextEncoding as LazyDecoder<'data>>::AnnotationsIterator {
        todo!()
    }

    fn read(&self) -> IonResult<RawValueRef<'data, TextEncoding>> {
        let matched_input = self.input.slice(0, self.encoded_value.data_length());
        let value_ref = match self.encoded_value.matched() {
            MatchedValue::Null(ion_type) => RawValueRef::Null(*ion_type),
            MatchedValue::Bool(b) => RawValueRef::Bool(*b),
            MatchedValue::Int(i) => RawValueRef::Int(i.read(matched_input)?),
            MatchedValue::Float(f) => RawValueRef::Float(f.read(matched_input)?),
            // ...decimal, timestamp...
            MatchedValue::String(s) => RawValueRef::String(s.read(matched_input)?),
            MatchedValue::Symbol(s) => RawValueRef::Symbol(s.read(matched_input)?),
            // ...and the rest!
        };
        Ok(value_ref)
    }
}

impl<'a> Debug for LazyRawTextValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "LazyRawTextValue {{\n  val={:?},\n  buf={:?}\n}}\n",
            self.encoded_value, self.input
        )
    }
}
