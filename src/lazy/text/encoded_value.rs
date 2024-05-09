use std::ops::Range;

use crate::lazy::encoding::TextEncoding;
use crate::lazy::text::matched::MatchedValue;
use crate::IonType;

/// Represents the type, offset, and length metadata of the various components of an encoded value
/// in a text input stream.
///
/// Each [`LazyRawTextValue`](crate::lazy::text::value::LazyRawTextValue) contains an `EncodedTextValue`,
/// allowing a user to re-read (that is: parse) the body of the value as many times as necessary
/// without re-parsing its header information each time.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct EncodedTextValue<'top, E: TextEncoding<'top>> {
    // Each encoded text value has up to three components, appearing in the following order:
    //
    //     [annotations? | data ]
    //
    // Components shown with a `?` are optional.

    // The following is an example encoding of an annotated value:
    //
    //   USD::55.99,
    //   └─┬─┘
    //     └─ data_offset: 5
    //
    // Notice that `data_offset` is a relative offset from the beginning of the matched buffer.
    // The offset accommodates leading annotations, potentially including interstitial whitespace
    // and/or comments.

    // The relative position within the buffer at which the data portion of this value begins.
    // All buffer contents beyond this point are part of the data; the buffer ends when the value
    // ends.
    data_offset: u16,

    // Information that was recorded about the value as it was being matched.
    // For some types (e.g. bool), matching the text is the complete parsing process so the whole
    // value is stored. For others (e.g. a timestamp), the various components of the value are
    // recognized during matching and partial information like subfield offsets can be stored here.
    matched_value: MatchedValue<'top, E>,
}

impl<'top, E: TextEncoding<'top>> EncodedTextValue<'top, E> {
    pub(crate) fn new(matched_value: MatchedValue<'top, E>) -> EncodedTextValue<'top, E> {
        EncodedTextValue {
            data_offset: 0,
            matched_value,
        }
    }

    // The annotations should include all of the symbol tokens, their delimiting '::'s, and any
    // interstitial or trailing whitespace. It should not include any leading whitespace or the
    // value itself.
    // Examples:
    //    foo::bar::
    //    'foo'::'bar'::
    //    foo   ::         'bar'      ::
    pub(crate) fn with_annotations_sequence(mut self, length: u16) -> EncodedTextValue<'top, E> {
        self.data_offset = length;
        self
    }

    pub fn ion_type(&self) -> IonType {
        match self.matched_value {
            MatchedValue::Null(ion_type) => ion_type,
            MatchedValue::Bool(_) => IonType::Bool,
            MatchedValue::Int(_) => IonType::Int,
            MatchedValue::Float(_) => IonType::Float,
            MatchedValue::Decimal(_) => IonType::Decimal,
            MatchedValue::Timestamp(_) => IonType::Timestamp,
            MatchedValue::String(_) => IonType::String,
            MatchedValue::Symbol(_) => IonType::Symbol,
            MatchedValue::Blob(_) => IonType::Blob,
            MatchedValue::Clob(_) => IonType::Clob,
            MatchedValue::List(_) => IonType::List,
            MatchedValue::SExp(_) => IonType::SExp,
            MatchedValue::Struct(_) => IonType::Struct,
        }
    }

    pub fn is_null(&self) -> bool {
        matches!(self.matched_value, MatchedValue::Null(_))
    }

    pub fn data_offset(&self) -> usize {
        self.data_offset as usize
    }

    pub fn annotations_range(&self) -> Option<Range<usize>> {
        if self.data_offset == 0 {
            return None;
        }
        Some(0..self.data_offset as usize)
    }

    pub fn has_annotations(&self) -> bool {
        self.data_offset > 0
    }

    pub fn matched(&self) -> MatchedValue<'top, E> {
        self.matched_value
    }
}
