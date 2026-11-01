use std::ops::Range;

use crate::lazy::encoding::TextEncoding;
use crate::lazy::text::matched::{MatchedScalar, MatchedValue};
use crate::IonType;

/// Represents the type, offset, and length metadata of the various components of an encoded value
/// in a text input stream.
///
/// Each [`LazyRawTextValue`](crate::lazy::text::value::LazyRawTextValue) contains an `EncodedTextValue`,
/// allowing a user to re-read (that is: parse) the body of the value as many times as necessary
/// without re-parsing its header information each time.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct EncodedTextValue<'top, E: TextEncoding> {
    // Each encoded text value has one or two components, appearing in the following order:
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

impl<'top, E: TextEncoding> EncodedTextValue<'top, E> {
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
            MatchedValue::Scalar(scalar) => scalar.ion_type(),
            MatchedValue::List(_) => IonType::List,
            MatchedValue::SExp(_) => IonType::SExp,
            MatchedValue::Struct(_) => IonType::Struct,
        }
    }

    pub fn is_null(&self) -> bool {
        matches!(self.matched_value, MatchedValue::Scalar(scalar) if scalar.is_null())
    }

    pub fn data_offset(&self) -> usize {
        self.data_offset as usize
    }

    /// [`data_offset`](Self::data_offset) at its stored width.
    pub(crate) fn data_offset_u16(&self) -> u16 {
        self.data_offset
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

    /// Returns this value's encoding without its lifetime if it is a scalar.
    pub(crate) fn as_scalar(&self) -> Option<EncodedTextScalar> {
        match self.matched_value {
            MatchedValue::Scalar(scalar) => Some(EncodedTextScalar {
                data_offset: self.data_offset,
                scalar,
            }),
            MatchedValue::List(_) | MatchedValue::SExp(_) | MatchedValue::Struct(_) => None,
        }
    }
}

/// The [`EncodedTextValue`] of a scalar, which borrows nothing and so has no lifetime.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct EncodedTextScalar {
    data_offset: u16,
    scalar: MatchedScalar,
}

impl EncodedTextScalar {
    pub fn data_offset(&self) -> usize {
        self.data_offset as usize
    }

    pub fn ion_type(&self) -> IonType {
        self.scalar.ion_type()
    }

    pub fn is_null(&self) -> bool {
        self.scalar.is_null()
    }

    pub fn has_annotations(&self) -> bool {
        self.data_offset > 0
    }

    pub fn to_encoded_value<'top, E: TextEncoding>(self) -> EncodedTextValue<'top, E> {
        EncodedTextValue {
            data_offset: self.data_offset,
            matched_value: MatchedValue::Scalar(self.scalar),
        }
    }
}
