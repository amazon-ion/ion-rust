use std::ops::Range;

use crate::lazy::encoding::TextEncoding;
use crate::lazy::text::matched::MatchedValue;
use crate::IonType;

/// Represents the type, offset, and length metadata of the various components of an encoded value
/// in a text input stream.
///
/// Each [`LazyRawTextValue`](crate::lazy::text::value::MatchedRawTextValue) contains an `EncodedValue`,
/// allowing a user to re-read (that is: parse) the body of the value as many times as necessary
/// without re-parsing its header information each time.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct EncodedTextValue<'top, E: TextEncoding<'top>> {
    // TODO: Update this comment now that field_name is not part of 'value'

    // Each encoded text value has up to three components, appearing in the following order:
    //
    //     [ field_name? | annotations? | data ]
    //
    // Components shown with a `?` are optional.

    // The following is an example encoding of a struct field with an annotated value-- the only kind
    // of Ion value that has both of the optional components--that appears 5 gigabytes into the input
    // stream:
    //
    //   ┌─── field_name_offset: 12
    //   │      ┌─── annotations_offset: 5
    //   │      │    ┌─── data_offset: 5_000_000_012
    //   price: USD::55.99,
    //   └─┬─┘  └─┬─┘└─┬─┘
    //     │      │    └─ data_length: 5
    //     │      └─ annotations_length: 5
    //     └─ field_name_length: 5
    //
    // Notice that only `data_offset` is an absolute offset from the beginning of the stream;
    // this is because `data` is the only field that is always guaranteed to be present.
    // `field_name_offset` and `annotations_offset` are stored as the number of bytes _before_
    // `data_offset`, allowing them to be stored in fewer bytes.

    // The absolute position (in bytes) of this value's `data` component within the overall stream
    // being decoded.
    data_offset: usize,
    // The number of bytes _before_ `data_offset` at which the field name begins. If this value
    // does not have a field name, this value will be zero.
    // field_name_offset: u32,
    // The number of bytes _before_ `data_offset` at which the annotations sequence begins.
    // If this value does not have a field name, this value will be zero.
    annotations_offset: u32,

    // The number of bytes used to encode the data component of this Ion value.
    data_length: usize,

    // The number of bytes used to encode the annotations sequence preceding the data, if any.
    // If there is no annotations sequence, this will be zero. If there is whitespace before the
    // annotations sequence, this will not include it.
    annotations_length: u32,

    // Information that was recorded about the value as it was being matched.
    // For some types (e.g. bool), matching the text is the complete parsing process so the whole
    // value is stored. For others (e.g. a timestamp), the various components of the value are
    // recognized during matching and partial information like subfield offsets can be stored here.
    matched_value: MatchedValue<'top, E>,
}

impl<'top, E: TextEncoding<'top>> EncodedTextValue<'top, E> {
    pub(crate) fn new(
        matched_value: MatchedValue<'top, E>,
        offset: usize,
        length: usize,
    ) -> EncodedTextValue<'top, E> {
        EncodedTextValue {
            data_offset: offset,
            data_length: length,
            annotations_offset: 0,
            annotations_length: 0,
            matched_value,
        }
    }

    // The annotations should include all of the symbol tokens, their delimiting '::'s, and any
    // interstitial whitespace. It should not include any leading/trailing whitespace or the value
    // itself.
    // Examples:
    //    foo::bar::
    //    'foo'::'bar'::
    //    foo   ::         'bar'      ::
    pub(crate) fn with_annotations_sequence(
        mut self,
        offset: usize,
        length: usize,
    ) -> EncodedTextValue<'top, E> {
        self.annotations_offset = (self.data_offset - offset) as u32;
        self.annotations_length = length as u32;
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
        self.data_offset
    }

    pub fn data_length(&self) -> usize {
        self.data_length
    }

    pub fn data_range(&self) -> Range<usize> {
        self.data_offset..(self.data_offset + self.data_length)
    }

    pub fn annotations_range(&self) -> Option<Range<usize>> {
        if self.annotations_offset == 0 {
            return None;
        }
        let start = self.data_offset - (self.annotations_offset as usize);
        let end = start + (self.annotations_length as usize);
        Some(start..end)
    }

    pub fn has_annotations(&self) -> bool {
        self.annotations_offset > 0
    }

    /// Returns the total number of bytes used to represent the current value, including its
    /// annotations (if any), its header (type descriptor + length bytes), and its value.
    pub fn total_length(&self) -> usize {
        self.data_length + self.annotations_offset as usize
    }

    pub fn annotated_value_range(&self) -> Range<usize> {
        let start = self.data_offset - self.annotations_length as usize;
        let end = self.data_offset + self.data_length;
        start..end
    }

    pub fn matched(&self) -> MatchedValue<'top, E> {
        self.matched_value
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::encoding::TextEncoding_1_0;

    use super::*;

    #[test]
    fn total_length_data_only() {
        let value =
            EncodedTextValue::<TextEncoding_1_0>::new(MatchedValue::Null(IonType::Null), 100, 12);
        assert_eq!(value.total_length(), 12);
    }

    #[test]
    fn total_length_data_with_annotations() {
        let value =
            EncodedTextValue::<TextEncoding_1_0>::new(MatchedValue::Null(IonType::Null), 100, 12)
                .with_annotations_sequence(90, 4);
        assert_eq!(value.total_length(), 22);
    }
}
