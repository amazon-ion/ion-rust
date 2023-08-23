use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::matched::{MatchedSymbol, MatchedValue};
use crate::result::IonFailure;
use crate::{IonResult, IonType};
use std::ops::Range;

/// Represents the type, offset, and length metadata of the various components of an encoded value
/// in a text input stream.
///
/// Each [`LazyRawTextValue`](crate::lazy::text::value::LazyRawTextValue) contains an `EncodedValue`,
/// allowing a user to re-read (that is: parse) the body of the value as many times as necessary
/// without re-parsing its header information each time.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct EncodedTextValue {
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
    field_name_offset: u32,
    // The number of bytes _before_ `data_offset` at which the annotations sequence begins.
    // If this value does not have a field name, this value will be zero.
    annotations_offset: u32,

    // The number of bytes used to encode the data component of this Ion value.
    data_length: usize,
    // The number of bytes used to encode the field name preceding the data, if any.
    // If there is no field name (i.e. the value is not inside a struct), this will be zero.
    // If there is whitespace before the field name, this will not include it.
    field_name_length: u32,
    // The number of bytes used to encode the annotations sequence preceding the data, if any.
    // If there is no annotations sequence, this will be zero. If there is whitespace before the
    // annotations sequence, this will not include it.
    annotations_length: u32,

    // Information that was recorded about the value as it was being matched.
    // For some types (e.g. bool), matching the text is the complete parsing process so the whole
    // value is stored. For others (e.g. a timestamp), the various components of the value are
    // recognized during matching and partial information like subfield offsets can be stored here.
    matched_value: MatchedValue,
    field_name_syntax: Option<MatchedSymbol>,
}

impl EncodedTextValue {
    pub(crate) fn new(
        matched_value: MatchedValue,
        offset: usize,
        length: usize,
    ) -> EncodedTextValue {
        EncodedTextValue {
            data_offset: offset,
            data_length: length,
            field_name_length: 0,
            field_name_offset: 0,
            annotations_offset: 0,
            annotations_length: 0,
            matched_value,
            field_name_syntax: None,
        }
    }

    // The field name range should contain the field name literal itself without any trailing
    // whitespace or the delimiting ':'.
    // Examples:
    //    foo
    //   'foo'
    //   "foo"
    //    $10
    pub(crate) fn with_field_name(
        mut self,
        field_name_syntax: MatchedSymbol,
        offset: usize,
        length: usize,
    ) -> EncodedTextValue {
        self.field_name_syntax = Some(field_name_syntax);
        self.field_name_offset = (self.data_offset - offset) as u32;
        self.field_name_length = length as u32;
        self
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
    ) -> EncodedTextValue {
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
            MatchedValue::String(_) => IonType::String,
            MatchedValue::Symbol(_) => IonType::Symbol,
            MatchedValue::List => IonType::List,
            MatchedValue::Struct => IonType::Struct,
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

    pub fn field_name<'data>(&self, input: TextBufferView<'data>) -> IonResult<&'data str> {
        if self.field_name_offset == 0 {
            return IonResult::illegal_operation(
                "requested field name, but value was not in a struct field",
            );
        }
        let relative_start = self.data_offset - input.offset() - (self.field_name_offset as usize);
        let field_name_bytes = input.slice(relative_start, self.field_name_length as usize);
        field_name_bytes.as_text()
    }

    pub fn field_name_range(&self) -> Option<Range<usize>> {
        if self.field_name_offset == 0 {
            return None;
        }
        let start = self.data_offset - (self.field_name_offset as usize);
        let end = start + (self.field_name_length as usize);
        Some(start..end)
    }

    pub fn annotations_range(&self) -> Option<Range<usize>> {
        if self.annotations_offset == 0 {
            return None;
        }
        let start = self.data_offset - (self.annotations_offset as usize);
        let end = start + (self.annotations_length as usize);
        Some(start..end)
    }

    pub fn has_field_name(&self) -> bool {
        self.field_name_offset > 0
    }

    pub fn has_annotations(&self) -> bool {
        self.annotations_offset > 0
    }

    /// Returns the total number of bytes used to represent the current value, including the
    /// field ID (if any), its annotations (if any), its header (type descriptor + length bytes),
    /// and its value.
    pub fn total_length(&self) -> usize {
        self.data_length + u32::max(self.annotations_offset, self.field_name_offset) as usize
    }

    pub fn field_name_syntax(&self) -> Option<MatchedSymbol> {
        self.field_name_syntax
    }

    pub fn matched(&self) -> MatchedValue {
        self.matched_value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn total_length_data_only() {
        let value = EncodedTextValue::new(MatchedValue::Null(IonType::Null), 100, 12);
        assert_eq!(value.total_length(), 12);
    }

    #[test]
    fn total_length_data_with_field_name() {
        let value = EncodedTextValue::new(MatchedValue::Null(IonType::Null), 100, 12)
            .with_field_name(MatchedSymbol::Identifier, 90, 4);
        assert_eq!(value.total_length(), 22);
    }

    #[test]
    fn total_length_data_with_annotations() {
        let value = EncodedTextValue::new(MatchedValue::Null(IonType::Null), 100, 12)
            .with_annotations_sequence(90, 4);
        assert_eq!(value.total_length(), 22);
    }

    #[test]
    fn total_length_data_with_field_name_and_annotations() {
        let value = EncodedTextValue::new(MatchedValue::Null(IonType::Null), 100, 12)
            .with_field_name(MatchedSymbol::Identifier, 90, 4)
            .with_annotations_sequence(94, 6);
        assert_eq!(value.total_length(), 22);

        // Same test but with extra whitespace between the components
        let value = EncodedTextValue::new(MatchedValue::Null(IonType::Null), 100, 12)
            .with_field_name(MatchedSymbol::Identifier, 80, 4)
            .with_annotations_sequence(91, 6);
        assert_eq!(value.total_length(), 32, "{:?}", value);
    }
}
