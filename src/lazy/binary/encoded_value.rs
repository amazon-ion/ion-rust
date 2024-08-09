use crate::lazy::binary::raw::type_descriptor::Header;
use crate::lazy::binary::raw::v1_1::immutable_buffer::AnnotationsEncoding;
use crate::lazy::expanded::template::ParameterEncoding;
use crate::IonType;
use std::ops::Range;

pub(crate) trait EncodedHeader: Copy {
    type TypeCode;
    fn ion_type(&self) -> IonType;
    fn type_code(&self) -> Self::TypeCode;
    fn low_nibble(&self) -> u8;

    fn is_null(&self) -> bool;
}

impl EncodedHeader for Header {
    type TypeCode = crate::binary::type_code::IonTypeCode;

    fn ion_type(&self) -> IonType {
        self.ion_type
    }

    fn type_code(&self) -> Self::TypeCode {
        self.ion_type_code
    }

    fn low_nibble(&self) -> u8 {
        self.length_code
    }

    fn is_null(&self) -> bool {
        self.is_null()
    }
}

/// Represents the type, offset, and length metadata of the various components of an encoded value
/// in an input stream.
///
/// Each [`LazyRawValue`](super::raw::value::LazyRawBinaryValue_1_0) contains an `EncodedValue`,
/// allowing a user to re-read (that is: parse) the body of the value as many times as necessary
/// without re-parsing its header information each time.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct EncodedValue<HeaderType: EncodedHeader> {
    pub(crate) encoding: ParameterEncoding,
    // If the compiler decides that a value is too large to be moved/copied with inline code,
    // it will relocate the value using memcpy instead. This can be quite slow by comparison.
    //
    // Be cautious when adding new member fields or modifying the data types of existing member
    // fields, as this may cause the in-memory size of `EncodedValue` instances to grow.
    //
    // See the Rust Performance Book section on measuring type sizes[1] for more information.
    // [1] https://nnethercote.github.io/perf-book/type-sizes.html#measuring-type-sizes

    // The type descriptor byte that identified this value; includes the type code, length code,
    // and IonType.
    pub(crate) header: HeaderType,

    // Each encoded value has up to four components, appearing in the following order:
    //
    // [ annotations? | header (type descriptor) | header_length? | value_body ]
    //
    // Components shown with a `?` are optional.
    //
    // EncodedValue stores the offset of the type descriptor byte from the beginning of the
    // data source (`header_offset`). The lengths of the other fields can be used to calculate
    // their positions relative to the type descriptor byte. For example, to find the offset of the
    // annotations header (if present), we can do:
    //     header_offset - annotations_header_length
    //
    // This allows us to store a single `usize` for the header offset, while other lengths can be
    // packed into a `u8`. In this implementation, values are not permitted to have annotations that
    // take more than 255 bytes to represent.
    //
    // We store the offset for the header byte because it is guaranteed to be present for all values.
    // Annotations appear earlier in the stream but are optional.

    // The number of bytes used to encode the header of the annotations wrapper preceding the Ion
    // value. If the value has no annotations, `annotations_header_length` will be zero.
    //
    // In Ion 1.0, the annotations header contains several fields: an opcode, a wrapper length, and
    // the length of the sequence itself. It does not include the actual sequence of annotations.
    //
    // In Ion 1.1, the annotations header contains an opcode and (in the case of opcode 0xE9) a
    // FlexUInt length.
    pub annotations_header_length: u8,
    // The number of bytes used to encode the series of symbol IDs inside the annotations wrapper.
    pub annotations_sequence_length: u16,
    // Whether the annotations sequence is encoded as `FlexSym`s or as symbol addresses.
    // In Ion 1.0, they are always encoded as symbol addresses.
    pub annotations_encoding: AnnotationsEncoding,
    // The offset of the type descriptor byte within the overall input stream.
    pub header_offset: usize,
    // If this value was written with a tagless encoding, this will be 0. Otherwise, it's 1.
    pub opcode_length: u8,
    // The number of bytes used to encode the optional length VarUInt following the header byte.
    pub length_length: u8,
    // The number of bytes used to encode the value itself, not including the header byte
    // or length fields.
    pub value_body_length: usize,
    // The sum total of:
    //     annotations_header_length + header_length + value_length
    // While this can be derived from the above fields, storing it for reuse offers a modest
    // optimization. `total_length` is needed when stepping into a value, skipping a value,
    // and reading a value's data.
    pub total_length: usize,
}

impl<HeaderType: EncodedHeader> EncodedValue<HeaderType> {
    pub fn header(&self) -> HeaderType {
        self.header
    }

    /// Returns the offset of the current value's type descriptor byte.
    pub fn header_offset(&self) -> usize {
        self.header_offset
    }

    /// Returns the length of this value's header, including the type descriptor byte and any
    /// additional bytes used to encode the value's length.
    pub fn header_length(&self) -> usize {
        // The `length_length` field does not include the type descriptor byte, so add 1.
        self.length_length as usize + 1
    }

    /// Returns an offset Range that contains this value's type descriptor byte and any additional
    /// bytes used to encode the `length`.
    pub fn header_range(&self) -> Range<usize> {
        let start = self.header_offset;
        let end = start + self.header_length();
        start..end
    }

    /// Returns the number of bytes used to encode this value's data.
    /// If the value can fit in the type descriptor byte (e.g. `true`, `false`, `null`, `0`),
    /// this function will return 0.
    #[inline(always)]
    pub fn value_body_length(&self) -> usize {
        self.value_body_length
    }

    /// The offset of the first byte following the header (including length bytes, if present).
    /// If `value_length()` returns zero, this offset is actually the first byte of
    /// the next encoded value and should not be read.
    pub fn value_body_offset(&self) -> usize {
        self.header_offset + self.header_length()
    }

    /// Returns an offset Range containing any bytes following the header.
    pub fn value_body_range(&self) -> Range<usize> {
        let start = self.value_body_offset();
        let end = start + self.value_body_length;
        start..end
    }

    /// Returns the index of the first byte that is beyond the end of the current value's encoding.
    pub fn value_end_exclusive(&self) -> usize {
        self.value_body_offset() + self.value_body_length
    }

    /// Returns true if this encoded value has an annotations wrapper.
    pub fn has_annotations(&self) -> bool {
        self.annotations_header_length > 0
    }

    /// Returns the number of bytes used to encode this value's annotations header, if any.
    ///
    /// In Ion 1.0, the annotations header contains several fields: an opcode, a wrapper length, and
    /// the length of the sequence itself. It does not include the actual sequence of annotations.
    ///
    /// In Ion 1.1, the annotations header contains an opcode and (in the case of opcode 0xE9) a
    /// FlexUInt representing the sequence length.
    pub fn annotations_header_length(&self) -> usize {
        self.annotations_header_length as usize
    }

    /// Returns the number of bytes used to encode the series of annotation symbols, if
    /// any.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#annotations>
    pub fn annotations_sequence_length(&self) -> usize {
        self.annotations_sequence_length as usize
    }

    /// Returns the combined length of the annotations header and sequence.
    pub fn annotations_total_length(&self) -> usize {
        self.annotations_header_length() + self.annotations_sequence_length()
    }

    /// Returns the offset range of the bytes in the stream that encoded the value's annotations
    /// sequence.
    pub fn annotations_sequence_range(&self) -> Range<usize> {
        let wrapper_offset = self
            .annotations_offset()
            .unwrap_or_else(|| self.header_offset());
        let wrapper_exclusive_end = wrapper_offset + self.annotations_header_length as usize;
        let sequence_length = self.annotations_sequence_length as usize;
        let sequence_offset = wrapper_exclusive_end;
        let sequence_exclusive_end = sequence_offset + sequence_length;
        debug_assert!(sequence_exclusive_end == self.header_offset);
        sequence_offset..sequence_exclusive_end
    }

    pub fn annotations_sequence_offset(&self) -> Option<usize> {
        if self.annotations_header_length() == 0 {
            return None;
        }
        Some(self.header_offset - self.annotations_sequence_length())
    }

    /// Returns the offset of the beginning of the annotations wrapper, if present.
    pub fn annotations_offset(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.header_offset - self.annotations_total_length())
    }

    /// Returns an offset Range that includes the bytes used to encode this value's annotations
    /// (including both the header and sequence), if any.
    pub fn annotations_range(&self) -> Option<Range<usize>> {
        if let Some(start) = self.annotations_offset() {
            // The annotations sequence always ends at the value's opcode.
            let end = self.header_offset();
            return Some(start..end);
        }
        None
    }

    /// Returns the total number of bytes used to represent the current value, including
    /// its annotations (if any), its header (type descriptor + length bytes), and the body of
    /// the value.
    pub fn total_length(&self) -> usize {
        self.total_length
    }

    /// The offset Range (starting from the beginning of the stream) that contains this value's
    /// complete encoding, including annotations.
    pub fn annotated_value_range(&self) -> Range<usize> {
        // [ annotations? | header (type descriptor) | header_length? | value ]
        let start = self.header_offset - self.annotations_total_length();
        let end = start + self.total_length;
        start..end
    }

    /// The offset Range (starting from the beginning of the stream) that contains this value's
    /// complete encoding, not including any annotations.
    pub fn unannotated_value_range(&self) -> Range<usize> {
        // [ annotations? | header (type descriptor) | header_length? | value ]
        let start = self.header_offset;
        let end = start + self.total_length - self.annotations_total_length();
        start..end
    }

    pub fn ion_type(&self) -> IonType {
        self.header.ion_type()
    }
}

#[cfg(test)]
mod tests {
    use crate::binary::IonTypeCode;
    use crate::lazy::binary::encoded_value::EncodedValue;
    use crate::lazy::binary::raw::type_descriptor::Header;
    use crate::lazy::binary::raw::v1_1::immutable_buffer::AnnotationsEncoding;
    use crate::lazy::expanded::template::ParameterEncoding;
    use crate::{IonResult, IonType};

    #[test]
    fn accessors() -> IonResult<()> {
        // 3-byte String with 1-byte annotation
        let value = EncodedValue {
            encoding: ParameterEncoding::Tagged,
            header: Header {
                ion_type: IonType::String,
                ion_type_code: IonTypeCode::String,
                length_code: 3,
            },
            annotations_header_length: 2,
            annotations_sequence_length: 1,
            annotations_encoding: AnnotationsEncoding::SymbolAddress,
            header_offset: 200,
            opcode_length: 1,
            length_length: 0,
            value_body_length: 3,
            total_length: 7,
        };
        assert_eq!(value.ion_type(), IonType::String);
        assert_eq!(
            value.header(),
            Header {
                ion_type: IonType::String,
                ion_type_code: IonTypeCode::String,
                length_code: 3,
            }
        );
        assert_eq!(value.header_offset(), 200);
        assert_eq!(value.header_length(), 1);
        assert_eq!(value.header_range(), 200..201);
        assert!(value.has_annotations());
        assert_eq!(value.annotations_range(), Some(197..200));
        assert_eq!(value.annotations_header_length(), 2);
        assert_eq!(value.annotations_sequence_offset(), Some(199));
        assert_eq!(value.annotations_sequence_length(), 1);
        assert_eq!(value.annotations_sequence_range(), 199..200);
        assert_eq!(value.value_body_length(), 3);
        assert_eq!(value.value_body_offset(), 201);
        assert_eq!(value.value_body_range(), 201..204);
        assert_eq!(value.value_end_exclusive(), 204);
        assert_eq!(value.total_length(), 7);
        Ok(())
    }
}
