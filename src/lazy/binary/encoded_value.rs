use crate::binary::non_blocking::type_descriptor::Header;
use crate::types::SymbolId;
use crate::IonType;
use std::ops::Range;

/// Represents the type, offset, and length metadata of the various components of an encoded value
/// in an input stream.
///
/// Each [`LazyRawValue`](super::raw::lazy_raw_value::LazyRawValue) contains an `EncodedValue`,
/// allowing a user to re-read (that is: parse) the body of the value as many times as necessary
/// without re-parsing its header information each time.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct EncodedValue {
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
    pub(crate) header: Header,

    // Each encoded value has up to five components, appearing in the following order:
    //
    // [ field_id? | annotations? | header (type descriptor) | header_length? | value ]
    //
    // Components shown with a `?` are optional.
    //
    // EncodedValue stores the offset of the type descriptor byte from the beginning of the
    // data source (`header_offset`). The lengths of the other fields can be used to calculate
    // their positions relative to the type descriptor byte. For example, to find the offset of the
    // field ID (if present), we can do:
    //     header_offset - annotations_header_length - field_id_length
    //
    // This allows us to store a single `usize` for the header offset, while other lengths can be
    // packed into a `u8`. Values are not permitted to have a field ID or annotations that take
    // more than 255 bytes to represent.
    //
    // We store the offset for the header byte because it is guaranteed to be present for all values.
    // Field IDs and annotations appear earlier in the stream but are optional.

    // The number of bytes used to encode the field ID (if present) preceding the Ion value. If
    // `field_id` is undefined, `field_id_length` will be zero.
    pub field_id_length: u8,
    // If this value is inside a struct, `field_id` will contain the SymbolId that represents
    // its field name.
    pub field_id: Option<SymbolId>,
    // The number of bytes used to encode the annotations wrapper (if present) preceding the Ion
    // value. If `annotations` is empty, `annotations_header_length` will be zero.
    pub annotations_header_length: u8,
    // The number of bytes used to encode the series of symbol IDs inside the annotations wrapper.
    pub annotations_sequence_length: u8,
    // The offset of the type descriptor byte within the overall input stream.
    pub header_offset: usize,
    // The number of bytes used to encode the optional length VarUInt following the header byte.
    pub length_length: u8,
    // The number of bytes used to encode the value itself, not including the header byte
    // or length fields.
    pub value_length: usize,
    // The sum total of:
    //     field_id_length + annotations_header_length + header_length + value_length
    // While this can be derived from the above fields, storing it for reuse offers a modest
    // optimization. `total_length` is needed when stepping into a value, skipping a value,
    // and reading a value's data.
    pub total_length: usize,
}

impl EncodedValue {
    pub fn header(&self) -> Header {
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
    pub fn value_length(&self) -> usize {
        self.value_length
    }

    /// The offset of the first byte following the header (including length bytes, if present).
    /// If `value_length()` returns zero, this offset is actually the first byte of
    /// the next encoded value and should not be read.
    pub fn value_offset(&self) -> usize {
        self.header_offset + self.header_length()
    }

    /// Returns an offset Range containing any bytes following the header.
    pub fn value_range(&self) -> Range<usize> {
        let start = self.value_offset();
        let end = start + self.value_length;
        start..end
    }

    /// Returns the index of the first byte that is beyond the end of the current value's encoding.
    pub fn value_end_exclusive(&self) -> usize {
        self.value_offset() + self.value_length
    }

    /// Returns the number of bytes used to encode this value's field ID, if present.
    pub fn field_id_length(&self) -> Option<usize> {
        self.field_id.as_ref()?;
        Some(self.field_id_length as usize)
    }

    /// Returns the offset of the first byte used to encode this value's field ID, if present.
    pub fn field_id_offset(&self) -> Option<usize> {
        self.field_id.as_ref()?;
        Some(
            self.header_offset
                - self.annotations_header_length as usize
                - self.field_id_length as usize,
        )
    }

    /// Returns an offset Range that contains the bytes used to encode this value's field ID,
    /// if present.
    pub fn field_id_range(&self) -> Option<Range<usize>> {
        if let Some(start) = self.field_id_offset() {
            let end = start + self.field_id_length as usize;
            return Some(start..end);
        }
        None
    }

    /// Returns true if this encoded value has an annotations wrapper.
    pub fn has_annotations(&self) -> bool {
        self.annotations_header_length > 0
    }

    /// Returns the number of bytes used to encode this value's annotations, if any.
    /// While annotations envelope the value that they decorate, this function does not include
    /// the length of the value itself.
    pub fn annotations_header_length(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.annotations_header_length as usize)
    }

    /// Returns the number of bytes used to encode the series of VarUInt annotation symbol IDs, if
    /// any.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#annotations>
    pub fn annotations_sequence_length(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.annotations_sequence_length as usize)
    }

    pub fn annotations_sequence_range(&self) -> Option<Range<usize>> {
        let wrapper_offset = self.annotations_offset()?;
        let wrapper_exclusive_end = wrapper_offset + self.annotations_header_length as usize;
        let sequence_length = self.annotations_sequence_length as usize;
        let sequence_offset = wrapper_exclusive_end - sequence_length;
        Some(sequence_offset..wrapper_exclusive_end)
    }

    pub fn annotations_sequence_offset(&self) -> Option<usize> {
        Some(self.annotations_sequence_range()?.start)
    }

    /// Returns the offset of the beginning of the annotations wrapper, if present.
    pub fn annotations_offset(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.header_offset - self.annotations_header_length as usize)
    }

    /// Returns an offset Range that includes the bytes used to encode this value's annotations,
    /// if any. While annotations envelope the value that they modify, this function does not
    /// include the bytes of the encoded value itself.
    pub fn annotations_range(&self) -> Option<Range<usize>> {
        if let Some(start) = self.annotations_offset() {
            let end = start + self.annotations_header_length as usize;
            return Some(start..end);
        }
        None
    }

    /// Returns the total number of bytes used to represent the current value, including the
    /// field ID (if any), its annotations (if any), its header (type descriptor + length bytes),
    /// and its value.
    pub fn total_length(&self) -> usize {
        self.total_length
    }

    pub fn ion_type(&self) -> IonType {
        self.header.ion_type
    }
}

#[cfg(test)]
mod tests {
    use crate::binary::non_blocking::type_descriptor::Header;
    use crate::binary::IonTypeCode;
    use crate::lazy::binary::encoded_value::EncodedValue;
    use crate::{IonResult, IonType};

    #[test]
    fn accessors() -> IonResult<()> {
        // 3-byte String with 1-byte annotation and field ID $10
        let value = EncodedValue {
            header: Header {
                ion_type: IonType::String,
                ion_type_code: IonTypeCode::String,
                length_code: 3,
            },
            field_id_length: 1,
            field_id: Some(10),
            annotations_header_length: 3,
            annotations_sequence_length: 1,
            header_offset: 200,
            length_length: 0,
            value_length: 3,
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
        assert_eq!(value.field_id_length(), Some(1));
        assert_eq!(value.field_id_offset(), Some(196));
        assert_eq!(value.field_id_range(), Some(196..197));
        assert!(value.has_annotations());
        assert_eq!(value.annotations_range(), Some(197..200));
        assert_eq!(value.annotations_header_length(), Some(3));
        assert_eq!(value.annotations_sequence_offset(), Some(199));
        assert_eq!(value.annotations_sequence_length(), Some(1));
        assert_eq!(value.annotations_sequence_range(), Some(199..200));
        assert_eq!(value.value_length(), 3);
        assert_eq!(value.value_offset(), 201);
        assert_eq!(value.value_range(), 201..204);
        assert_eq!(value.value_end_exclusive(), 204);
        assert_eq!(value.total_length(), 7);
        Ok(())
    }
}
