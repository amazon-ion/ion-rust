use std::mem;

use ice_code::ice as cold_path;

use crate::binary::decimal::DecimalBinaryEncoder;
use crate::binary::timestamp::TimestampBinaryEncoder;
use crate::binary::uint;
use crate::binary::uint::{minimal_be_bytes, DecodedUInt};
use crate::binary::var_uint::VarUInt;
use crate::lazy::encoder::annotation_seq::{AnnotationSeq, AnnotationsVec};
use crate::lazy::encoder::binary::v1_0::container_writers::{
    header_length, shift_tail, write_annotations_prefix, write_header, BinaryListWriter_1_0,
    BinarySExpWriter_1_0, BinaryStructWriter_1_0, TruncateOnDrop, ANNOTATIONS_WRAPPER_TYPE_CODE,
    HEADER_RESERVE,
};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::ValueWriter;
use crate::lazy::encoder::value_writer::{delegate_value_writer_to_self, AnnotatableWriter};
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::cold_error;
use crate::types::overflowing_int::Magnitude;
use crate::{v1_0, Decimal, Int, IonResult, IonType, RawSymbolRef, SymbolId, Timestamp};

/// The largest possible 'L' (length) value that can be written directly in a type descriptor byte.
/// Larger length values will need to be written as a VarUInt following the type descriptor.
pub(crate) const MAX_INLINE_LENGTH: usize = 13;

pub struct BinaryValueWriter_1_0<'value> {
    encoding_buffer: &'value mut Vec<u8>,
}

impl<'value> BinaryValueWriter_1_0<'value> {
    pub(crate) fn new(encoding_buffer: &'value mut Vec<u8>) -> BinaryValueWriter_1_0<'value> {
        BinaryValueWriter_1_0 { encoding_buffer }
    }

    #[inline]
    fn push_byte(&mut self, byte: u8) {
        self.encoding_buffer.push(byte);
    }

    #[inline]
    fn push_bytes(&mut self, bytes: &[u8]) {
        self.encoding_buffer.extend_from_slice(bytes)
    }

    pub fn write_symbol_id(mut self, symbol_id: SymbolId) -> IonResult<()> {
        const SYMBOL_BUFFER_SIZE: usize = mem::size_of::<u64>();
        let mut writer = std::io::Cursor::new([0u8; SYMBOL_BUFFER_SIZE]);
        let encoded_length = DecodedUInt::write_u64(&mut writer, symbol_id as u64)?;
        let buffer: [u8; SYMBOL_BUFFER_SIZE] = writer.into_inner();
        let encoded_id: &[u8] = &buffer[..encoded_length];

        let type_descriptor: u8;
        if encoded_length <= MAX_INLINE_LENGTH {
            type_descriptor = 0x70 | encoded_length as u8;
            self.push_byte(type_descriptor);
        } else {
            type_descriptor = 0x7E;
            self.push_byte(type_descriptor);
            VarUInt::write_u64(self.encoding_buffer, encoded_length as u64)?;
        }
        self.push_bytes(encoded_id);
        Ok(())
    }

    pub fn write_lob(mut self, value: &[u8], type_code: u8) -> IonResult<()> {
        let encoded_length = value.len();
        let type_descriptor: u8;
        if encoded_length <= MAX_INLINE_LENGTH {
            type_descriptor = type_code | encoded_length as u8;
            self.push_byte(type_descriptor);
        } else {
            type_descriptor = type_code | 0x0E;
            self.push_byte(type_descriptor);
            VarUInt::write_u64(self.encoding_buffer, encoded_length as u64)?;
        }
        self.push_bytes(value);
        Ok(())
    }

    pub fn write_null(mut self, ion_type: IonType) -> IonResult<()> {
        let byte: u8 = match ion_type {
            IonType::Null => 0x0F,
            IonType::Bool => 0x1F,
            IonType::Int => 0x2F,
            IonType::Float => 0x4F,
            IonType::Decimal => 0x5F,
            IonType::Timestamp => 0x6F,
            IonType::Symbol => 0x7F,
            IonType::String => 0x8F,
            IonType::Clob => 0x9F,
            IonType::Blob => 0xAF,
            IonType::List => 0xBF,
            IonType::SExp => 0xCF,
            IonType::Struct => 0xDF,
        };
        self.push_byte(byte);
        Ok(())
    }

    pub fn write_bool(mut self, value: bool) -> IonResult<()> {
        let byte: u8 = if value { 0x11 } else { 0x10 };
        self.push_byte(byte);
        Ok(())
    }

    pub fn write_i64(mut self, value: i64) -> IonResult<()> {
        // Get the absolute value of the i64 and store it in a u64.
        let magnitude: u64 = value.unsigned_abs();
        let encoded = uint::encode(magnitude);
        let bytes_to_write = encoded.as_bytes();

        // The encoded length will never be larger than 8 bytes, so it will
        // always fit in the Int's type descriptor byte.
        let encoded_length = bytes_to_write.len();
        let type_descriptor: u8 = if value >= 0 {
            0x20 | (encoded_length as u8)
        } else {
            0x30 | (encoded_length as u8)
        };
        self.push_byte(type_descriptor);
        self.push_bytes(bytes_to_write);

        Ok(())
    }

    pub fn write_int(mut self, value: &Int) -> IonResult<()> {
        let type_descriptor: u8 = if value.is_negative() { 0x30 } else { 0x20 };
        match value.as_overflowing_int().magnitude_ref() {
            Magnitude::Small(small) => {
                let (be, start) = minimal_be_bytes(small);
                self.write_int_header_and_bytes(type_descriptor, &be[start..])
            }
            Magnitude::Big(big) => cold_path! {{
                let be = big.to_bytes_be();
                self.write_int_header_and_bytes(type_descriptor, &be)
            }},
        }
    }

    #[inline]
    fn write_int_header_and_bytes(&mut self, type_descriptor: u8, bytes: &[u8]) -> IonResult<()> {
        let encoded_length = bytes.len();
        if encoded_length <= MAX_INLINE_LENGTH {
            self.push_byte(type_descriptor | encoded_length as u8);
        } else {
            // Cold path: the length does not fit in the type descriptor's `L` field, so it has to
            // be written as a trailing VarUInt.
            cold_path! {{
                self.push_byte(type_descriptor | 0x0E);
                VarUInt::write_u64(self.encoding_buffer, encoded_length as u64)
            }}?;
        }
        self.push_bytes(bytes);
        Ok(())
    }

    pub fn write_f32(mut self, value: f32) -> IonResult<()> {
        if value == 0f32 && !value.is_sign_negative() {
            self.push_byte(0x40);
            return Ok(());
        }

        self.push_byte(0x44);
        self.push_bytes(&value.to_be_bytes());
        Ok(())
    }

    pub fn write_f64(mut self, value: f64) -> IonResult<()> {
        if value == 0f64 && !value.is_sign_negative() {
            self.push_byte(0x40);
            return Ok(());
        }

        // See if this value can be losslessly encoded in 4 bytes instead of 8
        let float32 = value as f32;
        if float32 as f64 == value {
            // No data lost during cast; write it as an f32 instead.
            return self.write_f32(float32);
        }

        self.push_byte(0x48);
        self.push_bytes(&value.to_be_bytes());
        Ok(())
    }

    pub fn write_decimal(self, value: &Decimal) -> IonResult<()> {
        let _encoded_size = self.encoding_buffer.encode_decimal_value(value)?;
        Ok(())
    }

    pub fn write_timestamp(self, value: &Timestamp) -> IonResult<()> {
        let _ = self.encoding_buffer.encode_timestamp_value(value)?;
        Ok(())
    }

    pub fn write_string<A: AsRef<str>>(mut self, value: A) -> IonResult<()> {
        let text: &str = value.as_ref();
        let encoded_length = text.len(); // The number of utf8 bytes

        let type_descriptor: u8;
        if encoded_length <= MAX_INLINE_LENGTH {
            type_descriptor = 0x80 | encoded_length as u8;
            self.push_byte(type_descriptor);
        } else {
            type_descriptor = 0x8E;
            self.push_byte(type_descriptor);
            VarUInt::write_u64(self.encoding_buffer, encoded_length as u64)?;
        }
        self.push_bytes(text.as_bytes());
        Ok(())
    }

    pub fn write_symbol<A: AsRawSymbolRef>(self, value: A) -> IonResult<()> {
        match value.as_raw_symbol_ref() {
            RawSymbolRef::SymbolId(sid) => self.write_symbol_id(sid),
            other => cold_error!(
                illegal_operation,
                "the Ion 1.0 raw binary writer only supports symbol ID values; received: {other:?})"
            ),
        }
    }

    pub fn write_clob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()> {
        let bytes: &[u8] = value.as_ref();
        // The clob type descriptor's high nibble is type code 9
        self.write_lob(bytes, 0x90)
    }

    pub fn write_blob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()> {
        let bytes: &[u8] = value.as_ref();
        // The blob type descriptor's high nibble is type code 10 (0xA)
        self.write_lob(bytes, 0xA0)
    }

    fn list_writer(self) -> IonResult<BinaryListWriter_1_0<'value>> {
        Ok(BinaryListWriter_1_0::new(self.encoding_buffer))
    }

    fn sexp_writer(self) -> IonResult<BinarySExpWriter_1_0<'value>> {
        Ok(BinarySExpWriter_1_0::new(self.encoding_buffer))
    }

    fn struct_writer(self) -> IonResult<BinaryStructWriter_1_0<'value>> {
        Ok(BinaryStructWriter_1_0::new(self.encoding_buffer))
    }
}

impl Sealed for BinaryValueWriter_1_0<'_> {}

impl AnnotatableWriter for BinaryValueWriter_1_0<'_> {
    type AnnotatedValueWriter<'a>
        = BinaryAnnotatedValueWriter_1_0<'a>
    where
        Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(BinaryAnnotatedValueWriter_1_0::new(
            annotations.into_annotations_vec(),
            self.encoding_buffer,
        ))
    }
}

impl<'value> ValueWriter for BinaryValueWriter_1_0<'value> {
    type Encoding = v1_0::Binary;
    type ListWriter = BinaryListWriter_1_0<'value>;
    type SExpWriter = BinarySExpWriter_1_0<'value>;
    type StructWriter = BinaryStructWriter_1_0<'value>;

    delegate_value_writer_to_self!();
}

pub struct BinaryAnnotatedValueWriter_1_0<'value> {
    annotations: AnnotationsVec<'value>,
    output_buffer: &'value mut Vec<u8>,
}

impl<'value> BinaryAnnotatedValueWriter_1_0<'value> {
    pub(crate) fn new(
        annotations: AnnotationsVec<'value>,
        encoding_buffer: &'value mut Vec<u8>,
    ) -> BinaryAnnotatedValueWriter_1_0<'value> {
        BinaryAnnotatedValueWriter_1_0 {
            annotations,
            output_buffer: encoding_buffer,
        }
    }
}

/// Takes a series of `TYPE => METHOD` pairs, generating a function for each that encodes an
/// annotations wrapper and then delegates encoding the value to the corresponding value writer
/// method.
macro_rules! annotate_and_delegate_1_0 {
    // End of iteration
    () => {};
    // Recurses one argument pair at a time
    ($value_type:ty => $method:ident, $($rest:tt)*) => {
        fn $method(self, value: $value_type) -> IonResult<()> {
            Self::write_annotated_in_place(
                &self.annotations,
                self.output_buffer,
                |value_writer| value_writer.$method(value),
            )
        }
        annotate_and_delegate_1_0!($($rest)*);
    };
}

impl BinaryAnnotatedValueWriter_1_0<'_> {
    /// Encodes the value that `write_value` encodes at the end of `buffer`, inside an annotations
    /// wrapper unless `annotations` is empty. The wrapper header is reserved up front and filled in
    /// afterward. If `annotations` is non-empty and encoding fails or panics, `buffer` is truncated
    /// back to where it was; with no annotations, `write_value` writes to `buffer` directly.
    fn write_annotated_in_place(
        annotations: &AnnotationsVec<'_>,
        buffer: &mut Vec<u8>,
        write_value: impl FnOnce(BinaryValueWriter_1_0<'_>) -> IonResult<()>,
    ) -> IonResult<()> {
        if annotations.is_empty() {
            return write_value(BinaryValueWriter_1_0::new(buffer));
        }
        let encoding = TruncateOnDrop::new(buffer);
        let start = encoding.start;
        write_annotations_prefix(encoding.buffer, annotations)?;
        write_value(BinaryValueWriter_1_0::new(encoding.buffer))?;

        let envelope_length = encoding.buffer.len() - (start + HEADER_RESERVE);
        let wrapper_size = header_length(envelope_length);
        shift_tail(
            encoding.buffer,
            start + HEADER_RESERVE,
            wrapper_size as isize - HEADER_RESERVE as isize,
        );
        write_header(
            &mut encoding.buffer[start..start + wrapper_size],
            ANNOTATIONS_WRAPPER_TYPE_CODE,
            envelope_length,
        );
        encoding.commit();
        Ok(())
    }
}

impl Sealed for BinaryAnnotatedValueWriter_1_0<'_> {
    // No methods, precludes implementations outside the crate.
}

impl AnnotatableWriter for BinaryAnnotatedValueWriter_1_0<'_> {
    type AnnotatedValueWriter<'a>
        = BinaryAnnotatedValueWriter_1_0<'a>
    where
        Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(BinaryAnnotatedValueWriter_1_0 {
            annotations: annotations.into_annotations_vec(),
            output_buffer: self.output_buffer,
        })
    }
}

impl<'value> ValueWriter for BinaryAnnotatedValueWriter_1_0<'value> {
    type Encoding = v1_0::Binary;
    type ListWriter = BinaryListWriter_1_0<'value>;
    type SExpWriter = BinarySExpWriter_1_0<'value>;
    type StructWriter = BinaryStructWriter_1_0<'value>;

    annotate_and_delegate_1_0!(
        IonType => write_null,
        bool => write_bool,
        i64 => write_i64,
        &Int => write_int,
        f32 => write_f32,
        f64 => write_f64,
        &Decimal => write_decimal,
        &Timestamp => write_timestamp,
        impl AsRef<str> => write_string,
        impl AsRawSymbolRef => write_symbol,
        impl AsRef<[u8]> => write_clob,
        impl AsRef<[u8]> => write_blob,
    );

    fn list_writer(self) -> IonResult<Self::ListWriter> {
        BinaryListWriter_1_0::new_annotated(self.output_buffer, &self.annotations)
    }
    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        BinarySExpWriter_1_0::new_annotated(self.output_buffer, &self.annotations)
    }
    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        BinaryStructWriter_1_0::new_annotated(self.output_buffer, &self.annotations)
    }
}

#[cfg(test)]
mod tests {
    use std::panic::{self, AssertUnwindSafe};

    use super::BinaryListWriter_1_0;
    use crate::lazy::encoder::annotate::Annotatable;
    use crate::lazy::encoder::binary::v1_0::writer::LazyRawBinaryWriter_1_0;
    use crate::lazy::encoder::value_writer::StructWriter;
    use crate::lazy::encoder::value_writer::{AnnotatableWriter, SequenceWriter};
    use crate::lazy::encoder::write_as_ion::WriteAsSExp;
    use crate::raw_symbol_ref::AsRawSymbolRef;
    use crate::{
        Element, Int, IonData, IonResult, RawSymbolRef, SymbolId, Timestamp, UInt, ValueWriter,
    };
    use rstest::rstest;

    fn writer_test(
        expected: &str,
        test: impl FnOnce(&mut LazyRawBinaryWriter_1_0<Vec<u8>>) -> IonResult<()>,
    ) -> IonResult<()> {
        let expected = Element::read_all(expected)?;
        let mut writer = LazyRawBinaryWriter_1_0::new(Vec::new())?;
        test(&mut writer)?;
        let buffer = writer.close()?;
        let actual = Element::read_all(buffer)?;
        assert!(
            IonData::eq(&expected, &actual),
            "Actual \n    {actual:?}\nwas not equal to\n    {expected:?}\n"
        );
        Ok(())
    }

    /// Runs `test` and asserts the exact bytes it encodes after the Ion 1.0 IVM.
    fn encoding_test(
        test: impl FnOnce(&mut LazyRawBinaryWriter_1_0<&mut Vec<u8>>) -> IonResult<()>,
        expected_encoding: &[u8],
    ) -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut writer = LazyRawBinaryWriter_1_0::new(&mut buffer)?;
        test(&mut writer)?;
        writer.flush()?;
        // Make a byte array that starts with an Ion 1.0 IVM.
        let mut expected = vec![0xE0, 0x01, 0x00, 0xEA];
        expected.extend_from_slice(expected_encoding);
        let expected = expected.as_slice();
        let actual = buffer.as_slice();
        assert_eq!(
            expected, actual,
            "Actual \n    {actual:x?}\nwas not equal to\n    {expected:x?}\n"
        );
        Ok(())
    }

    /// Returns `2^128`, the smallest magnitude that `Int` cannot store inline. Encoding it takes
    /// `write_int`'s heap-allocating `BigUint` path.
    fn two_pow_128() -> Int {
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        Int::from_le_signed_bytes(&bytes)
    }

    /// Pins the bytes that `BinaryValueWriter_1_0::write_int` emits. `writer_test` only compares
    /// decoded `Element`s, and the reader accepts zero-padded magnitudes, so nothing else in this
    /// module would notice if the magnitude stopped being trimmed to its minimal length.
    #[rstest]
    // Zero is written as an explicit `0x00` magnitude byte (unlike `write_i64(0)`, which emits a
    // bare `0x20`).
    #[case::zero(Int::from(0i64), &[0x21, 0x00])]
    // The 127/128 boundary: Ion 1.0 stores the sign in the type descriptor, not the magnitude, so
    // 128 still fits in one magnitude byte.
    #[case::one_hundred_twenty_seven(Int::from(127i64), &[0x21, 0x7F])]
    #[case::one_hundred_twenty_eight(Int::from(128i64), &[0x21, 0x80])]
    #[case::negative_one_hundred_twenty_eight(Int::from(-128i64), &[0x31, 0x80])]
    // Eight-byte magnitudes.
    #[case::max_i64(Int::from(i64::MAX), &[0x28, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])]
    #[case::min_i64(Int::from(i64::MIN), &[0x38, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])]
    // 2^96 has a 13-byte magnitude: the largest length that fits in the descriptor's `L` field.
    #[case::thirteen_byte_magnitude(
        Int::from(1i128 << 96),
        &[
            0x2D,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    // 2^104 has a 14-byte magnitude, one past the boundary, so `L` becomes 14 (0xE) and the real
    // length follows as a VarUInt.
    #[case::fourteen_byte_magnitude(
        Int::from(1i128 << 104),
        &[
            0x2E, 0x8E,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    // Negative 14-byte magnitude: same VarUInt-length header as above, but the negative type
    // descriptor `0x3E`. Guards the sign nibble on the `L == 0xE` path.
    #[case::negative_fourteen_byte_magnitude(
        Int::from(-(1i128 << 104)),
        &[
            0x3E, 0x8E,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    // 2^126: the smallest magnitude stored on the heap. Sixteen magnitude bytes.
    #[case::two_pow_126(
        Int::from(1u128 << 126),
        &[
            0x2E, 0x90,
            0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    #[case::negative_two_pow_126(
        Int::from(1u128 << 126).neg(),
        &[
            0x3E, 0x90,
            0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    // `u128::MAX`: the largest sixteen-byte magnitude.
    #[case::max_u128_magnitude(
        Int::from(UInt::from(u128::MAX)),
        &[
            0x2E, 0x90,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        ]
    )]
    // 2^128: the smallest seventeen-byte magnitude.
    #[case::two_pow_128(
        two_pow_128(),
        &[
            0x2E, 0x91,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    #[case::negative_two_pow_128(
        two_pow_128().neg(),
        &[
            0x3E, 0x91,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    fn write_ints(#[case] value: Int, #[case] expected_encoding: &[u8]) -> IonResult<()> {
        encoding_test(
            |writer: &mut LazyRawBinaryWriter_1_0<&mut Vec<u8>>| {
                writer.write(&value)?;
                Ok(())
            },
            expected_encoding,
        )
    }

    #[test]
    fn write_scalars() -> IonResult<()> {
        let expected = r#"
            1
            false
            3e0
            "foo"
            name
            2023-11-09T
            {{4AEA6g==}}
        "#;

        writer_test(expected, |writer| {
            writer
                .write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write(RawSymbolRef::SymbolId(4))?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?;
            Ok(())
        })
    }

    #[test]
    fn write_empty_list() -> IonResult<()> {
        let expected = "[]";
        writer_test(expected, |writer| writer.list_writer()?.close())
    }

    #[test]
    fn write_list() -> IonResult<()> {
        let expected = r#"
            [
                1,
                false,
                3e0,
                "foo",
                name,
                2023-11-09T,
                {{4AEA6g==}},
                // Nested list
                [1, 2, 3],
            ]
        "#;
        writer_test(expected, |writer| {
            let mut list = writer.list_writer()?;
            list.write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write(RawSymbolRef::SymbolId(4))?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?
                .write([1, 2, 3])?;
            list.close()
        })
    }

    #[test]
    fn write_empty_sexp() -> IonResult<()> {
        let expected = "()";
        writer_test(expected, |writer| writer.sexp_writer()?.close())
    }

    #[test]
    fn write_sexp() -> IonResult<()> {
        let expected = r#"
            (
                1
                false
                3e0
                "foo"
                name
                2023-11-09T
                {{4AEA6g==}}
                // Nested list
                [1, 2, 3]
            )
        "#;
        writer_test(expected, |writer| {
            let mut sexp = writer.sexp_writer()?;
            sexp.write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write(RawSymbolRef::SymbolId(4))?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?
                .write([1, 2, 3])?;
            sexp.close()
        })
    }

    #[test]
    fn write_empty_struct() -> IonResult<()> {
        let expected = "{}";
        writer_test(expected, |writer| writer.struct_writer()?.close())
    }

    #[test]
    fn write_struct() -> IonResult<()> {
        let expected = r#"
            // This test uses symbol ID field names because the raw writer has no symbol table.
            {
                $0: 1,
                $1: false,
                $2: 3e0,
                $3: "foo",
                $4: name,
                $5: 2023-11-09T,
                $6: {{4AEA6g==}},
                // Nested list
                $7: [1, 2, 3],
            }
        "#;
        writer_test(expected, |writer| {
            let mut struct_ = writer.struct_writer()?;
            struct_
                .write(0, 1)?
                .write(1, false)?
                .write(2, 3f32)?
                .write(3, "foo")?
                .write(4, RawSymbolRef::SymbolId(4))?
                .write(5, Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write(6, [0xE0u8, 0x01, 0x00, 0xEA])?
                .write(7, [1, 2, 3])?;
            struct_.close()
        })
    }

    #[test]
    fn write_annotated_without_annotations() -> IonResult<()> {
        // This test explicitly adds an empty annotations sequence to values and value writers
        // to make sure they do not emit an annotations wrapper without annotations.
        let expected = "1 name 2024T";
        const EMPTY_ANNOTATIONS: [SymbolId; 0] = [];
        writer_test(expected, |writer| {
            writer.write(1.annotated_with(EMPTY_ANNOTATIONS))?;
            writer.write(RawSymbolRef::SymbolId(4).annotated_with(EMPTY_ANNOTATIONS))?;
            writer
                .value_writer()
                .with_annotations(EMPTY_ANNOTATIONS)?
                .write(Timestamp::with_year(2024).build()?)?;
            Ok(())
        })
    }

    #[test]
    fn write_annotated_scalars() -> IonResult<()> {
        let expected = r#"
        // The raw writer doesn't have a symbol table, so this only uses symbols
        // that are already in the system symbol table.
            name::1
            version::false
            imports::symbols::3e0
            max_id::version::"foo"
            $ion::$4
            $ion_symbol_table::2023-11-09T
            $ion_1_0::{{4AEA6g==}}
        "#;
        writer_test(expected, |writer| {
            writer
                .write(1.annotated_with(4))?
                .write(false.annotated_with([5]))?
                .write(3f32.annotated_with([6, 7]))?
                .write("foo".annotated_with([8, 5]))?
                .write(4usize.as_raw_symbol_ref().annotated_with(1))?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?.annotated_with(3))?
                .write((&[0xE0u8, 0x01, 0x00, 0xEA][..]).annotated_with(2))?;
            Ok(())
        })
    }

    #[test]
    fn write_annotated_containers() -> IonResult<()> {
        let expected = r#"
            []
            $4::[]
            $4::[1, 2, 3]
            $4::$7::[1, 2, 3]
            $4::$7::[
                $4::$7::[1, 2, 3]
            ]
            ()
            $4::()
            $4::(1 2 3)
            $4::$7::()
            $4::$7::(
                $4::$7::(1 2 3)
            )
        "#;
        writer_test(expected, |writer| {
            let empty_sequence: &[i32] = &[];
            // []
            writer
                .write(empty_sequence)?
                // $4::[]
                .write(empty_sequence.annotated_with([4]))?
                // $4::[1, 2, 3]
                .write([1, 2, 3].annotated_with([4]))?
                // $4::$7::[1, 2, 3]
                .write([1, 2, 3].annotated_with([4, 7]))?
                // $4::$7::[
                //      $4::$7::[1, 2, 3]
                // ]
                .write([[1usize, 2, 3].annotated_with([4, 7])].annotated_with([4, 7]))?
                // ()
                .write(empty_sequence.as_sexp())?
                // $4::()
                .write(empty_sequence.as_sexp().annotated_with([4]))?
                // $4::(1 2 3)
                .write([1, 2, 3].as_sexp().annotated_with([4]))?
                // $4::$7::()
                .write(empty_sequence.as_sexp().annotated_with([4, 7]))?
                // $4::$7::(
                //   $4::$7::(1 2 3)
                // )
                .write(
                    [[1, 2, 3].as_sexp().annotated_with([4, 7])]
                        .as_sexp()
                        .annotated_with([4, 7]),
                )?;
            Ok(())
        })
    }

    /// An empty annotations sequence, which an annotated value writer encodes as a bare value with
    /// no wrapper.
    const NO_ANNOTATIONS: [SymbolId; 0] = [];

    /// The writer type `encoding_test` passes to its test closure.
    type BufferWriter<'a> = LazyRawBinaryWriter_1_0<&'a mut Vec<u8>>;

    /// Pins the bytes of annotations wrappers at the boundaries of their length arithmetic. The
    /// wrapper's length `L` covers the `annot_length` VarUInt, the annotation SIDs, and the wrapped
    /// value; up to 13 it fits in the type descriptor (`0xE0 | L`), past that the descriptor is
    /// `0xEE` and `L` follows as a VarUInt. Each case shows `L` as
    /// `annot_length VarUInt + SIDs + wrapped value`.
    #[rstest]
    // L = 1 (0x81) + 1 (0x84) + 11 (0x8A + 10 bytes) = 13: the largest inline length.
    #[case::scalar_inline_length_13(
        |w: &mut BufferWriter<'_>| { w.write("a".repeat(10).annotated_with(4))?; Ok(()) },
        [&[0xED, 0x81, 0x84, 0x8A][..], &[b'a'; 10]].concat()
    )]
    // L = 1 (0x81) + 1 (0x84) + 12 (0x8B + 11 bytes) = 14: the smallest VarUInt length.
    #[case::scalar_varuint_length_14(
        |w: &mut BufferWriter<'_>| { w.write("a".repeat(11).annotated_with(4))?; Ok(()) },
        [&[0xEE, 0x8E, 0x81, 0x84, 0x8B][..], &[b'a'; 11]].concat()
    )]
    // L = 1 (0x81) + 1 (0x84) + 11 (0xBA + ten 0x20 ints) = 13.
    #[case::list_inline_length_13(
        |w: &mut BufferWriter<'_>| { w.write([0; 10].annotated_with(4))?; Ok(()) },
        [&[0xED, 0x81, 0x84, 0xBA][..], &[0x20; 10]].concat()
    )]
    // L = 1 (0x81) + 1 (0x84) + 12 (0xBB + eleven 0x20 ints) = 14.
    #[case::list_varuint_length_14(
        |w: &mut BufferWriter<'_>| { w.write([0; 11].annotated_with(4))?; Ok(()) },
        [&[0xEE, 0x8E, 0x81, 0x84, 0xBB][..], &[0x20; 11]].concat()
    )]
    // A 14-byte list body needs a VarUInt length of its own (0xBE 0x8E).
    // L = 1 (0x81) + 1 (0x84) + 16 (0xBE 0x8E + fourteen 0x20 ints) = 18 (0x92).
    #[case::list_body_varuint_length_14(
        |w: &mut BufferWriter<'_>| { w.write([0; 14].annotated_with(4))?; Ok(()) },
        [&[0xEE, 0x92, 0x81, 0x84, 0xBE, 0x8E][..], &[0x20; 14]].concat()
    )]
    // Struct body: five `$N: 0` fields, each `0x8N 0x20`, for 10 bytes.
    // L = 1 (0x81) + 1 (0x84) + 11 (0xDA + 10 bytes) = 13.
    #[case::struct_inline_length_13(
        |w: &mut BufferWriter<'_>| {
            let mut struct_ = w.value_writer().with_annotations(4)?.struct_writer()?;
            for field_id in 10..15 {
                struct_.write(field_id, 0)?;
            }
            struct_.close()
        },
        vec![
            0xED, 0x81, 0x84, 0xDA,
            0x8A, 0x20, 0x8B, 0x20, 0x8C, 0x20, 0x8D, 0x20, 0x8E, 0x20,
        ]
    )]
    // SID 200 = 1 * 128 + 72 is the two-byte VarUInt 0x01 0xC8.
    // L = 1 (0x82) + 2 (0x01 0xC8) + 1 (0x20) = 4.
    #[case::scalar_two_byte_sid(
        |w: &mut BufferWriter<'_>| { w.write(0.annotated_with(200))?; Ok(()) },
        vec![0xE4, 0x82, 0x01, 0xC8, 0x20]
    )]
    // L = 1 (0x82) + 2 (0x01 0xC8) + 2 (0xB1 0x20) = 5.
    #[case::list_two_byte_sid(
        |w: &mut BufferWriter<'_>| { w.write([0].annotated_with(200))?; Ok(()) },
        vec![0xE5, 0x82, 0x01, 0xC8, 0xB1, 0x20]
    )]
    // 128 one-byte SIDs: annot_length 128 is the two-byte VarUInt 0x01 0x80.
    // L = 2 (0x01 0x80) + 128 + 1 (0x20) = 131 = 1 * 128 + 3, the VarUInt 0x01 0x83.
    #[case::scalar_128_byte_annotations_sequence(
        |w: &mut BufferWriter<'_>| { w.write(0.annotated_with([4; 128]))?; Ok(()) },
        [&[0xEE, 0x01, 0x83, 0x01, 0x80][..], &[0x84; 128], &[0x20]].concat()
    )]
    // L = 2 (0x01 0x80) + 128 + 2 (0xB1 0x20) = 132 = 1 * 128 + 4, the VarUInt 0x01 0x84.
    #[case::list_128_byte_annotations_sequence(
        |w: &mut BufferWriter<'_>| { w.write([0].annotated_with([4; 128]))?; Ok(()) },
        [&[0xEE, 0x01, 0x84, 0x01, 0x80][..], &[0x84; 128], &[0xB1, 0x20]].concat()
    )]
    // An empty list: both the wrapper and the container header shrink from their two reserved bytes
    // to one. L = 1 (0x81) + 1 (0x84) + 1 (0xB0) = 3.
    #[case::list_empty_both_headers_shrink(
        |w: &mut BufferWriter<'_>| { w.write([0; 0].annotated_with(4))?; Ok(()) },
        vec![0xE3, 0x81, 0x84, 0xB0]
    )]
    // A 128-byte list body needs a two-byte VarUInt length (0xBE 0x01 0x80).
    // L = 1 (0x81) + 1 (0x84) + 131 (0xBE 0x01 0x80 + 128 0x20 ints) = 133 = 1 * 128 + 5 (0x01 0x85).
    #[case::list_body_two_byte_varuint_length(
        |w: &mut BufferWriter<'_>| { w.write([0; 128].annotated_with(4))?; Ok(()) },
        [&[0xEE, 0x01, 0x85, 0x81, 0x84, 0xBE, 0x01, 0x80][..], &[0x20; 128]].concat()
    )]
    // The wrapper grows to a two-byte VarUInt length while the list header fits (0xBE 0xFF).
    // L = 1 (0x81) + 1 (0x84) + 129 (0xBE 0xFF + 127 0x20 ints) = 131 = 1 * 128 + 3 (0x01 0x83).
    #[case::list_wrapper_grows_header_fits(
        |w: &mut BufferWriter<'_>| { w.write([0; 127].annotated_with(4))?; Ok(()) },
        [&[0xEE, 0x01, 0x83, 0x81, 0x84, 0xBE, 0xFF][..], &[0x20; 127]].concat()
    )]
    // The wrapper grows by two bytes while the list header shrinks to 0xB1, so the annotations
    // move further than the body. annot_length 16380 = 127 * 128 + 124 is 0x7F 0xFC.
    // L = 2 + 16380 + 2 (0xB1 0x20) = 16384 = 1 * 128^2, the VarUInt 0x01 0x00 0x80.
    #[case::list_wrapper_grows_by_two(
        |w: &mut BufferWriter<'_>| { w.write([0].annotated_with([4; 16380]))?; Ok(()) },
        [&[0xEE, 0x01, 0x00, 0x80, 0x7F, 0xFC][..], &[0x84; 16380], &[0xB1, 0x20]].concat()
    )]
    // L = 1 (0x81) + 1 (0x84) + 16388 (0x8E 0x01 0x00 0x80 + 16384 bytes) = 16390 = 128^2 + 6.
    #[case::scalar_wrapper_grows_by_two(
        |w: &mut BufferWriter<'_>| { w.write("a".repeat(16384).annotated_with(4))?; Ok(()) },
        [
            &[0xEE, 0x01, 0x00, 0x86, 0x81, 0x84, 0x8E, 0x01, 0x00, 0x80][..],
            &[b'a'; 16384],
        ]
        .concat()
    )]
    // No annotations: the list is written bare, with no wrapper.
    #[case::list_without_annotations(
        |w: &mut BufferWriter<'_>| {
            let mut list = w.value_writer().with_annotations(NO_ANNOTATIONS)?.list_writer()?;
            list.write(0)?.write(0)?;
            list.close()
        },
        vec![0xB2, 0x20, 0x20]
    )]
    fn write_annotations_wrapper_lengths(
        #[case] test: fn(&mut BufferWriter<'_>) -> IonResult<()>,
        #[case] expected_encoding: Vec<u8>,
    ) -> IonResult<()> {
        encoding_test(test, &expected_encoding)
    }

    /// Pins container headers at the boundaries of the in-place encoding. Two header bytes are
    /// reserved ahead of each body: bodies of up to 13 bytes shift left by one, 14–127 byte bodies
    /// fit exactly, and longer bodies shift right.
    #[rstest]
    // Empty body: 0xB0 alone, one byte shorter than reserved.
    #[case::body_0_shifts_left(
        |w: &mut BufferWriter<'_>| { w.write([0; 0])?; Ok(()) },
        vec![0xB0]
    )]
    // 13-byte body: the length fits in the type descriptor (0xBD), one byte shorter than reserved.
    #[case::body_13_shifts_left(
        |w: &mut BufferWriter<'_>| { w.write([0; 13])?; Ok(()) },
        [&[0xBD][..], &[0x20; 13]].concat()
    )]
    // 14-byte body: 0xBE plus the one-byte VarUInt 0x8E, exactly the reserved size.
    #[case::body_14_fits(
        |w: &mut BufferWriter<'_>| { w.write([0; 14])?; Ok(()) },
        [&[0xBE, 0x8E][..], &[0x20; 14]].concat()
    )]
    // 127-byte body: the largest one-byte VarUInt length, 0xFF.
    #[case::body_127_fits(
        |w: &mut BufferWriter<'_>| { w.write([0; 127])?; Ok(()) },
        [&[0xBE, 0xFF][..], &[0x20; 127]].concat()
    )]
    // 128-byte body: the two-byte VarUInt 0x01 0x80, one byte longer than reserved.
    #[case::body_128_shifts_right(
        |w: &mut BufferWriter<'_>| { w.write([0; 128])?; Ok(()) },
        [&[0xBE, 0x01, 0x80][..], &[0x20; 128]].concat()
    )]
    // 16383-byte body: 16383 = 127 * 128 + 127, the largest two-byte VarUInt, 0x7F 0xFF.
    #[case::body_16383_shifts_right(
        |w: &mut BufferWriter<'_>| { w.write(vec![0; 16383])?; Ok(()) },
        [&[0xBE, 0x7F, 0xFF][..], &vec![0x20; 16383]].concat()
    )]
    // 16384-byte body: 16384 = 1 * 128^2, the three-byte VarUInt 0x01 0x00 0x80.
    #[case::body_16384_shifts_right_by_two(
        |w: &mut BufferWriter<'_>| { w.write(vec![0; 16384])?; Ok(()) },
        [&[0xBE, 0x01, 0x00, 0x80][..], &vec![0x20; 16384]].concat()
    )]
    // A 128-byte inner list (0xBE 0x01 0x80 + 128) inside an outer list whose body is then 131 bytes
    // (0xBE 0x01 0x83): the inner shift happens while the outer container is still open.
    #[case::nested_body_shifts_right(
        |w: &mut BufferWriter<'_>| { w.write([[0; 128]])?; Ok(()) },
        [&[0xBE, 0x01, 0x83, 0xBE, 0x01, 0x80][..], &[0x20; 128]].concat()
    )]
    // A struct body of five `$N: 0` fields (10 bytes) shifts left to an inline length.
    #[case::struct_body_10_shifts_left(
        |w: &mut BufferWriter<'_>| {
            let mut struct_ = w.value_writer().struct_writer()?;
            for field_id in 10..15 {
                struct_.write(field_id, 0)?;
            }
            struct_.close()
        },
        vec![0xDA, 0x8A, 0x20, 0x8B, 0x20, 0x8C, 0x20, 0x8D, 0x20, 0x8E, 0x20]
    )]
    fn write_container_header_lengths(
        #[case] test: fn(&mut BufferWriter<'_>) -> IonResult<()>,
        #[case] expected_encoding: Vec<u8>,
    ) -> IonResult<()> {
        encoding_test(test, &expected_encoding)
    }

    /// A value that is abandoned or fails part way leaves no bytes behind: a container writer
    /// dropped without `close` (including through a failing child), an annotation that cannot be
    /// encoded, or a wrapped value that fails after its annotations. The values around it encode as
    /// though it was never started. Each case runs between a top-level `0` and `5`.
    #[rstest]
    #[case::abandoned_list(|w: &mut BufferWriter<'_>| {
        let mut list = w.value_writer().list_writer()?;
        list.write(1)?.write([2, 3])?;
        Ok(())
    })]
    #[case::abandoned_annotated_struct(|w: &mut BufferWriter<'_>| {
        let mut struct_ = w.value_writer().with_annotations(4)?.struct_writer()?;
        struct_.write(10, 1)?;
        Ok(())
    })]
    #[case::text_annotation_on_scalar(|w: &mut BufferWriter<'_>| {
        assert!(w.write(1.annotated_with("a")).is_err());
        Ok(())
    })]
    #[case::text_annotation_on_container(|w: &mut BufferWriter<'_>| {
        assert!(w.write([1, 2].annotated_with([4.as_raw_symbol_ref(), "a".as_raw_symbol_ref()])).is_err());
        Ok(())
    })]
    // The value fails after its annotations sequence has been written.
    #[case::text_symbol_value_annotated(|w: &mut BufferWriter<'_>| {
        assert!(w.write(RawSymbolRef::Text("a").annotated_with(4)).is_err());
        Ok(())
    })]
    #[case::failing_child_in_list(|w: &mut BufferWriter<'_>| {
        assert!(w.write([RawSymbolRef::SymbolId(4), RawSymbolRef::Text("a")]).is_err());
        Ok(())
    })]
    fn abandoned_values_leave_no_bytes(
        #[case] abandon: fn(&mut BufferWriter<'_>) -> IonResult<()>,
    ) -> IonResult<()> {
        encoding_test(
            |w| {
                w.write(0)?;
                abandon(w)?;
                w.write(5)?;
                Ok(())
            },
            &[0x20, 0x21, 0x05],
        )
    }

    /// A nested value abandoned part way leaves its parent intact: the parent's remaining children
    /// and its header are encoded as though the nested value was never started. Each case runs
    /// between the parent's `1` and `2`.
    #[rstest]
    #[case::abandoned_nested_container(|outer: &mut BinaryListWriter_1_0<'_>| {
        let mut inner = outer.value_writer().list_writer()?;
        inner.write([0; 20])?;
        Ok(())
    })]
    #[case::failing_annotated_scalar(|outer: &mut BinaryListWriter_1_0<'_>| {
        assert!(outer.write(RawSymbolRef::Text("a").annotated_with(4)).is_err());
        Ok(())
    })]
    fn abandoned_nested_value_leaves_parent_intact(
        #[case] abandon: fn(&mut BinaryListWriter_1_0<'_>) -> IonResult<()>,
    ) -> IonResult<()> {
        encoding_test(
            |w| {
                let mut outer = w.value_writer().list_writer()?;
                outer.write(1)?;
                abandon(&mut outer)?;
                outer.write(2)?;
                outer.close()
            },
            &[0xB4, 0x21, 0x01, 0x21, 0x02],
        )
    }

    /// A panic raised while an annotated top-level scalar is being encoded, after its annotations
    /// sequence has been written, leaves no bytes behind.
    #[test]
    fn panic_in_annotated_scalar_leaves_no_bytes() -> IonResult<()> {
        struct PanickingText;
        impl AsRef<str> for PanickingText {
            fn as_ref(&self) -> &str {
                panic!("PanickingText::as_ref");
            }
        }
        encoding_test(
            |w| {
                w.write(0)?;
                let result = panic::catch_unwind(AssertUnwindSafe(|| {
                    w.value_writer()
                        .with_annotations(4)?
                        .write_string(PanickingText)
                }));
                assert!(result.is_err(), "`PanickingText::as_ref` did not panic");
                w.write(5)?;
                Ok(())
            },
            &[0x20, 0x21, 0x05],
        )
    }
}
