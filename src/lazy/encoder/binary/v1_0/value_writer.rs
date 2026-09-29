use std::mem;

use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use ice_code::ice as cold_path;

use crate::binary::decimal::DecimalBinaryEncoder;
use crate::binary::timestamp::TimestampBinaryEncoder;
use crate::binary::uint;
use crate::binary::uint::DecodedUInt;
use crate::binary::var_uint::VarUInt;
use crate::lazy::encoder::annotation_seq::{AnnotationSeq, AnnotationsVec};
use crate::lazy::encoder::binary::v1_0::container_writers::{
    BinaryListWriter_1_0, BinarySExpWriter_1_0, BinaryStructWriter_1_0,
};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::ValueWriter;
use crate::lazy::encoder::value_writer::{delegate_value_writer_to_self, AnnotatableWriter};
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::{EncodingError, IonFailure};
use crate::types::integer::{AsBigOrSmallValue, UIntData};
use crate::{Decimal, Int, IonError, IonResult, IonType, RawSymbolRef, SymbolId, Timestamp};

/// The largest possible 'L' (length) value that can be written directly in a type descriptor byte.
/// Larger length values will need to be written as a VarUInt following the type descriptor.
pub(crate) const MAX_INLINE_LENGTH: usize = 13;

pub struct BinaryValueWriter_1_0<'value, 'top> {
    allocator: &'top BumpAllocator,
    encoding_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryValueWriter_1_0<'value, 'top> {
    pub fn new(
        allocator: &'top BumpAllocator,
        encoding_buffer: &'value mut BumpVec<'top, u8>,
    ) -> BinaryValueWriter_1_0<'value, 'top> {
        BinaryValueWriter_1_0 {
            allocator,
            encoding_buffer,
        }
    }

    #[inline]
    fn push_byte(&mut self, byte: u8) {
        self.encoding_buffer.push(byte);
    }

    #[inline]
    fn push_bytes(&mut self, bytes: &[u8]) {
        self.encoding_buffer.extend_from_slice_copy(bytes)
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
        let magnitude = value.unsigned_abs().data;
        let type_descriptor: u8 = if value.is_negative() { 0x30 } else { 0x20 };
        if let Some(mag) = magnitude.as_small_value() {
            // Common case: the magnitude is stored inline, so it can be encoded on the stack with
            // no heap allocation.
            let (be, start) = UIntData::small_to_be_bytes(mag);
            self.write_int_header_and_bytes(type_descriptor, &be[start..])
        } else {
            // Cold path: a BigUint magnitude, which has to be heap-allocated to be encoded.
            cold_path! {{
                let bytes_to_write = magnitude.to_be_bytes();
                self.write_int_header_and_bytes(type_descriptor, &bytes_to_write)
            }}
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
            other => IonResult::illegal_operation(format!(
                "the Ion 1.0 raw binary writer only supports symbol ID values; received: {other:?})"
            )),
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

    fn list_writer(self) -> IonResult<BinaryListWriter_1_0<'value, 'top>> {
        Ok(BinaryListWriter_1_0::new(
            self.allocator,
            self.encoding_buffer,
        ))
    }

    fn sexp_writer(self) -> IonResult<BinarySExpWriter_1_0<'value, 'top>> {
        Ok(BinarySExpWriter_1_0::new(
            self.allocator,
            self.encoding_buffer,
        ))
    }

    fn struct_writer(self) -> IonResult<BinaryStructWriter_1_0<'value, 'top>> {
        Ok(BinaryStructWriter_1_0::new(
            self.allocator,
            self.encoding_buffer,
        ))
    }
}

impl Sealed for BinaryValueWriter_1_0<'_, '_> {}

impl<'top> AnnotatableWriter for BinaryValueWriter_1_0<'_, 'top> {
    type AnnotatedValueWriter<'a>
        = BinaryAnnotatedValueWriter_1_0<'a, 'top>
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
            self.allocator,
            annotations.into_annotations_vec(),
            self.encoding_buffer,
        ))
    }
}

impl<'value, 'top> ValueWriter for BinaryValueWriter_1_0<'value, 'top> {
    type ListWriter = BinaryListWriter_1_0<'value, 'top>;
    type SExpWriter = BinarySExpWriter_1_0<'value, 'top>;
    type StructWriter = BinaryStructWriter_1_0<'value, 'top>;

    delegate_value_writer_to_self!();
}

pub struct BinaryAnnotatedValueWriter_1_0<'value, 'top> {
    annotations: AnnotationsVec<'value>,
    allocator: &'top BumpAllocator,
    output_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryAnnotatedValueWriter_1_0<'value, 'top> {
    pub fn new(
        allocator: &'top BumpAllocator,
        annotations: AnnotationsVec<'value>,
        encoding_buffer: &'value mut BumpVec<'top, u8>,
    ) -> BinaryAnnotatedValueWriter_1_0<'value, 'top> {
        BinaryAnnotatedValueWriter_1_0 {
            annotations,
            allocator,
            output_buffer: encoding_buffer,
        }
    }
}

/// Takes a series of `TYPE => METHOD` pairs, generating a function for each that encodes an
/// annotations sequence and then delegates encoding the value to the corresponding value writer
/// method.
macro_rules! annotate_and_delegate_1_0 {
    // End of iteration
    () => {};
    // Recurses one argument pair at a time
    ($value_type:ty => $method:ident, $($rest:tt)*) => {
        fn $method(mut self, value: $value_type) -> IonResult<()> {
            let allocator = self.allocator;
            let mut buffer = BumpVec::new_in(allocator);
            let value_writer =
                $crate::lazy::encoder::binary::v1_0::value_writer::BinaryValueWriter_1_0::new(
                    self.allocator,
                    &mut buffer,
                );
            value_writer.$method(value)?;
            self.annotate_encoded_value(buffer.as_slice())
        }
        annotate_and_delegate_1_0!($($rest)*);
    };
}

impl BinaryAnnotatedValueWriter_1_0<'_, '_> {
    pub(crate) fn annotate_encoded_value(&mut self, encoded_value: &[u8]) -> IonResult<()> {
        if self.annotations.is_empty() {
            self.output_buffer.extend_from_slice(encoded_value);
            return Ok(());
        }

        let mut encoded_annotations_sequence = BumpVec::new_in(self.allocator);
        self.encode_annotations_sequence(&mut encoded_annotations_sequence)?;

        let mut encoded_annotations_sequence_length = BumpVec::new_in(self.allocator);
        VarUInt::write_u64(
            &mut encoded_annotations_sequence_length,
            encoded_annotations_sequence.len() as u64,
        )?;

        let total_length = encoded_annotations_sequence.len()
            + encoded_annotations_sequence_length.len()
            + encoded_value.len();

        if total_length <= MAX_INLINE_LENGTH {
            self.output_buffer.push(0xE0u8 | total_length as u8);
        } else {
            self.output_buffer.push(0xEEu8);
            VarUInt::write_u64(self.output_buffer, total_length as u64)?;
        }

        self.output_buffer
            .extend_from_slice(encoded_annotations_sequence_length.as_slice());
        self.output_buffer
            .extend_from_slice(encoded_annotations_sequence.as_slice());
        self.output_buffer.extend_from_slice(encoded_value);

        Ok(())
    }

    fn encode_annotations_sequence(&self, buffer: &'_ mut BumpVec<'_, u8>) -> IonResult<()> {
        for annotation in &self.annotations {
            let RawSymbolRef::SymbolId(sid) = annotation.as_raw_symbol_ref() else {
                return Err(IonError::Encoding(EncodingError::new(
                    "binary Ion 1.0 cannot encode text literal annotations",
                )));
            };
            VarUInt::write_u64(buffer, sid as u64)?;
        }
        Ok(())
    }
}

impl Sealed for BinaryAnnotatedValueWriter_1_0<'_, '_> {
    // No methods, precludes implementations outside the crate.
}

impl<'top> AnnotatableWriter for BinaryAnnotatedValueWriter_1_0<'_, 'top> {
    type AnnotatedValueWriter<'a>
        = BinaryAnnotatedValueWriter_1_0<'a, 'top>
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
            allocator: self.allocator,
            output_buffer: self.output_buffer,
        })
    }
}

impl<'value, 'top> ValueWriter for BinaryAnnotatedValueWriter_1_0<'value, 'top> {
    type ListWriter = BinaryListWriter_1_0<'value, 'top>;
    type SExpWriter = BinarySExpWriter_1_0<'value, 'top>;
    type StructWriter = BinaryStructWriter_1_0<'value, 'top>;

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
        BinaryListWriter_1_0::new(self.allocator, self.output_buffer)
            .with_annotations(self.annotations)
    }
    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        BinarySExpWriter_1_0::new(self.allocator, self.output_buffer)
            .with_annotations(self.annotations)
    }
    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        BinaryStructWriter_1_0::new(self.allocator, self.output_buffer)
            .with_annotations(self.annotations)
    }
}

#[cfg(test)]
mod tests {
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

    /// Writes a single value and asserts the exact bytes that follow the Ion 1.0 IVM.
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
    // `u128::MAX` is stored as a `BigInt`, but its magnitude fits in a `u128`, so it still takes
    // the stack-only path. Sixteen magnitude bytes.
    #[case::max_u128_magnitude(
        Int::from(UInt::from(u128::MAX)),
        &[
            0x2E, 0x90,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        ]
    )]
    // Just past the seam: a magnitude that exceeds `u128` and takes the cold `BigUint` path.
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
}
