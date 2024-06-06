#![allow(non_camel_case_types)]

use crate::lazy::binary::raw::v1_1::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::v1_1::value::LazyRawBinaryValue_1_1;
use crate::lazy::decoder::{Decoder, LazyRawReader, RawVersionMarker};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoding::BinaryEncoding_1_1;
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem, RawStreamItem};
use crate::result::IonFailure;
use crate::{Encoding, IonResult};

use crate::lazy::any_encoding::IonEncoding;
use bumpalo::Bump as BumpAllocator;

pub struct LazyRawBinaryReader_1_1<'data> {
    data: ImmutableBuffer<'data>,
    bytes_to_skip: usize, // Bytes to skip in order to advance to the next item.
}

impl<'data> LazyRawBinaryReader_1_1<'data> {
    fn new(data: &'data [u8]) -> Self {
        Self::new_with_offset(data, 0)
    }

    fn new_with_offset(data: &'data [u8], offset: usize) -> Self {
        let data = ImmutableBuffer::new_with_offset(data, offset);
        Self {
            data,
            bytes_to_skip: 0,
        }
    }

    fn read_ivm<'top>(
        &mut self,
        buffer: ImmutableBuffer<'data>,
    ) -> IonResult<LazyRawStreamItem<'top, BinaryEncoding_1_1>>
    where
        'data: 'top,
    {
        let (marker, _buffer_after_ivm) = buffer.read_ivm()?;
        let (major, minor) = marker.version();
        if (major, minor) != (1, 1) {
            return IonResult::decoding_error(format!(
                "unsupported version of Ion: v{major}.{minor}; only 1.1 is supported by this reader",
            ));
        }
        self.data = buffer;
        self.bytes_to_skip = 4;
        Ok(LazyRawStreamItem::<BinaryEncoding_1_1>::VersionMarker(
            marker,
        ))
    }

    fn read_value<'top>(
        &mut self,
        buffer: ImmutableBuffer<'data>,
    ) -> IonResult<LazyRawStreamItem<'top, BinaryEncoding_1_1>>
    where
        'data: 'top,
    {
        let lazy_value = match ImmutableBuffer::peek_sequence_value(buffer)? {
            Some(lazy_value) => lazy_value,
            None => {
                return Ok(LazyRawStreamItem::<BinaryEncoding_1_1>::EndOfStream(
                    EndPosition::new(BinaryEncoding_1_1.encoding(), self.position()),
                ))
            }
        };
        self.data = buffer;
        self.bytes_to_skip = lazy_value.encoded_value.total_length();
        Ok(RawStreamItem::Value(lazy_value))
    }

    fn advance_to_next_item(&self) -> IonResult<ImmutableBuffer<'data>> {
        if self.data.len() < self.bytes_to_skip {
            return IonResult::incomplete(
                "cannot advance to next item, insufficient data in buffer",
                self.data.offset(),
            );
        }

        if self.bytes_to_skip > 0 {
            Ok(self.data.consume(self.bytes_to_skip))
        } else {
            Ok(self.data)
        }
    }

    pub fn next<'top>(&'top mut self) -> IonResult<LazyRawStreamItem<'top, BinaryEncoding_1_1>>
    where
        'data: 'top,
    {
        let mut buffer = self.advance_to_next_item()?;
        if buffer.is_empty() {
            return Ok(LazyRawStreamItem::<BinaryEncoding_1_1>::EndOfStream(
                EndPosition::new(BinaryEncoding_1_1.encoding(), buffer.offset()),
            ));
        }

        let type_descriptor = buffer.peek_opcode()?;
        if type_descriptor.is_nop() {
            (_, buffer) = buffer.consume_nop_padding(type_descriptor)?;
            if buffer.is_empty() {
                return Ok(LazyRawStreamItem::<BinaryEncoding_1_1>::EndOfStream(
                    EndPosition::new(BinaryEncoding_1_1.encoding(), buffer.offset()),
                ));
            }
        }
        if type_descriptor.is_ivm_start() {
            return self.read_ivm(buffer);
        }
        self.read_value(buffer)
    }

    /// Runs the provided parsing function on this reader's buffer.
    /// If it succeeds, marks the reader  as ready to advance by the 'n' bytes
    /// that were consumed.
    /// If it does not succeed, the `DataSource` remains unchanged.
    pub(crate) fn try_parse_next<
        F: Fn(ImmutableBuffer) -> IonResult<Option<LazyRawBinaryValue_1_1<'data>>>,
    >(
        &mut self,
        parser: F,
    ) -> IonResult<Option<LazyRawBinaryValue_1_1<'data>>> {
        let buffer = self.advance_to_next_item()?;

        let lazy_value = match parser(buffer) {
            Ok(Some(output)) => output,
            Ok(None) => return Ok(None),
            Err(e) => return Err(e),
        };

        // If the value we read doesn't start where we began reading, there was a NOP.
        // let num_nop_bytes = lazy_value.input.offset() - buffer.offset();
        self.bytes_to_skip = lazy_value.encoded_value.total_length();
        Ok(Some(lazy_value))
    }
}

impl<'data> Sealed for LazyRawBinaryReader_1_1<'data> {}

impl<'data> LazyRawReader<'data, BinaryEncoding_1_1> for LazyRawBinaryReader_1_1<'data> {
    fn new(data: &'data [u8]) -> Self {
        Self::new(data)
    }

    fn next<'top>(
        &'top mut self,
        _allocator: &'top BumpAllocator,
    ) -> IonResult<LazyRawStreamItem<'top, BinaryEncoding_1_1>>
    where
        'data: 'top,
    {
        self.next()
    }

    fn resume_at_offset(
        data: &'data [u8],
        offset: usize,
        _saved_state: <BinaryEncoding_1_1 as Decoder>::ReaderSavedState,
    ) -> Self {
        Self::new_with_offset(data, offset)
    }

    fn position(&self) -> usize {
        self.data.offset() + self.bytes_to_skip
    }

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Binary_1_1
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::raw::v1_1::reader::LazyRawBinaryReader_1_1;
    use crate::raw_symbol_ref::RawSymbolRef;
    use crate::{IonResult, IonType};
    use rstest::*;

    #[test]
    fn nop() -> IonResult<()> {
        let data: Vec<u8> = vec![
            0xE0, 0x01, 0x01, 0xEA, // IVM
            0xEC, // 1-Byte NOP
            0xEC, 0xEC, // 2-Byte NOP
            0xEC, 0xEC, 0xEC, // 3-Byte Nop
            0xED, 0x05, 0x00, 0x00, // 4-Byte NOP
            0xEA, // null.null
        ];

        let mut reader = LazyRawBinaryReader_1_1::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_null()?,
            IonType::Null
        );

        Ok(())
    }

    #[test]
    fn bools() -> IonResult<()> {
        let data: Vec<u8> = vec![
            0xE0, 0x01, 0x01, 0xEA, // IVM
            0x6E, // true
            0x6F, // false
        ];

        let mut reader = LazyRawBinaryReader_1_1::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        assert!(reader.next()?.expect_value()?.read()?.expect_bool()?);

        assert!(!(reader.next()?.expect_value()?.read()?.expect_bool()?));

        Ok(())
    }

    #[test]
    fn integers() -> IonResult<()> {
        #[rustfmt::skip]
        let data: Vec<u8> = vec![
            // IVM
            0xE0, 0x01, 0x01, 0xEA,

            // Integer: 0
            0x60,

            // Integer: 17
            0x61, 0x11,

            // Integer: -944
            0x62, 0x50, 0xFC,

            // Integer: 1
            0xF6, 0x03, 0x01,

            // Integer: 147573952589676412929
            0xF6, 0x13, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08,
        ];

        let mut reader = LazyRawBinaryReader_1_1::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_int()?,
            0.into()
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_int()?,
            17.into()
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_int()?,
            (-944).into()
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_int()?,
            1.into()
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_int()?,
            147573952589676412929i128.into()
        );
        Ok(())
    }

    #[test]
    fn strings() -> IonResult<()> {
        #[rustfmt::skip]
        let data: Vec<u8> = vec![
            // IVM
            0xe0, 0x01, 0x01, 0xea,

            // String: ""
            0x90,

            // String: "hello"
            0x95, 0x68, 0x65, 0x6c, 0x6c, 0x6f,

            // String: "fourteen bytes"
            0x9E, 0x66, 0x6F, 0x75, 0x72, 0x74, 0x65, 0x65, 0x6E, 0x20, 0x62, 0x79, 0x74, 0x65,
            0x73,

            // String: "variable length encoding"
            0xF9, 0x31, 0x76, 0x61, 0x72, 0x69, 0x61, 0x62, 0x6C, 0x65, 0x20, 0x6C, 0x65,
            0x6E, 0x67, 0x74, 0x68, 0x20, 0x65, 0x6E, 0x63, 0x6f, 0x64, 0x69, 0x6E, 0x67,
        ];

        let mut reader = LazyRawBinaryReader_1_1::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        assert_eq!(reader.next()?.expect_value()?.read()?.expect_string()?, "");

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_string()?,
            "hello"
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_string()?,
            "fourteen bytes"
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_string()?,
            "variable length encoding"
        );

        Ok(())
    }

    #[test]
    fn symbols() -> IonResult<()> {
        #[rustfmt::skip]
        let data: Vec<u8> = vec![
            // IVM
            0xE0, 0x01, 0x01, 0xEA,

            // Symbol: ''
            0xA0,

            // Symbol: 'fourteen bytes'
            0xAE, 0x66, 0x6F, 0x75, 0x72, 0x74, 0x65, 0x65, 0x6E, 0x20, 0x62, 0x79, 0x74, 0x65,
            0x73,

            // Symbol: 'variable length encoding'
            0xFA, 0x31, 0x76, 0x61, 0x72, 0x69, 0x61, 0x62, 0x6C, 0x65, 0x20, 0x6C, 0x65, 0x6E,
            0x67, 0x74, 0x68, 0x20, 0x65, 0x6E, 0x63, 0x6f, 0x64, 0x69, 0x6E, 0x67,

            // Symbol ID: 1
            0xE1, 0x01,

            // Symbol ID: 257
            0xE2, 0x01, 0x00,

            // Symbol ID: 65,793
            0xE3, 0x01, 0x00, 0x00,
        ];

        let mut reader = LazyRawBinaryReader_1_1::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_symbol()?,
            "".into()
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_symbol()?,
            "fourteen bytes".into()
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_symbol()?,
            "variable length encoding".into()
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_symbol()?,
            RawSymbolRef::SymbolId(1)
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_symbol()?,
            RawSymbolRef::SymbolId(257)
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_symbol()?,
            RawSymbolRef::SymbolId(65793)
        );

        Ok(())
    }

    #[test]
    #[allow(clippy::approx_constant)]
    fn floats() -> IonResult<()> {
        #[rustfmt::skip]
        let data: Vec<u8> = vec![
            // IVM
            0xe0, 0x01, 0x01, 0xea,
            // 0e0
            0x6A,

            // 3.14 (half-precision)
            // 0x6B, 0x42, 0x47,

            // 3.1415927 (single-precision)
            0x6C, 0xdb, 0x0F, 0x49, 0x40,

            // 3.141592653589793 (double-precision)
            0x6D, 0x18, 0x2D, 0x44, 0x54, 0xFB, 0x21, 0x09, 0x40,
        ];

        let mut reader = LazyRawBinaryReader_1_1::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        assert_eq!(reader.next()?.expect_value()?.read()?.expect_float()?, 0.0);

        // TODO: Implement Half-precision.
        // assert_eq!(reader.next()?.expect_value()?.read()?.expect_float()?, 3.14);

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_float()? as f32,
            3.1415927f32,
        );

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_float()?,
            std::f64::consts::PI,
        );

        Ok(())
    }

    #[rstest]
    #[case("0.", &[0x70])]
    #[case("0d1", &[0x71, 0x03])]
    #[case("0d63", &[0x71, 0x7F])]
    #[case("0d64", &[0x72, 0x02, 0x01])]
    #[case("0d99", &[0x72, 0x8E, 0x01])]
    #[case("0.0", &[0x71, 0xFF])]
    #[case("0.00", &[0x71, 0xFD])]
    #[case("0.000", &[0x71, 0xFB])]
    #[case("0d-64", &[0x71, 0x81])]
    #[case("0d-99", &[0x72, 0x76, 0xFE])]
    #[case("-0.", &[0x72, 0x01, 0x00])]
    #[case("-0d1", &[0x72, 0x03, 0x00])]
    #[case("-0d3", &[0x72, 0x07, 0x00])]
    #[case("-0d63", &[0x72, 0x7F, 0x00])]
    #[case("-0d199", &[0x73, 0x1E, 0x03, 0x00])]
    #[case("-0d-1", &[0x72, 0xFF, 0x00])]
    #[case("-0d-2", &[0x72, 0xFD, 0x00])]
    #[case("-0d-3", &[0x72, 0xFB, 0x00])]
    #[case("-0d-63", &[0x72, 0x83, 0x00])]
    #[case("-0d-64", &[0x72, 0x81, 0x00])]
    #[case("-0d-65", &[0x73, 0xFE, 0xFE, 0x00])]
    #[case("-0d-199", &[0x73, 0xE6, 0xFC, 0x00])]
    #[case("0.01", &[0x72, 0xFD, 0x01])]
    #[case("0.1", &[0x72, 0xFF, 0x01])]
    #[case("1d0", &[0x72, 0x01, 0x01])]
    #[case("1d1", &[0x72, 0x03, 0x01])]
    #[case("1d2", &[0x72, 0x05, 0x01])]
    #[case("1d63", &[0x72, 0x7F, 0x01])]
    #[case("1d64", &[0x73, 0x02, 0x01, 0x01])]
    #[case("1d65536", &[0x74, 0x04, 0x00, 0x08, 0x01])]
    #[case("2.", &[0x72, 0x01, 0x02])]
    #[case("7.", &[0x72, 0x01, 0x07])]
    #[case("14d0", &[0x72, 0x01, 0x0E])]
    #[case("14d0", &[0x73, 0x02, 0x00, 0x0E])] // overpadded exponent
    #[case("14d0", &[0x74, 0x01, 0x0E, 0x00, 0x00])] // Overpadded coefficient
    #[case("14d0", &[0x75, 0x02, 0x00, 0x0E, 0x00, 0x00])] // Overpadded coefficient and exponent
    #[case("1.0", &[0x72, 0xFF, 0x0A])]
    #[case("1.00", &[0x72, 0xFD, 0x64])]
    #[case("1.27", &[0x72, 0xFD, 0x7F])]
    #[case("1.28", &[0x73, 0xFD, 0x80, 0x00])]
    #[case("3.142", &[0x73, 0xFB, 0x46, 0x0C])]
    #[case("3.14159", &[0x74, 0xF7, 0x2F, 0xCB, 0x04])]
    #[case("3.1415927", &[0x75, 0xF3, 0x77, 0x5E, 0xDF, 0x01])]
    #[case("3.141592653", &[0x76, 0xEF, 0x4D, 0xE6, 0x40, 0xBB, 0x00])]
    #[case("3.141592653590", &[0x77, 0xE9, 0x16, 0x9F, 0x83, 0x75, 0xDB, 0x02])]
    #[case("3.14159265358979323", &[0x79, 0xDF, 0xFB, 0xA0, 0x9E, 0xF6, 0x2F, 0x1E, 0x5C, 0x04])]
    #[case("3.1415926535897932384626", &[0x7B, 0xD5, 0x72, 0x49, 0x64, 0xCC, 0xAF, 0xEF, 0x8F, 0x0F, 0xA7, 0x06])]
    #[case("3.141592653589793238462643383", &[0x7D, 0xCB, 0xB7, 0x3C, 0x92, 0x86, 0x40, 0x9F, 0x1B, 0x01, 0x1F, 0xAA, 0x26, 0x0A])]
    #[case("3.14159265358979323846264338327950", &[0x7F, 0xC1, 0x8E, 0x29, 0xE5, 0xE3, 0x56, 0xD5, 0xDF, 0xC5, 0x10, 0x8F, 0x55, 0x3F, 0x7D, 0x0F])]
    #[case("3.141592653589793238462643383279503", &[0xF7, 0x21, 0xBF, 0x8F, 0x9F, 0xF3, 0xE6, 0x64, 0x55, 0xBE, 0xBA, 0xA7, 0x96, 0x57, 0x79, 0xE4, 0x9A, 0x00])]
    fn decimals(#[case] expected_txt: &str, #[case] ion_data: &[u8]) -> IonResult<()> {
        use crate::lazy::decoder::{LazyRawReader, LazyRawValue};
        use crate::lazy::text::raw::v1_1::reader::LazyRawTextReader_1_1;
        let bump = bumpalo::Bump::new();

        let mut reader_txt = LazyRawTextReader_1_1::new(expected_txt.as_bytes());
        let mut reader_bin = LazyRawBinaryReader_1_1::new(ion_data);

        assert_eq!(
            reader_bin
                .next()?
                .expect_value()?
                .read()?
                .expect_decimal()?,
            reader_txt
                .next(&bump)?
                .expect_value()?
                .read()?
                .expect_decimal()?,
        );
        Ok(())
    }

    #[rstest]
    #[case("0.", &[0xF7, 0x01])]
    #[case("0d99", &[0xF7, 0x05, 0x8E, 0x01])]
    #[case("0.0", &[0xF7, 0x03, 0xFF])]
    #[case("0.00", &[0xF7, 0x03, 0xFD])]
    #[case("0d-99", &[0xF7, 0x05, 0x76, 0xFE])]
    #[case("-0.", &[0xF7, 0x05, 0x01, 0x00])]
    #[case("-0d199", &[0xF7, 0x07, 0x1E, 0x03, 0x00])]
    #[case("-0d-1", &[0xF7, 0x05, 0xFF, 0x00])]
    #[case("-0d-65", &[0xF7, 0x07, 0xFE, 0xFE, 0x00])]
    #[case("0.01", &[0xF7, 0x05, 0xFD, 0x01])]
    #[case("1.", &[0xF7, 0x05, 0x01, 0x01])]
    #[case("1d65536", &[0xF7, 0x09, 0x04, 0x00, 0x08, 0x01])]
    #[case("1.0", &[0xF7, 0x05, 0xFF, 0x0A])]
    #[case("1.28", &[0xF7, 0x07, 0xFD, 0x80, 0x00])]
    #[case("3.141592653590", &[0xF7, 0x0F, 0xE9, 0x16, 0x9F, 0x83, 0x75, 0xDB, 0x02])]
    #[case("3.14159265358979323", &[0xF7, 0x13, 0xDF, 0xFB, 0xA0, 0x9E, 0xF6, 0x2F, 0x1E, 0x5C, 0x04])]
    #[case("3.1415926535897932384626", &[0xF7, 0x17, 0xD5, 0x72, 0x49, 0x64, 0xCC, 0xAF, 0xEF, 0x8F, 0x0F, 0xA7, 0x06])]
    #[case("3.141592653589793238462643383", &[0xF7, 0x1B, 0xCB, 0xB7, 0x3C, 0x92, 0x86, 0x40, 0x9F, 0x1B, 0x01, 0x1F, 0xAA, 0x26, 0x0A])]
    #[case("3.14159265358979323846264338327950", &[0xF7, 0x1F, 0xC1, 0x8E, 0x29, 0xE5, 0xE3, 0x56, 0xD5, 0xDF, 0xC5, 0x10, 0x8F, 0x55, 0x3F, 0x7D, 0x0F])]
    fn decimals_long(#[case] expected_txt: &str, #[case] ion_data: &[u8]) -> IonResult<()> {
        use crate::ion_data::IonEq;
        use crate::lazy::decoder::{LazyRawReader, LazyRawValue};
        use crate::lazy::text::raw::v1_1::reader::LazyRawTextReader_1_1;
        let bump = bumpalo::Bump::new();

        let mut reader_txt = LazyRawTextReader_1_1::new(expected_txt.as_bytes());
        let mut reader_bin = LazyRawBinaryReader_1_1::new(ion_data);

        let expected_value = reader_txt.next(&bump)?.expect_value()?.read()?;
        let actual_value = reader_bin.next()?.expect_value()?.read()?;

        assert!(actual_value
            .expect_decimal()?
            .ion_eq(&expected_value.expect_decimal()?));

        Ok(())
    }

    #[rstest]
    #[case("2024T",                               &[0x80, 0x36])]
    #[case("2023-10T",                            &[0x81, 0x35, 0x05])]
    #[case("2023-10-15T",                         &[0x82, 0x35, 0x7D])]
    #[case("2023-10-15T05:04Z",                   &[0x83, 0x35, 0x7D, 0x85, 0x08])]
    #[case("2023-10-15T05:04:03Z",                &[0x84, 0x35, 0x7D, 0x85, 0x38, 0x00])]
    #[case("2023-10-15T05:04:03.123-00:00",       &[0x85, 0x35, 0x7D, 0x85, 0x30, 0xEC, 0x01])]
    #[case("2023-10-15T05:04:03.000123-00:00",    &[0x86, 0x35, 0x7D, 0x85, 0x30, 0xEC, 0x01, 0x00])]
    #[case("2023-10-15T05:04:03.000000123-00:00", &[0x87, 0x35, 0x7D, 0x85, 0x30, 0xEC, 0x01, 0x00, 0x00])]
    #[case("2023-10-15T05:04+01:00",              &[0x88, 0x35, 0x7D, 0x85, 0x20, 0x00])]
    #[case("2023-10-15T05:04-01:00",              &[0x88, 0x35, 0x7D, 0x85, 0xE0, 0x03])]
    #[case("2023-10-15T05:04:03+01:00",           &[0x89, 0x35, 0x7D, 0x85, 0x20, 0x0C])]
    #[case("2023-10-15T05:04:03.123+01:00",       &[0x8A, 0x35, 0x7D, 0x85, 0x20, 0x0C, 0x7B, 0x00])]
    #[case("2023-10-15T05:04:03.000123+01:00",    &[0x8B, 0x35, 0x7D, 0x85, 0x20, 0x0C, 0x7B, 0x00, 0x00])]
    #[case("2023-10-15T05:04:03.000000123+01:00", &[0x8C, 0x35, 0x7D, 0x85, 0x20, 0x0C, 0x7B, 0x00, 0x00, 0x00])]
    fn timestamps_short(#[case] expected_txt: &str, #[case] ion_data: &[u8]) -> IonResult<()> {
        use crate::lazy::decoder::{LazyRawReader, LazyRawValue};
        use crate::lazy::text::raw::v1_1::reader::LazyRawTextReader_1_1;

        let bump = bumpalo::Bump::new();
        let mut reader_txt = LazyRawTextReader_1_1::new(expected_txt.as_bytes());
        let mut reader_bin = LazyRawBinaryReader_1_1::new(ion_data);

        assert_eq!(
            reader_bin
                .next()?
                .expect_value()?
                .read()?
                .expect_timestamp()?,
            reader_txt
                .next(&bump)?
                .expect_value()?
                .read()?
                .expect_timestamp()?,
        );

        Ok(())
    }

    #[rstest]
    #[case("1947T",                         &[0xF8, 0x05, 0x9B, 0x07])]
    #[case("1947-12T",                      &[0xF8, 0x07, 0x9B, 0x07, 0x03])]
    #[case("1947-12-23T",                   &[0xF8, 0x07, 0x9B, 0x07, 0x5F])]
    #[case("1947-12-23T11:22-00:00",        &[0xF8, 0x0D, 0x9B, 0x07, 0xDF, 0x65, 0xFD, 0x3F])]
    #[case("1947-12-23T11:22:33+01:00",     &[0xF8, 0x0F, 0x9B, 0x07, 0xDF, 0x65, 0x71, 0x57, 0x08])]
    #[case("1947-12-23T11:22:33.127+01:15", &[0xF8, 0x13, 0x9B, 0x07, 0xDF, 0x65, 0xAD, 0x57, 0x08, 0x07, 0x7F])]
    #[case("1947-12-23T11:22:33-01:00",     &[0xF8, 0x0F, 0x9B, 0x07, 0xDF, 0x65, 0x91, 0x55, 0x08])]
    fn timestamps_long(#[case] expected_txt: &str, #[case] ion_data: &[u8]) -> IonResult<()> {
        use crate::lazy::decoder::{LazyRawReader, LazyRawValue};
        use crate::lazy::text::raw::v1_1::reader::LazyRawTextReader_1_1;

        let bump = bumpalo::Bump::new();
        let mut reader_txt = LazyRawTextReader_1_1::new(expected_txt.as_bytes());
        let mut reader_bin = LazyRawBinaryReader_1_1::new(ion_data);

        assert_eq!(
            reader_bin
                .next()?
                .expect_value()?
                .read()?
                .expect_timestamp()?,
            reader_txt
                .next(&bump)?
                .expect_value()?
                .read()?
                .expect_timestamp()?,
        );

        Ok(())
    }

    fn blobs() -> IonResult<()> {
        let data: Vec<u8> = vec![
            0xe0, 0x01, 0x01, 0xea, // IVM
            0xFE, 0x31, 0x49, 0x20, 0x61, 0x70, 0x70, 0x6c, 0x61, 0x75, 0x64, 0x20, 0x79, 0x6f,
            0x75, 0x72, 0x20, 0x63, 0x75, 0x72, 0x69, 0x6f, 0x73, 0x69, 0x74, 0x79,
        ];

        let mut reader = LazyRawBinaryReader_1_1::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        let bytes: &[u8] = &[
            0x49, 0x20, 0x61, 0x70, 0x70, 0x6c, 0x61, 0x75, 0x64, 0x20, 0x79, 0x6f, 0x75, 0x72,
            0x20, 0x63, 0x75, 0x72, 0x69, 0x6f, 0x73, 0x69, 0x74, 0x79,
        ];
        assert_eq!(reader.next()?.expect_value()?.read()?.expect_blob()?, bytes);

        Ok(())
    }

    #[test]
    fn clobs() -> IonResult<()> {
        let data: Vec<u8> = vec![
            0xe0, 0x01, 0x01, 0xea, // IVM
            0xFF, 0x31, 0x49, 0x20, 0x61, 0x70, 0x70, 0x6c, 0x61, 0x75, 0x64, 0x20, 0x79, 0x6f,
            0x75, 0x72, 0x20, 0x63, 0x75, 0x72, 0x69, 0x6f, 0x73, 0x69, 0x74, 0x79,
        ];

        let mut reader = LazyRawBinaryReader_1_1::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        let bytes: &[u8] = &[
            0x49, 0x20, 0x61, 0x70, 0x70, 0x6c, 0x61, 0x75, 0x64, 0x20, 0x79, 0x6f, 0x75, 0x72,
            0x20, 0x63, 0x75, 0x72, 0x69, 0x6f, 0x73, 0x69, 0x74, 0x79,
        ];

        assert_eq!(reader.next()?.expect_value()?.read()?.expect_clob()?, bytes);

        Ok(())
    }

    #[test]
    fn lists() -> IonResult<()> {
        use crate::lazy::decoder::LazyRawSequence;

        #[rustfmt::skip]
        let tests: &[(&[u8], &[IonType])] = &[
            // []
            (&[0xB0], &[]),

            // [null.null]
            (&[0xB1, 0xEA], &[IonType::Null]),

            // ['']
            (&[0xB1, 0xA0], &[IonType::Symbol]),

            // ["hello"]
            (
                &[0xB6, 0x95, 0x68, 0x65, 0x6C, 0x6C, 0x6F],
                &[IonType::String],
            ),

            // [null.null, '', "hello"]
            (
                &[0xB8, 0xEA, 0xA0, 0x95, 0x68, 0x65, 0x6C, 0x6c, 0x6F],
                &[IonType::Null, IonType::Symbol, IonType::String],
            ),

            // [3.1415927e0 3.1415927e0]
            (
                &[0xBA, 0x6C, 0xDB, 0x0F, 0x49, 0x40, 0x6C, 0xDB, 0x0F, 0x49, 0x40],
                &[IonType::Float, IonType::Float]
            ),

            // Long List Encoding

            // []
            (&[0xFB, 0x01], &[]),

            // ["variable length list"]
            (
                &[
                    0xFB, 0x2D, 0xF9, 0x29, 0x76, 0x61, 0x72, 0x69, 0x61, 0x62, 0x6C, 0x65,
                    0x20, 0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x20, 0x6C, 0x69, 0x73, 0x74,
                ],
                &[IonType::String]
            ),

            // [<nop>]
            (&[0xFB, 0x03, 0xEC], &[]),
        ];

        for (ion_data, expected_types) in tests {
            let mut reader = LazyRawBinaryReader_1_1::new(ion_data);
            let container = reader.next()?.expect_value()?.read()?.expect_list()?;
            let mut count = 0;
            for (actual_lazy_value, expected_type) in container.iter().zip(expected_types.iter()) {
                let value = actual_lazy_value?.expect_value()?;
                assert_eq!(value.ion_type(), *expected_type);
                count += 1;
            }
            assert_eq!(count, expected_types.len());
        }

        Ok(())
    }

    #[test]
    fn sexp() -> IonResult<()> {
        use crate::lazy::decoder::LazyRawSequence;

        #[rustfmt::skip]
        let tests: &[(&[u8], &[IonType])] = &[
            // ()
            (&[0xC0], &[]),

            // (1 2 3)
            (
                &[0xC6, 0x61, 0x01, 0x61, 0x02, 0x61, 0x03],
                &[IonType::Int, IonType::Int, IonType::Int],
            ),

            // Long S-Expression Encoding

            // ()
            (&[0xFC, 0x01], &[]),

            // ("variable length sexp")
            (
                &[
                    0xFC, 0x2D, 0xF9, 0x29, 0x76, 0x61, 0x72, 0x69, 0x61, 0x62, 0x6C, 0x65, 0x20,
                    0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x20, 0x73, 0x65, 0x78, 0x70
                ],
                &[IonType::String]
            ),

            // ( () () [] )
            (&[0xFC, 0x09, 0xFC, 0x01, 0xC0, 0xB0], &[IonType::SExp, IonType::SExp, IonType::List]),

            // ( $257 )
            (&[0xFC, 0x07, 0xE2, 0x01, 0x00], &[IonType::Symbol]),
        ];

        for (ion_data, expected_types) in tests {
            let mut reader = LazyRawBinaryReader_1_1::new(ion_data);
            let container = reader.next()?.expect_value()?.read()?.expect_sexp()?;
            let mut count = 0;
            for (actual_lazy_value, expected_type) in container.iter().zip(expected_types.iter()) {
                let value = actual_lazy_value?.expect_value()?;
                assert_eq!(value.ion_type(), *expected_type);
                count += 1;
            }
            assert_eq!(count, expected_types.len());
        }

        Ok(())
    }

    #[test]
    fn nulls() -> IonResult<()> {
        #[rustfmt::skip]
        let data: Vec<([u8; 2], IonType)> = vec![
            ([0xEB, 0x00], IonType::Bool),      // null.bool
            ([0xEB, 0x01], IonType::Int),       // null.int
            ([0xEB, 0x02], IonType::Float),     // null.float
            ([0xEB, 0x03], IonType::Decimal),   // null.decimal
            ([0xEB, 0x04], IonType::Timestamp), // null.timestamp
            ([0xEB, 0x05], IonType::String),    // null.string
            ([0xEB, 0x06], IonType::Symbol),    // null.symbol
            ([0xEB, 0x07], IonType::Blob),      // null.blob
            ([0xEB, 0x08], IonType::Clob),      // null.clob
            ([0xEB, 0x09], IonType::List),      // null.list
            ([0xEB, 0x0A], IonType::SExp),      // null.sexp
            ([0xEB, 0x0B], IonType::Struct),    // null.struct
        ];

        for (data, expected_type) in data {
            let mut reader = LazyRawBinaryReader_1_1::new(&data);
            let actual_type = reader.next()?.expect_value()?.read()?.expect_null()?;
            assert_eq!(actual_type, expected_type);
        }
        Ok(())
    }

    fn structs() -> IonResult<()> {
        use crate::lazy::decoder::{LazyRawFieldExpr, LazyRawFieldName};

        #[rustfmt::skip]
        #[allow(clippy::type_complexity)]
        let tests: &[(&[u8], &[(RawSymbolRef, IonType)])] = &[
            // Symbol Address
            (
                // {}
                &[0xD0],
                &[],
            ),
            (
                // { $10: 1, $11: 2 }
                &[0xD6, 0x15, 0x61, 0x01, 0x17, 0x61, 0x02],
                &[
                    (10usize.into(), IonType::Int),
                    (11usize.into(), IonType::Int),
                ]
            ),
            (
                // { $10: '', $11: 0e0 }
                &[0xD4, 0x15, 0xA0, 0x17, 0x6A],
                &[
                    (10usize.into(), IonType::Symbol),
                    (11usize.into(), IonType::Float),
                ],
            ),
            (
                // { $10: <NOP>, $11: 0e0 } - with nops, skip the NOP'd fields.
                &[ 0xD4, 0x15, 0xEC, 0x17, 0x6A ],
                &[
                    (11usize.into(), IonType::Float),
                ],
            ),
            (
                // { $10: 1, $11: <NOP> } - with nops at end of struct.
                &[ 0xD5, 0x15, 0x61, 0x01, 0x17, 0xEC ],
                &[
                    (10usize.into(), IonType::Int),
                ],
            ),
            (
                // { $10: { $11: "foo" }, $11: 2 }
                &[ 0xD6, 0x15, 0xC4, 0x93, 0x66, 0x6F, 0x6F, 0x17, 0x61, 0x02 ],
                &[
                    (10usize.into(), IonType::Struct),
                    (11usize.into(), IonType::Int),
                ],
            ),
            (
                // {}
                &[ 0xFD, 0x01 ],
                &[],
            ),
            (
                // { $10: "variable length struct" }
                &[
                    0xFD, 0x33, 0x15, 0xF9, 0x2D, 0x76, 0x61, 0x72, 0x69, 0x61,
                    0x62, 0x6C, 0x65, 0x20, 0x6c, 0x65, 0x6E, 0x67, 0x74, 0x68,
                    0x20, 0x73, 0x74, 0x72, 0x75, 0x63, 0x74
                ],
                &[ (10usize.into(), IonType::String) ],
            ),
            // FlexSym
            (
                // { "foo": 1, $11: 2 }
                &[ 0xD9, 0xFB, 0x66, 0x6F, 0x6F, 0x61, 0x01, 0x17, 0x61, 0x02],
                &[ ("foo".into(), IonType::Int), (11usize.into(), IonType::Int)],
            ),
            (
                // { "foo": 1, $11: 2 }
                &[ 0xFD, 0x13, 0xFB, 0x66, 0x6F, 0x6F, 0x61, 0x01, 0x17, 0x61, 0x02],
                &[ ("foo".into(), IonType::Int), (11usize.into(), IonType::Int)],
            ),
            (
                // { "foo": <NOP>, $11: 2 }
                &[ 0xFD, 0x11, 0xFB, 0x66, 0x6F, 0x6F, 0xEC, 0x17, 0x61, 0x02],
                &[ (11usize.into(), IonType::Int) ],
            ),
            (
                // { "foo": 2, $11: <NOP> }
                &[ 0xFD, 0x11, 0xFB, 0x66, 0x6F, 0x6F, 0x61, 0x02, 0x17, 0xEC],
                &[ ("foo".into(), IonType::Int) ],
            ),
            (
                // { "foo": { $10: 2 }, "bar": 2 }
                &[
                    0xFD, 0x1D, 0xFB, 0x66, 0x6F, 0x6F, 0xD3, 0x15, 0x61, 0x02,
                    0xFB, 0x62, 0x61, 0x72, 0x61, 0x02,
                ],
                &[
                    ("foo".into(), IonType::Struct),
                    ("bar".into(), IonType::Int),
                ],
            ),
            (
                // {}
                &[0xFD, 0x01],
                &[],
            )
        ];

        for (ion_data, field_pairs) in tests {
            let mut reader = LazyRawBinaryReader_1_1::new(ion_data);
            let actual_data = reader.next()?.expect_value()?.read()?.expect_struct()?;

            for (actual_field, expected_field) in actual_data.iter().zip(field_pairs.iter()) {
                let (expected_name, expected_value_type) = expected_field;
                match actual_field {
                    Ok(LazyRawFieldExpr::NameValue(name, value)) => {
                        assert_eq!(name.read()?, *expected_name);
                        assert_eq!(value.ion_type(), *expected_value_type);
                    }
                    other => panic!("unexpected value for field: {:?}", other),
                }
            }
        }
        Ok(())
    }
}
