use crate::lazy::decoder::LazyRawReader;
use crate::lazy::encoding::TextEncoding;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::AddContext;
use crate::result::IonFailure;
use crate::IonResult;

/// A text Ion 1.0 reader that yields [`RawStreamItem`]s representing the top level values found
/// in the provided input stream.
pub struct LazyRawTextReader<'data> {
    // The current view of the data we're reading from.
    buffer: TextBufferView<'data>,
    // Each time something is parsed from the buffer successfully, the caller will mark the number
    // of bytes that may be skipped the next time the reader advances.
    bytes_to_skip: usize,
}

impl<'data> LazyRawTextReader<'data> {
    /// Constructs a `LazyRawTextReader` positioned at the beginning of the provided input stream.
    pub fn new(data: &'data [u8]) -> LazyRawTextReader<'data> {
        Self::new_with_offset(data, 0)
    }

    /// Constructs a `LazyRawTextReader` positioned at the beginning of the provided input stream.
    /// The provided input stream is itself a slice starting `offset` bytes from the beginning
    /// of a larger data stream. This offset is used for reporting the absolute (stream-level)
    /// position of values encountered in `data`.
    fn new_with_offset(data: &'data [u8], offset: usize) -> LazyRawTextReader<'data> {
        LazyRawTextReader {
            buffer: TextBufferView::new_with_offset(data, offset),
            bytes_to_skip: 0,
        }
    }

    pub fn next<'top>(&'top mut self) -> IonResult<RawStreamItem<'data, TextEncoding>>
    where
        'data: 'top,
    {
        let buffer = self.buffer;
        if buffer.is_empty() {
            return IonResult::incomplete("reading a top-level value", buffer.offset());
        }
        let (buffer_after_whitespace, _whitespace) = buffer
            .match_optional_whitespace()
            .with_context("skipping whitespace between top-level values", buffer)?;
        let (remaining, matched) = buffer_after_whitespace
            .match_top_level()
            .with_context("reading a top-level value", buffer_after_whitespace)?;
        // If we successfully moved to the next value, store the remaining buffer view
        self.buffer = remaining;
        Ok(matched)
    }
}

impl<'data> LazyRawReader<'data, TextEncoding> for LazyRawTextReader<'data> {
    fn new(data: &'data [u8]) -> Self {
        LazyRawTextReader::new(data)
    }

    fn next<'a>(&'a mut self) -> IonResult<RawStreamItem<'data, TextEncoding>> {
        self.next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::decoder::LazyRawValue;
    use crate::IonType;

    #[test]
    fn test_top_level() -> IonResult<()> {
        let data = r#"
            null
            null.bool
            null.int
            false
            true
            500
            0x20
            0b0101
            +inf
            -inf
            nan
            3.6e0
            2.5e008
            -318e-2
        "#;
        let mut reader = LazyRawTextReader::new(data.as_bytes());

        // null
        let lazy_untyped_null = reader.next()?.expect_value()?;
        assert!(lazy_untyped_null.is_null());
        assert_eq!(lazy_untyped_null.ion_type(), IonType::Null);

        // null.bool
        let lazy_null_bool = reader.next()?.expect_value()?;
        assert!(lazy_null_bool.is_null());
        assert_eq!(lazy_null_bool.ion_type(), IonType::Bool);

        // null.int
        let lazy_null_int = reader.next()?.expect_value()?;
        assert!(lazy_null_int.is_null());
        assert_eq!(lazy_null_int.ion_type(), IonType::Int);

        // false
        let lazy_bool_false = reader.next()?.expect_value()?;
        assert!(!lazy_bool_false.is_null());
        assert_eq!(lazy_bool_false.ion_type(), IonType::Bool);
        assert!(!lazy_bool_false.read()?.expect_bool()?);

        // true
        let lazy_bool_true = reader.next()?.expect_value()?;
        assert!(!lazy_bool_true.is_null());
        assert_eq!(lazy_bool_true.ion_type(), IonType::Bool);
        assert!(lazy_bool_true.read()?.expect_bool()?);

        // 500
        let lazy_int_decimal_500 = reader.next()?.expect_value()?;
        assert!(!lazy_int_decimal_500.is_null());
        assert_eq!(lazy_int_decimal_500.ion_type(), IonType::Int);
        assert_eq!(lazy_int_decimal_500.read()?.expect_i64()?, 500);

        // 0x20
        let lazy_int_hex_20 = reader.next()?.expect_value()?;
        assert!(!lazy_int_hex_20.is_null());
        assert_eq!(lazy_int_hex_20.ion_type(), IonType::Int);
        assert_eq!(lazy_int_hex_20.read()?.expect_i64()?, 0x20); // decimal 32

        // 0b0101
        let lazy_int_binary_0101 = reader.next()?.expect_value()?;
        assert!(!lazy_int_binary_0101.is_null());
        assert_eq!(lazy_int_binary_0101.ion_type(), IonType::Int);
        assert_eq!(lazy_int_binary_0101.read()?.expect_i64()?, 0b0101); // decimal 5

        // +inf
        let lazy_float_pos_inf = reader.next()?.expect_value()?;
        assert!(!lazy_float_pos_inf.is_null());
        assert_eq!(lazy_float_pos_inf.ion_type(), IonType::Float);
        assert_eq!(lazy_float_pos_inf.read()?.expect_float()?, f64::INFINITY);

        // -inf
        let lazy_float_neg_inf = reader.next()?.expect_value()?;
        assert!(!lazy_float_neg_inf.is_null());
        assert_eq!(lazy_float_neg_inf.ion_type(), IonType::Float);
        assert_eq!(
            lazy_float_neg_inf.read()?.expect_float()?,
            f64::NEG_INFINITY
        );

        // nan
        let lazy_float_neg_inf = reader.next()?.expect_value()?;
        assert!(!lazy_float_neg_inf.is_null());
        assert_eq!(lazy_float_neg_inf.ion_type(), IonType::Float);
        assert!(lazy_float_neg_inf.read()?.expect_float()?.is_nan());

        // 3.6e0
        let lazy_float = reader.next()?.expect_value()?;
        assert!(!lazy_float.is_null());
        assert_eq!(lazy_float.ion_type(), IonType::Float);
        assert_eq!(lazy_float.read()?.expect_float()?, 3.6f64);

        // 2.5e008
        let lazy_float = reader.next()?.expect_value()?;
        assert!(!lazy_float.is_null());
        assert_eq!(lazy_float.ion_type(), IonType::Float);
        assert_eq!(lazy_float.read()?.expect_float()?, 2.5f64 * 10f64.powi(8));

        // -3.14
        let lazy_float = reader.next()?.expect_value()?;
        assert!(!lazy_float.is_null());
        assert_eq!(lazy_float.ion_type(), IonType::Float);
        assert_eq!(lazy_float.read()?.expect_float()?, -3.18);

        Ok(())
    }
}
