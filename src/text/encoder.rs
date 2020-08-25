use crate::result::IonResult;
use crate::IonType;
use bigdecimal::BigDecimal;
use chrono::{DateTime, FixedOffset};
use std::io;

/// Utility type for writing scalar Rust values as Ion text.
pub struct TextEncoder {}

impl TextEncoder {
    #[inline(always)]
    fn null_text(ion_type: IonType) -> &'static str {
        use IonType::*;
        match ion_type {
            Null => "null",
            Boolean => "null.bool",
            Integer => "null.int",
            Float => "null.float",
            Decimal => "null.decimal",
            Timestamp => "null.timestamp",
            Symbol => "null.symbol",
            String => "null.string",
            Blob => "null.blob",
            Clob => "null.clob",
            List => "null.list",
            SExpression => "null.sexp",
            Struct => "null.struct",
        }
    }

    #[inline(always)]
    fn bool_text(value: bool) -> &'static str {
        match value {
            true => "true",
            false => "false",
        }
    }

    /// Writes a null of the specified Ion type to `output`.
    pub fn encode_null<W: io::Write>(output: &mut W, ion_type: IonType) -> IonResult<()> {
        write!(output, "{}", TextEncoder::null_text(ion_type))?;
        Ok(())
    }

    /// Writes a bool value to `output` as an Ion boolean.
    pub fn encode_bool<W: io::Write>(output: &mut W, value: bool) -> IonResult<()> {
        write!(output, "{}", TextEncoder::bool_text(value))?;
        Ok(())
    }

    /// Writes an i64 value to `output` as an Ion integer.
    pub fn encode_i64<W: io::Write>(output: &mut W, value: i64) -> IonResult<()> {
        write!(output, "{}", value)?;
        Ok(())
    }

    /// Writes a BigDecimal value to `output` as an Ion decimal.
    pub fn encode_big_decimal<W: io::Write>(output: &mut W, value: &BigDecimal) -> IonResult<()> {
        write!(output, "{}", &value)?;
        Ok(())
    }

    /// Writes an f64 value to `output` as an Ion float.
    pub fn encode_f64<W: io::Write>(output: &mut W, value: f64) -> IonResult<()> {
        if value.is_nan() {
            write!(output, "nan")?;
            return Ok(());
        }

        if value.is_infinite() {
            if value.is_sign_positive() {
                write!(output, "+inf")?;
            } else {
                write!(output, "-inf")?;
            }
            return Ok(());
        }

        // The {:e} formatter provided by the Display trait writes floats using scientific
        // notation. It works for all floating point values except -0.0 (it drops the sign).
        // See: https://github.com/rust-lang/rust/issues/20596
        if value == 0.0f64 && value.is_sign_negative() {
            write!(output, "-0e0")?;
            return Ok(());
        }

        write!(output, "{:e}", value)?;
        Ok(())
    }

    /// Writes a DateTime value to `output` as an Ion timestamp.
    pub fn encode_datetime<W: io::Write, I: Into<DateTime<FixedOffset>>>(
        output: &mut W,
        value: I,
    ) -> IonResult<()> {
        let fixed_offset_datetime: DateTime<FixedOffset> = value.into();
        write!(output, "{}", fixed_offset_datetime.to_rfc3339())?;
        Ok(())
    }

    /// Writes a string value to `output` as an Ion symbol.
    pub fn encode_str_as_symbol<S: AsRef<str>, W: io::Write>(
        output: &mut W,
        value: S,
    ) -> IonResult<()> {
        write!(output, "'{}'", value.as_ref())?;
        Ok(())
    }

    /// Writes a string value to `output` as an Ion string.
    pub fn encode_str_as_string<S: AsRef<str>, W: io::Write>(
        output: &mut W,
        value: S,
    ) -> IonResult<()> {
        write!(output, "\"{}\"", value.as_ref())?;
        Ok(())
    }

    /// Writes a byte array slice to `output` as an Ion clob.
    pub fn encode_clob<W: io::Write>(_output: &mut W, _value: &[u8]) -> IonResult<()> {
        todo!()
    }

    /// Writes a byte array slice to `output` as an Ion blob.
    pub fn encode_blob<W: io::Write>(output: &mut W, value: &[u8]) -> IonResult<()> {
        // Rust format strings escape curly braces by doubling them. The following string is:
        // * The opening {{ from a text Ion blob, with each brace doubled to escape it.
        // * A {} pair used by the format string to indicate where the base64-encoded bytes
        //   should be inserted.
        // * The closing }} from a text Ion blob, with each brace doubled to escape it.
        // TODO: Provide a re-usable encoding buffer instead of allocating a String each time.
        write!(output, "{{{{{}}}}}", base64::encode(value))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::result::IonResult;
    use crate::text::encoder::TextEncoder;
    use crate::IonType;
    use bigdecimal::BigDecimal;
    use chrono::{FixedOffset, NaiveDate, TimeZone};
    use std::str;
    use std::str::FromStr;

    fn encoder_test<F>(mut commands: F, expected: &str)
    where
        F: FnMut(&mut Vec<u8>) -> IonResult<()>,
    {
        let mut output = Vec::new();
        commands(&mut output).expect("Invalid TextEncoder commands.");
        assert_eq!(str::from_utf8(&output).unwrap(), expected);
    }

    #[test]
    fn encode_null() {
        encoder_test(
            |output| TextEncoder::encode_null(output, IonType::Struct),
            "null.struct",
        );
    }

    #[test]
    fn encode_bool() {
        encoder_test(|output| TextEncoder::encode_bool(output, true), "true");
        encoder_test(|output| TextEncoder::encode_bool(output, false), "false");
    }

    #[test]
    fn encode_i64() {
        encoder_test(|output| TextEncoder::encode_i64(output, -99999), "-99999");
        encoder_test(|output| TextEncoder::encode_i64(output, -42), "-42");
        encoder_test(|output| TextEncoder::encode_i64(output, -1), "-1");
        encoder_test(|output| TextEncoder::encode_i64(output, 0), "0");
        encoder_test(|output| TextEncoder::encode_i64(output, 1), "1");
        encoder_test(|output| TextEncoder::encode_i64(output, 42), "42");
        encoder_test(|output| TextEncoder::encode_i64(output, 99999), "99999");
    }

    #[test]
    fn encode_f64() {
        encoder_test(
            |output| TextEncoder::encode_f64(output, -99999f64),
            "-9.9999e4",
        );
        encoder_test(|output| TextEncoder::encode_f64(output, -42f64), "-4.2e1");
        encoder_test(|output| TextEncoder::encode_f64(output, -1f64), "-1e0");
        encoder_test(|output| TextEncoder::encode_f64(output, -0.0f64), "-0e0");
        encoder_test(|output| TextEncoder::encode_f64(output, 0f64), "0e0");
        encoder_test(|output| TextEncoder::encode_f64(output, 1f64), "1e0");
        encoder_test(|output| TextEncoder::encode_f64(output, 42f64), "4.2e1");
        encoder_test(
            |output| TextEncoder::encode_f64(output, 99999f64),
            "9.9999e4",
        );

        encoder_test(
            |output| TextEncoder::encode_f64(output, f64::INFINITY),
            "+inf",
        );

        encoder_test(
            |output| TextEncoder::encode_f64(output, f64::NEG_INFINITY),
            "-inf",
        );

        encoder_test(|output| TextEncoder::encode_f64(output, f64::NAN), "nan");
    }

    #[test]
    fn encode_decimal() {
        encoder_test(
            |output| {
                TextEncoder::encode_big_decimal(
                    output,
                    &BigDecimal::from_str("731221.9948").unwrap(),
                )
            },
            "731221.9948",
        );
    }

    #[test]
    fn encode_datetime_epoch() {
        let naive_datetime = NaiveDate::from_ymd(2000 as i32, 1 as u32, 1 as u32)
            .and_hms(0 as u32, 0 as u32, 0 as u32);
        let offset = FixedOffset::west(0);
        let datetime = offset.from_utc_datetime(&naive_datetime);

        encoder_test(
            |output| TextEncoder::encode_datetime(output, datetime),
            "2000-01-01T00:00:00+00:00",
        );
    }

    #[test]
    fn encode_str_as_string() {
        encoder_test(
            |output| TextEncoder::encode_str_as_string(output, "foo"),
            "\"foo\"",
        );
    }

    #[test]
    fn encode_str_as_symbol() {
        encoder_test(
            |output| TextEncoder::encode_str_as_symbol(output, "foo"),
            "\'foo\'",
        );
    }

    #[test]
    #[ignore] // TODO
    fn encode_str_as_clob() {}

    #[test]
    fn encode_blob() {
        encoder_test(
            |output| TextEncoder::encode_blob(output, "hello".as_bytes()),
            "{{aGVsbG8=}}",
        );
    }
}
