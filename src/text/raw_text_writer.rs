use std::convert::TryInto;
use std::io::{BufWriter, Write};
use std::mem;

use bigdecimal::BigDecimal;
use chrono::{DateTime, Datelike, FixedOffset, NaiveDateTime, TimeZone, Timelike};

use crate::raw_symbol_token_ref::{AsRawSymbolTokenRef, RawSymbolTokenRef};
use crate::result::{illegal_operation, IonResult};
use crate::types::decimal::Decimal;
use crate::types::timestamp::{Precision, Timestamp};
use crate::writer::Writer;
use crate::{Integer, IonType};

pub struct RawTextWriter<W: Write> {
    output: BufWriter<W>,
    annotations: Vec<String>,
    field_name: Option<String>,
    containers: Vec<IonType>,
    string_escape_codes: Vec<String>,
}

/**
 * String escape codes, for Ion Clob.
 */
fn string_escape_code_init() -> Vec<String> {
    let mut string_escape_codes = vec![String::new(); 256];
    string_escape_codes[0x00] = "\\0".to_string();
    string_escape_codes[0x07] = "\\a".to_string();
    string_escape_codes[0x08] = "\\b".to_string();
    string_escape_codes['\t' as usize] = "\\t".to_string();
    string_escape_codes['\n' as usize] = "\\n".to_string();
    string_escape_codes[0x0B] = "\\v".to_string();
    string_escape_codes[0x0C] = "\\f".to_string();
    string_escape_codes['\r' as usize] = "\\r".to_string();
    string_escape_codes['\\' as usize] = "\\\\".to_string();
    string_escape_codes['\"' as usize] = "\\\"".to_string();
    for (i, code) in string_escape_codes
        .iter_mut()
        .enumerate()
        .take(0x20)
        .skip(1)
    {
        if code.is_empty() {
            let _ = mem::replace(code, format!("\\x{:02x}", i));
        }
    }
    for (i, code) in string_escape_codes
        .iter_mut()
        .enumerate()
        .take(0x100)
        .skip(0x7F)
    {
        let _ = mem::replace(code, format!("\\x{:x}", i));
    }
    string_escape_codes
}

impl<W: Write> RawTextWriter<W> {
    /// Constructs a new instance of TextWriter that writes values to the provided io::Write
    /// implementation.
    pub fn new(sink: W) -> RawTextWriter<W> {
        RawTextWriter {
            output: BufWriter::new(sink),
            annotations: vec![],
            field_name: None,
            containers: vec![],
            string_escape_codes: string_escape_code_init(),
        }
    }

    /// Returns a reference to the underlying io::Write implementation.
    pub fn output(&self) -> &W {
        self.output.get_ref()
    }

    /// Returns a mutable reference to the underlying io::Write implementation. Modifying the
    /// underlying sink is an inherently risky operation and can result in unexpected behavior.
    /// It is not recommended for most use cases.
    pub fn output_mut(&mut self) -> &mut W {
        self.output.get_mut()
    }

    /// Returns true if the TextWriter is currently positioned within a Struct.
    pub fn is_in_struct(&self) -> bool {
        if let Some(IonType::Struct) = self.containers.last() {
            return true;
        }
        false
    }

    // Called after each value is written to emit an appropriate delimiter before the next value.
    fn write_value_delimiter(&mut self) -> IonResult<()> {
        use IonType::*;
        let delimiter = match self.containers.last() {
            Some(Struct) | Some(List) => ",",
            Some(SExpression) => " ",
            Some(scalar) => unreachable!("Inside a non-container type: {:?}", scalar),
            None => "\n", // Top-level values appear on their own line
        };
        write!(self.output, "{}", delimiter)?;
        Ok(())
    }

    /// Returns `true` if the provided `token`'s text is an 'identifier'. That is, the text starts
    /// with a `$`, `_` or ASCII letter and is followed by a sequence of `$`, `_`, or ASCII letters
    /// and numbers. Examples:
    /// * `firstName`
    /// * `first_name`
    /// * `name_1`
    /// * `$name`
    /// Unlike other symbols, identifiers don't have to be wrapped in quotes.
    fn token_is_identifier(token: &str) -> bool {
        if token.is_empty() {
            return false;
        }
        let mut chars = token.chars();
        let first = chars.next().unwrap();
        (first == '$' || first == '_' || first.is_ascii_alphabetic())
            && chars.all(|c| c == '$' || c == '_' || c.is_ascii_alphanumeric())
    }

    /// Returns `true` if the provided text is an Ion keyword. Keywords like `true` or `null`
    /// resemble identifiers, but writers must wrap them in quotes when using them as symbol text.
    fn token_is_keyword(token: &str) -> bool {
        const KEYWORDS: &[&str] = &["true", "false", "nan", "null"];
        KEYWORDS.contains(&token)
    }

    /// Returns `true` if this token's text resembles a symbol ID literal. For example: `'$99'` is a
    /// symbol with the text `$99`. However, `$99` (without quotes) is a symbol ID that maps to
    /// different text.
    fn token_resembles_symbol_id(token: &str) -> bool {
        if token.is_empty() {
            return false;
        }
        let mut chars = token.chars();
        let first = chars.next().unwrap();
        first == '$' && chars.all(|c| c.is_numeric())
    }

    fn write_symbol_token<A: AsRawSymbolTokenRef>(
        output: &mut BufWriter<W>,
        token: A,
    ) -> IonResult<()> {
        match token.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(sid) => write!(output, "${}", sid)?,
            RawSymbolTokenRef::Text(text)
                if Self::token_is_keyword(text) || Self::token_resembles_symbol_id(text) =>
            {
                // Write the symbol text in single quotes
                write!(output, "'{}'", text)?;
            }
            RawSymbolTokenRef::Text(text) if Self::token_is_identifier(text) => {
                // Write the symbol text without quotes
                write!(output, "{}", text)?
            }
            RawSymbolTokenRef::Text(text) => {
                // Write the symbol text using quotes and escaping any characters that require it.
                write!(output, "\'")?;
                Self::write_escaped_text_body(output, text)?;
                write!(output, "\'")?;
            }
        };
        Ok(())
    }

    // Write the field name and annotations if set
    fn write_value_metadata(&mut self) -> IonResult<()> {
        if let Some(field_name) = &self.field_name.take() {
            Self::write_symbol_token(&mut self.output, field_name)?;
            write!(self.output, ":")?;
        } else if self.is_in_struct() {
            return illegal_operation("Values inside a struct must have a field name.");
        }

        if !self.annotations.is_empty() {
            for annotation in &self.annotations {
                Self::write_symbol_token(&mut self.output, annotation)?;
                write!(self.output, "::")?;
            }
            self.annotations.clear();
        }
        Ok(())
    }

    // Writes:
    // * the field name (if any)
    // * the annotations (if any)
    // * the value written by the `scalar_writer` closure
    // * a trailing delimiter (if any)
    fn write_scalar<F>(&mut self, scalar_writer: F) -> IonResult<()>
    where
        F: FnOnce(&mut BufWriter<W>) -> IonResult<()>,
    {
        self.write_value_metadata()?;
        scalar_writer(&mut self.output)?;
        self.write_value_delimiter()?;
        Ok(())
    }

    /// Writes the provided BigDecimal value as an Ion decimal.
    pub fn write_big_decimal(&mut self, value: &BigDecimal) -> IonResult<()> {
        self.write_scalar(|output| {
            write!(output, "{}", &value)?;
            Ok(())
        })
    }

    // Helper method for [write_timestamp]. Writes the timestamp to output using +/-HH:MM format.
    fn write_offset(output: &mut BufWriter<W>, offset_minutes: Option<i32>) -> IonResult<()> {
        if offset_minutes.is_none() {
            write!(output, "-00:00")?;
            return Ok(());
        }
        let offset_minutes = offset_minutes.unwrap();

        const MINUTES_PER_HOUR: i32 = 60;
        // Split the offset into a sign and magnitude for formatting
        let sign = if offset_minutes >= 0 { "+" } else { "-" };
        let offset_minutes = offset_minutes.abs();
        let hours = offset_minutes / MINUTES_PER_HOUR;
        let minutes = offset_minutes % MINUTES_PER_HOUR;
        write!(output, "{}{:0>2}:{:0>2}", sign, hours, minutes)?;
        Ok(())
    }

    /// Writes the provided DateTime value as an Ion timestamp.
    #[deprecated(
        since = "0.6.1",
        note = "Please use the `write_timestamp` method instead."
    )]
    pub fn write_datetime(&mut self, value: &DateTime<FixedOffset>) -> IonResult<()> {
        self.write_scalar(|output| {
            write!(output, "{}", value.to_rfc3339())?;
            Ok(())
        })
    }

    pub fn add_annotation<A: AsRawSymbolTokenRef>(&mut self, annotation: A) {
        // TODO: This function currently allocates a new string for each annotation.
        //       It will be common for this text to come from the symbol table; we should
        //       make it possible to pass an Rc<str> or similar when applicable.
        let text = match annotation.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(sid) => format!("${}", sid),
            RawSymbolTokenRef::Text(text) => text.to_string(),
        };
        self.annotations.push(text);
    }

    /// Writes the body (i.e. no start or end delimiters) of a string or symbol with any illegal
    /// characters escaped.
    fn write_escaped_text_body<S: AsRef<str>>(
        output: &mut BufWriter<W>,
        value: S,
    ) -> IonResult<()> {
        let mut start = 0usize;
        let text = value.as_ref();
        for (byte_index, character) in text.char_indices() {
            let escaped = match character {
                '\n' => r"\n",
                '\r' => r"\r",
                '\t' => r"\t",
                '\\' => r"\\",
                '/' => r"\/",
                '"' => r#"\""#,
                '\'' => r"\'",
                '?' => r"\?",
                '\x00' => r"\0", // NUL
                '\x07' => r"\a", // alert BEL
                '\x08' => r"\b", // backspace
                '\x0B' => r"\v", // vertical tab
                '\x0C' => r"\f", // form feed
                _ => {
                    // Other characters can be left as-is
                    continue;
                }
            };
            // If we reach this point, the current character needed to be escaped.
            // Write all of the text leading up to this character to output, then the escaped
            // version of this character.
            write!(output, "{}{}", &text[start..byte_index], escaped)?;
            // Update `start` to point to the first byte after the end of this character.
            start = byte_index + character.len_utf8();
        }
        write!(output, "{}", &text[start..])?;
        Ok(())
    }
}

impl<'a, W: Write> Writer for RawTextWriter<W> {
    fn ion_version(&self) -> (u8, u8) {
        (1, 0)
    }

    fn write_ion_version_marker(&mut self, major: u8, minor: u8) -> IonResult<()> {
        write!(self.output, "$ion_{}_{}", major, minor)?;
        Ok(())
    }

    fn supports_text_symbol_tokens(&self) -> bool {
        true
    }

    /// Sets a list of annotations that will be applied to the next value that is written.
    fn set_annotations<I, A>(&mut self, annotations: I)
    where
        A: AsRawSymbolTokenRef,
        I: IntoIterator<Item = A>,
    {
        self.annotations.clear();
        for annotation in annotations {
            self.add_annotation(annotation)
        }
    }

    /// Writes an Ion null of the specified type.
    fn write_null(&mut self, ion_type: IonType) -> IonResult<()> {
        use IonType::*;
        self.write_scalar(|output| {
            let null_text = match ion_type {
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
            };
            write!(output, "{}", null_text)?;
            Ok(())
        })
    }

    /// Writes the provided bool value as an Ion boolean.
    fn write_bool(&mut self, value: bool) -> IonResult<()> {
        self.write_scalar(|output| {
            let bool_text = match value {
                true => "true",
                false => "false",
            };
            write!(output, "{}", bool_text)?;
            Ok(())
        })
    }

    /// Writes the provided i64 value as an Ion integer.
    fn write_i64(&mut self, value: i64) -> IonResult<()> {
        self.write_scalar(|output| {
            write!(output, "{}", value)?;
            Ok(())
        })
    }

    /// Writes an Ion `integer` with the specified value to the output stream.
    fn write_integer(&mut self, value: &Integer) -> IonResult<()> {
        match value {
            Integer::I64(i) => self.write_i64(*i),
            Integer::BigInt(i) => self.write_scalar(|output| {
                write!(output, "{}", i)?;
                Ok(())
            }),
        }
    }

    /// Writes the provided f64 value as an Ion float.
    fn write_f32(&mut self, value: f32) -> IonResult<()> {
        // The text writer doesn't distinguish between f32 and f64 in its output.
        self.write_f64(value as f64)
    }

    /// Writes the provided f64 value as an Ion float.
    fn write_f64(&mut self, value: f64) -> IonResult<()> {
        self.write_scalar(|output| {
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
        })
    }

    /// Writes the provided Decimal as an Ion decimal.
    fn write_decimal(&mut self, value: &Decimal) -> IonResult<()> {
        self.write_scalar(|output| {
            write!(output, "{}", value)?;
            Ok(())
        })
    }

    /// Writes the provided Timestamp as an Ion timestamp.
    fn write_timestamp(&mut self, value: &Timestamp) -> IonResult<()> {
        // A space to format the offset
        self.write_scalar(|output| {
            let (offset_minutes, datetime) = if let Some(minutes) = value.offset {
                // Create a datetime with the appropriate offset that we can use for formatting.
                let datetime: DateTime<FixedOffset> = value.clone().try_into()?;
                // Convert the offset to minutes --v
                (Some(minutes.local_minus_utc() / 60), datetime)
            } else {
                // Our timestamp has an unknown offset. Per the spec, this means it makes no
                // assertions about *where* it was recorded, but its fields are still in UTC.
                // Create a UTC datetime that we can use for formatting.
                let datetime: NaiveDateTime = value.clone().try_into()?;
                let datetime: DateTime<FixedOffset> =
                    FixedOffset::east(0).from_utc_datetime(&datetime);
                (None, datetime)
            };

            write!(output, "{:0>4}", datetime.year())?;
            //                     ^-- 0-padded, right aligned, 4-digit year
            if value.precision == Precision::Year {
                write!(output, "T")?;
                return Ok(());
            }

            write!(output, "-{:0>2}", datetime.month())?;
            //                   ^-- delimiting hyphen and 0-padded, right aligned, 2-digit month
            if value.precision == Precision::Month {
                write!(output, "T")?;
                return Ok(());
            }

            write!(output, "-{:0>2}", datetime.day())?;
            //                   ^-- delimiting hyphen and 0-padded, right aligned, 2-digit day
            if value.precision == Precision::Day {
                write!(output, "T")?;
                return Ok(());
            }

            write!(output, "T{:0>2}:{:0>2}", datetime.hour(), datetime.minute())?;
            //                   ^-- delimiting T, formatted hour, delimiting colon, formatted minute
            if value.precision == Precision::HourAndMinute {
                RawTextWriter::write_offset(output, offset_minutes)?;
                return Ok(());
            }

            write!(output, ":{:0>2}", datetime.second())?;
            //                   ^-- delimiting colon, formatted second
            value.fmt_fractional_seconds(&mut *output)?;

            RawTextWriter::write_offset(output, offset_minutes)?;
            Ok(())
        })
    }

    /// Writes the provided &str value as an Ion symbol.
    fn write_symbol<A: AsRawSymbolTokenRef>(&mut self, value: A) -> IonResult<()> {
        self.write_scalar(|output| {
            RawTextWriter::write_symbol_token(output, value)?;
            Ok(())
        })
    }

    /// Writes the provided &str value as an Ion string.
    fn write_string<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
        self.write_scalar(|output| {
            write!(output, "\"")?;
            RawTextWriter::write_escaped_text_body(output, value)?;
            write!(output, "\"")?;
            Ok(())
        })
    }

    /// Writes the provided byte array slice as an Ion clob.
    fn write_clob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        // clob_value to be written based on defined STRING_ESCAPE_CODES.
        const NUM_DELIMITER_BYTES: usize = 4; // {{}}
        const NUM_HEX_BYTES_PER_BYTE: usize = 4; // \xHH

        let value: &[u8] = value.as_ref();

        // Set aside enough memory to hold a clob containing all hex-encoded bytes
        let mut clob_value =
            String::with_capacity((value.len() * NUM_HEX_BYTES_PER_BYTE) + NUM_DELIMITER_BYTES);

        for byte in value.iter().copied() {
            let c = byte as char;
            let escaped_byte = &self.string_escape_codes[c as usize];
            if !escaped_byte.is_empty() {
                clob_value.push_str(escaped_byte);
            } else {
                clob_value.push(c);
            }
        }
        self.write_scalar(|output| {
            write!(output, "{{{{\"{}\"}}}}", clob_value)?;
            Ok(())
        })
    }

    /// Writes the provided byte array slice as an Ion blob.
    fn write_blob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        self.write_scalar(|output| {
            // Rust format strings escape curly braces by doubling them. The following string is:
            // * The opening {{ from a text Ion blob, with each brace doubled to escape it.
            // * A {} pair used by the format string to indicate where the base64-encoded bytes
            //   should be inserted.
            // * The closing }} from a text Ion blob, with each brace doubled to escape it.
            write!(output, "{{{{{}}}}}", base64::encode(value))?;
            Ok(())
        })
    }

    /// Begins a container (List, S-Expression, or Struct). If `ion_type` is not a container type,
    /// `step_in` will return an Err(IllegalOperation).
    fn step_in(&mut self, ion_type: IonType) -> IonResult<()> {
        use IonType::*;
        self.write_value_metadata()?;
        match ion_type {
            Struct => write!(self.output, "{{")?,
            List => write!(self.output, "[")?,
            SExpression => write!(self.output, "(")?,
            _ => return illegal_operation(format!("Cannot step into a(n) {:?}", ion_type)),
        }
        self.containers.push(ion_type);
        Ok(())
    }

    /// Sets the current field name to `name`. If the TextWriter is currently positioned inside
    /// of a struct, the field name will be written before the next value. Otherwise, it will be
    /// ignored.
    fn set_field_name<A: AsRawSymbolTokenRef>(&mut self, name: A) {
        let name = match name.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(sid) => format!("${}", sid),
            RawSymbolTokenRef::Text(text) => text.to_string(),
        };
        self.field_name = Some(name);
    }

    fn parent_type(&self) -> Option<IonType> {
        self.containers.last().copied()
    }

    fn depth(&self) -> usize {
        self.containers.len()
    }

    /// Completes the current container. If the TextWriter is not currently positioned inside a
    /// container, `step_out` will return an Err(IllegalOperation).
    fn step_out(&mut self) -> IonResult<()> {
        use IonType::*;
        let end_delimiter = match self.containers.pop() {
            Some(Struct) => "}",
            Some(List) => "]",
            Some(SExpression) => ")",
            Some(scalar) => unreachable!("Inside a non-container type: {:?}", scalar),
            None => return illegal_operation("Cannot step out of the top level."),
        };
        write!(self.output, "{}", end_delimiter)?;
        self.write_value_delimiter()?;
        Ok(())
    }

    fn flush(&mut self) -> IonResult<()> {
        self.output.flush()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::str;
    use std::str::FromStr;

    use bigdecimal::BigDecimal;
    use chrono::{FixedOffset, NaiveDate, TimeZone};

    use crate::result::IonResult;
    use crate::text::raw_text_writer::RawTextWriter;
    use crate::types::timestamp::Timestamp;
    use crate::writer::Writer;
    use crate::IonType;

    fn writer_test<F>(mut commands: F, expected: &str)
    where
        F: FnMut(&mut RawTextWriter<&mut Vec<u8>>) -> IonResult<()>,
    {
        let mut output = Vec::new();
        let mut writer = RawTextWriter::new(&mut output);
        commands(&mut writer).expect("Invalid TextWriter test commands.");
        drop(writer);
        assert_eq!(str::from_utf8(&output).unwrap(), expected);
    }

    #[test]
    fn write_null_null() {
        writer_test(|w| w.write_null(IonType::Null), "null\n");
    }

    #[test]
    fn write_null_string() {
        writer_test(|w| w.write_null(IonType::String), "null.string\n");
    }

    #[test]
    fn write_bool_true() {
        writer_test(|w| w.write_bool(true), "true\n");
    }

    #[test]
    fn write_bool_false() {
        writer_test(|w| w.write_bool(false), "false\n");
    }

    #[test]
    fn write_i64() {
        writer_test(|w| w.write_i64(7), "7\n");
    }

    #[test]
    fn write_f32() {
        writer_test(|w| w.write_f32(700f32), "7e2\n");
    }

    #[test]
    fn write_f64() {
        writer_test(|w| w.write_f64(700f64), "7e2\n");
    }

    #[test]
    fn write_annotated_i64() {
        writer_test(
            |w| {
                w.set_annotations(&["foo", "bar", "baz quux"]);
                w.write_i64(7)
            },
            "foo::bar::'baz quux'::7\n",
        );
    }

    #[test]
    fn write_decimal() {
        let decimal_text = "731221.9948";
        writer_test(
            |w| w.write_big_decimal(&BigDecimal::from_str(decimal_text).unwrap()),
            &format!("{}\n", decimal_text),
        );
    }

    #[test]
    fn write_datetime_epoch() {
        #![allow(deprecated)] // `write_datetime` is deprecated
        let naive_datetime =
            NaiveDate::from_ymd(2000_i32, 1_u32, 1_u32).and_hms(0_u32, 0_u32, 0_u32);
        let offset = FixedOffset::west(0);
        let datetime = offset.from_utc_datetime(&naive_datetime);
        writer_test(
            |w| w.write_datetime(&datetime),
            "2000-01-01T00:00:00+00:00\n",
        );
    }

    #[test]
    fn write_timestamp_with_year() {
        let timestamp = Timestamp::with_year(2000)
            .build()
            .expect("building timestamp failed");
        writer_test(|w| w.write_timestamp(&timestamp), "2000T\n");
    }

    #[test]
    fn write_timestamp_with_month() {
        let timestamp = Timestamp::with_year(2000)
            .with_month(8)
            .build()
            .expect("building timestamp failed");
        writer_test(|w| w.write_timestamp(&timestamp), "2000-08T\n");
    }

    #[test]
    fn write_timestamp_with_ymd() {
        let timestamp = Timestamp::with_ymd(2000, 8, 22)
            .build()
            .expect("building timestamp failed");
        writer_test(|w| w.write_timestamp(&timestamp), "2000-08-22T\n");
    }

    #[test]
    fn write_timestamp_with_ymd_hms() {
        let timestamp = Timestamp::with_ymd(2000, 8, 22)
            .with_hms(15, 45, 11)
            .build_at_offset(2 * 60)
            .expect("building timestamp failed");
        writer_test(
            |w| w.write_timestamp(&timestamp),
            "2000-08-22T15:45:11+02:00\n",
        );
    }

    #[test]
    fn write_timestamp_with_ymd_hms_millis() {
        let timestamp = Timestamp::with_ymd_hms_millis(2000, 8, 22, 15, 45, 11, 931)
            .build_at_offset(-5 * 60)
            .expect("building timestamp failed");
        writer_test(
            |w| w.write_timestamp(&timestamp),
            "2000-08-22T15:45:11.931-05:00\n",
        );
    }

    #[test]
    fn write_timestamp_with_ymd_hms_millis_unknown_offset() {
        let timestamp = Timestamp::with_ymd_hms_millis(2000, 8, 22, 15, 45, 11, 931)
            .build_at_unknown_offset()
            .expect("building timestamp failed");
        writer_test(
            |w| w.write_timestamp(&timestamp),
            "2000-08-22T15:45:11.931-00:00\n",
        );
    }

    #[test]
    fn write_stream() {
        writer_test(
            |w| {
                w.write_string("foo")?;
                w.write_i64(21)?;
                w.write_symbol("bar")
            },
            "\"foo\"\n21\nbar\n",
        );
    }

    #[test]
    fn write_blob() {
        writer_test(|w| w.write_blob("hello".as_bytes()), "{{aGVsbG8=}}\n");
    }

    #[test]
    fn write_clob() {
        writer_test(
            |w| w.write_clob("a\"\'\n".as_bytes()),
            "{{\"a\\\"'\\n\"}}\n",
        );
        writer_test(
            |w| w.write_clob("❤️".as_bytes()),
            "{{\"\\xe2\\x9d\\xa4\\xef\\xb8\\x8f\"}}\n",
        );
        writer_test(
            |w| w.write_clob("hello world".as_bytes()),
            "{{\"hello world\"}}\n",
        );
    }

    #[test]
    fn write_list() {
        writer_test(
            |w| {
                w.step_in(IonType::List)?;
                w.write_string("foo")?;
                w.write_i64(21)?;
                w.write_symbol("bar")?;
                w.step_out()
            },
            "[\"foo\",21,bar,]\n",
        );
    }

    #[test]
    fn write_nested_list() {
        writer_test(
            |w| {
                w.step_in(IonType::List)?;
                w.write_string("foo")?;
                w.write_i64(21)?;
                w.step_in(IonType::List)?;
                w.write_symbol("bar")?;
                w.step_out()?;
                w.step_out()
            },
            "[\"foo\",21,[bar,],]\n",
        );
    }

    #[test]
    fn write_s_expression() {
        writer_test(
            |w| {
                w.step_in(IonType::SExpression)?;
                w.write_string("foo")?;
                w.write_i64(21)?;
                w.write_symbol("bar")?;
                w.step_out()
            },
            "(\"foo\" 21 bar )\n",
        );
    }

    #[test]
    fn write_struct() {
        writer_test(
            |w| {
                w.step_in(IonType::Struct)?;
                w.set_field_name("a");
                w.write_string("foo")?;
                w.set_field_name("b");
                w.write_i64(21)?;
                w.set_field_name("c");
                w.set_annotations(&["quux"]);
                w.write_symbol("bar")?;
                w.step_out()
            },
            "{a:\"foo\",b:21,c:quux::bar,}\n",
        );
    }
}
