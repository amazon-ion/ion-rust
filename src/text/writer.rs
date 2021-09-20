use crate::result::{illegal_operation, IonResult};
use crate::types::timestamp::{Precision, Timestamp};
use crate::IonType;
use bigdecimal::BigDecimal;
use chrono::{DateTime, Datelike, FixedOffset, NaiveDateTime, TimeZone, Timelike};
use std::convert::TryInto;
use std::io::{BufWriter, Write};

pub struct TextWriter<W: Write> {
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
    for i in 1..0x20 {
        if string_escape_codes[i] == "" {
            string_escape_codes[i] = format!("\\x{:02x}", i);
        }
    }
    for i in 0x7F..0x100 {
        string_escape_codes[i] = format!("\\x{:x}", i);
    }
    return string_escape_codes;
}

impl<W: Write> TextWriter<W> {
    /// Constructs a new instance of TextWriter that writes values to the provided io::Write
    /// implementation.
    pub fn new(sink: W) -> TextWriter<W> {
        TextWriter {
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

    /// Causes any buffered data to be written to the underlying io::Write implementation.
    pub fn flush(&mut self) -> IonResult<()> {
        self.output.flush()?;
        Ok(())
    }

    /// Sets the current field name to `name`. If the TextWriter is currently positioned inside
    /// of a struct, the field name will be written before the next value. Otherwise, it will be
    /// ignored.
    pub fn set_field_name(&mut self, name: &str) {
        self.field_name = Some(name.to_string());
    }

    /// Sets a list of annotations that will be applied to the next value that is written.
    pub fn set_annotations(&mut self, annotations: &[&str]) {
        self.annotations
            .extend(annotations.iter().map(|s| s.to_string()));
    }

    /// Begins a container (List, S-Expression, or Struct). If `ion_type` is not a container type,
    /// `step_in` will return an Err(IllegalOperation).
    pub fn step_in(&mut self, ion_type: IonType) -> IonResult<()> {
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

    /// Returns true if the TextWriter is currently positioned within a Struct.
    pub fn is_in_struct(&self) -> bool {
        if let Some(IonType::Struct) = self.containers.last() {
            return true;
        }
        false
    }

    // Completes the current container. If the TextWriter is not currently positioned inside a
    // container, `step_out` will return an Err(IllegalOperation).
    pub fn step_out(&mut self) -> IonResult<()> {
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

    // Write the field name and annotations if set
    fn write_value_metadata(&mut self) -> IonResult<()> {
        if let Some(field_name) = &self.field_name.take() {
            write!(self.output, "{}:", field_name)?;
        } else if self.is_in_struct() {
            return illegal_operation(format!("Values inside a struct must have a field name."));
        }
        if !self.annotations.is_empty() {
            for annotation in &self.annotations {
                write!(self.output, "'{}'::", annotation)?;
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

    /// Writes an Ion null of the specified type.
    pub fn write_null(&mut self, ion_type: IonType) -> IonResult<()> {
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
    pub fn write_bool(&mut self, value: bool) -> IonResult<()> {
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
    pub fn write_i64(&mut self, value: i64) -> IonResult<()> {
        self.write_scalar(|output| {
            write!(output, "{}", value)?;
            Ok(())
        })
    }

    /// Writes the provided f64 value as an Ion float.
    pub fn write_f64(&mut self, value: f64) -> IonResult<()> {
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

    /// Writes the provided Timestamp as an Ion timestamp.
    pub fn write_timestamp(&mut self, value: &Timestamp) -> IonResult<()> {
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
                Self::write_offset(output, offset_minutes)?;
                return Ok(());
            }

            write!(output, ":{:0>2}", datetime.second())?;
            //                   ^-- delimiting colon, formatted second
            if value.precision == Precision::Second {
                Self::write_offset(output, offset_minutes)?;
                return Ok(());
            }

            // We want the fractional seconds to show as many decimal places as are interesting.
            // Here we format the string as nanoseconds and then eliminate any trailing zeros.
            //TODO: The initial conversion to datetime will discard precision greater than nanoseconds.
            //TODO: Eliminate this allocation.
            let fractional_text = format!("{:0>9}", datetime.nanosecond());
            let fractional_text = fractional_text.trim_end_matches("0");

            write!(output, ".{}", fractional_text)?;
            //               ^-- delimiting decimal point, formatted fractional seconds
            Self::write_offset(output, offset_minutes)?;
            Ok(())
        })
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

    /// Writes the provided &str value as an Ion symbol.
    pub fn write_symbol<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
        self.write_scalar(|output| {
            write!(output, "'{}'", value.as_ref())?;
            Ok(())
        })
    }

    /// Writes the provided &str value as an Ion string.
    pub fn write_string<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
        self.write_scalar(|output| {
            write!(output, "\"{}\"", value.as_ref())?;
            Ok(())
        })
    }

    /// Writes the provided byte array slice as an Ion blob.
    pub fn write_blob(&mut self, value: &[u8]) -> IonResult<()> {
        self.write_scalar(|output| {
            // Rust format strings escape curly braces by doubling them. The following string is:
            // * The opening {{ from a text Ion blob, with each brace doubled to escape it.
            // * A {} pair used by the format string to indicate where the base64-encoded bytes
            //   should be inserted.
            // * The closing }} from a text Ion blob, with each brace doubled to escape it.
            // TODO: Provide a re-usable encoding buffer instead of allocating a String each time.
            write!(output, "{{{{{}}}}}", base64::encode(value))?;
            Ok(())
        })
    }

    /// Writes the provided byte array slice as an Ion clob.
    pub fn write_clob(&mut self, value: &[u8]) -> IonResult<()> {
        // clob_value to be written based on defined STRING_ESCAPE_CODES.
        const NUM_DELIMITER_BYTES: usize = 4; // {{}}
        const NUM_HEX_BYTES_PER_BYTE: usize = 4; // \xHH

        // Set aside enough memory to hold a clob containing all hex-encoded bytes
        let mut clob_value =
            String::with_capacity((value.len() * NUM_HEX_BYTES_PER_BYTE) + NUM_DELIMITER_BYTES);

        for i in 0..value.len() {
            let c = value[i] as char;
            let escaped_byte = &self.string_escape_codes[c as usize];
            if escaped_byte != "" {
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
}

#[cfg(test)]
mod tests {
    use crate::result::IonResult;
    use crate::text::writer::TextWriter;
    use crate::types::timestamp::Timestamp;
    use crate::IonType;
    use bigdecimal::BigDecimal;
    use chrono::{FixedOffset, NaiveDate, TimeZone};
    use std::str;
    use std::str::FromStr;

    fn writer_test<F>(mut commands: F, expected: &str)
    where
        F: FnMut(&mut TextWriter<&mut Vec<u8>>) -> IonResult<()>,
    {
        let mut output = Vec::new();
        let mut writer = TextWriter::new(&mut output);
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
    fn write_f64() {
        writer_test(|w| w.write_f64(700f64), "7e2\n");
    }

    #[test]
    fn write_annotated_i64() {
        writer_test(
            |w| {
                w.set_annotations(&["foo", "bar", "baz"]);
                w.write_i64(7)
            },
            "'foo'::'bar'::'baz'::7\n",
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
        let naive_datetime = NaiveDate::from_ymd(2000 as i32, 1 as u32, 1 as u32)
            .and_hms(0 as u32, 0 as u32, 0 as u32);
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
            "\"foo\"\n21\n'bar'\n",
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
            "[\"foo\",21,'bar',]\n",
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
            "[\"foo\",21,['bar',],]\n",
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
            "(\"foo\" 21 'bar' )\n",
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
                w.set_annotations(&["qux"]);
                w.write_symbol("bar")?;
                w.step_out()
            },
            "{a:\"foo\",b:21,c:'qux'::'bar',}\n",
        );
    }
}
