use crate::result::{illegal_operation, IonResult};
use crate::IonType;
use bigdecimal::BigDecimal;
use chrono::{DateTime, FixedOffset};
use std::io::{BufWriter, Write};

pub struct TextWriter<W: Write> {
    output: BufWriter<W>,
    annotations: Vec<String>,
    field_name: Option<String>,
    containers: Vec<IonType>,
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

    /// Writes the provided DateTime value as an Ion timestamp.
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
    pub fn write_clob(&mut self, _value: &[u8]) -> IonResult<()> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::result::IonResult;
    use crate::text::writer::TextWriter;
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
    #[ignore]
    fn write_clob() {
        todo!();
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
