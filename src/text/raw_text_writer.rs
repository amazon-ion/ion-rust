use std::convert::TryInto;
use std::io::{BufWriter, Write};

use bigdecimal::BigDecimal;
use chrono::{DateTime, Datelike, FixedOffset, NaiveDateTime, TimeZone, Timelike};

use crate::raw_symbol_token_ref::{AsRawSymbolTokenRef, RawSymbolTokenRef};
use crate::result::{illegal_operation, IonResult};
use crate::text::text_formatter::STRING_ESCAPE_CODES;
use crate::types::decimal::Decimal;
use crate::types::timestamp::{Precision, Timestamp};
use crate::types::ContainerType;
use crate::writer::IonWriter;
use crate::{Integer, IonType};

pub struct RawTextWriterBuilder {
    space_between_values: String,
    indentation: String,
    space_after_field_name: String,
    space_after_container_start: String,
}

impl RawTextWriterBuilder {
    /// Constructs a text Ion writer with modest (but not strictly minimal) spacing.
    ///
    /// For example:
    /// ```ignore
    /// {foo: 1, bar: 2, baz: 3} [1, 2, 3] true "hello"
    /// ```
    pub fn new() -> RawTextWriterBuilder {
        RawTextWriterBuilder {
            // Single space between values
            space_between_values: String::from(" "),
            // No indentation
            indentation: String::new(),
            // Single space between field names and values
            space_after_field_name: String::from(" "),
            // The first value in a container appears next to the opening delimiter
            space_after_container_start: String::new(),
        }
    }

    /// Constructs a 'pretty' text Ion writer that adds human-friendly spacing between values.
    ///
    /// For example:
    /// ```ignore
    /// {
    ///     foo: 1,
    ///     bar: 2,
    ///     baz: 3
    /// }
    /// [
    ///     1,
    ///     2,
    ///     3
    /// ]
    /// true
    /// "hello"
    /// ```
    pub fn pretty() -> RawTextWriterBuilder {
        RawTextWriterBuilder {
            // Each value appears on its own line
            space_between_values: String::from("\n"),
            // Values get four spaces of indentation per level of depth
            indentation: String::from("    "),
            // Field names and values are separated by a single space
            space_after_field_name: String::from(" "),
            // The first value in a container appears on a line by itself
            space_after_container_start: String::from("\n"),
        }
    }

    pub fn with_space_between_values<S: Into<String>>(
        mut self,
        space_between_values: S,
    ) -> RawTextWriterBuilder {
        self.space_between_values = space_between_values.into();
        self
    }

    pub fn with_indentation<S: Into<String>>(mut self, indentation: S) -> RawTextWriterBuilder {
        self.indentation = indentation.into();
        self
    }

    pub fn with_space_after_field_name<S: Into<String>>(
        mut self,
        space_after_field_name: S,
    ) -> RawTextWriterBuilder {
        self.space_after_field_name = space_after_field_name.into();
        self
    }

    pub fn with_space_after_container_start<S: Into<String>>(
        mut self,
        space_after_container_start: S,
    ) -> RawTextWriterBuilder {
        self.space_after_field_name = space_after_container_start.into();
        self
    }

    /// Constructs a new instance of [RawTextWriter] that writes values to the provided io::Write
    /// implementation.
    pub fn build<W: Write>(self, sink: W) -> IonResult<RawTextWriter<W>> {
        let raw_text_writer = RawTextWriter {
            output: BufWriter::new(sink),
            annotations: Vec::new(),
            field_name: None,
            containers: vec![EncodingLevel::default()],
            // TODO: We should consider putting these in a single struct (`WhitespaceConfig`?)
            //       and `Box`ing it. Each `String` is 24 bytes, making the writer much bigger.
            space_between_values: self.space_between_values,
            indentation: self.indentation,
            space_after_field_name: self.space_after_field_name,
            space_after_container_start: self.space_after_container_start,
        };
        // This method cannot currently fail. It returns an IonResult<_> to be consistent with the
        // other builder APIs and to allow for fallible setup operations in the future.
        Ok(raw_text_writer)
    }
}

impl Default for RawTextWriterBuilder {
    fn default() -> Self {
        RawTextWriterBuilder::new()
    }
}

#[derive(Debug, PartialEq, Default)]
struct EncodingLevel {
    container_type: ContainerType,
    child_count: usize,
}

pub struct RawTextWriter<W: Write> {
    output: BufWriter<W>,
    annotations: Vec<String>,
    field_name: Option<String>,
    containers: Vec<EncodingLevel>,
    space_between_values: String,
    indentation: String,
    space_after_field_name: String,
    space_after_container_start: String,
}

impl<W: Write> RawTextWriter<W> {
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

    /// Returns true if the RawTextWriter is currently positioned within a Struct.
    pub fn is_in_struct(&self) -> bool {
        self.parent_level().container_type == ContainerType::Struct
    }

    /// Returns the number of values that have already been written in this container.
    /// Before the first value in a container is written, this returns `0`.
    /// For the purposes of this method, the top level is considered a container.
    fn index_within_parent(&self) -> usize {
        self.parent_level().child_count
    }

    /// Returns the `&EncodingLevel` into which the RawTextWriter most recently stepped.
    fn parent_level(&self) -> &EncodingLevel {
        // `self.containers` is never empty; it always has at least the top level.
        self.containers.last().unwrap()
    }

    /// Increments the value returned by [Self::index_within_parent].
    fn increment_child_count(&mut self) {
        let parent_level = self.containers.last_mut().unwrap();
        parent_level.child_count += 1;
    }

    /// Called after each value is written to emit an appropriate delimiter before the next value.
    fn write_value_delimiter(&mut self) -> IonResult<()> {
        use ContainerType::*;
        let delimiter = match self.parent_level().container_type {
            TopLevel => "",
            Struct | List => ",",
            SExpression => "",
        };
        write!(self.output, "{}", delimiter)?;
        Ok(())
    }

    /// Writes any interstitial whitespace that is appropriate for the current context, including:
    /// * Whitespace following a container start
    /// * Whitespace between values
    /// * Indentation
    fn write_space_before_value(&mut self) -> IonResult<()> {
        // If this is the first value in this container...
        if self.index_within_parent() == 0 {
            // ...and we're not at the top level...
            if self.depth() > 0 {
                // ...then this is the first value inside a container. We'll write the
                // `space_after_container_start` so it will (e.g.) appear on its own line.
                write!(&mut self.output, "{}", self.space_after_container_start)?;
            }
        } else {
            // Otherwise, this is not the first value in this container. Emit the container's
            // delimiter (for example: in a list, write a `,`) before we write the value itself.
            self.write_value_delimiter()?;
            write!(&mut self.output, "{}", self.space_between_values)?;
        }
        // Write enough indentation for the current level of depth
        for _ in 0..self.depth() {
            write!(&mut self.output, "{}", self.indentation)?;
        }
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

    pub(crate) fn write_symbol_token<A: AsRawSymbolTokenRef>(
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
            write!(self.output, ":{}", self.space_after_field_name)?;
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
        self.write_space_before_value()?;
        self.write_value_metadata()?;
        scalar_writer(&mut self.output)?;
        // We just wrote another value; bump the child count.
        self.increment_child_count();
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
    pub(crate) fn write_escaped_text_body<S: AsRef<str>>(
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

impl<W: Write> IonWriter for RawTextWriter<W> {
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
            let escaped_byte = STRING_ESCAPE_CODES[c as usize];
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

        self.write_space_before_value()?;
        self.write_value_metadata()?;
        let container_type = match ion_type {
            Struct => {
                write!(self.output, "{{")?;
                ContainerType::Struct
            }
            List => {
                write!(self.output, "[")?;
                ContainerType::List
            }
            SExpression => {
                write!(self.output, "(")?;
                ContainerType::SExpression
            }
            _ => return illegal_operation(format!("Cannot step into a(n) {:?}", ion_type)),
        };
        self.containers.push(EncodingLevel {
            container_type,
            child_count: 0usize,
        });

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
        match self.parent_level().container_type {
            ContainerType::TopLevel => None,
            ContainerType::List => Some(IonType::List),
            ContainerType::SExpression => Some(IonType::SExpression),
            ContainerType::Struct => Some(IonType::Struct),
        }
    }

    fn depth(&self) -> usize {
        self.containers.len() - 1
    }

    /// Completes the current container. If the TextWriter is not currently positioned inside a
    /// container, `step_out` will return an Err(IllegalOperation).
    fn step_out(&mut self) -> IonResult<()> {
        use ContainerType::*;
        let end_delimiter = match self.parent_level().container_type {
            Struct => "}",
            List => "]",
            SExpression => ")",
            TopLevel => return illegal_operation("cannot step out of the top level"),
        };
        // Wait to pop() the encoding level until after we've confirmed it wasn't TopLevel
        let popped_encoding_level = self.containers.pop().unwrap();
        if popped_encoding_level.child_count > 0 {
            // If this isn't an empty container, put the closing delimiter on the next line
            // with proper indentation.
            if self.space_between_values.contains(&['\n', '\r']) {
                writeln!(&mut self.output)?;
                for _ in 0..self.depth() {
                    write!(&mut self.output, "{}", self.indentation)?;
                }
            }
        }
        write!(self.output, "{}", end_delimiter)?;
        self.increment_child_count();
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
    use crate::text::raw_text_writer::{RawTextWriter, RawTextWriterBuilder};
    use crate::types::timestamp::Timestamp;
    use crate::writer::IonWriter;
    use crate::IonType;

    fn writer_test_with_builder<F>(builder: RawTextWriterBuilder, mut commands: F, expected: &str)
    where
        F: FnMut(&mut RawTextWriter<&mut Vec<u8>>) -> IonResult<()>,
    {
        let mut output = Vec::new();
        let mut writer = builder
            .build(&mut output)
            .expect("could not create RawTextWriter");
        commands(&mut writer).expect("Invalid TextWriter test commands.");
        writer.flush().expect("Call to flush() failed.");
        drop(writer);
        assert_eq!(str::from_utf8(&output).unwrap(), expected);
    }

    /// Constructs a [RawTextWriter] using [RawTextReaderBuilder::new], passes it to the
    /// provided `commands` closure, and then verifies that its output matches `expected_default`.
    /// Then, constructs a [RawTextWriter] using [RawTextReaderBuilder::pretty], passes it to the
    /// provided `commands` closure, and then verifies that its output matches `expected_pretty`.
    fn writer_test<F>(mut commands: F, expected_default: &str, expected_pretty: &str)
    where
        F: Fn(&mut RawTextWriter<&mut Vec<u8>>) -> IonResult<()>,
    {
        writer_test_with_builder(RawTextWriterBuilder::new(), &mut commands, expected_default);
        writer_test_with_builder(RawTextWriterBuilder::pretty(), commands, expected_pretty)
    }

    /// When writing a scalar value, there shouldn't be any difference in output between the
    /// `default` and `pretty` text writers. This function simply calls `writer_test_with_builder`
    /// above using the same expected text for both cases.
    fn write_scalar_test<F>(mut commands: F, expected: &str)
    where
        F: Fn(&mut RawTextWriter<&mut Vec<u8>>) -> IonResult<()>,
    {
        writer_test_with_builder(RawTextWriterBuilder::new(), &mut commands, expected);
        writer_test_with_builder(RawTextWriterBuilder::pretty(), commands, expected)
    }

    #[test]
    fn write_null_null() {
        write_scalar_test(|w| w.write_null(IonType::Null), "null");
    }

    #[test]
    fn write_null_string() {
        write_scalar_test(|w| w.write_null(IonType::String), "null.string");
    }

    #[test]
    fn write_bool_true() {
        write_scalar_test(|w| w.write_bool(true), "true");
    }

    #[test]
    fn write_bool_false() {
        write_scalar_test(|w| w.write_bool(false), "false");
    }

    #[test]
    fn write_i64() {
        write_scalar_test(|w| w.write_i64(7), "7");
    }

    #[test]
    fn write_f32() {
        write_scalar_test(|w| w.write_f32(700f32), "7e2");
    }

    #[test]
    fn write_f64() {
        write_scalar_test(|w| w.write_f64(700f64), "7e2");
    }

    #[test]
    fn write_annotated_i64() {
        write_scalar_test(
            |w| {
                w.set_annotations(&["foo", "bar", "baz quux"]);
                w.write_i64(7)
            },
            "foo::bar::'baz quux'::7",
        );
    }

    #[test]
    fn write_decimal() {
        let decimal_text = "731221.9948";
        write_scalar_test(
            |w| w.write_big_decimal(&BigDecimal::from_str(decimal_text).unwrap()),
            decimal_text,
        );
    }

    #[test]
    fn write_datetime_epoch() {
        #![allow(deprecated)] // `write_datetime` is deprecated
        let naive_datetime =
            NaiveDate::from_ymd(2000_i32, 1_u32, 1_u32).and_hms(0_u32, 0_u32, 0_u32);
        let offset = FixedOffset::west(0);
        let datetime = offset.from_utc_datetime(&naive_datetime);
        write_scalar_test(|w| w.write_datetime(&datetime), "2000-01-01T00:00:00+00:00");
    }

    #[test]
    fn write_timestamp_with_year() {
        let timestamp = Timestamp::with_year(2000)
            .build()
            .expect("building timestamp failed");
        write_scalar_test(|w| w.write_timestamp(&timestamp), "2000T");
    }

    #[test]
    fn write_timestamp_with_month() {
        let timestamp = Timestamp::with_year(2000)
            .with_month(8)
            .build()
            .expect("building timestamp failed");
        write_scalar_test(|w| w.write_timestamp(&timestamp), "2000-08T");
    }

    #[test]
    fn write_timestamp_with_ymd() {
        let timestamp = Timestamp::with_ymd(2000, 8, 22)
            .build()
            .expect("building timestamp failed");
        write_scalar_test(|w| w.write_timestamp(&timestamp), "2000-08-22T");
    }

    #[test]
    fn write_timestamp_with_ymd_hms() {
        let timestamp = Timestamp::with_ymd(2000, 8, 22)
            .with_hms(15, 45, 11)
            .build_at_offset(2 * 60)
            .expect("building timestamp failed");
        write_scalar_test(
            |w| w.write_timestamp(&timestamp),
            "2000-08-22T15:45:11+02:00",
        );
    }

    #[test]
    fn write_timestamp_with_ymd_hms_millis() {
        let timestamp = Timestamp::with_ymd_hms_millis(2000, 8, 22, 15, 45, 11, 931)
            .build_at_offset(-5 * 60)
            .expect("building timestamp failed");
        write_scalar_test(
            |w| w.write_timestamp(&timestamp),
            "2000-08-22T15:45:11.931-05:00",
        );
    }

    #[test]
    fn write_timestamp_with_ymd_hms_millis_unknown_offset() {
        let timestamp = Timestamp::with_ymd_hms_millis(2000, 8, 22, 15, 45, 11, 931)
            .build_at_unknown_offset()
            .expect("building timestamp failed");
        write_scalar_test(
            |w| w.write_timestamp(&timestamp),
            "2000-08-22T15:45:11.931-00:00",
        );
    }

    #[test]
    fn write_blob() {
        write_scalar_test(|w| w.write_blob("hello".as_bytes()), "{{aGVsbG8=}}");
    }

    #[test]
    fn write_clob() {
        write_scalar_test(|w| w.write_clob("a\"\'\n".as_bytes()), "{{\"a\\\"'\\n\"}}");
        write_scalar_test(
            |w| w.write_clob("❤️".as_bytes()),
            "{{\"\\xe2\\x9d\\xa4\\xef\\xb8\\x8f\"}}",
        );
        write_scalar_test(
            |w| w.write_clob("hello world".as_bytes()),
            "{{\"hello world\"}}",
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
            "\"foo\" 21 bar",
            "\"foo\"\n21\nbar",
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
            "[\"foo\", 21, bar]",
            "[\n    \"foo\",\n    21,\n    bar\n]",
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
            "[\"foo\", 21, [bar]]",
            "[\n    \"foo\",\n    21,\n    [\n        bar\n    ]\n]",
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
            "(\"foo\" 21 bar)",
            "(\n    \"foo\"\n    21\n    bar\n)",
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
            "{a: \"foo\", b: 21, c: quux::bar}",
            "{\n    a: \"foo\",\n    b: 21,\n    c: quux::bar\n}",
        );
    }
}
