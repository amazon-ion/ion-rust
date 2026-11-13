use crate::raw_symbol_ref::{AsRawSymbolRef, RawSymbolRef};
use crate::{Annotations, Element, Sequence, Symbol, Value};
use crate::{Decimal, Int, Struct, Timestamp};
use crate::{IonResult, IonType};
use arrayvec::ArrayString;
use ice_code::ice as cold_path;
use std::{fmt, io};

pub const STRING_ESCAPE_CODES: &[&str] = &string_escape_code_init();

/**
 * String escape codes, for Ion Clob.
 */
pub(crate) const fn string_escape_code_init() -> [&'static str; 256] {
    let mut string_escape_codes = [""; 256];
    string_escape_codes[0] = "\\0";
    string_escape_codes[7] = "\\a";
    string_escape_codes[8] = "\\b";
    string_escape_codes['\t' as usize] = "\\t";
    string_escape_codes['\n' as usize] = "\\n";
    string_escape_codes[11] = "\\v";
    string_escape_codes[12] = "\\f";
    string_escape_codes['\r' as usize] = "\\r";
    string_escape_codes['\\' as usize] = "\\\\";
    string_escape_codes['\"' as usize] = "\\\"";

    string_escape_codes[1] = "\\x01";
    string_escape_codes[2] = "\\x02";
    string_escape_codes[3] = "\\x03";
    string_escape_codes[4] = "\\x04";
    string_escape_codes[5] = "\\x05";
    string_escape_codes[6] = "\\x06";
    string_escape_codes[14] = "\\x0e";
    string_escape_codes[15] = "\\x0f";
    string_escape_codes[16] = "\\x10";
    string_escape_codes[17] = "\\x11";
    string_escape_codes[18] = "\\x12";
    string_escape_codes[19] = "\\x13";
    string_escape_codes[20] = "\\x14";
    string_escape_codes[21] = "\\x15";
    string_escape_codes[22] = "\\x16";
    string_escape_codes[23] = "\\x17";
    string_escape_codes[24] = "\\x18";
    string_escape_codes[25] = "\\x19";
    string_escape_codes[26] = "\\x1a";
    string_escape_codes[27] = "\\x1b";
    string_escape_codes[28] = "\\x1c";
    string_escape_codes[29] = "\\x1d";
    string_escape_codes[30] = "\\x1e";
    string_escape_codes[31] = "\\x1f";

    string_escape_codes[127] = "\\x7f";
    string_escape_codes[128] = "\\x80";
    string_escape_codes[129] = "\\x81";
    string_escape_codes[130] = "\\x82";
    string_escape_codes[131] = "\\x83";
    string_escape_codes[132] = "\\x84";
    string_escape_codes[133] = "\\x85";
    string_escape_codes[134] = "\\x86";
    string_escape_codes[135] = "\\x87";
    string_escape_codes[136] = "\\x88";
    string_escape_codes[137] = "\\x89";
    string_escape_codes[138] = "\\x8a";
    string_escape_codes[139] = "\\x8b";
    string_escape_codes[140] = "\\x8c";
    string_escape_codes[141] = "\\x8d";
    string_escape_codes[142] = "\\x8e";
    string_escape_codes[143] = "\\x8f";
    string_escape_codes[144] = "\\x90";
    string_escape_codes[145] = "\\x91";
    string_escape_codes[146] = "\\x92";
    string_escape_codes[147] = "\\x93";
    string_escape_codes[148] = "\\x94";
    string_escape_codes[149] = "\\x95";
    string_escape_codes[150] = "\\x96";
    string_escape_codes[151] = "\\x97";
    string_escape_codes[152] = "\\x98";
    string_escape_codes[153] = "\\x99";
    string_escape_codes[154] = "\\x9a";
    string_escape_codes[155] = "\\x9b";
    string_escape_codes[156] = "\\x9c";
    string_escape_codes[157] = "\\x9d";
    string_escape_codes[158] = "\\x9e";
    string_escape_codes[159] = "\\x9f";
    string_escape_codes[160] = "\\xa0";
    string_escape_codes[161] = "\\xa1";
    string_escape_codes[162] = "\\xa2";
    string_escape_codes[163] = "\\xa3";
    string_escape_codes[164] = "\\xa4";
    string_escape_codes[165] = "\\xa5";
    string_escape_codes[166] = "\\xa6";
    string_escape_codes[167] = "\\xa7";
    string_escape_codes[168] = "\\xa8";
    string_escape_codes[169] = "\\xa9";
    string_escape_codes[170] = "\\xaa";
    string_escape_codes[171] = "\\xab";
    string_escape_codes[172] = "\\xac";
    string_escape_codes[173] = "\\xad";
    string_escape_codes[174] = "\\xae";
    string_escape_codes[175] = "\\xaf";
    string_escape_codes[176] = "\\xb0";
    string_escape_codes[177] = "\\xb1";
    string_escape_codes[178] = "\\xb2";
    string_escape_codes[179] = "\\xb3";
    string_escape_codes[180] = "\\xb4";
    string_escape_codes[181] = "\\xb5";
    string_escape_codes[182] = "\\xb6";
    string_escape_codes[183] = "\\xb7";
    string_escape_codes[184] = "\\xb8";
    string_escape_codes[185] = "\\xb9";
    string_escape_codes[186] = "\\xba";
    string_escape_codes[187] = "\\xbb";
    string_escape_codes[188] = "\\xbc";
    string_escape_codes[189] = "\\xbd";
    string_escape_codes[190] = "\\xbe";
    string_escape_codes[191] = "\\xbf";
    string_escape_codes[192] = "\\xc0";
    string_escape_codes[193] = "\\xc1";
    string_escape_codes[194] = "\\xc2";
    string_escape_codes[195] = "\\xc3";
    string_escape_codes[196] = "\\xc4";
    string_escape_codes[197] = "\\xc5";
    string_escape_codes[198] = "\\xc6";
    string_escape_codes[199] = "\\xc7";
    string_escape_codes[200] = "\\xc8";
    string_escape_codes[201] = "\\xc9";
    string_escape_codes[202] = "\\xca";
    string_escape_codes[203] = "\\xcb";
    string_escape_codes[204] = "\\xcc";
    string_escape_codes[205] = "\\xcd";
    string_escape_codes[206] = "\\xce";
    string_escape_codes[207] = "\\xcf";
    string_escape_codes[208] = "\\xd0";
    string_escape_codes[209] = "\\xd1";
    string_escape_codes[210] = "\\xd2";
    string_escape_codes[211] = "\\xd3";
    string_escape_codes[212] = "\\xd4";
    string_escape_codes[213] = "\\xd5";
    string_escape_codes[214] = "\\xd6";
    string_escape_codes[215] = "\\xd7";
    string_escape_codes[216] = "\\xd8";
    string_escape_codes[217] = "\\xd9";
    string_escape_codes[218] = "\\xda";
    string_escape_codes[219] = "\\xdb";
    string_escape_codes[220] = "\\xdc";
    string_escape_codes[221] = "\\xdd";
    string_escape_codes[222] = "\\xde";
    string_escape_codes[223] = "\\xdf";
    string_escape_codes[224] = "\\xe0";
    string_escape_codes[225] = "\\xe1";
    string_escape_codes[226] = "\\xe2";
    string_escape_codes[227] = "\\xe3";
    string_escape_codes[228] = "\\xe4";
    string_escape_codes[229] = "\\xe5";
    string_escape_codes[230] = "\\xe6";
    string_escape_codes[231] = "\\xe7";
    string_escape_codes[232] = "\\xe8";
    string_escape_codes[233] = "\\xe9";
    string_escape_codes[234] = "\\xea";
    string_escape_codes[235] = "\\xeb";
    string_escape_codes[236] = "\\xec";
    string_escape_codes[237] = "\\xed";
    string_escape_codes[238] = "\\xee";
    string_escape_codes[239] = "\\xef";
    string_escape_codes[240] = "\\xf0";
    string_escape_codes[241] = "\\xf1";
    string_escape_codes[242] = "\\xf2";
    string_escape_codes[243] = "\\xf3";
    string_escape_codes[244] = "\\xf4";
    string_escape_codes[245] = "\\xf5";
    string_escape_codes[246] = "\\xf6";
    string_escape_codes[247] = "\\xf7";
    string_escape_codes[248] = "\\xf8";
    string_escape_codes[249] = "\\xf9";
    string_escape_codes[250] = "\\xfa";
    string_escape_codes[251] = "\\xfb";
    string_escape_codes[252] = "\\xfc";
    string_escape_codes[253] = "\\xfd";
    string_escape_codes[254] = "\\xfe";
    string_escape_codes[255] = "\\xff";
    string_escape_codes
}

/// Writes `value` in base 10, left-padded with zeros to at least `width` digits.
pub(crate) fn write_zero_padded<W: fmt::Write>(
    output: &mut W,
    value: u64,
    width: usize,
) -> fmt::Result {
    // Pads every fixed-width timestamp field, and fractional seconds up to nanoseconds, in one
    // write.
    const ZEROS: &str = "00000000";
    let mut buffer = itoa::Buffer::new();
    let digits = buffer.format(value);
    let mut padding = width.saturating_sub(digits.len());
    while padding > 0 {
        let chunk = padding.min(ZEROS.len());
        output.write_str(&ZEROS[..chunk])?;
        padding -= chunk;
    }
    output.write_str(digits)
}

/// Views bytes the caller knows to be ASCII as a `str`.
fn ascii_str(bytes: &[u8]) -> Result<&str, fmt::Error> {
    std::str::from_utf8(bytes).map_err(|_| fmt::Error)
}

/// The capacity of the stack buffer that [`display_buffered`] fills before writing to the
/// `Formatter`.
const DISPLAY_CHUNK_LEN: usize = 1024;

/// A `fmt::Write` sink that collects text in a fixed-size stack buffer and writes the buffered text
/// to a `Formatter` when the next `&str` does not fit in the remaining space. A `&str` too large for
/// an empty buffer is written to the `Formatter` directly.
pub(crate) struct DisplayBuffer<'a, 'f> {
    chunk: ArrayString<DISPLAY_CHUNK_LEN>,
    output: &'a mut fmt::Formatter<'f>,
}

impl DisplayBuffer<'_, '_> {
    /// Writes any buffered text to the `Formatter`.
    fn flush(&mut self) -> fmt::Result {
        if !self.chunk.is_empty() {
            self.output.write_str(&self.chunk)?;
            self.chunk.clear();
        }
        Ok(())
    }

    /// Flushes the buffered text, then buffers `s` or, if it is larger than the buffer, writes it
    /// directly.
    #[cold]
    #[inline(never)]
    fn flush_and_write(&mut self, s: &str) -> fmt::Result {
        self.flush()?;
        if s.len() > DISPLAY_CHUNK_LEN {
            return self.output.write_str(s);
        }
        self.chunk.try_push_str(s).map_err(|_| fmt::Error)
    }
}

impl fmt::Write for DisplayBuffer<'_, '_> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        match self.chunk.try_push_str(s) {
            Ok(()) => Ok(()),
            Err(_) => self.flush_and_write(s),
        }
    }
}

/// Implements `Display` for an `Element`, `Value`, `List`, `SExp`, or `Struct`. `format` writes
/// into a [`DisplayBuffer`], a concrete sink that lets every nested write inline rather than
/// calling through `Formatter`'s `dyn Write`. The text reaches `f` in chunks of at most
/// [`DISPLAY_CHUNK_LEN`] bytes (or as a single larger `&str`, such as a long string's unescaped
/// text), so memory use is bounded regardless of the value's size.
pub(crate) fn display_buffered(
    f: &mut fmt::Formatter<'_>,
    format: impl FnOnce(&mut FmtValueFormatter<'_, DisplayBuffer<'_, '_>>) -> IonResult<()>,
) -> fmt::Result {
    let mut buffer = DisplayBuffer {
        chunk: ArrayString::new(),
        output: f,
    };
    format(&mut FmtValueFormatter::new(&mut buffer)).map_err(|_| fmt::Error)?;
    buffer.flush()
}

/// Provides a text formatter for Ion values.
///
/// This is the shared implementation behind the `Display` impls of `Element` and its parts and
/// behind the text writer's symbol, string, and clob encoding.
pub struct FmtValueFormatter<'a, W: fmt::Write> {
    pub(crate) output: &'a mut W,
}

impl<'a, W: fmt::Write> FmtValueFormatter<'a, W> {
    pub fn new(output: &'a mut W) -> Self {
        Self { output }
    }
}

/// A shim that allows values to be formatted to implementations of `io::Write` instead of being limited
/// to implementations of `fmt::Write`.
pub struct IoValueFormatter<W: io::Write> {
    output: W,
    // If an I/O error happens while writing the formatted text to output, `write_str` returns a
    // `fmt::Error` (which contains no information). `result` holds the first such I/O error, as an
    // `IonError::Io`; later writes do not clear it. This result can then be inspected for the
    // cause. This approach is similar to the one the Rust std library uses internally. See:
    // https://github.com/rust-lang/rust/blob/cc4dd6fc9f1a5c798df269933c7e442b79661a86/library/std/src/io/mod.rs#L1665
    result: IonResult<()>,
}

impl<W: io::Write> IoValueFormatter<W> {
    pub fn new(output: W) -> Self {
        Self {
            output,
            result: Ok(()),
        }
    }

    /// Returns the first I/O error any write hit, as an `IonError::Io`, or `Ok(())` if every write
    /// succeeded.
    pub fn into_result(self) -> IonResult<()> {
        self.result
    }

    pub fn value_formatter(&mut self) -> FmtValueFormatter<'_, Self> {
        FmtValueFormatter::new(self)
    }
}

impl<W: io::Write> fmt::Write for IoValueFormatter<W> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        match self.output.write_all(s.as_bytes()) {
            Ok(()) => Ok(()),
            Err(e) => {
                if self.result.is_ok() {
                    self.result = Err(e.into());
                }
                Err(fmt::Error)
            }
        }
    }
}

impl<W: fmt::Write> FmtValueFormatter<'_, W> {
    /// Returns `true` if the provided `token`'s text is an 'identifier'. That is, the text starts
    /// with a `$`, `_` or ASCII letter and is followed by a sequence of `$`, `_`, or ASCII letters
    /// and numbers. Examples:
    /// * `firstName`
    /// * `first_name`
    /// * `name_1`
    /// * `$name`
    ///
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
        match token.as_bytes() {
            [b'$', digits @ ..] => !digits.is_empty() && digits.iter().all(u8::is_ascii_digit),
            _ => false,
        }
    }

    /// Returns `true` if this token's text resembles an Ion version marker (e.g. `$ion_1_1`).
    /// Without quotes, such text at the top level reads as a version marker, not a symbol.
    fn token_resembles_version_marker(token: &str) -> bool {
        let is_digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
        token
            .strip_prefix("$ion_")
            .and_then(|version| version.split_once('_'))
            .is_some_and(|(major, minor)| is_digits(major) && is_digits(minor))
    }

    pub(crate) fn format_symbol_token<A: AsRawSymbolRef>(&mut self, token: A) -> IonResult<()> {
        use RawSymbolRef::*;
        let write_result = match token.as_raw_symbol_ref() {
            SymbolId(sid) => write!(self.output, "${sid}"),
            // If the text could be mistaken for a keyword, symbol ID, or version marker, wrap it in
            // single quotes.
            Text(text)
                if Self::token_is_keyword(text)
                    || Self::token_resembles_symbol_id(text)
                    || Self::token_resembles_version_marker(text) =>
            {
                write!(self.output, "'{text}'")
            }
            // If the text is an identifier, it doesn't require quotes.
            Text(text) if Self::token_is_identifier(text) => write!(self.output, "{text}"),
            // Any other text has its escape sequences substituted and is wrapped in quotes.
            Text(text) => {
                // Write the symbol text using quotes and escaping any characters that require it.
                write!(self.output, "\'")?;
                self.format_escaped_text_body(text)?;
                write!(self.output, "\'")
            }
        };
        // Convert the fmt::Result into an IonResult
        Ok(write_result?)
    }

    /// Writes the body (i.e. no start or end delimiters) of a string or symbol with any illegal
    /// characters escaped.
    // Always inlined so that each string or quoted symbol write runs the escape scan without a
    // further call.
    #[inline(always)]
    pub(crate) fn format_escaped_text_body<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
        let mut start = 0usize;
        let text = value.as_ref();
        for (byte_index, character) in text.char_indices() {
            let escaped = match character {
                '\n' => r"\n",
                '\r' => r"\r",
                '\t' => r"\t",
                '\\' => r"\\",
                '"' => r#"\""#,
                '\'' => r"\'",
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
            write!(self.output, "{}{}", &text[start..byte_index], escaped)?;
            // Update `start` to point to the first byte after the end of this character.
            start = byte_index + character.len_utf8();
        }
        write!(self.output, "{}", &text[start..])?;
        Ok(())
    }

    pub(crate) fn format_annotations(&mut self, annotations: &Annotations) -> IonResult<()> {
        for annotation in annotations {
            self.format_symbol(annotation)?;
            write!(self.output, "::")?;
        }
        Ok(())
    }

    pub fn format_null(&mut self, ion_type: IonType) -> IonResult<()> {
        use IonType::*;
        let null_text = match ion_type {
            Null => "null",
            Bool => "null.bool",
            Int => "null.int",
            Float => "null.float",
            Decimal => "null.decimal",
            Timestamp => "null.timestamp",
            Symbol => "null.symbol",
            String => "null.string",
            Blob => "null.blob",
            Clob => "null.clob",
            List => "null.list",
            SExp => "null.sexp",
            Struct => "null.struct",
        };
        self.output.write_str(null_text)?;
        Ok(())
    }

    pub fn format_bool(&mut self, value: bool) -> IonResult<()> {
        let bool_text = match value {
            true => "true",
            false => "false",
        };
        self.output.write_str(bool_text)?;
        Ok(())
    }

    pub fn format_integer(&mut self, value: &Int) -> IonResult<()> {
        value.format_text(self.output)?;
        Ok(())
    }

    pub fn format_float(&mut self, value: f64) -> IonResult<()> {
        if value.is_nan() {
            self.output.write_str("nan")?;
            return Ok(());
        }

        if value.is_infinite() {
            if value.is_sign_positive() {
                self.output.write_str("+inf")?;
            } else {
                self.output.write_str("-inf")?;
            }
            return Ok(());
        }

        // The {:e} formatter provided by the Display trait writes floats using scientific
        // notation. It works for all floating point values except -0.0 (it drops the sign).
        // See: https://github.com/rust-lang/rust/issues/20596
        if value == 0.0f64 && value.is_sign_negative() {
            self.output.write_str("-0e0")?;
            return Ok(());
        }

        write!(self.output, "{value:e}")?;
        Ok(())
    }

    pub fn format_decimal(&mut self, value: &Decimal) -> IonResult<()> {
        value.format_text(self.output)?;
        Ok(())
    }

    pub fn format_timestamp(&mut self, value: &Timestamp) -> IonResult<()> {
        value.format(self.output)
    }

    pub fn format_symbol<A: AsRawSymbolRef>(&mut self, value: A) -> IonResult<()> {
        self.format_symbol_token(value)?;
        Ok(())
    }

    // Always inlined so that a caller writing a string runs the escape scan in its own body. The
    // recursive `format_value` calls it in a `cold_path!` instead.
    #[inline(always)]
    pub fn format_string<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
        self.output.write_str("\"")?;
        self.format_escaped_text_body(value)?;
        self.output.write_str("\"")?;
        Ok(())
    }

    pub fn format_clob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        let bytes: &[u8] = value.as_ref();
        self.output.write_str("{{\"")?;
        // `unwritten` is the start of the bytes that have been scanned but not yet written. Every
        // byte without an entry in `STRING_ESCAPE_CODES` is printable ASCII, so each unwritten run
        // is valid UTF-8.
        let mut unwritten = 0usize;
        for (index, byte) in bytes.iter().copied().enumerate() {
            let escape = STRING_ESCAPE_CODES[byte as usize];
            if escape.is_empty() {
                continue;
            }
            if unwritten < index {
                self.output
                    .write_str(ascii_str(&bytes[unwritten..index])?)?;
            }
            self.output.write_str(escape)?;
            unwritten = index + 1;
        }
        self.output.write_str(ascii_str(&bytes[unwritten..])?)?;
        self.output.write_str("\"}}")?;
        Ok(())
    }

    // Keeps the `encoded` chunk buffer out of the stack frames of recursive value formatting.
    #[inline(never)]
    pub fn format_blob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        // Encoding a multiple of 3 bytes at a time produces no padding until the final chunk, so
        // the concatenated chunks are identical to encoding the whole blob at once.
        const INPUT_CHUNK_LEN: usize = 3 * 256;
        const OUTPUT_CHUNK_LEN: usize = INPUT_CHUNK_LEN / 3 * 4;
        let mut encoded = [0u8; OUTPUT_CHUNK_LEN];
        self.output.write_str("{{")?;
        for chunk in value.as_ref().chunks(INPUT_CHUNK_LEN) {
            let len = base64::encode_config_slice(chunk, base64::STANDARD, &mut encoded);
            self.output.write_str(ascii_str(&encoded[..len])?)?;
        }
        self.output.write_str("}}")?;
        Ok(())
    }

    /// Writes `element`, including its annotations, recursing into containers through this
    /// formatter rather than through `Display`. Each `Display` call puts a [`DISPLAY_CHUNK_LEN`]
    /// buffer on the stack, so nested values must not go through `Display`.
    pub(crate) fn format_element(&mut self, element: &Element) -> IonResult<()> {
        self.format_annotations(element.annotations())?;
        self.format_value(element.value())
    }

    /// Writes `value` without annotations. This method is on the recursive path, so a callee with a
    /// large stack local must stay out of line.
    pub(crate) fn format_value(&mut self, value: &Value) -> IonResult<()> {
        match value {
            Value::Null(ion_type) => self.format_null(*ion_type),
            Value::Bool(bool) => self.format_bool(*bool),
            Value::Int(integer) => self.format_integer(integer),
            Value::Float(float) => self.format_float(*float),
            Value::Decimal(decimal) => self.format_decimal(decimal),
            Value::Timestamp(timestamp) => self.format_timestamp(timestamp),
            Value::Symbol(symbol) => self.format_symbol(symbol),
            Value::String(string) => cold_path! { self.format_string(string.text()) },
            Value::Clob(clob) => self.format_clob(clob),
            Value::Blob(blob) => self.format_blob(blob),
            Value::List(sequence) => self.format_list(sequence),
            Value::SExp(sequence) => self.format_sexp(sequence),
            Value::Struct(struct_) => self.format_struct(struct_),
        }
    }

    pub(crate) fn format_struct(&mut self, value: &Struct) -> IonResult<()> {
        self.output.write_str("{")?;
        let mut fields = value.fields();
        if let Some((field_name, field_value)) = fields.next() {
            self.format_field(field_name, field_value)?;
            for (field_name, field_value) in fields {
                self.output.write_str(", ")?;
                self.format_field(field_name, field_value)?;
            }
        }
        self.output.write_str("}")?;
        Ok(())
    }

    fn format_field(&mut self, name: &Symbol, value: &Element) -> IonResult<()> {
        self.format_symbol(name.as_raw_symbol_ref())?;
        self.output.write_str(": ")?;
        self.format_element(value)
    }

    pub(crate) fn format_sexp<S: AsRef<Sequence>>(&mut self, sequence: S) -> IonResult<()> {
        self.output.write_str("(")?;
        self.format_sequence_elements(sequence, " ")?;
        self.output.write_str(")")?;
        Ok(())
    }

    pub(crate) fn format_list<S: AsRef<Sequence>>(&mut self, sequence: S) -> IonResult<()> {
        self.output.write_str("[")?;
        self.format_sequence_elements(sequence, ", ")?;
        self.output.write_str("]")?;
        Ok(())
    }

    fn format_sequence_elements<S: AsRef<Sequence>>(
        &mut self,
        sequence: S,
        delimiter: &'static str,
    ) -> IonResult<()> {
        let mut elements = sequence.as_ref().elements();
        if let Some(element) = elements.next() {
            self.format_element(element)?;
            for element in elements {
                self.output.write_str(delimiter)?;
                self.format_element(element)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod formatter_test {
    use crate::text::text_formatter::FmtValueFormatter;
    use crate::{ion_list, ion_sexp, ion_struct, IonResult, IonType, Timestamp};

    fn formatter<F>(mut f: F, expected: &str)
    where
        F: for<'a> FnMut(&mut FmtValueFormatter<'a, String>) -> IonResult<()>,
    {
        let mut actual = String::new();
        let mut ivf = FmtValueFormatter {
            output: &mut actual,
        };

        let _ = f(&mut ivf);
        assert_eq!(actual, expected)
    }

    #[test]
    fn test_format_null() -> IonResult<()> {
        formatter(|ivf| ivf.format_null(IonType::Symbol), "null.symbol");
        formatter(|ivf| ivf.format_null(IonType::Null), "null");
        Ok(())
    }

    #[test]
    fn test_format_bool() -> IonResult<()> {
        formatter(|ivf| ivf.format_bool(true), "true");
        formatter(|ivf| ivf.format_bool(false), "false");
        Ok(())
    }

    #[test]
    fn test_format_i64() -> IonResult<()> {
        formatter(|ivf| ivf.format_integer(&4i64.into()), "4");
        formatter(|ivf| ivf.format_integer(&(-4i64).into()), "-4");
        Ok(())
    }

    #[test]
    fn test_format_i128() -> IonResult<()> {
        formatter(|ivf| ivf.format_integer(&4i128.into()), "4");
        formatter(|ivf| ivf.format_integer(&(-4i128).into()), "-4");
        Ok(())
    }

    #[test]
    fn test_format_float() -> IonResult<()> {
        formatter(|ivf| ivf.format_float(400f64), "4e2");
        formatter(|ivf| ivf.format_float(-400f64), "-4e2");
        Ok(())
    }

    #[test]
    fn test_format_timestamp() -> IonResult<()> {
        let timestamp = Timestamp::with_year(2000)
            .with_month(8)
            .build()
            .expect("building timestamp failed");
        formatter(|ivf| ivf.format_timestamp(&timestamp), "2000-08T");
        Ok(())
    }

    #[test]
    fn test_format_symbol() -> IonResult<()> {
        formatter(|ivf| ivf.format_symbol("foo"), "foo");
        Ok(())
    }

    #[test]
    fn test_format_string() -> IonResult<()> {
        formatter(|ivf| ivf.format_string("bar"), "\"bar\"");

        // Test some string escapes
        formatter(|ivf| ivf.format_string("/"), "\"/\""); // slash is not escaped
        formatter(|ivf| ivf.format_string("\\"), "\"\\\\\""); // backslash is escaped
        formatter(|ivf| ivf.format_string("'"), "\"\\'\""); // single quote is escaped
        formatter(|ivf| ivf.format_string("\n"), "\"\\n\""); // newline is escaped
        formatter(|ivf| ivf.format_string("\r"), "\"\\r\""); // carriage return is escaped
        formatter(|ivf| ivf.format_string("\t"), "\"\\t\""); // tab is escaped
        formatter(|ivf| ivf.format_string("\0"), "\"\\0\""); // NUL is escaped

        Ok(())
    }

    #[test]
    fn test_format_blob() -> IonResult<()> {
        formatter(|ivf| ivf.format_blob("hello".as_bytes()), "{{aGVsbG8=}}");
        Ok(())
    }

    #[test]
    fn test_format_clob() -> IonResult<()> {
        formatter(
            |ivf| ivf.format_clob("❤️".as_bytes()),
            "{{\"\\xe2\\x9d\\xa4\\xef\\xb8\\x8f\"}}",
        );
        Ok(())
    }

    #[test]
    fn test_format_struct() -> IonResult<()> {
        formatter(
            |ivf| ivf.format_struct(&ion_struct! {"greetings": "hello"}),
            "{greetings: \"hello\"}",
        );
        Ok(())
    }

    #[test]
    fn test_format_sexp() -> IonResult<()> {
        formatter(
            |ivf| ivf.format_sexp(ion_sexp!("hello" 5 true)),
            "(\"hello\" 5 true)",
        );
        Ok(())
    }

    #[test]
    fn test_format_list() -> IonResult<()> {
        formatter(
            |ivf| ivf.format_list(ion_list!["hello", 5, true]),
            "[\"hello\", 5, true]",
        );
        Ok(())
    }
}

#[cfg(test)]
mod fast_path_tests {
    use super::*;
    use crate::{Element, IonResult};
    use rstest::rstest;

    #[rstest]
    #[case::zero_no_width(0, 0, "0")]
    #[case::pads(7, 2, "07")]
    #[case::exact_width(12, 2, "12")]
    #[case::wider_than_width(12345, 4, "12345")]
    #[case::year(2000, 4, "2000")]
    #[case::small_year(1, 4, "0001")]
    #[case::padding_longer_than_zeros(5, 40, "0000000000000000000000000000000000000005")]
    fn zero_padded(
        #[case] value: u64,
        #[case] width: usize,
        #[case] expected: &str,
    ) -> fmt::Result {
        let mut output = String::new();
        write_zero_padded(&mut output, value, width)?;
        assert_eq!(output, expected);
        Ok(())
    }

    #[rstest]
    #[case::zero("0")]
    #[case::one("1")]
    #[case::negative_one("-1")]
    #[case::i64_max("9223372036854775807")]
    #[case::i64_min("-9223372036854775808")]
    #[case::u64_max("18446744073709551615")]
    #[case::u64_max_plus_one("18446744073709551616")]
    #[case::i128_max("170141183460469231731687303715884105727")]
    #[case::i128_min("-170141183460469231731687303715884105728")]
    #[case::u128_max("340282366920938463463374607431768211455")]
    #[case::beyond_u128("-340282366920938463463374607431768211456")]
    fn integer_text_round_trips(#[case] text: &str) -> IonResult<()> {
        let element = Element::read_one(text)?;
        let mut output = String::new();
        FmtValueFormatter::new(&mut output).format_integer(element.expect_int()?)?;
        assert_eq!(output, text);
        Ok(())
    }

    /// Ion text for a list large enough to reach a `Display` sink in several chunks. The text is
    /// already in `Display`'s output form.
    fn large_list_text() -> String {
        format!("[{}]", vec!["\"abc\""; 2000].join(", "))
    }

    /// A sink that records each `write_str` separately and formats another `Element` from inside
    /// each one, re-entering `Display` between the outer value's chunks.
    struct ReentrantSink {
        chunks: Vec<String>,
        nested: Element,
        nested_texts: Vec<String>,
    }

    impl ReentrantSink {
        fn new(nested: Element) -> Self {
            Self {
                chunks: Vec::new(),
                nested,
                nested_texts: Vec::new(),
            }
        }
    }

    impl fmt::Write for ReentrantSink {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            self.nested_texts.push(self.nested.to_string());
            self.chunks.push(s.to_owned());
            Ok(())
        }
    }

    #[test]
    fn display_tolerates_reentrant_sink() -> IonResult<()> {
        let text = large_list_text();
        let outer = Element::read_one(&text)?;
        let mut sink = ReentrantSink::new(Element::read_one("(x y)")?);
        fmt::Write::write_fmt(&mut sink, format_args!("{outer}"))?;
        assert!(sink.chunks.len() > 1);
        assert_eq!(sink.chunks.concat(), text);
        assert!(sink.nested_texts.iter().all(|nested| nested == "(x y)"));
        Ok(())
    }

    /// A sink that records each `write_str` separately.
    #[derive(Default)]
    struct ChunkSink(Vec<String>);

    impl fmt::Write for ChunkSink {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            self.0.push(s.to_owned());
            Ok(())
        }
    }

    #[test]
    fn display_emits_bounded_chunks() -> IonResult<()> {
        // The longest `&str` that formatting `large_list_text()` writes (`abc`).
        const MAX_PIECE_LEN: usize = 3;
        let text = large_list_text();
        let element = Element::read_one(&text)?;
        let mut sink = ChunkSink::default();
        fmt::Write::write_fmt(&mut sink, format_args!("{element}"))?;
        let chunks = &sink.0;
        assert!(chunks.len() > 1);
        assert!(chunks.iter().all(|chunk| chunk.len() <= DISPLAY_CHUNK_LEN));
        // Every chunk but the last is flushed only when the next piece does not fit.
        assert!(chunks[..chunks.len() - 1]
            .iter()
            .all(|chunk| chunk.len() > DISPLAY_CHUNK_LEN - MAX_PIECE_LEN));
        assert_eq!(chunks.concat(), text);
        Ok(())
    }

    #[test]
    fn display_writes_oversized_text_directly() -> IonResult<()> {
        let body = "a".repeat(DISPLAY_CHUNK_LEN + 1);
        let element = Element::string(body.as_str());
        let mut sink = ChunkSink::default();
        fmt::Write::write_fmt(&mut sink, format_args!("{element}"))?;
        assert_eq!(sink.0, ["\"", body.as_str(), "\""]);
        Ok(())
    }

    /// A sink that accepts `remaining_writes` calls to `write_str` and fails every call after them,
    /// counting every call in `attempts`.
    struct FailingFmtSink {
        remaining_writes: usize,
        attempts: usize,
    }

    impl fmt::Write for FailingFmtSink {
        fn write_str(&mut self, _s: &str) -> fmt::Result {
            self.attempts += 1;
            if self.remaining_writes == 0 {
                return Err(fmt::Error);
            }
            self.remaining_writes -= 1;
            Ok(())
        }
    }

    #[rstest]
    #[case::final_flush_fails("(x y)".to_owned(), 0)]
    #[case::flush_during_formatting_fails(large_list_text(), 1)]
    fn display_reports_sink_failure(
        #[case] text: String,
        #[case] accepted_writes: usize,
    ) -> IonResult<()> {
        let element = Element::read_one(&text)?;
        let mut sink = FailingFmtSink {
            remaining_writes: accepted_writes,
            attempts: 0,
        };
        assert!(fmt::Write::write_fmt(&mut sink, format_args!("{element}")).is_err());
        // The first failed write must end formatting; any later write means the error was dropped.
        assert_eq!(sink.attempts, accepted_writes + 1);
        Ok(())
    }

    /// The per-byte clob encoder that the run-based `format_clob` must match.
    fn reference_clob(bytes: &[u8]) -> String {
        let mut body = String::new();
        for &byte in bytes {
            let escape = STRING_ESCAPE_CODES[byte as usize];
            if escape.is_empty() {
                body.push(byte as char);
            } else {
                body.push_str(escape);
            }
        }
        format!("{{{{\"{body}\"}}}}")
    }

    fn clob_text(bytes: &[u8]) -> IonResult<String> {
        let mut output = String::new();
        FmtValueFormatter::new(&mut output).format_clob(bytes)?;
        Ok(output)
    }

    #[test]
    fn clob_matches_reference_for_every_byte() -> IonResult<()> {
        for byte in 0..=u8::MAX {
            let bytes = [b'a', b'b', byte, b'c', b'd'];
            assert_eq!(
                clob_text(&bytes)?,
                reference_clob(&bytes),
                "byte {byte:#04x}"
            );
        }
        Ok(())
    }

    #[rstest]
    #[case::empty(b"", r#"{{""}}"#)]
    #[case::no_escapes(b"abc", r#"{{"abc"}}"#)]
    #[case::mixed(b"a\"b\\c\nd", r#"{{"a\"b\\c\nd"}}"#)]
    #[case::adjacent_escapes(b"\"\"\\\\", r#"{{"\"\"\\\\"}}"#)]
    #[case::leading_and_trailing_escapes(b"\x00ab\xff", r#"{{"\0ab\xff"}}"#)]
    fn clob_text_matches_expected(#[case] bytes: &[u8], #[case] expected: &str) -> IonResult<()> {
        assert_eq!(clob_text(bytes)?, expected);
        assert_eq!(reference_clob(bytes), expected);
        Ok(())
    }

    #[rstest]
    fn blob_matches_single_shot_base64(
        #[values(0, 1, 2, 3, 4, 5, 767, 768, 769, 770, 1536, 2000)] len: usize,
    ) -> IonResult<()> {
        let bytes: Vec<u8> = (0..len).map(|i| (i * 31 % 256) as u8).collect();
        let mut output = String::new();
        FmtValueFormatter::new(&mut output).format_blob(&bytes)?;
        assert_eq!(output, format!("{{{{{}}}}}", base64::encode(&bytes)));
        Ok(())
    }
}
