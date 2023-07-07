use crate::element::{Annotations, Sequence, Struct};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{Decimal, Int, IonResult, IonType, RawSymbolTokenRef, Timestamp};

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

/// Provides a text formatter for Ion values
/// This is used with the Display implementation of `OwnedElement`
pub struct IonValueFormatter<'a, W: std::fmt::Write> {
    pub(crate) output: &'a mut W,
}

impl<'a, W: std::fmt::Write> IonValueFormatter<'a, W> {
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

    pub(crate) fn format_symbol_token<A: AsRawSymbolTokenRef>(
        &mut self,
        token: A,
    ) -> IonResult<()> {
        match token.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(sid) => write!(self.output, "${sid}")?,
            RawSymbolTokenRef::Text(text)
                if Self::token_is_keyword(text) || Self::token_resembles_symbol_id(text) =>
            {
                // Write the symbol text in single quotes
                write!(self.output, "'{text}'")?;
            }
            RawSymbolTokenRef::Text(text) if Self::token_is_identifier(text) => {
                // Write the symbol text without quotes
                write!(self.output, "{text}")?
            }
            RawSymbolTokenRef::Text(text) => {
                // Write the symbol text using quotes and escaping any characters that require it.
                write!(self.output, "\'")?;
                self.format_escaped_text_body(text)?;
                write!(self.output, "\'")?;
            }
        };
        Ok(())
    }

    /// Writes the body (i.e. no start or end delimiters) of a string or symbol with any illegal
    /// characters escaped.
    pub(crate) fn format_escaped_text_body<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
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
        write!(self.output, "{null_text}")?;
        Ok(())
    }

    pub fn format_bool(&mut self, value: bool) -> IonResult<()> {
        let bool_text = match value {
            true => "true",
            false => "false",
        };
        write!(self.output, "{bool_text}")?;
        Ok(())
    }

    pub fn format_integer(&mut self, value: &Int) -> IonResult<()> {
        write!(self.output, "{value}")?;
        Ok(())
    }

    pub fn format_float(&mut self, value: f64) -> IonResult<()> {
        if value.is_nan() {
            write!(self.output, "nan")?;
            return Ok(());
        }

        if value.is_infinite() {
            if value.is_sign_positive() {
                write!(self.output, "+inf")?;
            } else {
                write!(self.output, "-inf")?;
            }
            return Ok(());
        }

        // The {:e} formatter provided by the Display trait writes floats using scientific
        // notation. It works for all floating point values except -0.0 (it drops the sign).
        // See: https://github.com/rust-lang/rust/issues/20596
        if value == 0.0f64 && value.is_sign_negative() {
            write!(self.output, "-0e0")?;
            return Ok(());
        }

        write!(self.output, "{value:e}")?;
        Ok(())
    }

    pub fn format_decimal(&mut self, value: &Decimal) -> IonResult<()> {
        write!(self.output, "{value}")?;
        Ok(())
    }

    pub fn format_timestamp(&mut self, value: &Timestamp) -> IonResult<()> {
        value.format(self.output)
    }

    pub(crate) fn format_symbol<A: AsRawSymbolTokenRef>(&mut self, value: A) -> IonResult<()> {
        self.format_symbol_token(value)?;
        Ok(())
    }

    pub(crate) fn format_string<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
        write!(self.output, "\"")?;
        self.format_escaped_text_body(value)?;
        write!(self.output, "\"")?;
        Ok(())
    }

    pub(crate) fn format_clob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        // clob_value to be written based on defined STRING_ESCAPE_CODES.
        const NUM_DELIMITER_BYTES: usize = 4; // {{}}
        const NUM_HEX_BYTES_PER_BYTE: usize = 4; // \xHH

        let value: &[u8] = value.as_ref();

        // Set aside enough memory to hold a clob containing all hex-encoded bytes
        let mut clob_value =
            String::with_capacity((value.len() * NUM_HEX_BYTES_PER_BYTE) + NUM_DELIMITER_BYTES);

        for byte in value.iter().copied() {
            let c = byte as char;
            let escaped_byte = &STRING_ESCAPE_CODES[c as usize];
            if !escaped_byte.is_empty() {
                clob_value.push_str(escaped_byte);
            } else {
                clob_value.push(c);
            }
        }
        write!(self.output, "{{{{\"{clob_value}\"}}}}")?;
        Ok(())
    }

    pub(crate) fn format_blob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        write!(self.output, "{{{{{}}}}}", base64::encode(value))?;
        Ok(())
    }

    pub(crate) fn format_struct(&mut self, value: &Struct) -> IonResult<()> {
        write!(self.output, "{{")?;
        let mut peekable_itr = value.fields().peekable();
        while let Some((field_name, field_value)) = peekable_itr.next() {
            self.format_symbol(field_name.as_raw_symbol_token_ref())?;
            write!(self.output, ": {field_value}")?;
            if peekable_itr.peek().is_some() {
                write!(self.output, ", ")?;
            }
        }
        write!(self.output, "}}")?;
        Ok(())
    }

    pub(crate) fn format_sexp<S: AsRef<Sequence>>(&mut self, sequence: S) -> IonResult<()> {
        write!(self.output, "(")?;
        self.format_sequence_elements(sequence, " ")?;
        write!(self.output, ")")?;
        Ok(())
    }

    pub(crate) fn format_list<S: AsRef<Sequence>>(&mut self, sequence: S) -> IonResult<()> {
        write!(self.output, "[")?;
        self.format_sequence_elements(sequence, ", ")?;
        write!(self.output, "]")?;
        Ok(())
    }

    fn format_sequence_elements<S: AsRef<Sequence>>(
        &mut self,
        sequence: S,
        delimiter: &'static str,
    ) -> IonResult<()> {
        let mut peekable_itr = sequence.as_ref().elements().peekable();
        while peekable_itr.peek().is_some() {
            let list_value = peekable_itr.next().unwrap();
            write!(self.output, "{list_value}")?;
            if peekable_itr.peek().is_some() {
                write!(self.output, "{}", delimiter)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod formatter_test {
    use crate::text::text_formatter::IonValueFormatter;
    use crate::{ion_list, ion_sexp, ion_struct, IonResult, IonType, Timestamp};
    use num_bigint::BigInt;

    fn formatter<F>(mut f: F, expected: &str)
    where
        F: for<'a> FnMut(&mut IonValueFormatter<'a, String>) -> IonResult<()>,
    {
        let mut actual = String::new();
        let mut ivf = IonValueFormatter {
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
    fn test_format_big_int() -> IonResult<()> {
        formatter(|ivf| ivf.format_integer(&BigInt::from(4).into()), "4");
        formatter(|ivf| ivf.format_integer(&BigInt::from(-4).into()), "-4");
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
