use crate::raw_symbol_ref::{AsRawSymbolRef, RawSymbolRef};
use crate::result::cold_error;
use crate::{Annotations, Sequence};
use crate::{Decimal, Int, Struct, Timestamp};
use crate::{IonResult, IonType};
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

/// Escape sequences for the bytes that string and symbol text must escape. An empty entry means the
/// byte is written as-is. Every escaped byte is ASCII, so scanning UTF-8 text a byte at a time
/// (rather than a `char` at a time) finds exactly the same escapes.
const TEXT_ESCAPE_CODES: [&str; 256] = text_escape_code_init();

const fn text_escape_code_init() -> [&'static str; 256] {
    let mut codes = [""; 256];
    codes[b'\n' as usize] = r"\n";
    codes[b'\r' as usize] = r"\r";
    codes[b'\t' as usize] = r"\t";
    codes[b'\\' as usize] = r"\\";
    codes[b'"' as usize] = r#"\""#;
    codes[b'\'' as usize] = r"\'";
    codes[0x00] = r"\0"; // NUL
    codes[0x07] = r"\a"; // alert BEL
    codes[0x08] = r"\b"; // backspace
    codes[0x0B] = r"\v"; // vertical tab
    codes[0x0C] = r"\f"; // form feed
    codes
}

const SWAR_LOW_BITS: u64 = u64::from_ne_bytes([0x01; 8]);
const SWAR_HIGH_BITS: u64 = u64::from_ne_bytes([0x80; 8]);

// The helpers below are SWAR (SIMD within a register) byte tests: the "has zero byte" and "has
// less than n" tricks from Sean Anderson's Bit Twiddling Hacks.

/// Returns a nonzero value if any byte of `word` is zero.
#[inline]
const fn swar_zero_byte_mask(word: u64) -> u64 {
    word.wrapping_sub(SWAR_LOW_BITS) & !word & SWAR_HIGH_BITS
}

/// Returns `true` if any byte of `word` may need escaping in string or symbol text: a byte below
/// `0x0E` (which covers every escaped control byte), a double quote, a single quote, or a
/// backslash. Bytes `0x01..=0x06` are false positives; the per-byte table resolves them.
///
/// The "has less than n" test for `0x0E` is exact only because `0x0E <= 0x80`.
#[inline]
const fn swar_may_need_escape(word: u64) -> bool {
    let below_0x0e = word.wrapping_sub(SWAR_LOW_BITS * 0x0E) & !word & SWAR_HIGH_BITS;
    let double_quote = swar_zero_byte_mask(word ^ (SWAR_LOW_BITS * b'"' as u64));
    let single_quote = swar_zero_byte_mask(word ^ (SWAR_LOW_BITS * b'\'' as u64));
    let backslash = swar_zero_byte_mask(word ^ (SWAR_LOW_BITS * b'\\' as u64));
    (below_0x0e | double_quote | single_quote | backslash) != 0
}

/// Returns `true` if `text` can be written as a symbol without quotes: it is an identifier (a `$`,
/// `_`, or ASCII letter followed by any number of `$`, `_`, or ASCII alphanumerics) that cannot be
/// mistaken for a keyword (`true`, `false`, `nan`, `null`), a symbol ID, or a version marker.
///
/// Text is quoted if it is `$` followed by one or more digits and nothing else (a symbol ID such as
/// `$12`; a lone `$` is not quoted) or if it is a version marker (`$ion_`, digits, `_`, digits,
/// such as `$ion_1_0`).
pub(crate) fn is_unquoted_symbol_text(text: &str) -> bool {
    let bytes = text.as_bytes();
    let Some(&first) = bytes.first() else {
        return false;
    };
    if first.is_ascii_digit() || !is_identifier_text(bytes) {
        return false;
    }
    match *bytes {
        [b'$', ref rest @ ..] => !resembles_symbol_id_or_version_marker(rest),
        [b't' | b'f' | b'n', ..] => !matches!(bytes, b"true" | b"false" | b"nan" | b"null"),
        _ => true,
    }
}

/// Returns `true` if `rest`, the text that follows a leading `$`, is one or more digits or is
/// `ion_` followed by one or more digits, `_`, and one or more digits.
fn resembles_symbol_id_or_version_marker(rest: &[u8]) -> bool {
    let is_digits = |bytes: &[u8]| !bytes.is_empty() && bytes.iter().all(u8::is_ascii_digit);
    match rest {
        [b'i', b'o', b'n', b'_', version @ ..] => version
            .iter()
            .position(|&byte| byte == b'_')
            .is_some_and(|split| is_digits(&version[..split]) && is_digits(&version[split + 1..])),
        _ => is_digits(rest),
    }
}

/// Returns a word with the high bit set in each byte of `word` that is in `low..=high`, where
/// `low <= high <= 0x7F`. The result is meaningful only if every byte of `word` is ASCII, so that
/// no byte's sum carries into the next; a non-ASCII byte gives meaningless bits, which the caller
/// discards by testing the high bits of `word` itself.
#[inline]
const fn swar_ascii_in_range(word: u64, low: u8, high: u8) -> u64 {
    let at_least_low = word.wrapping_add(SWAR_LOW_BITS * (0x80 - low as u64));
    let above_high = word.wrapping_add(SWAR_LOW_BITS * (0x7F - high as u64));
    at_least_low & !above_high & SWAR_HIGH_BITS
}

/// Returns `true` if every byte of `word` is `$`, `_`, or an ASCII alphanumeric.
#[inline]
const fn swar_is_identifier_word(word: u64) -> bool {
    // Setting bit 5 maps `A..=Z` onto `a..=z` and maps no other byte into that range.
    let letters = swar_ascii_in_range(word | (SWAR_LOW_BITS * 0x20), b'a', b'z');
    let digits = swar_ascii_in_range(word, b'0', b'9');
    let underscores = swar_ascii_in_range(word, b'_', b'_');
    let dollars = swar_ascii_in_range(word, b'$', b'$');
    // The ranges are meaningful only for an all-ASCII word, which the high-bit test checks.
    ((word & SWAR_HIGH_BITS) == 0) & ((letters | digits | underscores | dollars) == SWAR_HIGH_BITS)
}

/// Packs three bytes into the low lanes of a word whose other lanes hold an identifier byte.
#[inline]
const fn swar_short_word(first: u8, middle: u8, last: u8) -> u64 {
    (SWAR_LOW_BITS * b'a' as u64) & !0xFF_FFFF
        | first as u64
        | (middle as u64) << 8
        | (last as u64) << 16
}

/// Returns the last 8 bytes of `bytes` as a word or, for fewer bytes, a word in which every lane
/// holds a byte of `bytes` or `b'a'` (which needs no escaping and is an identifier byte). Every byte
/// of a shorter, nonempty `bytes` is in some lane; 4 to 7 bytes are packed as two overlapping
/// halves.
#[inline]
fn last_word(bytes: &[u8]) -> u64 {
    if let Some(word) = bytes.last_chunk::<8>() {
        return u64::from_ne_bytes(*word);
    }
    if let (Some(head), Some(tail)) = (bytes.first_chunk::<4>(), bytes.last_chunk::<4>()) {
        return u32::from_ne_bytes(*head) as u64 | (u32::from_ne_bytes(*tail) as u64) << 32;
    }
    match *bytes {
        [] => SWAR_LOW_BITS * b'a' as u64,
        [a] => swar_short_word(a, a, a),
        [a, b] => swar_short_word(a, a, b),
        [a, b, c, ..] => swar_short_word(a, b, c),
    }
}

/// Returns `true` if every byte of `bytes` is `$`, `_`, or an ASCII alphanumeric, testing a word
/// (8 bytes, or fewer packed into one word) at a time.
fn is_identifier_text(bytes: &[u8]) -> bool {
    if bytes.len() <= 8 {
        return swar_is_identifier_word(last_word(bytes));
    }
    let mut rest = bytes;
    while let Some((word, remaining)) = rest.split_first_chunk::<8>() {
        if !swar_is_identifier_word(u64::from_ne_bytes(*word)) {
            return false;
        }
        rest = remaining;
    }
    // The last word overlaps the bytes already tested.
    rest.is_empty() || swar_is_identifier_word(last_word(bytes))
}

const ZEROS: &str = "00000000000000000000000000000000";

/// Writes `value` in base 10, left-padded with zeros to at least `width` digits.
pub(crate) fn write_zero_padded<W: fmt::Write>(
    output: &mut W,
    value: u64,
    width: usize,
) -> fmt::Result {
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

/// Formats `magnitude` in base 10 into `buffer`.
#[inline]
pub(crate) fn format_u128(buffer: &mut itoa::Buffer, magnitude: u128) -> &str {
    match u64::try_from(magnitude) {
        Ok(magnitude) => buffer.format(magnitude),
        Err(_) => buffer.format(magnitude),
    }
}

/// Provides a text formatter for Ion values
/// This is used with the Display implementation of `OwnedElement`
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
    // If an I/O error happens while writing the formatted text to output, write!() will return
    // a `fmt::Error` (which contains no information). This result can then be inspected for the
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

    pub fn into_result(self) -> IonResult<()> {
        self.result
    }

    pub fn value_formatter(&mut self) -> FmtValueFormatter<'_, Self> {
        FmtValueFormatter::new(self)
    }
}

impl<W: io::Write> fmt::Write for IoValueFormatter<W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let io_result = self.output.write_all(s.as_bytes());
        match io_result {
            Ok(_) => {
                self.result = Ok(());
                Ok(())
            }
            Err(e) => {
                self.result = cold_error!(
                    encoding_error,
                    "I/O failure occurred during formatting: {e:?}"
                );
                Err(fmt::Error)
            }
        }
    }
}

impl<W: fmt::Write> FmtValueFormatter<'_, W> {
    // Always inlined so that the text writer's symbol and field name writes dispatch on the token
    // and write a SID or unquoted text without calling `format_symbol_token`.
    #[inline(always)]
    pub(crate) fn format_symbol_token<A: AsRawSymbolRef>(&mut self, token: A) -> IonResult<()> {
        use RawSymbolRef::*;
        match token.as_raw_symbol_ref() {
            SymbolId(sid) => {
                self.output.write_str("$")?;
                self.output.write_str(itoa::Buffer::new().format(sid))?;
            }
            // If the text is an identifier that can't be mistaken for a keyword, symbol ID, or
            // version marker, it doesn't require quotes.
            Text(text) if is_unquoted_symbol_text(text) => self.output.write_str(text)?,
            Text(text) => self.format_quoted_symbol_text(text)?,
        }
        Ok(())
    }

    /// Writes `text` wrapped in single quotes, with its escape sequences substituted.
    // Outlined so that inlining `format_symbol_token` does not copy the escape loop into each
    // symbol call site.
    #[inline(never)]
    fn format_quoted_symbol_text(&mut self, text: &str) -> IonResult<()> {
        self.output.write_str("'")?;
        self.format_escaped_text_body(text)?;
        self.output.write_str("'")?;
        Ok(())
    }

    /// Writes the body (i.e. no start or end delimiters) of a string or symbol with any illegal
    /// characters escaped. Runs of text that need no escaping are written with a single call.
    // Always inlined so that each string or quoted symbol write runs the escape scan without a
    // further call.
    #[inline(always)]
    pub(crate) fn format_escaped_text_body<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
        let text = value.as_ref();
        let bytes = text.as_bytes();
        // `unwritten` is the start of the text that has been scanned but not yet written.
        let mut unwritten = 0usize;
        let mut index = 0usize;
        while index < bytes.len() {
            let scan_end = match bytes[index..].first_chunk::<8>() {
                Some(word) if !swar_may_need_escape(u64::from_ne_bytes(*word)) => {
                    index += 8;
                    continue;
                }
                Some(_) => index + 8,
                // Fewer than 8 bytes remain. If the word ending at the last byte (which may
                // overlap bytes already scanned) needs no escaping, neither do they.
                None if !swar_may_need_escape(last_word(bytes)) => break,
                None => bytes.len(),
            };
            while index < scan_end {
                let escape = TEXT_ESCAPE_CODES[bytes[index] as usize];
                if !escape.is_empty() {
                    self.output.write_str(&text[unwritten..index])?;
                    self.output.write_str(escape)?;
                    unwritten = index + 1;
                }
                index += 1;
            }
        }
        self.output.write_str(&text[unwritten..])?;
        Ok(())
    }

    pub(crate) fn format_annotations(&mut self, annotations: &Annotations) -> IonResult<()> {
        for annotation in annotations {
            self.format_annotation(annotation)?;
        }
        Ok(())
    }

    /// Writes `annotation` followed by `::`.
    pub(crate) fn format_annotation<A: AsRawSymbolRef>(&mut self, annotation: A) -> IonResult<()> {
        self.format_symbol_token(annotation)?;
        self.output.write_str("::")?;
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

    pub fn format_string<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
        write!(self.output, "\"")?;
        self.format_escaped_text_body(value)?;
        write!(self.output, "\"")?;
        Ok(())
    }

    pub fn format_clob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
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

    pub fn format_blob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        write!(self.output, "{{{{{}}}}}", base64::encode(value))?;
        Ok(())
    }

    pub(crate) fn format_struct(&mut self, value: &Struct) -> IonResult<()> {
        write!(self.output, "{{")?;
        let mut peekable_itr = value.fields().peekable();
        while let Some((field_name, field_value)) = peekable_itr.next() {
            self.format_symbol(field_name.as_raw_symbol_ref())?;
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
                write!(self.output, "{delimiter}")?;
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

    /// The `char`-at-a-time escaper that the byte scan in `format_escaped_text_body` must match.
    fn reference_escaped_text_body(text: &str) -> String {
        let mut output = String::new();
        for character in text.chars() {
            match character {
                '\n' => output.push_str(r"\n"),
                '\r' => output.push_str(r"\r"),
                '\t' => output.push_str(r"\t"),
                '\\' => output.push_str(r"\\"),
                '"' => output.push_str(r#"\""#),
                '\'' => output.push_str(r"\'"),
                '\x00' => output.push_str(r"\0"),
                '\x07' => output.push_str(r"\a"),
                '\x08' => output.push_str(r"\b"),
                '\x0B' => output.push_str(r"\v"),
                '\x0C' => output.push_str(r"\f"),
                other => output.push(other),
            }
        }
        output
    }

    fn escaped_text_body(text: &str) -> IonResult<String> {
        let mut output = String::new();
        FmtValueFormatter::new(&mut output).format_escaped_text_body(text)?;
        Ok(output)
    }

    /// Each special byte (and a multi-byte character) at every position across two SWAR words,
    /// padded with text that never needs escaping.
    #[rstest]
    fn escaped_text_body_matches_reference_at_every_offset(
        #[values(
            "\n", "\r", "\t", "\\", "\"", "'", "\0", "\x07", "\x08", "\x0B", "\x0C", "\x01",
            "\x06", "\x0E", "\x1F", "\x7F", "é", "日", "😀"
        )]
        special: &str,
    ) -> IonResult<()> {
        for prefix_len in 0..20 {
            for suffix_len in 0..=9 {
                let text = format!(
                    "{}{special}{}",
                    "a".repeat(prefix_len),
                    "b".repeat(suffix_len)
                );
                assert_eq!(
                    escaped_text_body(&text)?,
                    reference_escaped_text_body(&text),
                    "text: {text:?}"
                );
            }
        }
        Ok(())
    }

    /// The SWAR prefilter must flag every byte that `TEXT_ESCAPE_CODES` escapes, in every lane of an
    /// otherwise clean word; a byte it missed would be written unescaped. The non-ASCII backgrounds
    /// set the high bit of every lane except `lane`.
    #[rstest]
    fn swar_prefilter_flags_every_escaped_byte(
        #[values(0, 1, 2, 3, 4, 5, 6, 7)] lane: usize,
        #[values(b'a', 0x80, 0xBF, 0xC3, 0xFF)] background: u8,
    ) {
        for byte in 0..=u8::MAX {
            if TEXT_ESCAPE_CODES[byte as usize].is_empty() {
                continue;
            }
            let mut word = [background; 8];
            word[lane] = byte;
            assert!(
                swar_may_need_escape(u64::from_ne_bytes(word)),
                "byte {byte:#04x} in lane {lane}, background {background:#04x}"
            );
        }
    }

    #[rstest]
    #[case::empty("")]
    #[case::all_escapes("\n\r\t\\\"'\0\x07\x08\x0B\x0C")]
    #[case::adjacent_escapes_across_words("aaaaaaa\"\"bbbbbbb\\\\ccccccc''")]
    #[case::non_ascii_between_escapes("é\"日\n😀'")]
    fn escaped_text_body_matches_reference(#[case] text: &str) -> IonResult<()> {
        assert_eq!(escaped_text_body(text)?, reference_escaped_text_body(text));
        Ok(())
    }

    #[rstest]
    #[case::identifier("foo", true)]
    #[case::leading_underscore("_foo", true)]
    #[case::leading_dollar("$foo", true)]
    #[case::trailing_digits("foo_12", true)]
    #[case::dollar_type("$type", true)]
    #[case::dollar_ion("$ion", true)]
    #[case::system_symbol("$ion_symbol_table", true)]
    #[case::dollar_ion_underscore("$ion_", true)]
    #[case::version_marker_prefix("$ion_1", true)]
    #[case::version_marker_then_letter("$ion_1_0x", true)]
    #[case::version_marker_then_underscore("$ion_1_0_0", true)]
    #[case::version_marker_without_minor("$ion_1_", true)]
    #[case::trailing_dollar_digits("a$12", true)]
    #[case::keyword_prefix("nulls", true)]
    #[case::keyword_suffix("anull", true)]
    #[case::capitalized_keyword("True", true)]
    #[case::long_identifier(
        "abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ$0123456789",
        true
    )]
    #[case::lone_dollar("$", true)]
    #[case::dollar_digits_then_letter("$1a", true)]
    #[case::dollar_digits_then_underscore("$1_0", true)]
    #[case::dollar_digits_then_dollar("$1$2", true)]
    #[case::version_marker("$ion_1_0", false)]
    #[case::other_version_marker("$ion_12_34", false)]
    #[case::empty("", false)]
    #[case::keyword_true("true", false)]
    #[case::keyword_false("false", false)]
    #[case::keyword_nan("nan", false)]
    #[case::keyword_null("null", false)]
    #[case::symbol_id("$12", false)]
    #[case::symbol_id_zero("$0", false)]
    #[case::leading_digit("1abc", false)]
    #[case::space("a b", false)]
    #[case::dash("a-b", false)]
    #[case::non_ascii("é", false)]
    #[case::non_ascii_digits_after_dollar("$١٢", false)]
    fn unquoted_symbol_text(#[case] text: &str, #[case] expected: bool) {
        assert_eq!(is_unquoted_symbol_text(text), expected);
    }

    /// Each byte value at every position of identifier text of each length up to a little more
    /// than two words, which covers the short, single-word, and multi-word paths of the SWAR test.
    #[rstest]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn identifier_text_matches_per_byte_test(
        #[values(b'a', b'Z', b'0', b'_', b'$')] background: u8,
    ) {
        for len in 0..=17 {
            let mut text = vec![background; len];
            assert!(is_identifier_text(&text), "len {len}");
            for position in 0..len {
                for byte in 0..=u8::MAX {
                    text[position] = byte;
                    assert_eq!(
                        is_identifier_text(&text),
                        byte == b'$' || byte == b'_' || byte.is_ascii_alphanumeric(),
                        "byte {byte:#04x} at {position} of {len}, background {background:#04x}"
                    );
                }
                text[position] = background;
            }
        }
    }

    #[rstest]
    #[case::identifier(RawSymbolRef::Text("foo"), "foo")]
    #[case::keyword(RawSymbolRef::Text("true"), "'true'")]
    #[case::resembles_symbol_id(RawSymbolRef::Text("$12"), "'$12'")]
    #[case::lone_dollar(RawSymbolRef::Text("$"), "$")]
    #[case::empty(RawSymbolRef::Text(""), "''")]
    #[case::space(RawSymbolRef::Text("a b"), "'a b'")]
    #[case::single_quote(RawSymbolRef::Text("a'b"), r"'a\'b'")]
    #[case::symbol_id(RawSymbolRef::SymbolId(10), "$10")]
    fn symbol_token_text(#[case] token: RawSymbolRef<'_>, #[case] expected: &str) -> IonResult<()> {
        let mut output = String::new();
        FmtValueFormatter::new(&mut output).format_symbol_token(token)?;
        assert_eq!(output, expected);
        Ok(())
    }

    #[rstest]
    #[case::text(RawSymbolRef::Text("foo"), "foo::")]
    #[case::quoted_text(RawSymbolRef::Text("a b"), "'a b'::")]
    #[case::symbol_id(RawSymbolRef::SymbolId(10), "$10::")]
    fn annotation_text(#[case] token: RawSymbolRef<'_>, #[case] expected: &str) -> IonResult<()> {
        let mut output = String::new();
        FmtValueFormatter::new(&mut output).format_annotation(token)?;
        assert_eq!(output, expected);
        Ok(())
    }

    /// Symbol text that starts like a symbol ID, a version marker, or a keyword, as a top-level
    /// value (where a version marker is recognized) and inside a list.
    #[rstest]
    #[case::symbol_id("$12")]
    #[case::symbol_id_then_identifier("$12a")]
    #[case::symbol_id_then_dollar("$1$2")]
    #[case::lone_dollar("$")]
    #[case::version_marker("$ion_1_1")]
    #[case::version_marker_then_identifier("$ion_1_0x")]
    #[case::keyword("null")]
    fn ambiguous_symbol_text_round_trips(#[case] text: &str) -> IonResult<()> {
        for element in [
            Element::symbol(text),
            Element::from(crate::ion_list![Element::symbol(text)]),
        ] {
            let read = Element::read_all(element.to_string())?;
            assert_eq!(read, Sequence::from(vec![element.clone()]), "{element}");
        }
        Ok(())
    }

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
}
