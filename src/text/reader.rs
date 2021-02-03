use std::num::{ParseIntError, ParseFloatError};
use std::str::FromStr;

use bigdecimal::{BigDecimal, ParseBigDecimalError};
use chrono::{DateTime, FixedOffset, Offset};
use nom::{Parser, AsChar};
use nom::branch::alt;
use nom::bytes::streaming::{is_a, tag, take_while1, is_not, take_until};
use nom::character::{is_digit, is_hex_digit};
use nom::character::streaming::{alpha1, char, digit0, digit1, none_of, one_of, satisfy, anychar};
use nom::combinator::{map, map_res, not, opt, peek, recognize, success, verify, value};
use nom::error::{context, VerboseError};
use nom::Finish;
use nom::IResult;
use nom::multi::{many0, many0_count, many1, many1_count, separated_list1, many_m_n, fold_many0};
use nom::sequence::{pair, preceded, separated_pair, terminated, tuple, delimited};

use crate::IonType;
use crate::result::{decoding_error, IonResult, IonError, decoding_error_raw};
use crate::types::SymbolId;
use nom::number::complete::recognize_float;

// TODO: Modify impl to match this description.
//       See: https://crates.io/crates/encoding_rs_io
// We have a String buffer that we fill periodically by reading from input.
// We read the string N lines-at-a-time.
// If a read comes back as incomplete, we clear the buffer of any already-processed text
// and then append the next N lines from input. Then we try the same read again.

pub struct TextReader {
    input: String,
}

// As this is text Ion, we're always reading a &str slice from the String input buffer
type ParseResult<'a, T> = IResult<&'a str, T, VerboseError<&'a str>>;

#[derive(Debug, Clone, PartialEq)]
enum TextStreamItem {
    Null(IonType),
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Decimal(BigDecimal),
    Timestamp(DateTime<FixedOffset>), //TODO: Proper Ion Timestamp value w/Precision
    String(String),
    Symbol(String), // TODO: SymbolToken API
    Blob(Vec<u8>),
    Clob(Vec<u8>),
    ListStart,
    SExpressionStart,
    StructStart,
}

impl TextStreamItem {
    pub fn ion_type(&self) -> IonType {
        match self {
            TextStreamItem::Null(ion_type) => *ion_type,
            TextStreamItem::Boolean(_) => IonType::Boolean,
            TextStreamItem::Integer(_) => IonType::Integer,
            TextStreamItem::Float(_) => IonType::Float,
            TextStreamItem::Decimal(_) => IonType::Decimal,
            TextStreamItem::Timestamp(_) => IonType::Timestamp,
            TextStreamItem::String(_) => IonType::String,
            TextStreamItem::Symbol(_) => IonType::Symbol,
            TextStreamItem::Blob(_) => IonType::Blob,
            TextStreamItem::Clob(_) => IonType::Clob,
            TextStreamItem::ListStart => IonType::List,
            TextStreamItem::SExpressionStart => IonType::SExpression,
            TextStreamItem::StructStart => IonType::Struct,
        }
    }
}

#[derive(Debug, Clone)]
enum StringFragment<'a> {
    Substring(&'a str),
    EscapedChar(char),
    EscapedNewline,
}

//TODO: Explanatory note about how `recognize` works and how to combine it with many0_count and many1_count.

impl TextReader {
    fn buffer(&self) -> &str {
        self.input.as_str()
    }

    // TODO: Are these only stop characters for numeric values? See the ANTLR grammar:
    // https://amzn.github.io/ion-docs/grammar/IonText.g4.txt
    fn stop_character(input: &str) -> IResult<&str, char> {
        peek(one_of("{}[](),\"' \t\n\r\u{0b}\u{0c}"))(input)
    }

    // Recognizes a null and converts it into a TextStreamItem::Null containing the associated
    // IonType.
    fn null(input: &str) -> IResult<&str, TextStreamItem> {
        map_res(
            delimited(
                tag("null"),
                opt(preceded(char('.'), alpha1)),
                Self::stop_character,
            ),
            |maybe_ion_type_text| {
                if let Some(ion_type_text) = maybe_ion_type_text {
                    match Self::ion_type_from_text(ion_type_text) {
                        Some(ion_type) => Ok(TextStreamItem::Null(ion_type)),
                        None => decoding_error(format!("Invalid Ion type used in `null.{}`", ion_type_text))
                    }
                } else {
                    Ok(TextStreamItem::Null(IonType::Null))
                }
            }
        )(input)
    }

    // Maps the type text from an Ion null to its corresponding IonType.
    fn ion_type_from_text(text: &str) -> Option<IonType> {
        use IonType::*;
        let ion_type = match text {
            "null" => Null,
            "bool" => Boolean,
            "int" => Integer,
            "float" => Float,
            "decimal" => Decimal,
            "timestamp" => Timestamp,
            "string" => String,
            "symbol" => Symbol,
            "blob" => Blob,
            "clob" => Clob,
            "struct" => Struct,
            "list" => List,
            "sexp" => SExpression,
            _ => return None,
        };
        Some(ion_type)
    }

    // Recognizes a boolean and converts it into a TextStreamItem::Binary containing the resulting
    // bool.
    fn boolean(input: &str) -> IResult<&str, TextStreamItem> {
        map_res(
            recognize(terminated(tag("true").or(tag("false")), Self::stop_character)),
            |bool_text: &str| {
                match bool_text {
                    "true" => Ok(TextStreamItem::Boolean(true)),
                    "false" => Ok(TextStreamItem::Boolean(false)),
                    _ => decoding_error(format!("Illegal boolean value: {}", bool_text))
                }
            }
        )(input)
    }

    // Recognizes an integer of any supported notation (binary, decimal, hexadecimal) and converts
    // it into a TextStreamItem::Integer containing the resulting i64.
    fn integer(input: &str) -> IResult<&str, TextStreamItem> {
        // We have to check for binary and hex first because decimal numbers don't have a
        // header like "0b" or "0x" prefix.
        terminated(
            alt((Self::base_16_integer, Self::base_2_integer, Self::base_10_integer)),
            Self::stop_character
        )(input)
    }

    // Recognizes a hexadecimal notation integer (sign, '0x', digits) and converts it into a
    // TextStreamItem::Integer containing the resulting i64 value.
    fn base_16_integer(input: &str) -> IResult<&str, TextStreamItem> {
        map_res(
            separated_pair(
                opt(char('-')),
                alt((tag("0x"), tag("0X"))),
                Self::base_16_integer_digits
            ),
            |(maybe_sign, text_digits)| {
                Self::parse_i64_with_radix(text_digits, 16)
                    .map(|i| if maybe_sign.is_some() {-i} else {i})
                    .map(|i| TextStreamItem::Integer(i))
            }
        )(input)
    }

    // Recognizes the 'digits' portion of a hexadecimal notation integer (sign, '0b', digits)
    fn base_16_integer_digits(input: &str) -> IResult<&str, &str> {
        recognize(
            terminated(
                // Zero or more digits-followed-by-underscores
                many0_count(pair(Self::take_base_16_digits1, char('_'))),
                // One or more digits
                Self::take_base_16_digits1
            )
        )(input)
    }

    // The "1" suffix is a style borrowed from `nom`.
    // Recognizes 1 or more hex digits in a row
    fn take_base_16_digits1(input: &str) -> IResult<&str, &str> {
        take_while1(|c: char| c.is_digit(16))(input)
    }

    // Recognizes a binary notation integer (sign, '0b', digits) and converts it into a
    // TextStreamItem::Integer containing the resulting i64 value.
    fn base_2_integer(input: &str) -> IResult<&str, TextStreamItem> {
        map_res(
            separated_pair(
                    opt(char('-')),
                    alt((tag("0b"), tag("0B"))),
                    Self::base_2_integer_digits
                ),
            |(maybe_sign, text_digits)| {
                Self::parse_i64_with_radix(text_digits, 2)
                    .map(|i| if maybe_sign.is_some() {-i} else {i})
                    .map(|i| TextStreamItem::Integer(i))
            }
        )(input)
    }

    // Recognizes the 'digits' portion of a binary notation integer (sign, '0b', digits)
    fn base_2_integer_digits(input: &str) -> IResult<&str, &str> {
        recognize(
            terminated(
            // Zero or more digits-followed-by-underscores
            many0_count(pair(is_a("01"), char('_'))),
            // One or more digits
            is_a("01")
            )
        )(input)
    }

    // Recognizes a decimal notation integer (sign, digits) and converts it into a
    // TextStreamItem::Integer containing the resulting i64 value.
    fn base_10_integer(input: &str) -> IResult<&str, TextStreamItem> {
        map_res(
            recognize(
                preceded(
                    opt(char('-')),
                    Self::base_10_integer_digits
                )
            ),
            |text| {
                Self::parse_i64_with_radix(text, 10)
                    .map(|i| TextStreamItem::Integer(i))
            }
        )(input)
    }

    // Just like i64::from_str_radix, but will remove any underscores from the input text first.
    fn parse_i64_with_radix(text: &str, radix: u32) -> Result<i64, ParseIntError> {
        if text.contains('_') {
            let sanitized = text.replace("_", "");
            return i64::from_str_radix(&sanitized, radix);
        }
        i64::from_str_radix(text, radix)
    }

    fn base_10_integer_digits(input: &str) -> IResult<&str, &str> {
        alt((
            // The number is either a zero...
            recognize(char('0')),
            // Or it's a non-zero followed by some number of '_'-separated digits
            Self::digits_before_delimiter
        ))(input)
    }

    fn leading_digit(input: &str) -> IResult<&str, &str> {
        recognize(one_of("123456789"))(input)
    }

    // Any number of digits with underscores optionally appearing in the middle.
    // This parser accepts leading zeros, which is why it cannot be used for the beginning
    // of a number.
    fn trailing_digits(input: &str) -> IResult<&str, &str> {
        recognize(
            many0_count(
                pair(
                    opt(char('_')),
                        digit1
                )
            )
        )(input)
    }

    fn decimal(input: &str) -> IResult<&str, TextStreamItem> {
        terminated(
            alt((Self::decimal_with_exponent, Self::decimal_without_exponent)),
            Self::stop_character
        )(input)
    }

    fn decimal_with_exponent(input: &str) -> IResult<&str, TextStreamItem> {
        map_res::<_, _, _, _, ParseBigDecimalError, _, _>(
            recognize(
                tuple((
                    opt(tag("-")),
                    alt((Self::floating_point_number, Self::digits_before_delimiter)),
                    recognize(Self::decimal_exponent_marker_followed_by_digits),
                ))),
            |text| {
                println!("Decimal w/exp text: {:?}", text);
                // TODO: Reusable buffer for sanitization
                let substitute_exponent_markers: &[char] = &['d', 'D'];
                let mut sanitized = text.replace(substitute_exponent_markers, "e");
                sanitized = sanitized.replace("_", "");
                if sanitized.ends_with("e") {
                    sanitized.push_str("0");
                }
                println!("Decimal w/exp sanitized: {:?}", &sanitized);
                Ok(TextStreamItem::Decimal(BigDecimal::from_str(&sanitized)?))
            }
        )(input)
    }

    fn decimal_without_exponent(input: &str) -> IResult<&str, TextStreamItem> {
        map_res::<_, _, _, _, ParseBigDecimalError, _, _>(
        Self::floating_point_number,
            |text| {
                println!("Decimal w/o exp text: {:?}", text);
                // TODO: Reusable buffer for sanitization
                let sanitized = text.replace("_", "");
                println!("Decimal w/o exp sanitized: {:?}", &sanitized);
                Ok(TextStreamItem::Decimal(BigDecimal::from_str(&sanitized)?))
            }
        )(input)
    }

    fn floating_point_number(input: &str) -> IResult<&str, &str> {
        recognize(
        tuple((
            opt(tag("-")),
            Self::digits_before_delimiter,
            recognize(Self::dot_followed_by_digits),
        )))(input)
    }

    fn float(input: &str) -> IResult<&str, TextStreamItem> {
        alt((Self::float_special_value, Self::float_numeric_value))(input)
    }

    fn float_special_value(input: &str) -> IResult<&str, TextStreamItem> {
        map(tag("nan"), |_| TextStreamItem::Float(f64::NAN))
            .or(map(tag("+inf"), |_| TextStreamItem::Float(f64::INFINITY)))
            .or(map(tag("-inf"), |_| TextStreamItem::Float(f64::NEG_INFINITY)))
            .parse(input)
    }

    fn float_numeric_value(input: &str) -> IResult<&str, TextStreamItem> {
        map_res::<_, _, _, _, ParseFloatError, _, _>(
            recognize(
                tuple((
                    opt(tag("-")),
                    alt((Self::floating_point_number, Self::digits_before_delimiter)),
                    recognize(Self::float_exponent_marker_followed_by_digits),
                ))),
            |text| {
                println!("Numeric float: {:?}", text);
                // TODO: Reusable buffer for sanitization
                let mut sanitized = text.replace("_", "");
                if sanitized.ends_with('e') || sanitized.ends_with('E') {
                    sanitized.push_str("0");
                }
                println!("Sanitized: {:?}", &sanitized);
                Ok(TextStreamItem::Float(f64::from_str(&sanitized)?))
            }
        )(input)
    }

    fn digits_before_delimiter(input: &str) -> IResult<&str, &str> {
        alt((
            tag("0"),
            recognize(
                pair(Self::leading_digit, Self::trailing_digits)
            )
        ))(input)
    }

    fn dot_followed_by_digits(input: &str) -> IResult<&str, Option<&str>> {
        preceded(
            tag("."),
            opt(Self::digits_after_delimiter)
        )(input)
    }

    fn decimal_exponent_marker_followed_by_digits(input: &str) -> IResult<&str, Option<&str>> {
        preceded(
            one_of("dD"),
            opt(Self::exponent_digits)
        )(input)
    }

    fn float_exponent_marker_followed_by_digits(input: &str) -> IResult<&str, Option<&str>> {
        preceded(
            one_of("eE"),
            opt(Self::exponent_digits)
        )(input)
    }

    fn exponent_digits(input: &str) -> IResult<&str, &str> {
        recognize(pair(opt(char('-')), Self::digits_after_delimiter))(input)
    }

    // Unlike before the delimiter, the digits that follow the delimiter can start with one or more
    // zeros.
    fn digits_after_delimiter(input: &str) -> IResult<&str, &str> {
        recognize(
            terminated(
                // Zero or more digits-followed-by-underscores
                many0_count(pair(digit1, char('_'))),
                // One or more digits
                digit1
            )
        )(input)
    }

    fn whitespace(input: &str) -> IResult<&str, &str> {
        //TODO Comments
        is_a(" \r\n\t")(input)
    }

    fn string(input: &str) -> IResult<&str, TextStreamItem> {
        alt((Self::short_string, Self::long_string))(input)
    }

    fn short_string(input: &str) -> IResult<&str, TextStreamItem> {
        map(
            delimited(char('"'), Self::short_string_body, char('"')),
            |text| {
                println!("Short string parts: {:?}", &text);
                TextStreamItem::String(text)
            }
        )(input)
    }

    // TODO: This parser allocates a Vec to hold each intermediate '''...''' string
    //       and then again to merge them into a finished product. These allocations
    //       could be removed with some refactoring.
    fn long_string(input: &str) -> IResult<&str, TextStreamItem> {
        map(
            terminated(
                    many1(
                        terminated(
                            delimited(tag("'''"), Self::long_string_body, tag("'''")),
                            opt(Self::whitespace)
                        )
                    ),
                    peek(not(tag("'''")))
                ),
            |text| {
                println!("Long string parts: {:?}", &text);
                TextStreamItem::String(text.join(""))
            }
        )(input)
    }

    fn long_string_body(input: &str) -> IResult<&str, String> {
        fold_many0(
            Self::long_string_fragment,
            String::new(),
            |mut string, fragment| {
                match fragment {
                    StringFragment::EscapedNewline => {} // Discard escaped newlines
                    StringFragment::EscapedChar(c) => string.push(c),
                    StringFragment::Substring(s) => string.push_str(s),
                }
                string
            },
        )(input)
    }

    fn long_string_fragment(input: &str) -> IResult<&str, StringFragment> {
        alt((
            Self::escaped_newline,
            Self::escaped_char,
            Self::long_string_fragment_without_escaped_text,
        ))(input)
    }

    fn long_string_fragment_without_escaped_text(input: &str) -> IResult<&str, StringFragment> {
        map(
            verify(take_until("'''"), |s: &str| !s.is_empty()),
            |text| StringFragment::Substring(text)
        )(input)
    }

    // TODO: This allocates a new String in order to perform character substitutions for escape
    //       sequences. With some refactoring, we should be able to instead load the string into
    //       a reusable buffer. This would require changing TextStreamItem::String(String) to
    //       TextStreamItem::String, and the APIs would have to look for the loaded value in the
    //       buffer.
    fn short_string_body(input: &str) -> IResult<&str, String> {
        fold_many0(
            Self::short_string_fragment,
            String::new(),
            |mut string, fragment| {
                match fragment {
                    StringFragment::EscapedNewline => {} // Discard escaped newlines
                    StringFragment::EscapedChar(c) => string.push(c),
                    StringFragment::Substring(s) => string.push_str(s),
                }
                string
            },
        )(input)
    }

    fn short_string_fragment(input: &str) -> IResult<&str, StringFragment> {
        alt((
            Self::escaped_newline,
            Self::escaped_char,
            Self::short_string_fragment_without_escaped_text,
        ))(input)
    }

    fn short_string_fragment_without_escaped_text(input: &str) -> IResult<&str, StringFragment> {
        map(
            verify(is_not("\"\\\""), |s: &str| !s.is_empty()),
            |text| StringFragment::Substring(text)
        )(input)
    }

    fn symbol(input: &str) -> IResult<&str, TextStreamItem> {
        alt((Self::identifier, Self::quoted_symbol))(input)
    }

    fn quoted_symbol(input: &str) -> IResult<&str, TextStreamItem> {
        map(
            delimited(char('\''), Self::quoted_symbol_body, char('\'')),
            |text| {
                println!("Symbol text: {:?}", &text);
                TextStreamItem::Symbol(text)
            }
        )(input)
    }

    fn quoted_symbol_body(input: &str) -> IResult<&str, String> {
        fold_many0(
            Self::quoted_symbol_string_fragment,
            String::new(),
            |mut string, fragment| {
                match fragment {
                    StringFragment::EscapedNewline => {} // Discard escaped newlines
                    StringFragment::EscapedChar(c) => string.push(c),
                    StringFragment::Substring(s) => string.push_str(s),
                }
                string
            },
        )(input)
    }

    fn quoted_symbol_string_fragment(input: &str) -> IResult<&str, StringFragment> {
        alt((
            Self::escaped_newline,
            Self::escaped_char,
            Self::quoted_symbol_fragment_without_escaped_text,
        ))(input)
    }

    fn quoted_symbol_fragment_without_escaped_text(input: &str) -> IResult<&str, StringFragment> {
        map(
            verify(is_not("'\\'"), |s: &str| !s.is_empty()),
            |text| StringFragment::Substring(text)
        )(input)
    }

    fn identifier(input: &str) -> IResult<&str, TextStreamItem> {
        map(
            recognize(
                terminated(
                    pair(
                        Self::identifier_initial_character,
                        Self::identifier_trailing_characters
                    ),
                    Self::stop_character
                )
            ),
            |text| {
                TextStreamItem::Symbol(text.to_owned())
            }
        )(input)
    }

    fn identifier_initial_character(input: &str) -> IResult<&str, char> {
        alt((one_of("$_"), satisfy(|c| c.is_ascii_alphabetic())))(input)
    }

    fn identifier_trailing_characters(input: &str) -> IResult<&str, &str> {
        recognize(
            many0_count(
                alt((
                    one_of("$_"),
                    satisfy(|c| c.is_ascii_alphanumeric())
                ))
            )
        )(input)
    }

    // Discards escaped newlines
    fn escaped_newline(input: &str) -> IResult<&str, StringFragment> {
        value(StringFragment::EscapedNewline, tag("\\\n"))(input)
    }

    // Some escape sequences discard the associated character (like escaped newlines),
    // so this returns Option<char> to accommodate that.
    fn escaped_char(input: &str) -> IResult<&str, StringFragment> {
        map(
            preceded(
                char('\\'),
                alt((
                    Self::escaped_char_unicode,
                    Self::escaped_char_literal,
                ))
            ),
            |c| StringFragment::EscapedChar(c)
        )(input)
    }

    // See: https://amzn.github.io/ion-docs/docs/spec.html#escapes
    fn escaped_char_literal(input: &str) -> IResult<&str, char> {
        alt((
            value('\n', char('n')),
            value('\r', char('r')),
            value('\t', char('t')),
            value('\\', char('\\')),
            value('/', char('/')),
            value('"', char('"')),
            value('\'', char('\'')),
            value('?', char('?')),
            value('\u{00}', char('0')), // NUL
            value('\u{07}', char('a')), // alert BEL
            value('\u{08}', char('b')), // backspace
            value('\u{0B}', char('v')), // vertical tab
            value('\u{0C}', char('f')), // form feed
        ))(input)
    }

    fn escaped_char_unicode(input: &str) -> IResult<&str, char> {
        map_res::<_, _, _, _, IonError, _, _>(
            alt((
                Self::escaped_char_unicode_2_digit_hex,
                Self::escaped_char_unicode_4_digit_hex,
                Self::escaped_char_unicode_8_digit_hex,
            )),
            |hex_digits| {
                let number_value = u32::from_str_radix(hex_digits, 16)
                    .or_else(|e| Err(decoding_error_raw(
                    format!("Couldn't parse unicode escape '{}': {:?}", hex_digits, e)
                )))?;
                let char_value = std::char::from_u32(number_value)
                    .ok_or_else(|| decoding_error_raw(
                        format!("Couldn't parse unicode escape '{}': {} is not a valid codepoint.", hex_digits, number_value))
                    )?;
                Ok(char_value)
            }
        )(input)
    }

    fn escaped_char_unicode_2_digit_hex(input: &str) -> IResult<&str, &str> {
        let hex_digit = Self::single_hex_digit;
        preceded(
        char('x'),
        recognize(
            tuple(
                (hex_digit, hex_digit)
                )
            )
        )(input)
    }

    fn escaped_char_unicode_4_digit_hex(input: &str) -> IResult<&str, &str> {
        let hex_digit = Self::single_hex_digit;
        preceded(
            char('u'),
            recognize(
                tuple(
                    (hex_digit, hex_digit, hex_digit, hex_digit)
                )
            )
        )(input)
    }

    fn escaped_char_unicode_8_digit_hex(input: &str) -> IResult<&str, &str> {
        let hex_digit = Self::single_hex_digit;
        preceded(
            char('U'),
            recognize(
                tuple(
                    (hex_digit, hex_digit, hex_digit, hex_digit,
                     hex_digit, hex_digit, hex_digit, hex_digit)
                )
            )
        )(input)
    }

    fn single_hex_digit(input: &str) -> IResult<&str, char> {
        satisfy(|c| <char as AsChar>::is_hex_digit(c))(input)
    }

    fn stream_item(input: &str) -> IResult<&str, TextStreamItem> {
        alt((
            Self::null,
            Self::boolean,
            Self::integer,
            Self::float,
            Self::decimal,
            Self::string,
            Self::symbol
        ))(input)
    }
}

#[cfg(test)]
mod reader_tests {
    use std::result::Result;

    use nom::bytes::streaming::is_a;
    use nom::character::streaming::char;
    use nom::combinator::recognize;
    use nom::error::ParseError;
    use nom::Finish;
    use nom::IResult;
    use nom::sequence::pair;

    use crate::IonType;
    use crate::text::reader::TextStreamItem;

    use super::{ParseResult, TextReader};
    use bigdecimal::BigDecimal;
    use std::str::FromStr;

    type TestParser = fn(&str) -> IResult<&str, TextStreamItem>;

    fn parse_unwrap(parser: TestParser, text: &str) -> TextStreamItem {
        let parsed = parser(text);
        if parsed.is_err() {
            panic!("{:?}: Parse unexpectedly failed on input: {:?}", parsed.finish(), text);
        }
        parsed.unwrap().1
    }

    fn parse_test_ok(parser: TestParser, text: &str, expected: TextStreamItem) {
        let actual = parse_unwrap(parser, text);
        assert_eq!(expected, actual);
    }

    fn parse_test_err(parser: TestParser, text: &str) {
        let parsed = parser(text);
        if parsed.is_ok() {
            panic!("Parse unexpectedly succeeded: {:?} -> {:?}", text, parsed.unwrap().1);
        }
    }


    #[test]
    fn test_parse_nulls() {
        let good = |s: &str, t: IonType| parse_test_ok(TextReader::null, s, TextStreamItem::Null(t));
        let bad = |s: &str| parse_test_err(TextReader::null, s);

        use IonType::*;
        good("null ", Null);
        good("null.null ", Null);
        good("null.bool ", Boolean);
        good("null.int ", Integer);
        good("null.float ", Float);
        good("null.decimal ", Decimal);
        good("null.timestamp ", Timestamp);
        good("null.string ", String);
        good("null.symbol ", Symbol);
        good("null.blob ", Blob);
        good("null.clob ", Clob);
        good("null.list ", List);
        good("null.sexp ", SExpression);
        good("null.struct ", Struct);

        // Misspelled null
        bad("nlul ");
        // Unrecognized type
        bad("null.strunct ");
        // Leading whitespace
        bad(" null.strunct ");
        // Null is end of current input; might be an incomplete stream
        bad("null.struct");
    }

    #[test]
    fn test_parse_bools() {
        let good = |s: &str, b: bool| parse_test_ok(TextReader::boolean, s, TextStreamItem::Boolean(b));
        let bad = |s: &str| parse_test_err(TextReader::boolean, s);

        good("true ", true);
        good("false ", false);

        // Misspelled boolean name
        bad("ture ");
        bad("fasle ");
        // Leading whitespace
        bad(" true");
        // Boolean is end of current input; might be an incomplete stream
        bad("true");
    }

    #[test]
    fn test_parse_decimal_integers() {
        let good = |s: &str, i: i64| parse_test_ok(TextReader::integer, s, TextStreamItem::Integer(i));
        let bad = |s: &str| parse_test_err(TextReader::integer, s);

        good("1 ", 1);
        good("305 ", 305);
        good("111_111_222 ", 111_111_222);
        good("-279 ", -279);
        good("-999_999 ", -999_999);

        // Doesn't consume leading whitespace
        bad(" 305 ");
        // Doesn't accept leading underscores
        bad("_305 ");
        // Doesn't accept trailing underscores
        bad("305_ ");
        // Doesn't accept multiple consecutive underscores
        bad("3__05 ");
        // Doesn't accept leading plus sign
        bad("+305 ");
        // Doesn't accept multiple negative signs
        bad("--305 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        bad(" 305");
    }

    #[test]
    fn test_parse_binary_integers() {
        let good = |s: &str, i: i64| parse_test_ok(TextReader::integer, s, TextStreamItem::Integer(i));
        let bad = |s: &str| parse_test_err(TextReader::integer, s);

        good("0b1 ", 1);
        good("0b101 ", 5);
        good("0B101 ", 5);
        good("0b1_0_1 ", 5);
        good("-0b111 ", -7);
        good("-0b11110000 ", -240);
        good("-0b1111_0000 ", -240);

        // Doesn't consume leading whitespace
        bad(" 0b0011_0001 ");
        // Doesn't accept leading underscores
        bad("0b_0011_0001 ");
        // Doesn't accept trailing underscores
        bad("0b0011_0001_ ");
        // Doesn't accept multiple consecutive underscores
        bad("0b0011__0001 ");
        // Doesn't accept leading plus sign
        bad("+0b0011_0001 ");
        // Doesn't accept multiple negative signs
        bad("--0b0011_0001 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        bad(" 0b0011_0001");
    }

    #[test]
    fn test_parse_hex_integers() {
        let good = |s: &str, i: i64| parse_test_ok(TextReader::integer, s, TextStreamItem::Integer(i));
        let bad = |s: &str| parse_test_err(TextReader::integer, s);

        good("0x1 ", 1);
        good("0xA ", 10);
        good("0xFF ", 255);
        good("0xff ", 255);
        good("0Xff ", 255);
        good("0xFA_CE ", 64_206);
        good("-0xDECAF ", -912559);

        // Doesn't consume leading whitespace
        bad(" 0xCAFE ");
        // Doesn't accept leading underscores
        bad("0x_CAFE ");
        // Doesn't accept trailing underscores
        bad("0xCAFE_ ");
        // Doesn't accept multiple consecutive underscores
        bad("0xCA__FE ");
        // Doesn't accept leading plus sign
        bad("+0xCAFE ");
        // Doesn't accept multiple negative signs
        bad("--0xCAFE ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        bad(" 0xCAFE");
    }

    #[test]
    fn test_parse_floats() {
        let good = |s: &str, f: f64|
            parse_test_ok(TextReader::float, s, TextStreamItem::Float(f));
        let bad = |s: &str| parse_test_err(TextReader::decimal, s);

        good("0.0e ", 0.0);
        good("0E ", 0.0);
        good("0e0 ", 0e0);
        good("305e1 ", 3050.0);
        good("305.0e1 ", 3050.0);
        good("111_111e222 ", 111111.0 * 10f64.powf(222f64));
        good("111_111.667e222 ", 111111.667 * 10f64.powf(222f64));
        good("111_111e222_222 ", 111111.0 * 10f64.powf(222222f64));
        good("-279e ", -279.0);
        good("-279e0 ", -279.0);
        good("-279.5e ", -279.5);
        good("-999_9e9_9 ", f64::from_str("-9999e99").unwrap());

        good("+inf", f64::INFINITY);
        good("-inf", f64::NEG_INFINITY);

        // Can't test two NaNs for equality
        let item = parse_unwrap(TextReader::float, "nan");
        if let TextStreamItem::Float(f) = item {
            assert!(f.is_nan());
        } else {
            panic!("Expected NaN, but got: {:?}", item);
        }

        // // Missing exponent (would be parsed as an integer)
        bad("305 ");
        // Fractional exponent
        bad("305e0.5");
        // Negative fractional exponent
        bad("305e-0.5");
        // Doesn't consume leading whitespace
        bad(" 305e1 ");
        // Doesn't accept leading underscores
        bad("_305e1 ");
        // Doesn't accept leading zeros
        bad("0305e1 ");
        // Doesn't accept trailing underscores
        bad("305e1_ ");
        // Doesn't accept multiple consecutive underscores
        bad("30__5e1 ");
        // Doesn't accept leading plus sign
        bad("+305e1 ");
        // Doesn't accept multiple negative signs
        bad("--305e1 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        bad("305e1");
    }

    #[test]
    fn test_parse_decimals_with_exponents() {
        let to_decimal = |s: &str| BigDecimal::from_str(s)
            .map_err(|e| panic!("BigDecimal couldn't parse {:?}", s))
            .unwrap();
        let good = |s: &str, d: &str|
            parse_test_ok(TextReader::decimal, s, TextStreamItem::Decimal(to_decimal(d)));
        let bad = |s: &str| parse_test_err(TextReader::decimal, s);

        // All of the strings on the right side below are passed to BigDecimal's parser, which
        // recognizes 'e', not 'd'.
        good("0d ", "0e0");
        good("0D ", "0e0");
        good("0d0 ", "0e0");
        good("305d1 ", "305e1");
        good("305d-1 ", "305e-1");
        good("111_111d222 ", "111111e222");
        good("111_111d-222 ", "111111e-222");
        good("111_111d222_222 ", "111111e222222");
        good("-279d ", "-279e0");
        good("-279d0 ", "-279e0");
        good("-999_9d9_9 ", "-9999e99");
        good("-999_9d-9_9 ", "-9999e-99");

        // Missing decimal (would be parsed as an integer)
        bad("305 ");
        // Fractional exponent
        bad("305d0.5");
        // Negative fractional exponent
        bad("305d-0.5");
        // Doesn't consume leading whitespace
        bad(" 305d1 ");
        // Doesn't accept leading underscores
        bad("_305d1 ");
        // Doesn't accept leading zeros
        bad("0305d1 ");
        // Doesn't accept trailing underscores
        bad("305d1_ ");
        // Doesn't accept multiple consecutive underscores
        bad("30__5d1 ");
        // Doesn't accept leading plus sign
        bad("+305d1 ");
        // Doesn't accept multiple negative signs
        bad("--305d1 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        bad("305d1");
    }

    #[test]
    fn test_parse_decimals_without_exponents() {
        let to_decimal = |s: &str| BigDecimal::from_str(s)
            .map_err(|e| panic!("BigDecimal couldn't parse {:?}", s))
            .unwrap();
        let good = |s: &str, d: &str|
            parse_test_ok(TextReader::decimal, s, TextStreamItem::Decimal(to_decimal(d)));
        let bad = |s: &str| parse_test_err(TextReader::decimal, s);

        // All of the strings on the right side below are passed to BigDecimal's parser, which
        // recognizes 'e', not 'd'.
        good("0. ", "0e0");
        good("0.0 ", "0e0");
        good("0.5 ", "0.5e0");
        good("3050. ", "3050.");
        good("3050.667 ", "3050.667");
        good("111_111.000 ", "111111.000");
        good("111_111.0_0_0 ", "111111.000");
        good("-279. ", "-279e0");
        good("-279.0 ", "-279e0");
        good("-279.701 ", "-279.701e0");
        good("-999_9.0_0 ", "-9999.00");

        // // Missing decimal (would be parsed as an integer)
        bad("305 ");
        // Doesn't consume leading whitespace
        bad(" 3050.0 ");
        // Doesn't accept leading underscores
        bad("_3050.0 ");
        // Doesn't accept leading zeros
        bad("03050.0 ");
        // Doesn't accept trailing underscores
        bad("3050.0_ ");
        // Doesn't accept multiple consecutive underscores
        bad("30__50.0 ");
        // Doesn't accept leading plus sign
        bad("+3050.0 ");
        // Doesn't accept multiple negative signs
        bad("--3050.0 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        bad("3050.0");
    }

    #[test]
    fn test_parse_short_strings() {
        let good = |text: &str, expected: &str| {
            parse_test_ok(
                TextReader::string,
                text,
                TextStreamItem::String(expected.to_owned()));
        };
        let bad = |s: &str| parse_test_err(TextReader::string, s);

        good("\"\" ", "");
        good("\"Hello, world!\" ", "Hello, world!");
        // Escape literals
        good("\"Hello\nworld!\" ", "Hello\nworld!");
        good("\"Hello\tworld!\" ", "Hello\tworld!");
        good("\"\\\"Hello, world!\\\"\" ", "\"Hello, world!\"");
        // 2-digit Unicode hex escape sequences
        good("\"\\x48ello, \\x77orld!\" ", "Hello, world!");
        // 4-digit Unicode hex escape sequences
        good("\"\\u0048ello, \\u0077orld!\" ", "Hello, world!");
        // 8-digit Unicode hex escape sequences
        good("\"\\U00000048ello, \\U00000077orld!\" ", "Hello, world!");
        // Escaped newlines are discarded
        good("\"Hello,\\\n world!\" ", "Hello, world!");

        // Missing quotes
        bad("Hello, world ");
        // Missing closing quote
        bad("\"Hello, world ");
        // Leading whitespace not accepted
        bad(" \"Hello, world\" ");
    }

    #[test]
    fn test_parse_long_strings() {
        let good = |text: &str, expected: &str| {
            parse_test_ok(
                TextReader::string,
                text,
                TextStreamItem::String(expected.to_owned()));
        };
        let bad = |s: &str| parse_test_err(TextReader::string, s);

        // Long strings can have any number of segments separated by whitespace.
        // These test strings end in an integer so the parser knows the long string is done.
        good("'''foo''' 1", "foo");
        good("'''foo bar baz''' 1", "foo bar baz");
        good("'''foo''' '''bar''' '''baz''' 1", "foobarbaz");
        good("'''foo'''\n\n\n'''bar'''\n\n\n'''baz''' 1", "foobarbaz");
        good("'''\\x66oo''' '''\\u0062\\U00000061r''' '''\\x62\\U00000061z''' 1", "foobarbaz");
    }

    #[test]
    fn test_parse_symbol_identifiers() {
        let good = |text: &str, expected: &str| {
            parse_test_ok(
                TextReader::symbol,
                text,
                TextStreamItem::Symbol(expected.to_owned()));
        };
        let bad = |s: &str| parse_test_err(TextReader::string, s);

        good("foo ", "foo");
        good("$foo ", "$foo");
        good("_foo ", "_foo");
        good("$_ ", "$_");
        good("$ion_1_0 ", "$ion_1_0");
        good("__foo__ ", "__foo__");
        good("foo12345 ", "foo12345");

        // Starts with a digit
        bad("1foo ");
        // Leading whitespace not accepted
        bad(" foo ");
        // Cannot be the last thing in input (stream might be incomplete
        bad("foo");
    }

    #[test]
    fn test_parse_quoted_symbols() {
        let good = |text: &str, expected: &str| {
            parse_test_ok(
                TextReader::symbol,
                text,
                TextStreamItem::Symbol(expected.to_owned()));
        };
        let bad = |s: &str| parse_test_err(TextReader::string, s);

        good("'foo' ", "foo");
        good("'$foo' ", "$foo");
        good("'_foo' ", "_foo");
        good("'11foo' ", "11foo");
        good("'$_' ", "$_");
        good("'$ion_1_0' ", "$ion_1_0");
        good("'__foo__' ", "__foo__");
        good("'foo12345' ", "foo12345");
        good("'foo bar baz' ", "foo bar baz");
        good("'foo \"bar\" baz' ", "foo \"bar\" baz");
        good("'7@#$%^&*()!' ", "7@#$%^&*()!");

        // Leading whitespace not accepted
        bad(" 'foo' ");
        // Cannot be the last thing in input (stream might be incomplete
        bad("'foo'");
    }

    #[test]
    fn test_detect_stream_item_types() {
        let expect_type = |text: &str, expected_ion_type: IonType| {
            let value = parse_unwrap(TextReader::stream_item, text);
            assert_eq!(expected_ion_type, value.ion_type());
        };

        expect_type("null ", IonType::Null);
        expect_type("null.timestamp ", IonType::Timestamp);
        expect_type("null.list ", IonType::List);
        expect_type("true ", IonType::Boolean);
        expect_type("false ", IonType::Boolean);
        expect_type("5 ", IonType::Integer);
        expect_type("-5 ", IonType::Integer);
        expect_type("5.0 ", IonType::Decimal);
        expect_type("-5.0 ", IonType::Decimal);
        expect_type("5.0d ", IonType::Decimal);
        expect_type("-5.0d ", IonType::Decimal);
        expect_type("5.0e ", IonType::Float);
        expect_type("-5.0e ", IonType::Float);
        expect_type("\"foo\"", IonType::String);
        expect_type("'''foo''' 1", IonType::String);
        expect_type("foo ", IonType::Symbol);
        expect_type("'foo bar baz' ", IonType::Symbol);
    }
}
