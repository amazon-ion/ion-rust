use crate::raw_symbol_token::{local_sid_token, text_token};
use crate::text::parse_result::{IonParseError, IonParseResult, OrFatalParseError, UpgradeIResult};
use crate::text::parsers::stop_character;
use crate::text::parsers::text_support::{escaped_char, escaped_newline, StringFragment};
use crate::text::text_value::TextValue;
use nom::branch::alt;
use nom::bytes::streaming::{is_a, is_not, tag};
use nom::character::streaming::{char, digit1, multispace0, one_of, satisfy};
use nom::combinator::{map, not, peek, recognize, verify};
use nom::multi::{fold_many0, many0_count};
use nom::sequence::{delimited, pair, preceded, terminated};
use nom::Err;

/// Matches the text representation of a symbol value and returns the resulting [String]
/// as a [TextValue::Symbol].
pub(crate) fn parse_symbol(input: &str) -> IonParseResult<TextValue> {
    alt((symbol_id, identifier, quoted_symbol))(input)
}

/// Matches a quoted symbol (e.g. `'foo bar'`) and returns the resulting [String]
/// as a [TextValue::Symbol].
fn quoted_symbol(input: &str) -> IonParseResult<TextValue> {
    map(
        delimited(char('\''), quoted_symbol_body, char('\'')),
        |text| TextValue::Symbol(text_token(text)),
    )(input)
}

/// Matches the body of a quoted symbol. (The `hello` in `'hello'`.)
fn quoted_symbol_body(input: &str) -> IonParseResult<String> {
    fold_many0(
        quoted_symbol_string_fragment,
        String::new,
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

/// Matches an escaped character or a substring without any escapes in a long string.
fn quoted_symbol_string_fragment(input: &str) -> IonParseResult<StringFragment> {
    alt((
        escaped_newline,
        escaped_char,
        quoted_symbol_fragment_without_escaped_text,
    ))(input)
}

/// Matches the next quoted symbol string fragment while respecting the symbol delimiter (`'`).
fn quoted_symbol_fragment_without_escaped_text(input: &str) -> IonParseResult<StringFragment> {
    map(verify(is_not(r"'\"), |s: &str| !s.is_empty()), |text| {
        StringFragment::Substring(text)
    })(input)
}

/// Matches an identifier (e.g. `foo`) and returns the resulting [String]
/// as a [TextValue::Symbol].
fn identifier(input: &str) -> IonParseResult<TextValue> {
    let (remaining, identifier_text) = recognize(terminated(
        pair(identifier_initial_character, identifier_trailing_characters),
        not(identifier_trailing_character),
    ))(input)?;
    // Ion defines a number of keywords that are syntactically indistinguishable from
    // identifiers. Keywords take precedence; we must ensure that any identifier we find
    // is not actually a keyword.
    const KEYWORDS: &[&str] = &["true", "false", "nan", "null"];
    // In many situations, this check will not be necessary. Another type's parser will
    // recognize the keyword as its own. (For example, `parse_boolean` would match the input
    // text `false`.) However, because symbols can appear in annotations and the check for
    // annotations precedes the parsing for all other types, we need this extra verification.
    if KEYWORDS.iter().any(|k| *k == identifier_text) {
        // Finding a keyword is not a fatal error, it just means that this parser doesn't match.
        return Err(Err::Error(IonParseError::new(input)));
    }
    Ok((remaining, TextValue::Symbol(text_token(identifier_text))))
}

/// Matches any character that can appear at the start of an identifier.
fn identifier_initial_character(input: &str) -> IonParseResult<char> {
    alt((one_of("$_"), satisfy(|c| c.is_ascii_alphabetic())))(input)
}

/// Matches any character that is legal in an identifier, though not necessarily at the beginning.
fn identifier_trailing_character(input: &str) -> IonParseResult<char> {
    alt((one_of("$_"), satisfy(|c| c.is_ascii_alphanumeric())))(input)
}

/// Matches characters that are legal in an identifier, though not necessarily at the beginning.
fn identifier_trailing_characters(input: &str) -> IonParseResult<&str> {
    recognize(many0_count(identifier_trailing_character))(input)
}

/// Matches an operator (e.g. `++` or `@`) and returns the resulting [String]
/// as a [TextValue::Symbol]. This symbol syntax is only recognized inside of an s-expression.
pub(crate) fn parse_operator(input: &str) -> IonParseResult<TextValue> {
    // This function is used by the [s_expression_value] parser in the [containers] module.

    // The 'recognizer' below  is a parser responsible for identifying the &str slice at the
    // beginning of input that represents an operator. The `map` operation that follows uses
    // this parser's output to construct the necessary TextValue.

    // Other parsers don't have their own leading whitespace matcher because the overarching
    // top_level_stream_value parser takes care of this. However, operators can't appear at the top
    // level and so must fend for themselves.
    let recognizer = preceded(multispace0, is_a("!#%&*+-./;<=>?@^`|~"));
    map(recognizer, |op_text| TextValue::Symbol(text_token(op_text)))(input).upgrade()
}

/// Matches a symbol ID in the format `$ID` (For example, `$0` or `$42`.)
fn symbol_id(input: &str) -> IonParseResult<TextValue> {
    use crate::types::SymbolId;
    let (remaining, symbol_id_text) = terminated(
        // Discard a `$` and parse an integer representing the symbol ID.
        // Note that symbol ID integers:
        //   * CANNOT have underscores in them. For example: `$1_0` is considered an identifier.
        //   * CAN have leading zeros. There's precedent for this in ion-java.
        preceded(tag("$"), digit1),
        // Peek at the next character to make sure it's unrelated to the symbol ID.
        // The spec does not offer a formal definition of what ends a symbol ID.
        // This checks for either a stop_character (which performs its own `peek()`)
        // or a colon (":"), which could be a field delimiter (":") or the beginning of
        // an annotation delimiter ('::').
        alt((
            // Each of the parsers passed to `alt` must have the same return type. `stop_character`
            // returns a char instead of a &str, so we use `recognize()` to get a &str instead.
            recognize(stop_character),
            peek(tag(":")), // Field delimiter (":") or annotation delimiter ("::")
        )),
    )(input)?;
    const RADIX: u32 = 10;
    let symbol = i64::from_str_radix(symbol_id_text, RADIX)
        .or_fatal_parse_error(input, "could not parse symbol ID")
        .map(|(_, i)| TextValue::Symbol(local_sid_token(i as SymbolId)))?;
    Ok((remaining, symbol))
}

#[cfg(test)]
mod symbol_parsing_tests {
    use super::*;
    use crate::raw_symbol_token::local_sid_token;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::types::SymbolId;
    use rstest::*;

    // Asserts that when parsed, the provided text produces a TextValue::Symbol
    // that contains the expected text.
    fn parse_equals(text: &str, expected: &str) {
        parse_test_ok(parse_symbol, text, TextValue::Symbol(text_token(expected)))
    }

    // Asserts that when parsed, the provided text produces a TextValue::Symbol
    // that contains the expected local symbol ID.
    fn parse_sid_equals(text: &str, expected: SymbolId) {
        parse_test_ok(
            symbol_id,
            text,
            TextValue::Symbol(local_sid_token(expected)),
        )
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_symbol, text)
    }

    fn parse_sid_fails(text: &str) {
        parse_test_err(symbol_id, text)
    }

    #[test]
    fn test_parse_quoted_symbols() {
        parse_equals("'foo' ", "foo");
        parse_equals("'$foo' ", "$foo");
        parse_equals("'_foo' ", "_foo");
        parse_equals("'11foo' ", "11foo");
        parse_equals("'$_' ", "$_");
        parse_equals("'$ion_1_0' ", "$ion_1_0");
        parse_equals("'__foo__' ", "__foo__");
        parse_equals("'foo12345' ", "foo12345");
        parse_equals("'foo bar baz' ", "foo bar baz");
        parse_equals("'foo \"bar\" baz' ", "foo \"bar\" baz");
        parse_equals("'7@#$%^&*()!' ", "7@#$%^&*()!");
        parse_equals(r"'$99' ", r"$99");

        parse_equals(r"'foo \' foo' ", "foo ' foo");

        // Leading whitespace not accepted
        parse_fails(" 'foo' ");
    }

    #[test]
    fn test_parse_symbol_identifiers() {
        parse_equals("foo ", "foo");
        parse_equals("$foo ", "$foo");
        parse_equals("_foo ", "_foo");
        parse_equals("$_ ", "$_");
        parse_equals("$ion_1_0 ", "$ion_1_0");
        parse_equals("__foo__ ", "__foo__");
        parse_equals("foo12345 ", "foo12345");

        // Starts with a digit
        parse_fails("1foo ");
        // Leading whitespace not accepted
        parse_fails(" foo ");
        // Cannot be the last thing in input (stream might be incomplete
        parse_fails("foo");
    }

    #[rstest]
    #[case::sid_zero("$0 ", 0)]
    #[case("$21 ", 21)]
    #[case("$509 ", 509)]
    //        v--- Symbol IDs can have leading zeros
    #[case("$007 ", 7)]
    #[case("$17305 ", 17_305)]
    #[should_panic]
    //              v--- Symbol IDs cannot have underscores in them
    #[case::bad("$17_305 ", 17_305)]
    fn test_parse_symbol_ids(#[case] text: &str, #[case] expected: SymbolId) {
        parse_sid_equals(text, expected);
    }

    #[rstest]
    #[case("-> ", "->")]
    #[case("->)", "->")]
    #[case("++ ", "++")]
    #[case("++)", "++")]
    #[case("... ", "...")]
    #[case("...)", "...")]
    #[case("// ", "//")]
    #[case("//)", "//")]
    fn test_parse_operators(#[case] text: &str, #[case] expected: &str) {
        parse_test_ok(
            parse_operator,
            text,
            TextValue::Symbol(text_token(expected)),
        )
    }

    #[test]
    fn operators_and_negative_numbers() {
        parse_test_ok(parse_operator, "--3", TextValue::Symbol(text_token("--")));
    }

    #[test]
    fn operators_adjacent_to_sexp() {
        parse_test_ok(parse_operator, "+(2)-", TextValue::Symbol(text_token("+")));
    }
}
