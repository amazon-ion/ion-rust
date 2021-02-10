use crate::IonType;
use nom::{IResult};
use crate::text::TextStreamItem;
use nom::combinator::{map_res, opt};
use nom::sequence::{delimited, preceded};
use nom::bytes::streaming::tag;
use crate::text::parsers::stop_character;
use crate::result::decoding_error;
use nom::character::streaming::{char, alpha1};

// Recognizes a null and converts it into a TextStreamItem::Null containing the associated
// IonType.
pub(crate) fn parse_null(input: &str) -> IResult<&str, TextStreamItem> {
    map_res(
        delimited(
            tag("null"),
            opt(preceded(char('.'), alpha1)),
            stop_character,
        ),
        |maybe_ion_type_text| {
            if let Some(ion_type_text) = maybe_ion_type_text {
                match ion_type_from_text(ion_type_text) {
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

#[cfg(test)]
mod null_parsing_tests {
    use crate::text::parsers::unit_test_support::{parse_test_ok, parse_test_err};
    use crate::text::TextStreamItem;
    use crate::text::parsers::null::parse_null;
    use crate::IonType;

    fn parse_equals(text: &str, expected: IonType) {
        parse_test_ok(parse_null, text, TextStreamItem::Null(expected))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_null, text)
    }

    #[test]
    fn test_parse_nulls() {
        use IonType::*;
        parse_equals("null ", Null);
        parse_equals("null.null ", Null);
        parse_equals("null.bool ", Boolean);
        parse_equals("null.int ", Integer);
        parse_equals("null.float ", Float);
        parse_equals("null.decimal ", Decimal);
        parse_equals("null.timestamp ", Timestamp);
        parse_equals("null.string ", String);
        parse_equals("null.symbol ", Symbol);
        parse_equals("null.blob ", Blob);
        parse_equals("null.clob ", Clob);
        parse_equals("null.list ", List);
        parse_equals("null.sexp ", SExpression);
        parse_equals("null.struct ", Struct);

        // Misspelled null
        parse_fails("nlul ");
        // Unrecognized type
        parse_fails("null.strunct ");
        // Leading whitespace
        parse_fails(" null.strunct ");
        // Null is end of current input; might be an incomplete stream
        parse_fails("null.struct");
    }
}