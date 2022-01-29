use std::ops::DivAssign;
use std::str::FromStr;

use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::complete::digit1;
use nom::character::streaming::{char, one_of};
use nom::combinator::{map, map_res, opt, recognize};
use nom::sequence::{pair, preceded, separated_pair, terminated, tuple};
use nom::IResult;
use num_bigint::BigUint;

use crate::result::IonError;
use crate::text::parsers::{digit, stop_character, trim_zeros_expect_i32, trim_zeros_expect_u32};
use crate::text::text_value::TextValue;
use crate::types::decimal::Decimal;
use crate::types::timestamp::{FractionalSecondSetter, Timestamp};

/// Matches the text representation of a timestamp value and returns the resulting Timestamp
/// as a [TextValue::Timestamp].
pub(crate) fn parse_timestamp(input: &str) -> IResult<&str, TextValue> {
    alt((
        timestamp_precision_y,
        timestamp_precision_ym,
        timestamp_precision_ymd,
        timestamp_precision_ymd_hm,
        timestamp_precision_ymd_hms,
        timestamp_precision_ymd_hms_fractional,
    ))(input)
}

/// Matches the text representation of a timestamp value with year precision (e.g. `2018T`) and
/// returns the resulting Timestamp as a [TextValue::Timestamp].
fn timestamp_precision_y(input: &str) -> IResult<&str, TextValue> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(year, pair(tag("T"), stop_character)),
        |year| {
            let timestamp = Timestamp::with_year(year).build()?;
            Ok(TextValue::Timestamp(timestamp))
        },
    )(input)
}

/// Matches the text representation of a timestamp value with month precision (e.g. `2018-06T`) and
/// returns the resulting Timestamp as a [TextValue::Timestamp].
fn timestamp_precision_ym(input: &str) -> IResult<&str, TextValue> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(pair(year, month), pair(tag("T"), stop_character)),
        |(year, month)| {
            let timestamp = Timestamp::with_year(year).with_month(month).build()?;
            Ok(TextValue::Timestamp(timestamp))
        },
    )(input)
}

/// Matches the text representation of a timestamp value with day precision (e.g. `2018-06-12T`) and
/// returns the resulting Timestamp as a [TextValue::Timestamp].
fn timestamp_precision_ymd(input: &str) -> IResult<&str, TextValue> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(
            tuple((year, month, day)),
            pair(opt(tag("T")), stop_character),
        ),
        |(year, month, day)| {
            let timestamp = Timestamp::with_ymd(year, month, day).build()?;
            Ok(TextValue::Timestamp(timestamp))
        },
    )(input)
}

/// Matches the text representation of a timestamp value with minute precision
/// (e.g. `2018-06-12T:23:57-05:00`) and returns the resulting Timestamp as
/// a [TextValue::Timestamp].
fn timestamp_precision_ymd_hm(input: &str) -> IResult<&str, TextValue> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(
            pair(tuple((year, month, day, hour_and_minute)), timezone_offset),
            stop_character,
        ),
        |((year, month, day, (hour, minute)), offset)| {
            let builder = Timestamp::with_ymd(year, month, day).with_hour_and_minute(hour, minute);
            let timestamp = if let Some(minutes) = offset {
                builder.build_at_offset(minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            Ok(TextValue::Timestamp(timestamp))
        },
    )(input)
}

/// Matches the text representation of a timestamp value with second precision
/// (e.g. `2018-06-12T:23:57:45-05:00`) and returns the resulting Timestamp as
/// a [TextValue::Timestamp].
fn timestamp_precision_ymd_hms(input: &str) -> IResult<&str, TextValue> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(
            pair(
                tuple((year, month, day, hour_and_minute, second)),
                timezone_offset,
            ),
            stop_character,
        ),
        |((year, month, day, (hour, minute), second), offset)| {
            let builder = Timestamp::with_ymd(year, month, day).with_hms(hour, minute, second);
            let timestamp = if let Some(minutes) = offset {
                builder.build_at_offset(minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            Ok(TextValue::Timestamp(timestamp))
        },
    )(input)
}

/// Matches the text representation of a timestamp value with fractional second precision
/// (e.g. `2018-06-12T:23:57:45.993-05:00`) and returns the resulting Timestamp as
/// a [TextValue::Timestamp].
fn timestamp_precision_ymd_hms_fractional(input: &str) -> IResult<&str, TextValue> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(
            pair(
                tuple((
                    year,
                    month,
                    day,
                    hour_and_minute,
                    second,
                    recognize_fractional_seconds,
                )),
                timezone_offset,
            ),
            stop_character,
        ),
        |((year, month, day, (hour, minute), second, fractional), offset)| {
            let builder = Timestamp::with_ymd(year, month, day).with_hms(hour, minute, second);
            let builder = assign_fractional_seconds(fractional, builder);
            let timestamp = if let Some(minutes) = offset {
                builder.build_at_offset(minutes)?
            } else {
                builder.build_at_unknown_offset()?
            };
            Ok(TextValue::Timestamp(timestamp))
        },
    )(input)
}

/// Parses the fractional seconds and stores it in the [FractionalSecondSetter].
fn assign_fractional_seconds(
    fractional: &str,
    mut setter: FractionalSecondSetter,
) -> FractionalSecondSetter {
    let number_of_digits = fractional.len();
    // If the precision is less than or equal to nanoseconds...
    if number_of_digits <= 9 {
        // Convert the number to nanoseconds and make a note of its original precision.
        let power = 9 - number_of_digits;
        let nanoseconds =
            trim_zeros_expect_u32(fractional, "fractional seconds") * 10u32.pow(power as u32);
        setter = setter.with_nanoseconds_and_precision(nanoseconds, number_of_digits as u32);
    } else {
        // Otherwise, the number's precision is great enough that we'll need to construct a Decimal
        // to store it without loss of fidelity.
        let coefficient =
            BigUint::from_str(fractional).expect("parsing fractional seconds as BigUint failed");
        let mut digit_count = 1i64;
        let mut tmp_coefficient = coefficient.clone();
        let ten = BigUint::from(10u32);
        while tmp_coefficient > ten {
            tmp_coefficient.div_assign(&ten);
            digit_count += 1;
        }
        let decimal = Decimal::new(coefficient, -digit_count);
        setter = setter.with_fractional_seconds(decimal);
    }
    setter
}

/// Matches a four-digit year, returning it as a u32.
fn year(input: &str) -> IResult<&str, u32> {
    let y = digit;
    map(recognize(tuple((y, y, y, y))), |year| {
        trim_zeros_expect_u32(year, "year")
    })(input)
}

/// Matches a two-digit month, returning it as a u32.
fn month(input: &str) -> IResult<&str, u32> {
    map(
        preceded(
            tag("-"),
            recognize(alt((
                pair(char('0'), one_of("123456789")),
                pair(char('1'), one_of("012")),
            ))),
        ),
        |month: &str| trim_zeros_expect_u32(month, "month"),
    )(input)
}

/// Matches a two-digit day, returning it as a u32.
fn day(input: &str) -> IResult<&str, u32> {
    map(
        preceded(
            tag("-"),
            recognize(alt((
                pair(char('0'), one_of("123456789")),
                pair(one_of("12"), digit),
                pair(char('3'), one_of("01")),
            ))),
        ),
        |day| trim_zeros_expect_u32(day, "day"),
    )(input)
}

/// Matches a 'T' followed by the hour and minute (`T15:35`), returning them as as a (u32, u32) pair.
fn hour_and_minute(input: &str) -> IResult<&str, (u32, u32)> {
    map(
        preceded(
            tag("T"),
            separated_pair(
                recognize(alt((
                    pair(one_of("01"), digit),
                    pair(one_of("2"), one_of("0123")),
                ))),
                tag(":"),
                recognize(pair(one_of("012345"), digit)),
            ),
        ),
        |(hours, minutes)| {
            let hours = trim_zeros_expect_u32(hours, "hours");
            let minutes = trim_zeros_expect_u32(minutes, "minutes");
            (hours, minutes)
        },
    )(input)
}

/// Matches a ':' followed by a two-digit second field. (`:44`)
fn second(input: &str) -> IResult<&str, u32> {
    map(
        preceded(tag(":"), recognize(pair(one_of("012345"), digit))),
        |seconds| trim_zeros_expect_u32(seconds, "seconds"),
    )(input)
}

/// Recognizes a decimal point followed by one or more digits.
fn recognize_fractional_seconds(input: &str) -> IResult<&str, &str> {
    preceded(tag("."), digit1)(input)
}

/// Matches a timezone offset (`Z`, `-00:00`, `-05:00`, or `+01:00`) and returns it as a number of
/// minutes offset from UTC. Negative numbers indicate timezones west of UTC.
fn timezone_offset(input: &str) -> IResult<&str, Option<i32>> {
    alt((
        map(tag("Z"), |_| Some(0)),
        map(tag("-00:00"), |_| None),
        map(
            pair(one_of("-+"), timezone_offset_hours_minutes),
            |(sign, (hours, minutes))| {
                let hours = trim_zeros_expect_i32(hours, "offset hours");
                let minutes = trim_zeros_expect_i32(minutes, "offset minutes");
                let offset_minutes = (hours * 60) + minutes;
                if sign == '-' {
                    return Some(-offset_minutes);
                }
                Some(offset_minutes)
            },
        ),
    ))(input)
}

/// Recognizes the hours and minutes portions of a timezone offset. (`12` and `35` in `12:35`)
fn timezone_offset_hours_minutes(input: &str) -> IResult<&str, (&str, &str)> {
    separated_pair(
        // The parser does not restrict the range of hours/minutes allowed in the offset.
        recognize(pair(digit, digit)),
        tag(":"),
        recognize(pair(digit, digit)),
    )(input)
}

#[cfg(test)]
mod reader_tests {
    use crate::result::IonResult;
    use crate::text::parsers::timestamp::parse_timestamp;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::text_value::TextValue;
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;

    fn parse_equals(text: &str, expected: Timestamp) {
        parse_test_ok(parse_timestamp, text, TextValue::Timestamp(expected))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_timestamp, text)
    }

    #[test]
    fn test_parse_timestamp_y() -> IonResult<()> {
        parse_equals("0001T ", Timestamp::with_year(1).build()?);
        parse_equals("1997T ", Timestamp::with_year(1997).build()?);
        parse_equals("2021T ", Timestamp::with_year(2021).build()?);

        // Leading whitespace
        parse_fails(" 1997T ");
        // No trailing 'T', would parse as integers
        parse_fails("1997 ");
        // Must be exactly 4 digits
        parse_fails("997T ");
        Ok(())
    }

    #[test]
    fn test_parse_timestamp_ym() -> IonResult<()> {
        parse_equals(
            "2021-01T ",
            Timestamp::with_year(2021).with_month(1).build()?,
        );
        parse_equals(
            "2021-09T ",
            Timestamp::with_year(2021).with_month(9).build()?,
        );

        // Leading whitespace
        parse_fails(" 2021-09T ");
        // No trailing 'T'
        parse_fails("2021-06 ");
        // Multiple '-'s
        parse_fails("2021--06 ");
        // No month 0
        parse_fails("2021-00T ");
        Ok(())
    }

    #[test]
    fn test_parse_timestamp_ymd() -> IonResult<()> {
        parse_equals("2021-09-01 ", Timestamp::with_ymd(2021, 9, 1).build()?);
        parse_equals("2021-09-30T ", Timestamp::with_ymd(2021, 9, 30).build()?);

        // Wrong delimiter
        parse_fails("2021/09/30 ");
        // No 31st of September
        parse_fails("2021-09-31T ");
        // No 17th month
        parse_fails("2021-17-31T ");
        // No negative years
        parse_fails("-2021-09-30T ");
        // Years must be exactly 4 digits
        parse_fails("900-09-30T ");
        parse_fails("19900-09-30T ");
        Ok(())
    }

    #[test]
    fn test_parse_timestamp_ymd_hm() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 9, 30);
        parse_equals(
            "2021-09-30T00:00Z ",
            builder
                .clone()
                .with_hour_and_minute(0, 0)
                .build_at_offset(0)?,
        );
        parse_equals(
            "2021-09-30T23:11+00:00 ",
            builder
                .clone()
                .with_hour_and_minute(23, 11)
                .build_at_offset(0)?,
        );
        parse_equals(
            "2021-09-30T23:11-05:00 ",
            builder
                .clone()
                .with_hour_and_minute(23, 11)
                .build_at_offset(-300)?,
        );
        parse_equals(
            "2021-09-30T21:47-00:00 ",
            builder
                .with_hour_and_minute(21, 47)
                .build_at_unknown_offset()?,
        );

        // Missing offset
        parse_fails("2021-09-01T23:11");
        Ok(())
    }

    #[test]
    fn test_parse_timestamp_ymd_hms() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 12, 25);
        parse_equals(
            "2021-12-25T00:00:00Z ",
            builder.clone().with_hms(0, 0, 0).build_at_offset(0)?,
        );
        parse_equals(
            "2021-12-25T17:00:38+00:00 ",
            builder.clone().with_hms(17, 0, 38).build_at_offset(0)?,
        );
        parse_equals(
            "2021-12-25T08:35:07-05:30 ",
            builder.clone().with_hms(8, 35, 7).build_at_offset(-330)?,
        );
        parse_equals(
            "2021-12-25T12:25:59-00:00 ",
            builder.with_hms(12, 25, 59).build_at_unknown_offset()?,
        );
        Ok(())
    }

    #[test]
    fn test_parse_timestamp_ymd_hms_f() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 12, 25).with_hms(14, 30, 31);
        parse_equals(
            "2021-12-25T14:30:31.193+00:00 ",
            builder.clone().with_milliseconds(193).build_at_offset(0)?,
        );
        parse_equals(
            "2021-12-25T14:30:31.193193-05:00 ",
            builder
                .clone()
                .with_microseconds(193193)
                .build_at_offset(-300)?,
        );
        parse_equals(
            "2021-12-25T14:30:31.193193193-00:00 ",
            builder
                .clone()
                .with_nanoseconds(193193193)
                .build_at_unknown_offset()?,
        );
        parse_equals(
            "2021-12-25T14:30:31.19319319319-00:00 ",
            builder
                .clone()
                .with_fractional_seconds(Decimal::new(19319319319i64, -11))
                .build_at_unknown_offset()?,
        );
        parse_equals(
            "2021-12-25T14:30:31.193193193193193-00:00 ",
            builder
                .with_fractional_seconds(Decimal::new(193193193193193i64, -15))
                .build_at_unknown_offset()?,
        );
        Ok(())
    }
}
