use std::str::FromStr;

use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::complete::digit1;
use nom::character::streaming::{char, one_of, satisfy};
use nom::combinator::{map, opt, recognize};
use nom::sequence::{pair, preceded, separated_pair, terminated, tuple};
use nom::IResult;
use num_bigint::BigUint;

use crate::text::parse_result::{
    fatal_parse_error, IonParseResult, OrFatalParseError, UpgradeIResult,
};
use crate::text::parsers::{stop_character, trim_zeros_and_parse_i32, trim_zeros_and_parse_u32};
use crate::text::text_value::TextValue;
use crate::types::{Decimal, FractionalSecondSetter, Timestamp};

/// Matches the text representation of a timestamp value and returns the resulting Timestamp
/// as a [TextValue::Timestamp].
pub(crate) fn parse_timestamp(input: &str) -> IonParseResult<TextValue> {
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
fn timestamp_precision_y(input: &str) -> IonParseResult<TextValue> {
    let (remaining, year) = terminated(year, pair(tag("T"), stop_character))(input)?;
    let timestamp = Timestamp::with_year(year)
        .build()
        .or_fatal_parse_error(input, "could not create timestamp")?
        .1;
    Ok((remaining, TextValue::Timestamp(timestamp)))
}

/// Matches the text representation of a timestamp value with month precision (e.g. `2018-06T`) and
/// returns the resulting Timestamp as a [TextValue::Timestamp].
fn timestamp_precision_ym(input: &str) -> IonParseResult<TextValue> {
    let (remaining, (year, month)) =
        terminated(pair(year, month), pair(tag("T"), stop_character))(input)?;
    let timestamp = Timestamp::with_year(year)
        .with_month(month)
        .build()
        .or_fatal_parse_error(input, "could not create timestamp")?
        .1;
    Ok((remaining, TextValue::Timestamp(timestamp)))
}

/// Matches the text representation of a timestamp value with day precision (e.g. `2018-06-12T`) and
/// returns the resulting Timestamp as a [TextValue::Timestamp].
fn timestamp_precision_ymd(input: &str) -> IonParseResult<TextValue> {
    let (remaining, (year, month, day)) = terminated(
        tuple((year, month, day)),
        pair(opt(tag("T")), stop_character),
    )(input)?;
    let timestamp = Timestamp::with_ymd(year, month, day)
        .build()
        .or_fatal_parse_error(input, "could not create timestamp")?
        .1;
    Ok((remaining, TextValue::Timestamp(timestamp)))
}

/// Matches the text representation of a timestamp value with minute precision
/// (e.g. `2018-06-12T:23:57-05:00`) and returns the resulting Timestamp as
/// a [TextValue::Timestamp].
fn timestamp_precision_ymd_hm(input: &str) -> IonParseResult<TextValue> {
    let (remaining, ((year, month, day, (hour, minute)), offset)) = terminated(
        pair(tuple((year, month, day, hour_and_minute)), timezone_offset),
        stop_character,
    )(input)?;
    let builder = Timestamp::with_ymd(year, month, day).with_hour_and_minute(hour, minute);
    let timestamp = if let Some(minutes) = offset {
        builder.build_at_offset(minutes)
    } else {
        builder.build_at_unknown_offset()
    }
    .or_fatal_parse_error(input, "could not create timestamp")?
    .1;
    Ok((remaining, TextValue::Timestamp(timestamp)))
}

/// Matches the text representation of a timestamp value with second precision
/// (e.g. `2018-06-12T:23:57:45-05:00`) and returns the resulting Timestamp as
/// a [TextValue::Timestamp].
fn timestamp_precision_ymd_hms(input: &str) -> IonParseResult<TextValue> {
    let (remaining, ((year, month, day, (hour, minute), second), offset)) = terminated(
        pair(
            tuple((year, month, day, hour_and_minute, second)),
            timezone_offset,
        ),
        stop_character,
    )(input)?;
    let builder = Timestamp::with_ymd(year, month, day).with_hms(hour, minute, second);
    let timestamp = if let Some(minutes) = offset {
        builder.build_at_offset(minutes)
    } else {
        builder.build_at_unknown_offset()
    }
    .or_fatal_parse_error(input, "could not create timestamp")?
    .1;
    Ok((remaining, TextValue::Timestamp(timestamp)))
}

/// Matches the text representation of a timestamp value with fractional second precision
/// (e.g. `2018-06-12T:23:57:45.993-05:00`) and returns the resulting Timestamp as
/// a [TextValue::Timestamp].
fn timestamp_precision_ymd_hms_fractional(input: &str) -> IonParseResult<TextValue> {
    let (remaining, ((year, month, day, (hour, minute), second, fractional_text), offset)) =
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
        )(input)?;
    let builder = Timestamp::with_ymd(year, month, day).with_hms(hour, minute, second);
    let (_, builder) = assign_fractional_seconds(fractional_text, builder)?;
    let timestamp = if let Some(minutes) = offset {
        builder.build_at_offset(minutes)
    } else {
        builder.build_at_unknown_offset()
    }
    .or_fatal_parse_error(input, "could not create timestamp")?
    .1;
    Ok((remaining, TextValue::Timestamp(timestamp)))
}

/// Parses the fractional seconds and stores it in the [FractionalSecondSetter].
fn assign_fractional_seconds(
    fractional_text: &str,
    mut setter: FractionalSecondSetter,
) -> IonParseResult<FractionalSecondSetter> {
    let number_of_digits = fractional_text.len();
    // If the precision is less than or equal to nanoseconds...
    if number_of_digits <= 9 {
        // Convert the number to nanoseconds and make a note of its original precision.
        let power = 9 - number_of_digits;
        let (_, fractional) = trim_zeros_and_parse_u32(fractional_text, "fractional seconds")?;
        let nanoseconds = fractional * 10u32.pow(power as u32);
        setter = setter.with_nanoseconds_and_precision(nanoseconds, number_of_digits as u32);
    } else {
        // Otherwise, the number's precision is great enough that we'll need to construct a Decimal
        // to store it without loss of fidelity.
        let coefficient = BigUint::from_str(fractional_text)
            .or_fatal_parse_error(
                fractional_text,
                "parsing fractional seconds as BigUInt failed",
            )?
            .1;
        let decimal = Decimal::new(coefficient, -(number_of_digits as i64));
        setter = setter.with_fractional_seconds(decimal);
    }
    Ok(("", setter))
}

/// Matches a four-digit year, returning it as a u32.
fn year(input: &str) -> IonParseResult<u32> {
    let y = digit;
    let (remaining, year_text) = recognize(tuple((y, y, y, y)))(input).upgrade()?;
    let (_, year) = trim_zeros_and_parse_u32(year_text, "year")?;
    Ok((remaining, year))
}

/// Matches a two-digit month, returning it as a u32.
fn month(input: &str) -> IonParseResult<u32> {
    let (remaining, month_text) = preceded(
        tag("-"),
        recognize(alt((
            pair(char('0'), one_of("123456789")),
            pair(char('1'), one_of("012")),
        ))),
    )(input)
    .upgrade()?;
    let (_, month) = trim_zeros_and_parse_u32(month_text, "month")?;
    Ok((remaining, month))
}

/// Matches a two-digit day, returning it as a u32.
fn day(input: &str) -> IonParseResult<u32> {
    let (remaining, day_text) = preceded(
        tag("-"),
        recognize(alt((
            pair(char('0'), one_of("123456789")),
            pair(one_of("12"), digit),
            pair(char('3'), one_of("01")),
        ))),
    )(input)
    .upgrade()?;

    let (_, day) = trim_zeros_and_parse_u32(day_text, "day")?;
    Ok((remaining, day))
}

/// Matches a 'T' followed by the hour and minute (`T15:35`), returning them as as a (u32, u32) pair.
fn hour_and_minute(input: &str) -> IonParseResult<(u32, u32)> {
    let (remaining, (hours_text, minutes_text)) = preceded(
        tag("T"),
        separated_pair(
            recognize(alt((
                pair(one_of("01"), digit),
                pair(one_of("2"), one_of("0123")),
            ))),
            tag(":"),
            recognize(pair(one_of("012345"), digit)),
        ),
    )(input)
    .upgrade()?;
    let (_, hours) = trim_zeros_and_parse_u32(hours_text, "hours")?;
    let (_, minutes) = trim_zeros_and_parse_u32(minutes_text, "minutes")?;
    Ok((remaining, (hours, minutes)))
}

/// Matches a ':' followed by a two-digit second field. (`:44`)
fn second(input: &str) -> IonParseResult<u32> {
    let (remaining, seconds) =
        preceded(tag(":"), recognize(pair(one_of("012345"), digit)))(input).upgrade()?;
    let (_, seconds) = trim_zeros_and_parse_u32(seconds, "seconds")?;
    Ok((remaining, seconds))
}

/// Recognizes a decimal point followed by one or more digits.
fn recognize_fractional_seconds(input: &str) -> IonParseResult<&str> {
    preceded(tag("."), digit1)(input).upgrade()
}

/// Matches a timezone offset (`Z`, `-00:00`, `-05:00`, or `+01:00`) and returns it as a number of
/// minutes offset from UTC. Negative numbers indicate timezones west of UTC.
fn timezone_offset(input: &str) -> IonParseResult<Option<i32>> {
    alt((
        map(tag("Z"), |_| Some(0)),
        map(tag("-00:00"), |_| None),
        map(
            pair(one_of("-+"), timezone_offset_hours_minutes),
            |(sign, (hours, minutes))| {
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
fn timezone_offset_hours_minutes(input: &str) -> IonParseResult<(i32, i32)> {
    let (remaining_input, (hours, minutes)) = separated_pair(
        recognize(pair(digit, digit)),
        tag(":"),
        recognize(pair(digit, digit)),
    )(input)
    .upgrade()?;
    let (_, hour_int) = trim_zeros_and_parse_i32(hours, "offset hours")?;
    let (_, minute_int) = trim_zeros_and_parse_i32(minutes, "offset minutes")?;
    if hour_int >= 24 {
        return fatal_parse_error(hours, "timestamp hours were >= 24");
    }
    if minute_int >= 60 {
        return fatal_parse_error(hours, "timestamp minutes were >= 60");
    }
    Ok((remaining_input, (hour_int, minute_int)))
}

#[cfg(test)]
mod reader_tests {
    use crate::result::IonResult;
    use crate::text::parsers::timestamp::parse_timestamp;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::text_value::TextValue;
    use crate::types::{Decimal, Timestamp};

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

/// Matches the next input character if it is a base-10 digit. This wraps [char::is_digit] in the
/// nom parsing function signature.
pub(crate) fn digit(input: &str) -> IResult<&str, char> {
    satisfy(|c| c.is_ascii_digit())(input)
}
