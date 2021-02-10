use std::str::FromStr;

use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::complete::digit1;
use nom::character::streaming::{one_of, char};
use nom::combinator::{map, map_res, recognize, opt};
use nom::IResult;
use nom::sequence::{pair, preceded, separated_pair, terminated, tuple};
use num_bigint::BigUint;

use crate::result::{IonError, IonResult};
use crate::text::parsers::{stop_character, trim_zeros_expect_u32, digit, trim_zeros_expect_i32};
use crate::types::decimal::{Decimal, Sign};
use crate::types::timestamp::{FractionalSecondSetter, Timestamp};
use std::ops::DivAssign;
use crate::text::TextStreamItem;

pub(crate) fn parse_timestamp(input: &str) -> IResult<&str, TextStreamItem> {
    alt((
        timestamp_precision_y,
        timestamp_precision_ym,
        timestamp_precision_ymd,
        timestamp_precision_ymd_hm,
        timestamp_precision_ymd_hms,
        timestamp_precision_ymd_hms_fractional
    ))(input)
}

fn timestamp_precision_y(input: &str) -> IResult<&str, TextStreamItem> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(year, pair(tag("T"), stop_character)),
        |year| {
            let timestamp = Timestamp::with_year(year).build()?;
            Ok(TextStreamItem::Timestamp(timestamp))
        },
    )(input)
}

fn timestamp_precision_ym(input: &str) -> IResult<&str, TextStreamItem> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(pair(year, month), pair(tag("T"), stop_character)),
        |(year, month)| {
            let timestamp = Timestamp::with_year(year)
                .with_month(month)
                .build()?;
            Ok(TextStreamItem::Timestamp(timestamp))
        },
    )(input)
}

fn timestamp_precision_ymd(input: &str) -> IResult<&str, TextStreamItem> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(tuple((year, month, day)), pair(opt(tag("T")), stop_character)),
        |(year, month, day)| {
            let timestamp = Timestamp::with_ymd(year, month, day).build()?;
            Ok(TextStreamItem::Timestamp(timestamp))
        },
    )(input)
}

fn timestamp_precision_ymd_hm(input: &str) -> IResult<&str, TextStreamItem> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(pair(tuple((year, month, day, hour_and_minute)), timezone_offset), stop_character),
        |((year, month, day, (hour, minute)), offset)| {
            let builder = Timestamp::with_ymd(year, month, day)
                .with_hour_and_minute(hour, minute);
            let timestamp = if let Some(minutes) = offset {
                builder.build_at_offset(minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            Ok(TextStreamItem::Timestamp(timestamp))
        },
    )(input)
}

fn timestamp_precision_ymd_hms(input: &str) -> IResult<&str, TextStreamItem> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(pair(tuple((year, month, day, hour_and_minute, second)), timezone_offset), stop_character),
        |((year, month, day, (hour, minute), second), offset)| {
            let builder = Timestamp::with_ymd(year, month, day)
                .with_hms(hour, minute, second);
            let timestamp = if let Some(minutes) = offset {
                builder.build_at_offset(minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            Ok(TextStreamItem::Timestamp(timestamp))
        },
    )(input)
}

fn timestamp_precision_ymd_hms_fractional(input: &str) -> IResult<&str, TextStreamItem> {
    map_res::<_, _, _, _, IonError, _, _>(
        terminated(pair(tuple((year, month, day, hour_and_minute, second, recognize_fractional_seconds)), timezone_offset), stop_character),
        |((year, month, day, (hour, minute), second, fractional), offset)| {
            let builder = Timestamp::with_ymd(year, month, day)
                .with_hms(hour, minute, second);
            let timestamp = assign_fractional_seconds_and_build(fractional, builder, offset)?;
            Ok(TextStreamItem::Timestamp(timestamp))
        },
    )(input)
}

fn assign_fractional_seconds_and_build(fractional: &str, mut setter: FractionalSecondSetter, offset: Option<i32>) -> IonResult<Timestamp> {
    // If the precision is less than or equal to nanoseconds...
    let number_of_digits = fractional.len();
    if number_of_digits <= 9 {
        let power = 9 - number_of_digits;
        let nanoseconds = trim_zeros_expect_u32(fractional, "fractional seconds") * 10u32.pow(power as u32);
        setter = setter.with_nanoseconds_and_precision(nanoseconds, number_of_digits as u32);
    } else {
        let coefficient = BigUint::from_str(fractional)
            .expect("parsing fractional seconds as BigUint failed");
        let mut digit_count = 1i64;
        let mut tmp_coefficient = coefficient.clone();
        let ten = BigUint::from(10u32);
        while tmp_coefficient > ten {
            tmp_coefficient.div_assign(&ten);
            digit_count += 1;
        }
        let decimal = Decimal::new(Sign::Positive, coefficient, -1 * digit_count);
        setter = setter.with_fractional_seconds(decimal);
    }
    if let Some(minutes) = offset {
        return Ok(setter.build_at_offset(minutes)?);
    }

    Ok(setter.build_at_unknown_offset()?)
}

fn year(input: &str) -> IResult<&str, u32> {
    let y = digit;
    map(
        recognize(tuple((y, y, y, y))),
        |year| trim_zeros_expect_u32(year, "year"),
    )(input)
}

fn month(input: &str) -> IResult<&str, u32> {
    map(
        preceded(
            tag("-"),
            recognize(
                alt((
                    pair(char('0'), one_of("123456789")),
                    pair(char('1'), one_of("012"))
                ))
            ),
        ),
        |month: &str| trim_zeros_expect_u32(month, "month"),
    )(input)
}

fn day(input: &str) -> IResult<&str, u32> {
    map(
        preceded(
            tag("-"),
            recognize(
                alt((
                    pair(char('0'), one_of("123456789")),
                    pair(one_of("12"), digit),
                    pair(char('3'), one_of("01"))
                ))
            ),
        ),
        |day| trim_zeros_expect_u32(day, "day"),
    )(input)
}

fn hour_and_minute(input: &str) -> IResult<&str, (u32, u32)> {
    map(
        preceded(
            tag("T"),
            separated_pair(
                recognize(
                    alt((
                        pair(one_of("01"), digit),
                        pair(one_of("2"), one_of("0123")),
                    ))
                ),
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

fn second(input: &str) -> IResult<&str, u32> {
    map(
        preceded(
            tag(":"),
            recognize(pair(one_of("012345"), digit)),
        ),
        |seconds| trim_zeros_expect_u32(seconds, "seconds"),
    )(input)
}

fn recognize_fractional_seconds(input: &str) -> IResult<&str, &str> {
    preceded(tag("."), digit1)(input)
}

fn timezone_offset(input: &str) -> IResult<&str, Option<i32>> {
    alt((
        map(tag("Z"), |_| Some(0)),
        map(tag("-00:00"), |_| None),
        map(pair(one_of("-+"), timezone_offset_hours_minutes),
            |(sign, (hours, minutes))| {
                let hours = trim_zeros_expect_i32(hours, "offset hours");
                let minutes = trim_zeros_expect_i32(minutes, "offset minutes");
                let offset_minutes = (hours * 60) + minutes;
                if sign == '-' {
                    return Some(-1 * offset_minutes);
                }
                Some(offset_minutes)
            })
    ))(input)
}

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
    use crate::types::timestamp::Timestamp;
    use crate::result::IonResult;
    use crate::text::parsers::timestamp::parse_timestamp;
    use crate::types::decimal::{Decimal, Sign};
    use crate::text::parsers::unit_test_support::{parse_test_ok, parse_test_err};
    use crate::text::TextStreamItem;

    fn parse_equals(text: &str, expected: Timestamp) {
        parse_test_ok(parse_timestamp, text, TextStreamItem::Timestamp(expected))
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
        parse_equals("2021-01T ", Timestamp::with_year(2021).with_month(1).build()?);
        parse_equals("2021-09T ", Timestamp::with_year(2021).with_month(9).build()?);

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
        parse_equals("2021-09-30T00:00Z ", builder.clone().with_hour_and_minute(0, 0).build_at_offset(0)?);
        parse_equals("2021-09-30T23:11+00:00 ", builder.clone().with_hour_and_minute(23, 11).build_at_offset(0)?);
        parse_equals("2021-09-30T23:11-05:00 ", builder.clone().with_hour_and_minute(23, 11).build_at_offset(-300)?);
        parse_equals("2021-09-30T21:47-00:00 ", builder.clone().with_hour_and_minute(21, 47).build_at_unknown_offset()?);

        // Missing offset
        parse_fails("2021-09-01T23:11");
        Ok(())
    }

    #[test]
    fn test_parse_timestamp_ymd_hms() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 12, 25);
        parse_equals("2021-12-25T00:00:00Z ", builder.clone().with_hms(0, 0, 0).build_at_offset(0)?);
        parse_equals("2021-12-25T17:00:38+00:00 ", builder.clone().with_hms(17, 0, 38).build_at_offset(0)?);
        parse_equals("2021-12-25T08:35:07-05:30 ", builder.clone().with_hms(8, 35, 7).build_at_offset(-330)?);
        parse_equals("2021-12-25T12:25:59-00:00 ", builder.clone().with_hms(12, 25, 59).build_at_unknown_offset()?);
        Ok(())
    }

    #[test]
    fn test_parse_timestamp_ymd_hms_f() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 12, 25).with_hms(14, 30, 31);
        parse_equals("2021-12-25T14:30:31.193+00:00 ", builder.clone().with_milliseconds(193).build_at_offset(0)?);
        parse_equals("2021-12-25T14:30:31.193193-05:00 ", builder.clone().with_microseconds(193193).build_at_offset(-300)?);
        parse_equals("2021-12-25T14:30:31.193193193-00:00 ", builder.clone().with_nanoseconds(193193193).build_at_unknown_offset()?);
        parse_equals("2021-12-25T14:30:31.19319319319-00:00 ",
                     builder.clone()
                         .with_fractional_seconds(Decimal::new(Sign::Positive, 19319319319, -11))
                         .build_at_unknown_offset()?
        );
        parse_equals("2021-12-25T14:30:31.193193193193193-00:00 ",
                     builder.clone()
                         .with_fractional_seconds(Decimal::new(Sign::Positive, 193193193193193, -15))
                         .build_at_unknown_offset()?
        );
        Ok(())
    }
}