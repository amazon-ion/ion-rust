use crate::types::decimal::Decimal;
use chrono::{DateTime, FixedOffset, NaiveDateTime, Datelike, Timelike, TimeZone, NaiveDate};
use std::time::SystemTime;
use crate::result::{IonResult, illegal_operation, illegal_operation_raw};
use std::fmt::Debug;

//TODO: Revise doc
//
// This class cannot be part of Timestamp's public API because it is not self-contained. If its
// value is `Digits`, then it contains information about how to interpret the `nanoseconds` data
// in its parent `Timestamp`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Mantissa {
    /// The number of decimal places of precision in the accompanying Timestamp's fractional seconds.
    /// For example, a value of `3` would indicate millisecond precision. A value of `6` would
    /// indiciate microsecond precision. All precisions less than or equal to nanoseconds should use
    /// this representation.
    Digits(u32),
    /// Specifies the mantissa precisely as a `Decimal` in the range `>= 0` and `< 1`.
    /// This representation should only be used for precisions greater than nanoseconds as it
    /// can require allocations.
    Arbitrary(Decimal),
}

//TODO: Revise doc
/// Precision of a [Timestamp]].
///
/// All Ion timestamps are complete points in time, but they have explicit precision
/// that is either at the date components, the minute, or second (including sub-second)
/// granularity.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd)]
pub enum Precision {
    /// Year-level precision (e.g. `2020T`)
    Year,
    /// Month-level precision (e.g. `2020-08T`)
    Month,
    /// Day-level precision (e.g. `2020-08-01T`)
    Day,
    /// Minute-level precision (e.g. `2020-08-01T12:34Z`)
    HourAndMinute,
    /// Second-level precision. (e.g. `2020-08-01T12:34:56Z`)
    Second,
    /// Sub-second precision (e.g. `2020-08-01T12:34:56.123456789Z`)
    FractionalSeconds,
}

impl Default for Precision {
    fn default() -> Self {
        Precision::Year
    }
}

pub(crate) fn first_n_digits_of(num_digits: u32, value: u32) -> u32 {
    let total_digits = number_of_digits(value);
    if total_digits <= num_digits {
        return value;
    }
    // Truncate the trailing digits
    value / 10u32.pow(total_digits - num_digits)
}

pub(crate) fn number_of_digits(value: u32) -> u32 {
    match value {
        0 => 1,
        1 => 1,
        i => (i as f64).log10().ceil() as u32
    }
}



//TODO: doc
//
// Cannot derive PartialEq, Eq, PartialOrd, Ord because FractionalSeconds requires a manual impl
#[derive(Debug, Clone)]
pub struct Timestamp {
    date_time: NaiveDateTime,
    offset: Option<FixedOffset>,
    precision: Precision,
    fractional_seconds: Option<Mantissa>
}

impl Timestamp {
    pub fn from_datetime<D>(datetime: D,
                        precision: Precision) -> Timestamp
        where D: Datelike + Timelike + Into<Timestamp>
    {
        let mut timestamp: Timestamp = datetime.into();
        if precision < Precision::FractionalSeconds {
            timestamp.fractional_seconds = None;
        }
        timestamp.precision = precision;
        timestamp
    }

    // `Year` is the only required field for a timestamp, so this is the entry
    // point for using the builder API.
    pub fn with_year(year: u32) -> MonthSetter {
        let mut builder: TimestampBuilder = Default::default();
        builder.precision = Precision::Year;
        builder.year = year as u16;
        MonthSetter {
            builder
        }
    }

    // Convenience function for specifying several fields at once
    pub fn with_ymd(year: u32, month: u32, day: u32) -> HourAndMinuteSetter {
        let builder = Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .into_builder();
        HourAndMinuteSetter {
            builder
        }
    }

    // Convenience function for specifying several fields at once
    pub fn with_ymd_hms(
        year: u32,
        month: u32,
        day: u32,
        hour: u32,
        minute: u32,
        second: u32
    ) -> FractionalSecondSetter {
        let builder = Timestamp::with_ymd(year, month, day)
            .with_hms(hour, minute, second)
            .into_builder();
        FractionalSecondSetter {
            builder
        }
    }

    // Convenience function for specifying several fields at once
    pub fn with_ymd_hms_millis(
        year: u32,
        month: u32,
        day: u32,
        hour: u32,
        minute: u32,
        second: u32,
        milliseconds: u32,
    ) -> FractionalSecondSetter {
        let builder = Timestamp::with_ymd(year, month, day)
            .with_hms(hour, minute, second)
            .with_milliseconds(milliseconds)
            .into_builder();
        FractionalSecondSetter {
            builder
        }
    }

    fn fractional_seconds_equal(&self, other: &Timestamp) -> bool {
        use Mantissa::*;
        match (self.fractional_seconds.as_ref(), other.fractional_seconds.as_ref()) {
            (None, None) => true,
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (Some(Digits(d1)), Some(Digits(d2))) => {
                if d1 != d2 {
                    // Different precisions
                    return false;
                }
                let d1 = first_n_digits_of(*d1, self.date_time.nanosecond());
                let d2 = first_n_digits_of(*d2, other.date_time.nanosecond());
                d1 == d2
            },
            (Some(Arbitrary(d1)), Some(Arbitrary(d2))) => {
                d1.eq(d2)
            }
            (Some(Digits(d1)), Some(Arbitrary(d2))) => {
                let upgraded: Decimal = (*d1).into();
                upgraded.eq(d2)
            }
            (Some(Arbitrary(d1)), Some(Digits(d2))) => {
                let upgraded: Decimal = (*d2).into();
                d1.eq(&upgraded)
            }
        }
    }
}

impl PartialEq for Timestamp {
    fn eq(&self, other: &Self) -> bool {
        if self.precision != other.precision {
            return false;
        }
        if self.offset != other.offset {
            return false;
        }
        let self_dt = self.date_time;
        let other_dt = other.date_time;
        if self_dt.year() != other_dt.year() {
            return false;
        }
        if self.precision >= Precision::Month && self_dt.month() != other_dt.month() {
            return false;
        }
        if self.precision >= Precision::Day && self_dt.day() != other_dt.day() {
            return false;
        }
        if self.precision >= Precision::HourAndMinute &&
            (self_dt.hour() != other_dt.hour() || self_dt.minute() != other_dt.minute()) {
            return false;
        }
        if self.precision >= Precision::Second && self_dt.second() != other_dt.second() {
            return false;
        }
        if self.precision >= Precision::FractionalSeconds && !self.fractional_seconds_equal(other) {
            return false;
        }
        true
    }
}

impl From<NaiveDateTime> for Timestamp {
    fn from(date_time: NaiveDateTime) -> Self {
        Timestamp {
            date_time,
            offset: None,
            precision: Precision::Day,
            fractional_seconds: Some(Mantissa::Digits(9))
        }
    }
}

impl From<DateTime<FixedOffset>> for Timestamp {
    fn from(fixed_offset_date_time: DateTime<FixedOffset>) -> Self {
        // Discard the offset
        let date_time = fixed_offset_date_time.naive_utc();
        // Get a copy of the offset to store separately
        let offset = Some(*fixed_offset_date_time.offset());
        let precision = Precision::FractionalSeconds;
        let fractional_seconds = Some(Mantissa::Digits(9));
        Timestamp {
            date_time,
            offset,
            precision,
            fractional_seconds,
        }
    }
}

//TODO: PartialOrd for Timestamps with a known offset?

#[derive(Debug, Clone, Default)]
struct TimestampBuilder {
    precision: Precision,
    offset: Option<i32>,
    year: u16,
    month: Option<u8>,
    day: Option<u8>,
    hour: Option<u8>,
    minute: Option<u8>,
    second: Option<u8>,
    fractional_seconds: Option<Mantissa>,
    nanoseconds: Option<u32>,
}

impl TimestampBuilder {
    fn configure_datetime<D>(&mut self, mut datetime: D) -> IonResult<D>
        where D: Datelike + Timelike + Debug
    {
        datetime = datetime
            .with_year(self.year as i32)
            .ok_or_else(
                || illegal_operation_raw(format!("specified year ('{}') is invalid", self.year))
            )?;
        if self.precision == Precision::Year {
            return Ok(datetime);
        }

        // If precision >= Month, the month must be set.
        let month = self.month.expect("missing month");
        datetime = datetime
            .with_month(month as u32)
            .ok_or_else(
                || illegal_operation_raw(format!("specified month ('{}') is invalid", month))
            )?;
        if self.precision == Precision::Month {
            return Ok(datetime);
        }

        // If precision >= Day, the day must be set.
        let day = self.day.expect("missing day");
        datetime = datetime
            .with_day(day as u32)
            .ok_or_else(
                || illegal_operation_raw(format!("specified day ('{}') is invalid", day))
            )?;
        if self.precision == Precision::Day {
            return Ok(datetime);
        }

        // If precision >= HourAndMinute, the hour and minute must be set.
        let hour = self.hour.expect("missing hour");
        datetime = datetime
            .with_hour(hour as u32)
            .ok_or_else(
                || illegal_operation_raw(format!("specified hour ('{}') is invalid", hour))
            )?;
        let minute = self.minute.expect("missing minute");
        datetime = datetime
            .with_minute(minute as u32)
            .ok_or_else(
                || illegal_operation_raw(format!("specified minute ('{}') is invalid", minute))
            )?;
        if self.precision == Precision::HourAndMinute {
            return Ok(datetime);
        }

        // If precision >= Second, the second must be set.
        let second = self.second.expect("missing second");
        datetime = datetime
            .with_second(second as u32)
            .ok_or_else(
                || illegal_operation_raw(format!("provided second ('{}') is invalid.", second))
            )?;
        if self.precision == Precision::Second {
            return Ok(datetime);
        }

        // If precision == FractionalSecond, the fractional_second must be set.
        // If fractional seconds is Digit, self.nanoseconds will be Some(_).
        // If it's Arbitrary, self.nanoseconds will be None and we should set the nanoseconds
        // field to 0. The real value will be stored in the Timestamp alongside the DateTime
        // as a Decimal.
        datetime = datetime
            .with_nanosecond(self.nanoseconds.unwrap_or(0))
            .ok_or_else(
                || illegal_operation_raw(
                    format!("provided nanosecond ('{}') is invalid", second)
                )
            )?;

        Ok(datetime)
    }

    fn build(mut self) -> IonResult<Timestamp> {
        if let Some(offset) = self.offset {
            let offset = FixedOffset::west_opt(offset)
                .ok_or_else(|| illegal_operation_raw(
                    format!("specified offset ('{}') is invalid", offset)
                ))?;
            let mut datetime: DateTime<FixedOffset> = offset
                .ymd(0,1,1)
                .and_hms_nano(0,0,0, 0);
            datetime = self.configure_datetime(datetime)?;
            let mut timestamp = Timestamp::from_datetime(datetime, self.precision);
            if self.precision == Precision::FractionalSeconds {
                timestamp.fractional_seconds = self.fractional_seconds;
            }
            Ok(timestamp)
        } else {
            let mut datetime: NaiveDateTime = NaiveDate::from_ymd(0, 1, 1)
                .and_hms_nano(0, 0, 0, 0);
            datetime = self.configure_datetime(datetime)?;
            let mut timestamp = Timestamp::from_datetime(datetime, self.precision);
            if self.precision == Precision::FractionalSeconds {
                timestamp.fractional_seconds = self.fractional_seconds;
            }
            Ok(timestamp)
        }
    }
}

#[derive(Debug, Clone)]
pub struct MonthSetter {
    builder: TimestampBuilder
}

impl MonthSetter {
    // Libraries have conflicting opinions about whether months should be
    // 0- or 1-indexed, so Timestamp follows chrono's lead and provides
    // convenient ways to do both. Internally, it uses a 1-based representation.

    // 0-indexed month
    pub fn with_month0(self, year: u32) -> DaySetter {
        self.with_month(year+1)
    }

    // 1-indexed month
    pub fn with_month(self, month: u32) -> DaySetter {
        let mut builder = self.builder;
        builder.precision = Precision::Month;
        builder.month = Some(month as u8);
        DaySetter {
            builder
        }
    }

    pub fn build(self) -> IonResult<Timestamp> {
        self.into_builder().build()
    }
}

#[derive(Debug, Clone)]
pub struct DaySetter {
    builder: TimestampBuilder
}

impl DaySetter {
    // Libraries have conflicting opinions about whether days should be
    // 0- or 1-indexed, so Timestamp follows chrono's lead and provides
    // convenient ways to do both. Internally, it uses a 1-based representation.

    // 0-indexed day
    pub fn with_day0(self, day: u32) -> HourAndMinuteSetter {
        self.with_day(day+1)
    }

    // 1-indexed day
    pub fn with_day(self, day: u32) -> HourAndMinuteSetter {
        let mut builder = self.builder;
        builder.precision = Precision::Day;
        builder.day = Some(day as u8);
        HourAndMinuteSetter {
            builder
        }
    }

    pub fn build(self) -> IonResult<Timestamp> {
        self.into_builder().build()
    }
}

#[derive(Debug, Clone)]
pub struct HourAndMinuteSetter {
    builder: TimestampBuilder
}

impl HourAndMinuteSetter {
    pub fn with_hms(self, hour: u32, minute: u32, second: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.hour = Some(hour as u8);
        builder.minute = Some(minute as u8);
        builder.second = Some(second as u8);
        builder.precision = Precision::Second;
        FractionalSecondSetter {
            builder
        }
    }

    // Timestamp doesn't allow you to specify an hour without specifying the minutes too.
    pub fn with_hour_and_minute(self, hour: u32, minute: u32) -> SecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::HourAndMinute;
        builder.hour = Some(hour as u8);
        builder.minute = Some(minute as u8);
        SecondSetter {
            builder
        }
    }

    pub fn build(self) -> IonResult<Timestamp> {
        self.into_builder().build()
    }
}

#[derive(Debug, Clone)]
pub struct SecondSetter {
    builder: TimestampBuilder
}

impl SecondSetter {
    pub fn with_second(self, second: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::Second;
        builder.second = Some(second as u8);
        FractionalSecondSetter {
            builder
        }
    }

    pub fn build_at_offset(mut self, offset_minutes: i32) -> IonResult<Timestamp> {
        self.builder.offset = Some(offset_minutes);
        self.into_builder().build()
    }

    pub fn build_at_unknown_offset(mut self) -> IonResult<Timestamp> {
        self.builder.offset = None;
        self.into_builder().build()
    }
}

#[derive(Debug, Clone)]
pub struct FractionalSecondSetter {
    builder: TimestampBuilder
}

impl FractionalSecondSetter {
    pub fn with_nanoseconds(self, nanosecond: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Digits(9));
        builder.nanoseconds = Some(nanosecond);
        FractionalSecondSetter {
            builder
        }
    }

    pub fn with_microseconds(self, microsecond: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Digits(6));
        builder.nanoseconds = Some(microsecond * 1000);
        FractionalSecondSetter {
            builder
        }
    }

    pub fn with_milliseconds(self, millisecond: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Digits(3));
        builder.nanoseconds = Some(millisecond * 1_000_000);
        FractionalSecondSetter {
            builder
        }
    }

    pub fn with_nanoseconds_and_precision(self, nanoseconds: u32, precision_digits: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Digits(precision_digits));
        builder.nanoseconds = Some(nanoseconds);
        FractionalSecondSetter {
            builder
        }
    }

    pub fn with_fractional_seconds(self, fractional_seconds: Decimal) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Arbitrary(fractional_seconds));
        builder.nanoseconds = None;
        FractionalSecondSetter {
            builder
        }
    }

    pub fn build_at_offset(mut self, offset_minutes: i32) -> IonResult<Timestamp> {
        self.builder.offset = Some(offset_minutes);
        self.into_builder().build()
    }

    pub fn build_at_unknown_offset(mut self) -> IonResult<Timestamp> {
        self.builder.offset = None;
        self.into_builder().build()
    }
}

trait TimeUnitSetter {
    fn into_builder(self) -> TimestampBuilder;
}

macro_rules! impl_time_unit_setter_for {
    ($type_name:ty) => {
        impl TimeUnitSetter for $type_name {
            fn into_builder(self) -> TimestampBuilder {
                self.builder
            }
        }
    }
}

impl_time_unit_setter_for!(MonthSetter);
impl_time_unit_setter_for!(DaySetter);
impl_time_unit_setter_for!(HourAndMinuteSetter);
impl_time_unit_setter_for!(SecondSetter);
impl_time_unit_setter_for!(FractionalSecondSetter);

#[cfg(test)]
mod timestamp_tests {
    use crate::types::decimal::{Decimal, Sign};
    use chrono::{DateTime, Timelike, Datelike, FixedOffset, TimeZone, NaiveDateTime};
    use crate::types::timestamp::{Timestamp, Precision, TimestampBuilder, Mantissa};
    use std::str::FromStr;
    use crate::result::IonResult;

    fn timestamp_from_datetimes_eq_test<I: Into<Timestamp>>(t1: I, t2: I) {
        let t1 = t1.into();
        let t2 = t2.into();
        assert_eq!(t1, t2);
    }

    fn timestamp_from_datetimes_ne_test<I: Into<Timestamp>>(t1: I, t2: I) {
        let t1 = t1.into();
        let t2 = t2.into();
        assert_ne!(t1, t2);
    }

    // TODO: This relies on DateTime's string parsing, which follows different (but overlapping)
    //       rules from text Ion timestamp parsers. We should replace it when the text reader
    //       is available.
    fn timestamp_from_str(s: &str, precision: Precision) -> Timestamp {
        if let Ok(datetime) = DateTime::<FixedOffset>::from_str(s) {
            return Timestamp::from_datetime(datetime, precision);
        }
        NaiveDateTime::from_str(s).unwrap().into()
    }

    fn timestamp_eq_test(s1: &str, precision1: Precision, s2: &str, precision2: Precision) {
        let t1 = timestamp_from_str(s1, precision1);
        let t2 = timestamp_from_str(s2, precision2);
        timestamp_from_datetimes_eq_test(t1, t2);
    }

    fn timestamp_ne_test(s1: &str, precision1: Precision, s2: &str, precision2: Precision) {
        let t1 = timestamp_from_str(s1, precision1);
        let t2 = timestamp_from_str(s2, precision2);
        timestamp_from_datetimes_ne_test(t1, t2);
    }

    #[test]
    fn test_timestamp_eq() {
        use Precision::*;
        let timezone = FixedOffset::west(5 * 60 * 60); // UTC-4:00
        let f = Precision::FractionalSeconds;
        timestamp_eq_test("2021-02-05T16:43:51-05:00", f, "2021-02-05T16:43:51-05:00", f);
        timestamp_eq_test("2021-02-05T16:43:51Z", f, "2021-02-05T16:43:51Z", f);
        timestamp_eq_test("2021-02-05T16:43:51+00:00", f, "2021-02-05T16:43:51+00:00", f);
        timestamp_eq_test("2021-02-05T16:43:51+05:00", f, "2021-02-05T16:43:51+05:00", f);
        timestamp_eq_test("2021-02-05T16:43:51Z", f, "2021-02-05T16:43:51+00:00", f);

        // Unknown offset
        timestamp_eq_test("2021-02-05T16:43:51", f, "2021-02-05T16:43:51", f);
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_known_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp1 = builder.clone().build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone().build_at_offset(5 * 60 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp1 = builder.clone().build_at_unknown_offset()?;
        let timestamp2 = builder.clone().build_at_unknown_offset()?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_at_known_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder.clone().build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone().build_at_offset(5 * 60 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder.clone().build_at_unknown_offset()?;
        let timestamp2 = builder.clone().build_at_unknown_offset()?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hm_at_known_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone().build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone().build_at_offset(5 * 60 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hm_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone().build_at_unknown_offset()?;
        let timestamp2 = builder.clone().build_at_unknown_offset()?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.clone().build()?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ym_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021).with_month(2);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.clone().build()?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_year_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.clone().build()?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_at_different_offsets_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp1 = builder.clone().build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone().build_at_offset(4 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_known_and_unknown_offsets_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp1 = builder.clone().build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone().build_at_unknown_offset()?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_precisions_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder.clone().build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone()
            .with_milliseconds(192)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_second_precision_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder.clone()
            .with_milliseconds(192)
            .build_at_offset(5 * 60 * 60)?;
        // The microseconds field has the same amount of time, but a different precision.
        let timestamp2 = builder.clone()
            .with_microseconds(193 * 1_000)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_seconds_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder.clone()
            .with_milliseconds(192)
            .build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone()
            .with_milliseconds(193)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_seconds_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5)
            .with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone()
            .with_second(12)
            .build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone()
            .with_second(13)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_minutes_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5);
        let timestamp1 = builder.clone()
            .with_hour_and_minute(16, 42)
            .build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone()
            .with_hour_and_minute(16, 43)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_hours_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5);
        let timestamp1 = builder.clone()
            .with_hour_and_minute(16, 42)
            .build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder.clone()
            .with_hour_and_minute(17, 42)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_days_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021).with_month(2);
        let timestamp1 = builder.clone()
            .with_day(5)
            .build();
        let timestamp2 = builder.clone()
            .with_day(6)
            .build();
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_months_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021);
        let timestamp1 = builder.clone()
            .with_month(2)
            .build();
        let timestamp2 = builder.clone()
            .with_month(3)
            .build();
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_years_are_not_equal() -> IonResult<()> {
        let timestamp1 = Timestamp::with_year(2021).build();
        let timestamp2 = Timestamp::with_year(2022).build();
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamp_builder() {
        // Using individual field setters produces the same Timestamp as using setters
        // for common combinations of fields (with_ymd, with_hms).
        let timestamp1 = Timestamp::with_year(2021)
            .with_month(2)
            .with_day(5)
            .with_hour_and_minute(17, 39)
            .with_second(51)
            .with_milliseconds(194)
            .build_at_offset(-4 * 60)
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {:?}", e));

        let timestamp2 = Timestamp::with_ymd(2021, 2, 5)
            .with_hms(17, 39, 51)
            .with_milliseconds(194)
            .build_at_offset(-4 * 60)
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {:?}", e));

        assert_eq!(timestamp1.precision, Precision::FractionalSeconds);
        assert_eq!(timestamp1.fractional_seconds, Some(Mantissa::Digits(3)));
        assert_eq!(timestamp1, timestamp2);
    }

    #[test]
    fn test_first_n_digits_of() {
        assert_eq!(0, super::first_n_digits_of(1, 0));
        assert_eq!(1, super::first_n_digits_of(1, 1));
        assert_eq!(2, super::first_n_digits_of(1, 2));

        assert_eq!(0, super::first_n_digits_of(3, 0));
        assert_eq!(1, super::first_n_digits_of(3, 1));
        assert_eq!(2, super::first_n_digits_of(3, 2));
        assert_eq!(99, super::first_n_digits_of(9, 99));
        assert_eq!(999, super::first_n_digits_of(9, 999));
        assert_eq!(9999, super::first_n_digits_of(9, 9999));

        assert_eq!(0, super::first_n_digits_of(0, 123456789));
        assert_eq!(1, super::first_n_digits_of(1, 123456789));
        assert_eq!(12, super::first_n_digits_of(2, 123456789));
        assert_eq!(123, super::first_n_digits_of(3, 123456789));
        assert_eq!(1234, super::first_n_digits_of(4, 123456789));
        assert_eq!(12345, super::first_n_digits_of(5, 123456789));
        assert_eq!(123456, super::first_n_digits_of(6, 123456789));
        assert_eq!(1234567, super::first_n_digits_of(7, 123456789));
        assert_eq!(12345678, super::first_n_digits_of(8, 123456789));
        assert_eq!(123456789, super::first_n_digits_of(9, 123456789));
    }

}