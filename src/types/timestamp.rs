use crate::result::{illegal_operation, illegal_operation_raw, IonError, IonResult};
use crate::types::decimal::Decimal;
use chrono::{DateTime, Datelike, FixedOffset, NaiveDate, NaiveDateTime, TimeZone, Timelike};
use ion_c_sys::timestamp::{IonDateTime, TSOffsetKind, TSPrecision};
use std::convert::TryInto;
use std::fmt::Debug;

/// Indicates the most precise time unit that has been specified in the accompanying [Timestamp].
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

// [Default] cannot be derived for enum types. Providing a manual implementation of this type
// allows us to derive Default for [Timestamp].
impl Default for Precision {
    fn default() -> Self {
        Precision::Year
    }
}

/// Stores the precision of a Timestamp's fractional seconds, if present. This type is not
/// self-contained; if the Timestamp has a precision that is less than or equal to nanoseconds
/// (i.e. fewer than 10 digits), the fractional seconds value will be stored in the Timestamp's
/// NaiveDateTime component and the Mantissa will indicate the number of digits from that value
/// that should be used. If the precision is 10 or more digits, the Mantissa will store the value
/// itself as a Decimal with the correct precision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Mantissa {
    /// The number of digits of precision in the Timestamp's fractional seconds. For example, a
    /// value of `3` would indicate millisecond precision. A value of `6` would indicate
    /// microsecond precision. All precisions less than or equal to nanoseconds should use
    /// this representation.
    Digits(u32),
    /// Specifies the fractional seconds precisely as a `Decimal` in the range `>= 0` and `< 1`.
    /// The Decimal will have the correct precision; the complete value can and should be used.
    /// This representation should only be used for precisions greater than nanoseconds as it
    /// requires allocations.
    Arbitrary(Decimal),
}

/// Returns the first `num_digits` digits of the specified `value`.
// This is used in Timestamp's implementation of [PartialEq].
fn first_n_digits_of(num_digits: u32, value: u32) -> u32 {
    let total_digits = number_of_digits(value);
    if total_digits <= num_digits {
        return value;
    }
    // Truncate the trailing digits
    value / 10u32.pow(total_digits - num_digits)
}

/// Returns the number of base-10 digits needed to represent `value`.
fn number_of_digits(value: u32) -> u32 {
    match value {
        0 => 1,
        1 => 1,
        i => (i as f64).log10().ceil() as u32,
    }
}

/// Represents a point in time to a specified degree of precision. Unlike `chrono`'s [NaiveDateTime]
/// and [DateTime], a `Timestamp` has variable precision ranging from a year to fractional seconds
/// of an arbitrary unit.
#[derive(Debug, Clone)]
pub struct Timestamp {
    pub(crate) date_time: NaiveDateTime,
    pub(crate) offset: Option<FixedOffset>,
    pub(crate) precision: Precision,
    pub(crate) fractional_seconds: Option<Mantissa>,
}

// TODO: Timestamp does not yet provide useful accessors for its individual fields. It can be
//       instantiated and tested for equality, but will not very useful as a general purpose
//       datetime until these methods are added.
impl Timestamp {
    /// Converts a [NaiveDateTime] or [DateTime<FixedOffset>] to a Timestamp with the specified
    /// precision. If the precision is [Precision::FractionalSeconds], nanosecond precision is
    /// assumed.
    pub fn from_datetime<D>(datetime: D, precision: Precision) -> Timestamp
    where
        D: Datelike + Timelike + Into<Timestamp>,
    {
        let mut timestamp: Timestamp = datetime.into();
        if precision < Precision::FractionalSeconds {
            timestamp.fractional_seconds = None;
        }
        timestamp.precision = precision;
        timestamp
    }

    /// Tests the fractional seconds fields of two timestamps for equality. This function will
    /// only be called if both Timestamps have a precision of [Precision::FractionalSeconds].
    fn fractional_seconds_equal(&self, other: &Timestamp) -> bool {
        use Mantissa::*;
        match (
            self.fractional_seconds.as_ref(),
            other.fractional_seconds.as_ref(),
        ) {
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
            }
            (Some(Arbitrary(d1)), Some(Arbitrary(d2))) => d1.eq(d2),
            //TODO: I believe that the public API makes it impossible for a user to create a
            //      Timestamp with a Mantissa::Arbitrary(_) unless it is required. If this is
            //      correct, the following two cases can be reduced to `false`, as two Timestamps
            //      using different Mantissa variants are inherently unequal. Both of these
            //      branches currently allocate, so this would be a worthwhile optimization.
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

    // ============================================================================
    // ====== The below methods are public entry points for the builder API. ======
    // ============================================================================
    //
    // These methods names are inspired by those of the chrono crate, the most
    // widely used datetime library in the Rust ecosystem.
    //
    // See [TimestampBuilder]'s documentation for more details.

    /// Creates a TimestampBuilder with the specified year and [Precision::Year].
    pub fn with_year(year: u32) -> MonthSetter {
        let mut builder: TimestampBuilder = Default::default();
        builder.precision = Precision::Year;
        builder.year = year as u16;
        MonthSetter { builder }
    }

    /// Creates a TimestampBuilder with the specified year, month, and day. Its precision is
    /// set to [Precision::Day].
    pub fn with_ymd(year: u32, month: u32, day: u32) -> HourAndMinuteSetter {
        let builder = Timestamp::with_year(year)
            .with_month(month)
            .with_day(day)
            .into_builder();
        HourAndMinuteSetter { builder }
    }

    /// Creates a TimestampBuilder with the specified year, month, day, hour, minute, and second.
    /// Its precision is set to [Precision::Second].
    pub fn with_ymd_hms(
        year: u32,
        month: u32,
        day: u32,
        hour: u32,
        minute: u32,
        second: u32,
    ) -> FractionalSecondSetter {
        let builder = Timestamp::with_ymd(year, month, day)
            .with_hms(hour, minute, second)
            .into_builder();
        FractionalSecondSetter { builder }
    }

    /// Creates a TimestampBuilder with the specified year, month, day, hour, minute, second and
    /// milliseconds. Its precision is set to [Precision::FractionalSeconds].
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
        FractionalSecondSetter { builder }
    }
}

impl PartialEq for Timestamp {
    fn eq(&self, other: &Self) -> bool {
        // Timestamps are only considered equal if they have the same precision.
        if self.precision != other.precision {
            return false;
        }
        // Timestamps are only considered equal if they have the same offset, including "unknown".
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
        if self.precision >= Precision::HourAndMinute
            && (self_dt.hour() != other_dt.hour() || self_dt.minute() != other_dt.minute())
        {
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

// We cannot provide an implementation of [Ord] for [Timestamp] because many instances cannot be
// meaningfully compared to each other to derive an ordering. For example, a Timestamp with
// Precision::Year cannot be compared to a timestamp with Precision::Day, and a Timestamp with
// an unknown offset cannot be compared to one with a known offset.
//TODO: It would be possible to provide a PartialOrd for Timestamps with the same precision and
//      either known or unknown offsets. It's unclear how valuable that would be.

/// A Builder object for incrementally configuring and finally instantiating a [Timestamp].
/// For the time being, this type is not publicly visible. Users are expected to use any of the
/// [TimeUnitSetter] implementations that wrap it. These wrappers expose only those methods which
/// can result in a valid Timestamp. For example, it is not possible to set the `day` field
/// without first setting the `year` and `month` fields.
// See the unit tests for usage examples.
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
    /// Sets all of the fields on the given [NaiveDateTime] or [DateTime<FixedOffset>] using the
    /// values from the TimestampBuilder. Only those fields required by the TimestampBuilder's
    /// configured [Precision] will be set.
    fn configure_datetime<D>(&mut self, mut datetime: D) -> IonResult<D>
    where
        D: Datelike + Timelike + Debug,
    {
        datetime = datetime.with_year(self.year as i32).ok_or_else(|| {
            illegal_operation_raw(format!("specified year ('{}') is invalid", self.year))
        })?;
        if self.precision == Precision::Year {
            return Ok(datetime);
        }

        // If precision >= Month, the month must be set.
        let month = self.month.expect("missing month");
        datetime = datetime.with_month(month as u32).ok_or_else(|| {
            illegal_operation_raw(format!("specified month ('{}') is invalid", month))
        })?;
        if self.precision == Precision::Month {
            return Ok(datetime);
        }

        // If precision >= Day, the day must be set.
        let day = self.day.expect("missing day");
        datetime = datetime.with_day(day as u32).ok_or_else(|| {
            illegal_operation_raw(format!("specified day ('{}') is invalid", day))
        })?;
        if self.precision == Precision::Day {
            return Ok(datetime);
        }

        // If precision >= HourAndMinute, the hour and minute must be set.
        let hour = self.hour.expect("missing hour");
        datetime = datetime.with_hour(hour as u32).ok_or_else(|| {
            illegal_operation_raw(format!("specified hour ('{}') is invalid", hour))
        })?;
        let minute = self.minute.expect("missing minute");
        datetime = datetime.with_minute(minute as u32).ok_or_else(|| {
            illegal_operation_raw(format!("specified minute ('{}') is invalid", minute))
        })?;
        if self.precision == Precision::HourAndMinute {
            return Ok(datetime);
        }

        // If precision >= Second, the second must be set.
        let second = self.second.expect("missing second");
        datetime = datetime.with_second(second as u32).ok_or_else(|| {
            illegal_operation_raw(format!("provided second ('{}') is invalid.", second))
        })?;
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
            .ok_or_else(|| {
                illegal_operation_raw(format!("provided nanosecond ('{}') is invalid", second))
            })?;

        Ok(datetime)
    }

    /// Attempt to construct a [Timestamp] using the values configured on the [TimestampBuilder].
    /// If any of the individual fields are invalid (for example, a `month` value that is greater
    /// than `12`) or if the resulting timestamp would represent a non-existent point in time
    /// (like those bypassed by daylight saving time), this method will return an `Err(IonError)`.
    fn build(mut self) -> IonResult<Timestamp> {
        if let Some(offset) = self.offset {
            let offset = FixedOffset::west_opt(offset).ok_or_else(|| {
                illegal_operation_raw(format!("specified offset ('{}') is invalid", offset))
            })?;
            let mut datetime: DateTime<FixedOffset> = offset.ymd(0, 1, 1).and_hms_nano(0, 0, 0, 0);
            datetime = self.configure_datetime(datetime)?;
            let mut timestamp = Timestamp::from_datetime(datetime, self.precision);
            if self.precision == Precision::FractionalSeconds {
                timestamp.fractional_seconds = self.fractional_seconds;
            }
            Ok(timestamp)
        } else {
            let mut datetime: NaiveDateTime = NaiveDate::from_ymd(0, 1, 1).and_hms_nano(0, 0, 0, 0);
            datetime = self.configure_datetime(datetime)?;
            let mut timestamp = Timestamp::from_datetime(datetime, self.precision);
            if self.precision == Precision::FractionalSeconds {
                timestamp.fractional_seconds = self.fractional_seconds;
            }
            Ok(timestamp)
        }
    }
}

/// Allows the user to set the `month` field on a builder that has already had its `year`
/// field set. Or, if `Year` is the desired precision, they may build the [Timestamp] with an
/// unknown offset instead.
#[derive(Debug, Clone)]
pub struct MonthSetter {
    builder: TimestampBuilder,
}

impl MonthSetter {
    // Libraries have conflicting opinions about whether months should be
    // 0- or 1-indexed, so Timestamp follows chrono's lead and provides
    // convenient ways to do both. Internally, it uses a 1-based representation.

    // 0-indexed month
    pub fn with_month0(self, year: u32) -> DaySetter {
        self.with_month(year + 1)
    }

    // 1-indexed month
    pub fn with_month(self, month: u32) -> DaySetter {
        let mut builder = self.builder;
        builder.precision = Precision::Month;
        builder.month = Some(month as u8);
        DaySetter { builder }
    }

    pub fn build(self) -> IonResult<Timestamp> {
        self.into_builder().build()
    }
}

/// Allows the user to set the `day` field on a builder that has already had its `year`
/// and `month` fields set. Or, if `Month` is the desired precision, they may build the [Timestamp]
/// with an unknown offset instead.
#[derive(Debug, Clone)]
pub struct DaySetter {
    builder: TimestampBuilder,
}

impl DaySetter {
    // Libraries have conflicting opinions about whether days should be
    // 0- or 1-indexed, so Timestamp follows chrono's lead and provides
    // convenient ways to do both. Internally, it uses a 1-based representation.

    // 0-indexed day
    pub fn with_day0(self, day: u32) -> HourAndMinuteSetter {
        self.with_day(day + 1)
    }

    // 1-indexed day
    pub fn with_day(self, day: u32) -> HourAndMinuteSetter {
        let mut builder = self.builder;
        builder.precision = Precision::Day;
        builder.day = Some(day as u8);
        HourAndMinuteSetter { builder }
    }

    pub fn build(self) -> IonResult<Timestamp> {
        self.into_builder().build()
    }
}

/// Allows the user to set the `hour` and `minute` fields on a builder that has already
/// had its `year`, `month`, and `day` fields set. Or, if `Day` is the desired precision,
/// they may build the [Timestamp] with an unknown offset instead.
#[derive(Debug, Clone)]
pub struct HourAndMinuteSetter {
    builder: TimestampBuilder,
}

impl HourAndMinuteSetter {
    pub fn with_hms(self, hour: u32, minute: u32, second: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.hour = Some(hour as u8);
        builder.minute = Some(minute as u8);
        builder.second = Some(second as u8);
        builder.precision = Precision::Second;
        FractionalSecondSetter { builder }
    }

    pub fn with_hour_and_minute(self, hour: u32, minute: u32) -> SecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::HourAndMinute;
        builder.hour = Some(hour as u8);
        builder.minute = Some(minute as u8);
        SecondSetter { builder }
    }

    pub fn build(self) -> IonResult<Timestamp> {
        self.into_builder().build()
    }
}

/// Allows the user to set the `second` field on a builder that has already
/// had its `year`, `month`, `day`, `hour`, and `minute` fields set. Or, if `HourAndMinute` is the
/// desired precision, they may build the [Timestamp] instead, optionally specifying an offset if
/// known.
#[derive(Debug, Clone)]
pub struct SecondSetter {
    builder: TimestampBuilder,
}

impl SecondSetter {
    pub fn with_second(self, second: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::Second;
        builder.second = Some(second as u8);
        FractionalSecondSetter { builder }
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

/// Allows the user to set the `fractional_seconds` field on a builder that has already
/// had its `year`, `month`, `day`, `hour`, `minute`, and `second` fields set. Or, if
/// `Second` is the desired precision, they may build the [Timestamp] instead, optionally
/// specifying an offset if known.
#[derive(Debug, Clone)]
pub struct FractionalSecondSetter {
    builder: TimestampBuilder,
}

impl FractionalSecondSetter {
    pub fn with_nanoseconds(self, nanosecond: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Digits(9));
        builder.nanoseconds = Some(nanosecond);
        FractionalSecondSetter { builder }
    }

    pub fn with_microseconds(self, microsecond: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Digits(6));
        builder.nanoseconds = Some(microsecond * 1000);
        FractionalSecondSetter { builder }
    }

    pub fn with_milliseconds(self, millisecond: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Digits(3));
        builder.nanoseconds = Some(millisecond * 1_000_000);
        FractionalSecondSetter { builder }
    }

    pub fn with_nanoseconds_and_precision(
        self,
        nanoseconds: u32,
        precision_digits: u32,
    ) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Digits(precision_digits));
        builder.nanoseconds = Some(nanoseconds);
        FractionalSecondSetter { builder }
    }

    pub fn with_fractional_seconds(self, fractional_seconds: Decimal) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.precision = Precision::FractionalSeconds;
        builder.fractional_seconds = Some(Mantissa::Arbitrary(fractional_seconds));
        builder.nanoseconds = None;
        FractionalSecondSetter { builder }
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
    };
}

impl_time_unit_setter_for!(MonthSetter);
impl_time_unit_setter_for!(DaySetter);
impl_time_unit_setter_for!(HourAndMinuteSetter);
impl_time_unit_setter_for!(SecondSetter);
impl_time_unit_setter_for!(FractionalSecondSetter);

// Allows a NaiveDateTime to be converted to a Timestamp with an unknown offset.
impl From<NaiveDateTime> for Timestamp {
    fn from(date_time: NaiveDateTime) -> Self {
        Timestamp {
            date_time,
            offset: None,
            precision: Precision::FractionalSeconds,
            fractional_seconds: Some(Mantissa::Digits(9)),
        }
    }
}

// Allows a DateTime<FixedOffset> to be converted to a Timestamp with the correct offset in minutes.
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

impl From<ion_c_sys::timestamp::IonDateTime> for Timestamp {
    fn from(ionc_dt: IonDateTime) -> Self {
        use ion_c_sys::timestamp::Mantissa as IonCMantissa;

        let offset = match ionc_dt.offset_kind() {
            TSOffsetKind::KnownOffset => Some(ionc_dt.as_datetime().offset().clone()),
            TSOffsetKind::UnknownOffset => None,
        };
        let precision = match ionc_dt.precision() {
            TSPrecision::Year => Precision::Year,
            TSPrecision::Month => Precision::Month,
            TSPrecision::Day => Precision::Day,
            TSPrecision::Minute => Precision::HourAndMinute,
            TSPrecision::Second => Precision::Second,
            TSPrecision::Fractional(_) => Precision::FractionalSeconds,
        };
        let fractional_seconds = if let TSPrecision::Fractional(mantissa) = ionc_dt.precision() {
            Some(match mantissa {
                IonCMantissa::Digits(digits) => Mantissa::Digits(*digits),
                IonCMantissa::Fraction(fraction) => Mantissa::Arbitrary(fraction.clone().into()),
            })
        } else {
            None
        };
        let date_time = ionc_dt.into_datetime().naive_utc();
        Timestamp {
            date_time,
            offset,
            precision,
            fractional_seconds,
        }
    }
}

/// In general there should be 1-to-1 fidelity between these types, but there
/// is no static way to guarantee this because of [`Decimal`] and the public constructor for
/// [`IonDateTime`](ion_c_sys::timestamp::IonDateTime).
impl TryInto<ion_c_sys::timestamp::IonDateTime> for Timestamp {
    type Error = IonError;

    fn try_into(self) -> Result<IonDateTime, Self::Error> {
        use ion_c_sys::timestamp::Mantissa as IonCMantissa;

        let (offset_kind, offset) = match self.offset {
            None => (TSOffsetKind::UnknownOffset, FixedOffset::east(0)),
            Some(offset) => (TSOffsetKind::KnownOffset, offset),
        };
        let precision = match (self.precision, self.fractional_seconds) {
            (Precision::Year, _) => TSPrecision::Year,
            (Precision::Month, _) => TSPrecision::Month,
            (Precision::Day, _) => TSPrecision::Day,
            (Precision::HourAndMinute, _) => TSPrecision::Minute,
            (Precision::Second, _) => TSPrecision::Second,
            (Precision::FractionalSeconds, Some(mantissa)) => {
                TSPrecision::Fractional(match mantissa {
                    Mantissa::Digits(digits) => IonCMantissa::Digits(digits),
                    Mantissa::Arbitrary(fraction) => IonCMantissa::Fraction(fraction.try_into()?),
                })
            }
            _ => {
                // invariant violation
                return illegal_operation(format!(
                    "Could not convert timestamp with fractional seconds and no mantissa"
                ));
            }
        };
        let date_time = offset.from_utc_datetime(&self.date_time);

        Ok(IonDateTime::try_new(date_time, precision, offset_kind)?)
    }
}

#[cfg(test)]
mod timestamp_tests {
    use crate::result::IonResult;
    use crate::types::timestamp::{Mantissa, Precision, Timestamp};

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
        let timestamp2 = builder
            .clone()
            .with_milliseconds(192)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_second_precision_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder
            .clone()
            .with_milliseconds(192)
            .build_at_offset(5 * 60 * 60)?;
        // The microseconds field has the same amount of time, but a different precision.
        let timestamp2 = builder
            .clone()
            .with_microseconds(193 * 1_000)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_seconds_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder
            .clone()
            .with_milliseconds(192)
            .build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder
            .clone()
            .with_milliseconds(193)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_seconds_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder
            .clone()
            .with_second(12)
            .build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder
            .clone()
            .with_second(13)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_minutes_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5);
        let timestamp1 = builder
            .clone()
            .with_hour_and_minute(16, 42)
            .build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder
            .clone()
            .with_hour_and_minute(16, 43)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_hours_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5);
        let timestamp1 = builder
            .clone()
            .with_hour_and_minute(16, 42)
            .build_at_offset(5 * 60 * 60)?;
        let timestamp2 = builder
            .clone()
            .with_hour_and_minute(17, 42)
            .build_at_offset(5 * 60 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_days_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021).with_month(2);
        let timestamp1 = builder.clone().with_day(5).build();
        let timestamp2 = builder.clone().with_day(6).build();
        assert_ne!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_months_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021);
        let timestamp1 = builder.clone().with_month(2).build();
        let timestamp2 = builder.clone().with_month(3).build();
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

        let timestamp3 = Timestamp::with_ymd_hms_millis(2021, 2, 5, 17, 39, 51, 194)
            .build_at_offset(-4 * 60)
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {:?}", e));

        assert_eq!(timestamp1.precision, Precision::FractionalSeconds);
        assert_eq!(timestamp1.fractional_seconds, Some(Mantissa::Digits(3)));
        assert_eq!(timestamp1, timestamp2);
        assert_eq!(timestamp2, timestamp3);
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

#[cfg(test)]
mod ionc_tests {
    use super::*;
    use bigdecimal::BigDecimal;
    use ion_c_sys::timestamp as ionc_ts;
    use rstest::*;

    fn fractional(lit: &str) -> ionc_ts::Mantissa {
        ionc_ts::Mantissa::Fraction(BigDecimal::parse_bytes(lit.as_bytes(), 10).unwrap())
    }

    fn decimal(lit: &str) -> Decimal {
        BigDecimal::parse_bytes(lit.as_bytes(), 10).unwrap().into()
    }

    /// Creates an `IonDateTime` from constituent components or panics.
    fn ionc_dt(dt_lit: &str, precision: TSPrecision, offset_kind: TSOffsetKind) -> IonDateTime {
        let dt = DateTime::parse_from_rfc3339(dt_lit).unwrap();
        IonDateTime::try_new(dt, precision, offset_kind).unwrap()
    }

    #[rstest]
    #[case::year(
        ionc_dt(
            "2020-01-01T00:01:00Z",
            ionc_ts::TSPrecision::Year,
            ionc_ts::TSOffsetKind::UnknownOffset
        ),
        Timestamp::with_year(2020).build().unwrap()
    )]
    #[case::month(
        ionc_dt(
            "2020-01-01T00:01:00Z",
            ionc_ts::TSPrecision::Month,
            ionc_ts::TSOffsetKind::UnknownOffset
        ),
        Timestamp::with_year(2020)
            .with_month(1)
            .build()
            .unwrap()
    )]
    #[case::day(
        ionc_dt(
            "2020-01-01T00:01:00Z",
            ionc_ts::TSPrecision::Day,
            ionc_ts::TSOffsetKind::UnknownOffset
        ),
        Timestamp::with_year(2020)
            .with_month(1)
            .with_day(1)
            .build()
            .unwrap()
    )]
    #[case::minute_unknown(
        ionc_dt(
            "2020-01-01T00:01:00Z",
            ionc_ts::TSPrecision::Minute,
            ionc_ts::TSOffsetKind::UnknownOffset
        ),
        Timestamp::with_ymd(2020, 1, 1)
            .with_hour_and_minute(0, 1)
            .build_at_unknown_offset()
            .unwrap()
    )]
    #[case::minute_minus0800(
        ionc_dt(
            "2020-01-01T00:01:00-08:00",
            ionc_ts::TSPrecision::Minute,
            ionc_ts::TSOffsetKind::KnownOffset
        ),
        Timestamp::with_ymd(2020, 1, 1)
            .with_hour_and_minute(0, 1)
            .build_at_offset(8 * 60 * 60)
            .unwrap()
    )]
    #[case::second_plus0400(
        ionc_dt(
            "2020-01-01T00:01:23+04:00",
            ionc_ts::TSPrecision::Second,
            ionc_ts::TSOffsetKind::KnownOffset
        ),
        Timestamp::with_ymd(2020, 1, 1)
            .with_hms(0, 1, 23)
            .build_at_offset(-4 * 60 * 60)
            .unwrap()
    )]
    #[case::millis_zulu(
        ionc_dt(
            "2020-01-01T00:01:23.678Z",
            ionc_ts::TSPrecision::Fractional(ionc_ts::Mantissa::Digits(3)),
            ionc_ts::TSOffsetKind::KnownOffset
        ),
        Timestamp::with_ymd(2020, 1, 1)
            .with_hms(0, 1, 23)
            .with_milliseconds(678)
            .build_at_offset(0)
            .unwrap()
    )]
    #[case::fivedigits_zulu(
        ionc_dt(
            "2020-01-01T00:01:23.6789Z",
            ionc_ts::TSPrecision::Fractional(ionc_ts::Mantissa::Digits(4)),
            ionc_ts::TSOffsetKind::KnownOffset
        ),
        Timestamp::with_ymd(2020, 1, 1)
            .with_hms(0, 1, 23)
            .with_nanoseconds_and_precision(678900000, 4)
            .build_at_offset(0)
            .unwrap()
    )]
    #[case::beyondnanos_zulu(
        ionc_dt(
            "2020-01-01T00:01:23.999888777Z",
            ionc_ts::TSPrecision::Fractional(fractional("0.99988877766")),
            ionc_ts::TSOffsetKind::KnownOffset
        ),
        Timestamp::with_ymd(2020, 1, 1)
            .with_hms(0, 1, 23)
            .with_fractional_seconds(decimal("0.99988877766"))
            .build_at_offset(0)
            .unwrap()
    )]
    fn convert_from_to_ionc(
        #[case] source: IonDateTime,
        #[case] expected: Timestamp,
    ) -> IonResult<()> {
        let actual: Timestamp = source.clone().into();
        assert_eq!(expected, actual);
        let converted_source: IonDateTime = actual.try_into()?;
        assert_eq!(source, converted_source);
        Ok(())
    }
}
