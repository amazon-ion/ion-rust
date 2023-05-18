use crate::ion_data::{IonEq, IonOrd};
use crate::result::{
    encoding_error, illegal_operation, illegal_operation_raw, IonError, IonResult,
};
use crate::types::Sign::Negative;
use crate::types::{Decimal, UInt};
use chrono::{
    DateTime, Datelike, FixedOffset, LocalResult, NaiveDate, NaiveDateTime, TimeZone, Timelike,
};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use std::cmp::Ordering;
use std::convert::TryInto;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Div;

/// Indicates the most precise time unit that has been specified in the accompanying [Timestamp].
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Default)]
pub enum Precision {
    /// Year-level precision (e.g. `2020T`)
    #[default]
    Year,
    /// Month-level precision (e.g. `2020-08T`)
    Month,
    /// Day-level precision (e.g. `2020-08-01T`)
    Day,
    /// Minute-level precision (e.g. `2020-08-01T12:34Z`)
    HourAndMinute,
    /// Second-level precision or greater. (e.g. `2020-08-01T12:34:56Z` or `2020-08-01T12:34:56.123456789Z`)
    Second,
}

// [Default] cannot be derived for enum types. Providing a manual implementation of this type
// allows us to derive Default for [Timestamp].

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
    /// this representation when possible.
    Digits(u32),
    /// Specifies the fractional seconds precisely as a `Decimal` in the range `>= 0` and `< 1`.
    /// The Decimal will have the correct precision; the complete value can and should be used.
    /// This representation should only be used for precisions greater than nanoseconds as can
    /// require allocations.
    Arbitrary(Decimal),
}

impl Mantissa {
    fn decimals_equal(d1: &Decimal, d2: &Decimal) -> bool {
        // See the [EmptyMantissa] trait for details about `is_empty()`
        (d1.is_empty() && d2.is_empty())
            // Exact equality test
            || d1.eq(d2)
            // Coefficient zeros' signs don't have to match for fractional seconds.
            || (d1.coefficient.is_zero() && d2.coefficient.is_zero() && d1.exponent == d2.exponent)
    }

    fn decimals_compare(d1: &Decimal, d2: &Decimal) -> Ordering {
        // See the [EmptyMantissa] trait for details about `is_empty()`
        if d1.is_empty() && d2.is_empty() {
            Ordering::Equal
        } else if d1.coefficient.is_zero() && d2.coefficient.is_zero() {
            // Coefficient zeros' signs don't have to be compared for fractional seconds.
            d1.exponent.cmp(&d2.exponent)
        } else {
            // Exact comparison test
            d1.cmp(d2)
        }
    }
}

trait EmptyMantissa {
    /// Returns true if the Mantissa's value is equivalent to not having specified a
    /// sub-second precision at all. For example, `Mantissa::Digits(0)` or
    /// `Mantissa::Arbitrary(Decimal::new(0, 0))`.
    fn is_empty(&self) -> bool;

    /// Returns true if the Mantissa's value is equivalent to a zero value
    /// For example, `Mantissa::Digits(0)` or `Mantissa::Arbitrary(Decimal::new(0, x))`.
    /// For Decimal, it ignores the exponent value for a zero coefficient.
    fn is_zero(&self) -> bool;
}

impl EmptyMantissa for Decimal {
    fn is_empty(&self) -> bool {
        self.coefficient.is_zero() && self.exponent == 0
    }

    fn is_zero(&self) -> bool {
        // if the coefficient is zero then ignore the exponent value
        self.coefficient.is_zero()
    }
}

impl EmptyMantissa for Mantissa {
    fn is_empty(&self) -> bool {
        match self {
            // Look at zero digits of the DateTime's nanoseconds
            Mantissa::Digits(0) => true,
            // Or a Decimal with a coefficient of zero (any sign) and an exponent of zero.
            Mantissa::Arbitrary(d) => d.is_empty(),
            _ => false,
        }
    }

    fn is_zero(&self) -> bool {
        match self {
            // Look at zero digits of the DateTime's nanoseconds
            Mantissa::Digits(0) => true,
            // Or a Decimal with a coefficient of zero (any sign).
            Mantissa::Arbitrary(d) => d.is_zero(),
            _ => false,
        }
    }
}

/// Returns the first `num_digits` digits of the specified `value`.
// This is used in Timestamp's implementation of [PartialEq].
fn first_n_digits_of(num_digits: u32, value: u32) -> u32 {
    let total_digits = super::num_decimal_digits_in_u64(value as u64) as u32;
    if total_digits <= num_digits {
        return value;
    }
    // Truncate the trailing digits
    value / 10u32.pow(total_digits - num_digits)
}

/// Constructs a [FixedOffset] at the specified offset seconds from UTC. If the specified offset
/// is out of bounds, this method will panic.
fn offset_east(seconds_east: i32) -> FixedOffset {
    FixedOffset::east_opt(seconds_east)
        // This error case is expected to be handled before this method is called.
        .expect("seconds_east was outside the supported range")
}

/// Constructs a [`DateTime<FixedOffset>`] at the specified offset using the fields of
/// [`NaiveDateTime`] representing the desired UTC datetime.
fn datetime_at_offset(utc_datetime: &NaiveDateTime, seconds_east: i32) -> DateTime<FixedOffset> {
    offset_east(seconds_east).from_utc_datetime(utc_datetime)
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

impl Timestamp {
    /// Converts a [`NaiveDateTime`] or [`DateTime<FixedOffset>`] to a Timestamp with the specified
    /// precision. If the precision is [`Precision::Second`], nanosecond precision (the maximum
    /// supported by a [`Timelike`]) is assumed.
    pub fn from_datetime<D>(datetime: D, precision: Precision) -> Timestamp
    where
        D: Datelike + Timelike + Into<Timestamp>,
    {
        let mut timestamp: Timestamp = datetime.into();
        if precision < Precision::Second {
            timestamp.fractional_seconds = None;
        }
        timestamp.precision = precision;
        timestamp
    }

    /// If the precision is [Precision::Second], returns the Decimal scale of this Timestamp's
    /// fractional seconds; otherwise, returns None.
    ///
    /// For example, a Timestamp with 553 milliseconds would return a Decimal scale of 3.
    pub fn fractional_seconds_scale(&self) -> Option<i64> {
        // This function is used when comparing two Timestamps with different Mantissa representations.
        use Mantissa::*;
        match self.fractional_seconds.as_ref() {
            // number_of_digits represent number of digits of precision in the Timestamp's fractional seconds.
            // this is equivalent to the decimal scale when we convert the fractional seconds into a decimal
            // and return its scale
            Some(Digits(number_of_digits)) => Some(*number_of_digits as i64),
            // This timestamp already stores its fractional seconds as a Decimal; return the scale of this Decimal.
            Some(Arbitrary(decimal)) => Some(decimal.scale()),
            // This Timestamp's precision is too low to have a fractional seconds field.
            None => None,
        }
    }

    /// If the precision is [Precision::Second], returns a Decimal representation of this Timestamp's
    /// fractional seconds; otherwise, returns None.
    ///
    /// For example, a Timestamp with 553 milliseconds would return a Decimal with
    /// coefficient 553, exponent -3.
    pub(crate) fn fractional_seconds_as_decimal(&self) -> Option<Decimal> {
        // This function is used when comparing two Timestamps with different Mantissa representations.
        use Mantissa::*;
        match self.fractional_seconds.as_ref() {
            // This timestamp stores its fractional seconds in its `date_time` field.
            // We'll need to convert the date_time's nanoseconds to a Decimal and return it.
            Some(Digits(number_of_digits)) => {
                const MAX_NANOSECOND_DIGITS: u32 = 9; // If it were 10, it'd be > a second
                let nanoseconds = self.date_time.nanosecond();
                let leading_zeros = MAX_NANOSECOND_DIGITS
                    - super::num_decimal_digits_in_u64(nanoseconds as u64) as u32;
                let coefficient = if leading_zeros >= *number_of_digits {
                    0
                } else {
                    first_n_digits_of(*number_of_digits - leading_zeros, nanoseconds)
                };
                let exponent = -i64::from(*number_of_digits);
                Some(Decimal::new(coefficient, exponent))
            }
            // This timestamp already stores its fractional seconds as a Decimal; return a clone.
            Some(Arbitrary(decimal)) => Some(decimal.clone()),
            // This Timestamp's precision is too low to have a fractional seconds field.
            None => None,
        }
    }

    /// If the precision is [Precision::Second], returns a u32 representing
    /// this Timestamp's fractional seconds in nanoseconds; otherwise, returns None.
    ///
    /// NOTE: This is a potentially lossy operation. A Timestamp with picoseconds would return a
    /// number of nanoseconds, losing precision. Similarly, a Timestamp with milliseconds would
    /// also return a number of nanoseconds, erroneously gaining precision.
    fn fractional_seconds_as_nanoseconds(&self) -> Option<u32> {
        // This function is used when converting a Timestamp to a DateTime<FixedOffset> or
        // NaiveDateTime.
        use Mantissa::*;
        match self.fractional_seconds.as_ref() {
            // This timestamp already stores its fractional seconds in its `date_time` field.
            // We can ignore the `number_of_digits` (which tracks its precision) and simply return
            // `self.date_time`'s nanoseconds.
            Some(Digits(_number_of_digits)) => Some(self.date_time.nanosecond()),
            // This timestamp stores its fractional seconds as a Decimal. Down-convert it to a u32.
            Some(Arbitrary(decimal)) => {
                const NANOSECONDS_EXPONENT: i64 = -9;
                let exponent_delta = decimal.exponent - NANOSECONDS_EXPONENT;
                let magnitude = match decimal.coefficient.magnitude() {
                    UInt::U64(magnitude) => *magnitude,
                    UInt::BigUInt(magnitude) => {
                        // If the magnitude is small enough to fit in a u64, do the conversion.
                        if let Ok(small_magnitude) = u64::try_from(magnitude) {
                            small_magnitude
                        } else {
                            // Otherwise, the magnitude is definitely bigger than 999,999,999
                            // (the max number of nanoseconds). We'll need to scale it down to
                            // nanoseconds, losing precision in the process.
                            let nanoseconds = magnitude
                                .div(BigUint::from(10f64.powi(exponent_delta.abs() as i32) as u64))
                                .to_u32()
                                .expect("failed to convert BigUint magnitude to u32");
                            return Some(nanoseconds);
                        }
                    }
                };
                let nanoseconds = (magnitude as f64 * 10f64.powi(exponent_delta as i32)) as u32;
                Some(nanoseconds)
            }
            // This Timestamp's precision is too low to have a fractional seconds field.
            None => None,
        }
    }

    /// Tests the fractional seconds fields of two timestamps for ordering. This function will
    /// only be called if both Timestamps have a precision of [Precision::Second].
    fn fractional_seconds_compare(&self, other: &Timestamp) -> Ordering {
        use Mantissa::*;
        match (
            self.fractional_seconds.as_ref(),
            other.fractional_seconds.as_ref(),
        ) {
            (None, None) => Ordering::Equal,
            (Some(_m), None) => {
                let d1 = self.fractional_seconds_as_decimal().unwrap();
                let d2 = Decimal::new(0u64, 0);
                d1.cmp(&d2)
            }
            (None, Some(_m)) => {
                let d1 = Decimal::new(0u64, 0);
                let d2 = other.fractional_seconds_as_decimal().unwrap();
                d1.cmp(&d2)
            }
            (Some(Digits(_d1)), Some(Digits(_d2))) => {
                let d1 = self.date_time.nanosecond();
                let d2 = other.date_time.nanosecond();
                d1.cmp(&d2)
            }
            (Some(Arbitrary(d1)), Some(Arbitrary(d2))) => Mantissa::decimals_compare(d1, d2),
            (Some(Digits(_d1)), Some(Arbitrary(d2))) => {
                let d1 = &self.fractional_seconds_as_decimal().unwrap();
                Mantissa::decimals_compare(d1, d2)
            }
            (Some(Arbitrary(d1)), Some(Digits(_d2))) => {
                let d2 = &other.fractional_seconds_as_decimal().unwrap();
                Mantissa::decimals_compare(d1, d2)
            }
        }
    }

    /// Tests the fractional seconds fields of two timestamps for equality. This function will
    /// only be called if both Timestamps have a precision of [Precision::Second].
    fn fractional_seconds_equal(&self, other: &Timestamp) -> bool {
        use Mantissa::*;

        // TODO: make Timestamp::fractional_seconds to be Mantissa when creating a Timestamp to get rid of below conversion
        // convert Option<&Mantissa> to &Mantissa
        let m1 = match &self.fractional_seconds {
            None => &Mantissa::Digits(0),
            Some(m) => m,
        };

        let m2 = match &other.fractional_seconds {
            None => &Mantissa::Digits(0),
            Some(m) => m,
        };

        // compare fractional seconds
        match (m1, m2) {
            (Digits(d1), Digits(d2)) => {
                if d1 != d2 {
                    // Different precisions
                    return false;
                }
                let d1 = first_n_digits_of(*d1, self.date_time.nanosecond());
                let d2 = first_n_digits_of(*d2, other.date_time.nanosecond());
                d1 == d2
            }
            (Arbitrary(d1), Arbitrary(d2)) => Mantissa::decimals_equal(d1, d2),
            (Digits(_d1), Arbitrary(d2)) => {
                let d1 = match self.fractional_seconds_as_decimal() {
                    Some(decimal_value) => decimal_value,
                    None => Decimal::new(0, 0),
                };
                Mantissa::decimals_equal(&d1, d2)
            }
            (Arbitrary(d1), Digits(_d2)) => {
                let d2 = match other.fractional_seconds_as_decimal() {
                    Some(decimal_value) => decimal_value,
                    None => Decimal::new(0, 0),
                };
                Mantissa::decimals_equal(d1, &d2)
            }
        }
    }

    /// Writes the fractional seconds portion of a text timestamp, including a leading `.`.
    fn format_fractional_seconds<W: std::fmt::Write>(&self, output: &mut W) -> IonResult<()> {
        if self.fractional_seconds.is_none() {
            // Nothing to do.
            return Ok(());
        }
        let mantissa = self.fractional_seconds.as_ref().unwrap();
        if mantissa.is_empty() {
            // No need to write anything.
            return Ok(());
        }
        match mantissa {
            Mantissa::Digits(num_digits) => {
                // Scale the nanoseconds down to the requested number of digits.
                // Example: if `num_digits` is 3 (that is: millisecond precision), we need to
                // divide the nanoseconds by 10^(9-3) to get the correct precision:
                //      123,000,000 nanoseconds / 10^(9-3) = 123 milliseconds
                let scaled = self.date_time.nanosecond() / 10u32.pow(9 - *num_digits);
                // If our scaled number has fewer digits than the precision states, add leading
                // zeros to the output to make up the difference.
                // Example: `num_digits` is 6 (microsecond precision) but our number of microseconds
                // is `9500` (only 4 digits), we need to add two leading zeros to make: `009500`.
                let actual_num_digits = super::num_decimal_digits_in_u64(scaled as u64);
                let num_leading_zeros = (*num_digits as u64) - actual_num_digits;
                write!(output, ".")?;
                for _ in 0..num_leading_zeros {
                    write!(output, "0")?;
                }
                write!(output, "{scaled}")?;
                Ok(())
            }
            Mantissa::Arbitrary(decimal) => {
                let exponent = decimal.exponent;
                let coefficient = &decimal.coefficient;
                if exponent >= 0 {
                    // We know that the coefficient is non-zero (the mantissa was not empty),
                    // so having a positive exponent would result in an illegal fractional
                    // seconds value.
                    return encoding_error("found fractional seconds decimal that was >= 1.");
                }

                let num_digits = decimal.coefficient.number_of_decimal_digits();
                let abs_exponent = decimal.exponent.unsigned_abs();
                // At this point, we know that the abs_exponent is greater than num_digits because
                // the decimal has to be < 1.
                let num_leading_zeros = abs_exponent - num_digits;
                write!(output, ".")?;
                for _ in 0..num_leading_zeros {
                    write!(output, "0")?;
                }
                if coefficient.is_negative_zero() {
                    write!(output, "0")?;
                } else if coefficient.sign == Negative {
                    return encoding_error(
                        "fractional seconds cannot have a negative coefficient (other than -0)",
                    );
                } else {
                    write!(output, "{}", decimal.coefficient)?;
                }
                Ok(())
            }
        }
    }

    pub(crate) fn format<W: std::fmt::Write>(&self, output: &mut W) -> IonResult<()> {
        let (offset_minutes, datetime) = if let Some(minutes) = self.offset {
            // Create a datetime with the appropriate offset that we can use for formatting.
            let datetime: DateTime<FixedOffset> = self.clone().try_into()?;
            // Convert the offset to minutes --v
            (Some(minutes.local_minus_utc() / 60), datetime)
        } else {
            // Our timestamp has an unknown offset. Per the spec, this means it makes no
            // assertions about *where* it was recorded, but its fields are still in UTC.
            // Create a UTC datetime that we can use for formatting.
            let datetime: NaiveDateTime = self.clone().try_into()?;
            let datetime: DateTime<FixedOffset> = datetime_at_offset(&datetime, 0);
            (None, datetime)
        };

        write!(output, "{:0>4}", datetime.year())?;
        //                  ^-- 0-padded, right aligned, 4-digit year
        if self.precision == Precision::Year {
            write!(output, "T")?;
            return Ok(());
        }

        write!(output, "-{:0>2}", datetime.month())?;
        //                   ^-- delimiting hyphen and 0-padded, right aligned, 2-digit month
        if self.precision == Precision::Month {
            write!(output, "T")?;
            return Ok(());
        }

        write!(output, "-{:0>2}", datetime.day())?;
        //                   ^-- delimiting hyphen and 0-padded, right aligned, 2-digit day
        if self.precision == Precision::Day {
            write!(output, "T")?;
            return Ok(());
        }

        write!(
            output,
            "T{:0>2}:{:0>2}",
            // ^-- delimiting T, formatted hour, delimiting colon, formatted minute
            datetime.hour(),
            datetime.minute()
        )?;
        if self.precision == Precision::HourAndMinute {
            self.format_offset(offset_minutes, output)?;
            return Ok(());
        }

        write!(output, ":{:0>2}", datetime.second())?;
        //                   ^-- delimiting colon, formatted second
        self.format_fractional_seconds(output)?;
        self.format_offset(offset_minutes, output)?;
        Ok(())
    }

    fn format_offset<W: std::fmt::Write>(
        &self,
        offset_minutes: Option<i32>,
        output: &mut W,
    ) -> IonResult<()> {
        let (sign, hours, minutes) = match offset_minutes {
            None => ("-", 0, 0),
            Some(offset_minutes) => {
                const MINUTES_PER_HOUR: i32 = 60;
                // Split the offset into a sign and magnitude for formatting
                let sign = if offset_minutes >= 0 { "+" } else { "-" };
                let offset_minutes = offset_minutes.abs();
                let hours = offset_minutes / MINUTES_PER_HOUR;
                let minutes = offset_minutes % MINUTES_PER_HOUR;

                (sign, hours, minutes)
            }
        };
        write!(output, "{sign}{hours:0>2}:{minutes:0>2}")?;
        Ok(())
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
        let builder: TimestampBuilder = TimestampBuilder {
            year: year as u16,
            ..Default::default()
        };
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
    /// milliseconds. Its precision is set to [Precision::Second].
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

    /// Returns the offset in minutes that has been specified in the [Timestamp].
    /// A positive value indicates Eastern Hemisphere, while a negative value indicates Western Hemisphere.
    pub fn offset(&self) -> Option<i32> {
        self.offset.map(|offset| offset.local_minus_utc() / 60)
    }

    /// Returns the precision that has been specified in the [Timestamp].
    pub fn precision(&self) -> Precision {
        self.precision
    }

    /// Returns the year that has been specified in the [Timestamp].
    pub fn year(&self) -> i32 {
        // verify if the timestamp has an offset
        if let Some(offset) = self.offset {
            // `NaiveDateTime#hours()` returns hours normalized as per UTC
            // for local time we need to +/- the difference
            let local_date_time = DateTime::<FixedOffset>::from_utc(self.date_time, offset);
            return local_date_time.year();
        }
        self.date_time.year()
    }

    /// Returns the month that has been specified in the [Timestamp].
    /// Returns the month number starting from 1.
    /// The return value ranges from 1 to 12.
    pub fn month(&self) -> u32 {
        // verify if the timestamp has an offset
        if let Some(offset) = self.offset {
            // `NaiveDateTime#hours()` returns hours normalized as per UTC
            // for local time we need to +/- the difference
            let local_date_time = DateTime::<FixedOffset>::from_utc(self.date_time, offset);
            return local_date_time.month();
        }
        self.date_time.month()
    }

    /// Returns the day that has been specified in the [Timestamp].
    /// Returns the day of month starting from 1.
    // The return value ranges from 1 to 31. (The last day of month differs by months.)
    pub fn day(&self) -> u32 {
        // verify if the timestamp has an offset
        if let Some(offset) = self.offset {
            // `NaiveDateTime#hours()` returns hours normalized as per UTC
            // for local time we need to +/- the difference
            let local_date_time = DateTime::<FixedOffset>::from_utc(self.date_time, offset);
            return local_date_time.day();
        }
        self.date_time.day()
    }

    /// Returns the hour(s) that has been specified in the [Timestamp].
    /// Returns the hour number from 0 to 23.
    pub fn hour(&self) -> u32 {
        // verify if the timestamp has an offset
        if let Some(offset) = self.offset {
            // `NaiveDateTime#hours()` returns hours normalized as per UTC
            // for local time we need to +/- the difference
            let local_date_time = DateTime::<FixedOffset>::from_utc(self.date_time, offset);
            return local_date_time.hour();
        }
        self.date_time.hour()
    }

    /// Returns the minute(s) that has been specified in the [Timestamp].
    /// Returns the minute number from 0 to 59.
    pub fn minute(&self) -> u32 {
        // verify if the timestamp has an offset
        if let Some(offset) = self.offset {
            // `NaiveDateTime#hours()` returns minutes normalized as per UTC
            // for local time we need to +/- the difference
            let local_date_time = DateTime::<FixedOffset>::from_utc(self.date_time, offset);
            return local_date_time.minute();
        }
        self.date_time.minute()
    }

    /// Returns the second(s) that has been specified in the [Timestamp].
    /// Returns the second number from 0 to 59.
    pub fn second(&self) -> u32 {
        self.date_time.second()
    }

    /// Return a UTC timestamp for this [Timestamp]
    pub fn to_utc(&self) -> Timestamp {
        self.date_time.into()
    }

    /// Returns this Timestamp's fractional seconds in nanoseconds
    ///
    /// NOTE: This is a potentially lossy operation. A Timestamp with picoseconds would return a
    /// number of nanoseconds, losing precision. If it loses precision then truncation is preformed.
    /// (e.g. a timestamp with fractional seconds of `0.000000000999` would be returned as `0`)
    pub fn nanoseconds(&self) -> u32 {
        self.fractional_seconds_as_nanoseconds().unwrap_or_default()
    }

    /// Returns this Timestamp's fractional seconds in milliseconds
    ///
    /// NOTE: This is a potentially lossy operation. A Timestamp with picoseconds would return a
    /// number of milliseconds, losing precision. If it loses precision then truncation is preformed.
    /// (e.g. a timestamp with fractional seconds of `0.000999` would be returned as `0`)
    pub fn milliseconds(&self) -> u32 {
        self.fractional_seconds_as_nanoseconds()
            .map(|s| s / 1000000)
            .unwrap_or_default()
    }
}

/// Formats an ISO-8601 timestamp of appropriate precision and offset.
impl Display for Timestamp {
    fn fmt(&self, output: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.format(output).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl PartialOrd for Timestamp {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Timestamp {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_datetime = self.date_time.with_nanosecond(0).unwrap();
        let other_datetime = other.date_time.with_nanosecond(0).unwrap();

        let self_datetime = self
            .offset
            .map(|offset| offset.from_utc_datetime(&self_datetime))
            .unwrap_or_else(|| datetime_at_offset(&self_datetime, 0));
        let other_datetime = other
            .offset
            .map(|offset| offset.from_utc_datetime(&other_datetime))
            .unwrap_or_else(|| datetime_at_offset(&other_datetime, 0));

        let date_time_comparison = self_datetime.cmp(&other_datetime);

        match date_time_comparison {
            // if the datetime comparison is Ordering::Equal,
            // then return fractional seconds comparison result
            Ordering::Equal => self.fractional_seconds_compare(other),
            // if datetime comparison is not equal,
            // then no need to check for fractional seconds comparison
            _ => date_time_comparison,
        }
    }
}

/// Two Timestamps are considered equal (though not necessarily IonEq) if they represent the same
/// instant in time. Precision is ignored. Offsets do not have to match as long as the instants
/// being represented match. Examples:
/// * `2022T` == `2022T-01`
/// * `2022T` == `2022T-01-01T00:00:00.000+00:00`
/// * `2022T-05-11T12:00:00.000Z` == `2022T-05-11T07:00:00.000-05:00`
impl PartialEq for Timestamp {
    fn eq(&self, other: &Self) -> bool {
        // First, compare the two Timestamps' fractional seconds. We do this first because
        // Timestamps with different Mantissa representations are a bit tricky to compare. Once
        // we've established that the fractional seconds match, we can compare all of the other
        // fields in the timestamp by comparing their respective `DateTime`s.
        if !self.fractional_seconds_equal(other) {
            return false;
        }

        // When a Timestamp is created, any fields beyond its precision are set to the lowest
        // legal value for that field. So the Timestamp `2022-05T` (which has `Month` precision)
        // would have a `day` field of `1` and hour, minute, and seconds fields of `0`. This makes
        // it easy to compare Timestamps with different precisions.

        // Make copies of their respective DateTime values but with the fractional seconds zeroed
        // out. We're not modifying `self` or `other`, and we've already compared their fractional
        // seconds so it's ok to ignore them from here on.
        let self_datetime = self.date_time.with_nanosecond(0).unwrap();
        let other_datetime = other.date_time.with_nanosecond(0).unwrap();

        // Apply each Timestamp's offset to the DateTime. If there's no offset, set it to UTC.
        let self_datetime = self
            .offset
            .map(|offset| offset.from_utc_datetime(&self_datetime))
            .unwrap_or_else(|| datetime_at_offset(&self_datetime, 0));
        let other_datetime = other
            .offset
            .map(|offset| offset.from_utc_datetime(&other_datetime))
            .unwrap_or_else(|| datetime_at_offset(&other_datetime, 0));

        // Compare the resulting `DateTime<FixedOffset>`s
        self_datetime == other_datetime
    }
}

impl Eq for Timestamp {}

impl IonEq for Timestamp {
    fn ion_eq(&self, other: &Self) -> bool {
        if self.precision != other.precision {
            return false;
        }
        // Timestamps are only considered Ion-equal if they have the same offset, including "unknown".
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
        if self.precision <= Precision::HourAndMinute {
            return true;
        }

        if self_dt.second() != other_dt.second() || !self.fractional_seconds_equal(other) {
            return false;
        }

        true
    }
}

impl IonOrd for Timestamp {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        // Compare by point in time
        let ord = self.cmp(other);
        if ord != Ordering::Equal {
            return ord;
        };

        // And then by precision
        let ord = self.precision.cmp(&other.precision);
        if ord != Ordering::Equal {
            return ord;
        };
        match [
            self.fractional_seconds_scale(),
            other.fractional_seconds_scale(),
        ] {
            [None, Some(b)] if b > 0 => return Ordering::Less,
            [Some(a), None] if a > 0 => return Ordering::Greater,
            [Some(a), Some(b)] => {
                let ord = a.cmp(&b);
                if ord != Ordering::Equal {
                    return ord;
                }
            }
            _ => {}
        }

        // And finally by offset (unknown, then least to greatest)
        match [self.offset, other.offset] {
            [None, Some(_)] => Ordering::Less,
            [None, None] => Ordering::Equal,
            [Some(_), None] => Ordering::Greater,
            [Some(o1), Some(o2)] => o1.local_minus_utc().cmp(&o2.local_minus_utc()),
        }
    }
}

/// A Builder object for incrementally configuring and finally instantiating a [Timestamp].
/// For the time being, this type is not publicly visible. Users are expected to use any of the
/// [TimeUnitSetter] implementations that wrap it. These wrappers expose only those methods which
/// can result in a valid Timestamp. For example, it is not possible to set the `day` field
/// without first setting the `year` and `month` fields.
// See the unit tests for usage examples.
#[derive(Debug, Clone, Default)]
struct TimestampBuilder {
    fields_are_utc: bool,
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
    /// Sets all of the fields on the given [`NaiveDateTime`] or [`DateTime<FixedOffset>`] using the
    /// values from the TimestampBuilder. Only those fields required by the TimestampBuilder's
    /// configured [`Precision`] will be set.
    fn configure_datetime<D>(&mut self, mut datetime: D) -> IonResult<D>
    where
        D: Datelike + Timelike + Debug,
    {
        if self.year == 0 || self.year > 9999 {
            return illegal_operation(format!(
                "Timestamp year '{}' out of range (1-9999)",
                self.year
            ));
        }
        datetime = datetime.with_year(self.year as i32).ok_or_else(|| {
            illegal_operation_raw(format!("specified year ('{}') is invalid", self.year))
        })?;
        if self.precision == Precision::Year {
            return Ok(datetime);
        }

        // If precision >= Month, the month must be set.
        let month = self.month.expect("missing month");
        datetime = datetime.with_month(month as u32).ok_or_else(|| {
            illegal_operation_raw(format!("specified month ('{month}') is invalid"))
        })?;
        if self.precision == Precision::Month {
            return Ok(datetime);
        }

        // If precision >= Day, the day must be set.
        let day = self.day.expect("missing day");
        datetime = datetime
            .with_day(day as u32)
            .ok_or_else(|| illegal_operation_raw(format!("specified day ('{day}') is invalid")))?;
        if self.precision == Precision::Day {
            return Ok(datetime);
        }

        // If precision >= HourAndMinute, the hour and minute must be set.
        let hour = self.hour.expect("missing hour");
        datetime = datetime.with_hour(hour as u32).ok_or_else(|| {
            illegal_operation_raw(format!("specified hour ('{hour}') is invalid"))
        })?;
        let minute = self.minute.expect("missing minute");
        datetime = datetime.with_minute(minute as u32).ok_or_else(|| {
            illegal_operation_raw(format!("specified minute ('{minute}') is invalid"))
        })?;
        if self.precision == Precision::HourAndMinute {
            return Ok(datetime);
        }

        // If precision >= Second, the second must be set...
        let second = self.second.expect("missing second");
        datetime = datetime.with_second(second as u32).ok_or_else(|| {
            illegal_operation_raw(format!("provided second ('{second}') is invalid."))
        })?;

        // ...along with the fractional seconds.
        // If fractional seconds is Digit, self.nanoseconds will be Some(_).
        // If it's Arbitrary, self.nanoseconds will be None and we should set the nanoseconds
        // field to 0. The real value will be stored in the Timestamp alongside the DateTime
        // as a Decimal.
        datetime = datetime
            .with_nanosecond(self.nanoseconds.unwrap_or(0))
            .ok_or_else(|| {
                illegal_operation_raw(format!("provided nanosecond ('{second}') is invalid"))
            })?;

        Ok(datetime)
    }

    // A [NaiveDateTime] has no offset. This function attempts to apply the provided offset to the
    // NaiveDateTime, producing a DateTime<FixedOffset>. If the offset is invalid or the combination
    // of offset and datetime would produce an invalid Timestamp, this function will return Err.
    fn apply_offset(
        offset_minutes: i32,
        fields_are_utc: bool,
        datetime: NaiveDateTime,
    ) -> IonResult<DateTime<FixedOffset>> {
        // The chrono APIs express their DateTime offsets in seconds, but the Ion APIs use minutes.
        const SECONDS_PER_MINUTE: i32 = 60;
        let offset_seconds = offset_minutes * SECONDS_PER_MINUTE;
        let offset = FixedOffset::east_opt(offset_seconds).ok_or_else(|| {
            illegal_operation_raw(format!(
                "specified offset ({offset_minutes} minutes) is invalid"
            ))
        })?;

        // If the fields of the datetime are UTC, constructing a DateTime<FixedOffset> is guaranteed
        // to succeed. Return it directly.
        if fields_are_utc {
            return Ok(offset.from_utc_datetime(&datetime));
        }

        // Otherwise, apply the offset to our (local) NaiveDateTime and make sure the resulting
        // DateTime<FixedOffset> is valid.
        match offset.from_local_datetime(&datetime) {
            LocalResult::None => {
                illegal_operation(
                    format!(
                        "specified offset/datetime pair is invalid (offset={offset_minutes}, datetime={datetime})"
                    )
                )
            },
            LocalResult::Single(datetime) => Ok(datetime),
            LocalResult::Ambiguous(_min, _max) => {
                illegal_operation(
                    format!(
                        "specified offset/datetime pair produces an ambiguous timestamp (offset={offset_minutes}, datetime={datetime})"
                    )
                )
            }
        }
    }

    /// Attempt to construct a [Timestamp] using the values configured on the [TimestampBuilder].
    /// If any of the individual fields are invalid (for example, a `month` value that is greater
    /// than `12`) or if the resulting timestamp would represent a non-existent point in time
    /// (like those bypassed by daylight saving time), this method will return an `Err(IonError)`.
    fn build(mut self) -> IonResult<Timestamp> {
        // Start with a clean slate NaiveDateTime that we can configure. (These are cheap to copy.)
        let mut datetime: NaiveDateTime = NaiveDate::from_ymd_opt(0, 1, 1)
            .unwrap()
            .and_hms_nano_opt(0, 0, 0, 0)
            .unwrap();
        // Set all of the time fields on the datetime using the data from our TimestampBuilder
        datetime = self.configure_datetime(datetime)?;
        // If the timestamp we're building has a known offset...
        let mut timestamp: Timestamp = if let Some(offset_minutes) = self.offset {
            // ...apply the offset to our NaiveDateTime, producing a DateTime<FixedOffset>
            let datetime_with_offset: DateTime<FixedOffset> =
                Self::apply_offset(offset_minutes, self.fields_are_utc, datetime)?;
            // ...and convert the DateTime<FixedOffset> into a full Timestamp.
            Timestamp::from_datetime(datetime_with_offset, self.precision)
        } else {
            // Otherwise, there's not a known offset. We can directly convert our NaiveDateTime
            // into a full Timestamp.
            Timestamp::from_datetime(datetime, self.precision)
        };

        // Copy the fractional seconds from the builder to the Timestamp.
        if self.precision == Precision::Second {
            timestamp.fractional_seconds = self.fractional_seconds;
            if let Some(Mantissa::Arbitrary(ref decimal)) = &timestamp.fractional_seconds {
                if decimal.is_less_than_zero() {
                    return illegal_operation(
                        "cannot create a timestamp with negative fractional seconds",
                    );
                }
                if decimal.is_greater_than_or_equal_to_one() {
                    return illegal_operation(
                        "cannot create a timestamp with a fractional seconds >= 1.0",
                    );
                }
                if decimal.is_zero() && decimal.exponent >= 0 {
                    timestamp.fractional_seconds = None;
                }
            }
        }
        Ok(timestamp)
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

    /// Sets the difference, in minutes, from UTC. A positive value indicates
    /// Eastern Hemisphere, while a negative value indicates Western Hemisphere.
    // The unit (minutes) could be seconds (which is what the chrono crate uses
    // internally), but Ion uses minutes in its binary representation, so it
    // makes sense to be consistent.
    pub fn build_at_offset(mut self, offset_minutes: i32) -> IonResult<Timestamp> {
        self.builder.offset = Some(offset_minutes);
        self.into_builder().build()
    }

    /// Like [Self::build_at_offset], but the fields provided for each time unit are understood
    /// to be in UTC rather than in the local time of the specified offset.
    pub fn build_utc_fields_at_offset(mut self, offset_minutes: i32) -> IonResult<Timestamp> {
        self.builder.fields_are_utc = true;
        self.build_at_offset(offset_minutes)
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
    // Note that in order to create a `FractionalSecondSetter`, the user will have had to first
    // create a `SecondSetter`. Because of this, the builder's precision is already set to
    // `Precision::Second`.
    pub fn with_nanoseconds(self, nanosecond: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.fractional_seconds = Some(Mantissa::Digits(9));
        builder.nanoseconds = Some(nanosecond);
        FractionalSecondSetter { builder }
    }

    pub fn with_microseconds(self, microsecond: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.fractional_seconds = Some(Mantissa::Digits(6));
        builder.nanoseconds = Some(microsecond * 1000);
        FractionalSecondSetter { builder }
    }

    pub fn with_milliseconds(self, millisecond: u32) -> FractionalSecondSetter {
        let mut builder = self.builder;
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
        builder.fractional_seconds = Some(Mantissa::Digits(precision_digits));
        builder.nanoseconds = Some(nanoseconds);
        FractionalSecondSetter { builder }
    }

    pub fn with_fractional_seconds(self, fractional_seconds: Decimal) -> FractionalSecondSetter {
        let mut builder = self.builder;
        builder.fractional_seconds = Some(Mantissa::Arbitrary(fractional_seconds));
        builder.nanoseconds = None;
        FractionalSecondSetter { builder }
    }

    pub fn build_at_offset(mut self, offset_minutes: i32) -> IonResult<Timestamp> {
        self.builder.offset = Some(offset_minutes);
        self.into_builder().build()
    }

    /// Like [Self::build_at_offset], but the fields provided for each time unit are understood
    /// to be in UTC rather than in the local time of the specified offset.
    pub fn build_utc_fields_at_offset(mut self, offset_minutes: i32) -> IonResult<Timestamp> {
        self.builder.fields_are_utc = true;
        self.build_at_offset(offset_minutes)
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

fn downconvert_to_naive_datetime_with_nanoseconds(timestamp: &Timestamp) -> NaiveDateTime {
    if timestamp.precision == Precision::Second {
        // DateTime always uses nanosecond precision. If our Timestamp uses a Decimal for
        // its fractional seconds, attempt to convert it to a number of nanoseconds.
        // This operation may add or lose precision, but is necessary to conform with
        // chrono's expectations.
        let nanoseconds = timestamp.fractional_seconds_as_nanoseconds().unwrap_or(0);
        // Copy `self.date_time` and set the copy's nanoseconds to this new value.
        // Modifying the nanoseconds should never be invalid.
        timestamp.date_time.with_nanosecond(nanoseconds).unwrap()
    } else {
        // NaiveDateTime implements `Copy`
        timestamp.date_time
    }
}

// Allows a Timestamp with an unknown offset to be converted to a NaiveDateTime.
impl TryInto<NaiveDateTime> for Timestamp {
    type Error = IonError;

    fn try_into(self) -> Result<NaiveDateTime, Self::Error> {
        if self.offset.is_some() {
            return illegal_operation(
                "cannot convert a Timestamp with a known offset into a NaiveDateTime",
            );
        }
        Ok(downconvert_to_naive_datetime_with_nanoseconds(&self))
    }
}

impl TryInto<DateTime<FixedOffset>> for Timestamp {
    type Error = IonError;

    fn try_into(self) -> Result<DateTime<FixedOffset>, Self::Error> {
        if self.offset.is_none() {
            return illegal_operation(
                "cannot convert a Timestamp with an unknown offset into a DateTime<FixedOffset>",
            );
        }
        let date_time = downconvert_to_naive_datetime_with_nanoseconds(&self);
        Ok(self.offset.unwrap().from_utc_datetime(&date_time))
    }
}

// Allows a NaiveDateTime to be converted to a Timestamp with an unknown offset.
impl From<NaiveDateTime> for Timestamp {
    fn from(date_time: NaiveDateTime) -> Self {
        Timestamp {
            date_time,
            offset: None,
            precision: Precision::Second,
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
        let precision = Precision::Second;
        let fractional_seconds = Some(Mantissa::Digits(9));
        Timestamp {
            date_time,
            offset,
            precision,
            fractional_seconds,
        }
    }
}

#[cfg(test)]
mod timestamp_tests {
    use super::*;
    use crate::ion_data::IonEq;
    use crate::result::IonResult;
    use crate::types::{Decimal, Mantissa, Precision, Timestamp};
    use chrono::{DateTime, FixedOffset, NaiveDate, NaiveDateTime, TimeZone, Timelike};
    use rstest::*;
    use std::cmp::Ordering;
    use std::convert::TryInto;
    use std::io::Write;
    use std::str::FromStr;

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_known_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp1 = builder.clone().build_at_offset(5 * 60)?;
        let timestamp2 = builder.build_at_offset(5 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_known_offset_are_equal_ordering() -> IonResult<()>
    {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp1 = builder.clone().build_at_offset(5 * 60)?;
        let timestamp2 = builder.build_at_offset(5 * 60)?;
        assert!(timestamp1 == timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp1 = builder.clone().build_at_unknown_offset()?;
        let timestamp2 = builder.build_at_unknown_offset()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_at_known_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder.clone().build_at_offset(5 * 60)?;
        let timestamp2 = builder.build_at_offset(5 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_from_utc_and_local_hm_fields_at_same_offset_are_equal() -> IonResult<()> {
        // Builder 1 specifies its time fields in the local time of the specified offset
        let builder1 = Timestamp::with_ymd(2021, 2, 5).with_hour_and_minute(11, 43);
        let timestamp1 = builder1.build_at_offset(-5 * 60)?;
        // Builder 2 specifies its time fields in UTC and expects the offset to be applied afterwards
        let builder2 = Timestamp::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp2 = builder2.build_utc_fields_at_offset(-5 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_from_utc_and_local_hms_fields_at_same_offset_are_equal() -> IonResult<()> {
        // Builder 1 specifies its time fields in the local time of the specified offset
        let builder1 = Timestamp::with_ymd_hms(2021, 2, 5, 11, 43, 51);
        let timestamp1 = builder1.build_at_offset(-5 * 60)?;
        // Builder 2 specifies its time fields in UTC and expects the offset to be applied afterwards
        let builder2 = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp2 = builder2.build_utc_fields_at_offset(-5 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder.clone().build_at_unknown_offset()?;
        let timestamp2 = builder.build_at_unknown_offset()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hm_at_known_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone().build_at_offset(5 * 60)?;
        let timestamp2 = builder.build_at_offset(5 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hm_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone().build_at_unknown_offset()?;
        let timestamp2 = builder.build_at_unknown_offset()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ym_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021).with_month(2);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_year_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_at_different_offsets_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp1 = builder.clone().build_at_offset(5 * 60)?;
        let timestamp2 = builder.build_at_offset(4 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_known_and_unknown_offsets_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp1 = builder.clone().build_at_offset(5 * 60)?;
        let timestamp2 = builder.build_at_unknown_offset()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_precisions_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder.clone().build_at_offset(5 * 60)?;
        let timestamp2 = builder.with_milliseconds(192).build_at_offset(5 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_second_precision_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder
            .clone()
            .with_milliseconds(192)
            .build_at_offset(5 * 60)?;
        // The microseconds field has the same amount of time, but a different precision.
        let timestamp2 = builder
            .with_microseconds(193 * 1_000)
            .build_at_offset(5 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_seconds_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms(2021, 2, 5, 16, 43, 51);
        let timestamp1 = builder
            .clone()
            .with_milliseconds(192)
            .build_at_offset(5 * 60)?;
        let timestamp2 = builder.with_milliseconds(193).build_at_offset(5 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_seconds_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone().with_second(12).build_at_offset(5 * 60)?;
        let timestamp2 = builder.with_second(13).build_at_offset(5 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_minutes_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5);
        let timestamp1 = builder
            .clone()
            .with_hour_and_minute(16, 42)
            .build_at_offset(5 * 60)?;
        let timestamp2 = builder
            .with_hour_and_minute(16, 43)
            .build_at_offset(5 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_hours_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_ymd(2021, 2, 5);
        let timestamp1 = builder
            .clone()
            .with_hour_and_minute(16, 42)
            .build_at_offset(5 * 60)?;
        let timestamp2 = builder
            .with_hour_and_minute(17, 42)
            .build_at_offset(5 * 60)?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_days_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021).with_month(2);
        let timestamp1 = builder.clone().with_day(5).build()?;
        let timestamp2 = builder.with_day(6).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_months_are_not_equal() -> IonResult<()> {
        let builder = Timestamp::with_year(2021);
        let timestamp1 = builder.clone().with_month(2).build()?;
        let timestamp2 = builder.with_month(3).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_years_are_not_equal() -> IonResult<()> {
        let timestamp1 = Timestamp::with_year(2021).build()?;
        let timestamp2 = Timestamp::with_year(2022).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamp_try_into_naive_datetime() -> IonResult<()> {
        let timestamp = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_unknown_offset()?;
        let naive_datetime: NaiveDateTime = timestamp.try_into()?;
        let expected = NaiveDate::from_ymd_opt(2021, 4, 6)
            .unwrap()
            .and_hms_opt(10, 15, 0)
            .unwrap();
        assert_eq!(expected, naive_datetime);
        Ok(())
    }

    #[test]
    fn test_timestamp_try_into_naive_datetime_fractional_seconds() -> IonResult<()> {
        let timestamp = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0)
            .with_milliseconds(449)
            .build_at_unknown_offset()?;
        let datetime: NaiveDateTime = timestamp.try_into()?;
        let naive_datetime = NaiveDate::from_ymd_opt(2021, 4, 6)
            .unwrap()
            .and_hms_opt(10, 15, 0)
            .unwrap()
            .with_nanosecond(449000000)
            .unwrap();
        assert_eq!(datetime, naive_datetime);
        Ok(())
    }

    #[test]
    fn test_timestamp_try_into_naive_datetime_error() -> IonResult<()> {
        let timestamp = Timestamp::with_ymd_hms(2021, 1, 1, 0, 0, 0).build_at_offset(0)?;
        //     ^---- This timestamp has a known offset, so we cannot convert it into a NaiveDateTime
        let result: IonResult<NaiveDateTime> = timestamp.try_into();
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_timestamp_try_into_fixed_offset_datetime() -> IonResult<()> {
        let timestamp = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_offset(-5 * 60)?;
        //                    ^-- Timestamp's offset API takes minutes
        let datetime: DateTime<FixedOffset> = timestamp.try_into()?;
        // chrono's FixedOffset takes seconds ----------v
        let expected_offset = offset_east(-5 * 60 * 60);
        let naive_datetime = NaiveDate::from_ymd_opt(2021, 4, 6)
            .unwrap()
            .and_hms_opt(10, 15, 0)
            .unwrap();
        let expected_datetime = expected_offset
            .from_local_datetime(&naive_datetime)
            .unwrap();
        assert_eq!(datetime, expected_datetime);
        Ok(())
    }

    #[test]
    fn test_timestamp_try_into_fixed_offset_datetime_fractional_seconds() -> IonResult<()> {
        let timestamp = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0)
            .with_milliseconds(449)
            .build_at_offset(-5 * 60)?;
        //                    ^-- Timestamp's offset API takes minutes
        let datetime: DateTime<FixedOffset> = timestamp.try_into()?;
        // chrono's FixedOffset takes seconds ----------v
        let expected_offset = offset_east(-5 * 60 * 60);
        let naive_datetime = NaiveDate::from_ymd_opt(2021, 4, 6)
            .unwrap()
            .and_hms_opt(10, 15, 0)
            .unwrap()
            .with_nanosecond(449000000)
            .unwrap();
        let expected_datetime = expected_offset
            .from_local_datetime(&naive_datetime)
            .unwrap();
        assert_eq!(datetime, expected_datetime);
        Ok(())
    }

    #[test]
    fn test_timestamp_try_into_datetime_fixedoffset_error() -> IonResult<()> {
        let timestamp = Timestamp::with_ymd_hms(2021, 1, 1, 0, 0, 0).build_at_unknown_offset()?;
        //     ^---- This timestamp has an unknown offset, so we cannot convert it into a DateTime<FixedOffset>
        let result: IonResult<DateTime<FixedOffset>> = timestamp.try_into();
        assert!(result.is_err());
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
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        let timestamp2 = Timestamp::with_ymd(2021, 2, 5)
            .with_hms(17, 39, 51)
            .with_milliseconds(194)
            .build_at_offset(-4 * 60)
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        let timestamp3 = Timestamp::with_ymd_hms_millis(2021, 2, 5, 17, 39, 51, 194)
            .build_at_offset(-4 * 60)
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        assert_eq!(timestamp1.precision, Precision::Second);
        assert_eq!(timestamp1.fractional_seconds, Some(Mantissa::Digits(3)));
        assert_eq!(timestamp1, timestamp2);
        assert_eq!(timestamp2, timestamp3);

        assert!(timestamp1.ion_eq(&timestamp2));
        assert!(timestamp1.ion_eq(&timestamp3));
    }

    #[test]
    fn test_timestamp_fixed_offset() -> IonResult<()> {
        let timestamp = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0)
            .with_milliseconds(449)
            .build_at_offset(-5 * 60)?;
        //                    ^-- Timestamp's offset API takes minutes
        // expected offset in minutes
        let expected_offset = -5 * 60;

        assert_eq!(timestamp.offset().unwrap(), expected_offset);
        Ok(())
    }

    #[test]
    fn test_timestamp_precision() -> IonResult<()> {
        let timestamp = Timestamp::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp.precision(), Precision::Month);
        Ok(())
    }

    #[test]
    fn test_timestamp_year() -> IonResult<()> {
        let timestamp_1 = Timestamp::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp_1.year(), 2021);

        let timestamp_2 =
            Timestamp::with_ymd_hms(2021, 12, 31, 10, 15, 30).build_at_offset(-11 * 60)?;

        assert_eq!(timestamp_2.year(), 2021);

        let timestamp_3 =
            Timestamp::with_ymd_hms(2021, 12, 31, 15, 15, 30).build_at_offset(10 * 60)?;

        assert_eq!(timestamp_3.year(), 2021);

        Ok(())
    }

    #[test]
    fn test_timestamp_month() -> IonResult<()> {
        let timestamp_1 = Timestamp::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp_1.month(), 2);

        let timestamp_2 =
            Timestamp::with_ymd_hms(2021, 1, 31, 10, 15, 30).build_at_offset(-11 * 60)?;

        assert_eq!(timestamp_2.month(), 1);

        let timestamp_3 =
            Timestamp::with_ymd_hms(2021, 1, 31, 15, 15, 30).build_at_offset(10 * 60)?;

        assert_eq!(timestamp_3.month(), 1);

        Ok(())
    }

    #[test]
    fn test_timestamp_day() -> IonResult<()> {
        let timestamp_1 = Timestamp::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp_1.day(), 1);

        let timestamp_2 = Timestamp::with_year(2021)
            .with_month(2)
            .with_day(4)
            .build()?;

        assert_eq!(timestamp_2.day(), 4);

        let timestamp_3 =
            Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-11 * 60)?;

        assert_eq!(timestamp_3.day(), 6);

        let timestamp_4 =
            Timestamp::with_ymd_hms(2021, 4, 6, 15, 15, 30).build_at_offset(10 * 60)?;

        assert_eq!(timestamp_4.day(), 6);

        Ok(())
    }

    #[rstest]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-90), 10)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-5 * 60), 10)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(5 * 60), 10)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(15), 10)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(30), 10)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(0), 10)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 0, 15, 30).build_at_offset(5 * 60), 0)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 23, 15, 30).build_at_offset(-5 * 60), 23)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 0, 15, 30).build_at_offset(23 * 60), 0)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-11 * 60), 10)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 15, 15, 30).build_at_offset(10 * 60), 15)]
    fn test_timestamp_hour(
        #[case] timestamp: IonResult<Timestamp>,
        #[case] expected_hours: u32,
    ) -> IonResult<()> {
        assert_eq!(timestamp?.hour(), expected_hours);
        Ok(())
    }

    #[rstest]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-90), 15)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-5 * 60), 15)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(5 * 60), 15)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(0), 15)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 0, 30).build_at_offset(5 * 60), 0)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 59, 30).build_at_offset(5 * 60), 59)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-11 * 60), 15)]
    #[case(Timestamp::with_ymd_hms(2021, 4, 6, 15, 15, 30).build_at_offset(10 * 60), 15)]
    fn test_timestamp_minute(
        #[case] timestamp: IonResult<Timestamp>,
        #[case] expected_minutes: u32,
    ) -> IonResult<()> {
        assert_eq!(timestamp?.minute(), expected_minutes);
        Ok(())
    }

    #[test]
    fn test_timestamp_second() -> IonResult<()> {
        let timestamp = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-5 * 60)?;
        assert_eq!(timestamp.second(), 30);
        Ok(())
    }

    #[test]
    fn test_timestamp_nanoseconds() -> IonResult<()> {
        let timestamp_1 = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30)
            .with_nanoseconds(192)
            .build_at_offset(-5 * 60)?;
        assert_eq!(timestamp_1.nanoseconds(), 192);

        let timestamp_2 = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30)
            .with_milliseconds(192)
            .build_at_offset(-5 * 60)?;
        assert_eq!(timestamp_2.nanoseconds(), 192000000);

        let timestamp_3 =
            Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-5 * 60)?;
        assert_eq!(timestamp_3.nanoseconds(), 0);

        Ok(())
    }

    #[test]
    fn test_timestamp_milliseconds() -> IonResult<()> {
        let timestamp_1 = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30)
            .with_milliseconds(192)
            .build_at_offset(-5 * 60)?;
        assert_eq!(timestamp_1.milliseconds(), 192);

        let timestamp_2 =
            Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 30).build_at_offset(-5 * 60)?;
        assert_eq!(timestamp_2.milliseconds(), 0);
        Ok(())
    }

    #[test]
    fn test_timestamp_to_utc() -> IonResult<()> {
        let new_years_eve_nyc =
            Timestamp::with_ymd_hms(2022, 12, 31, 23, 59, 00).build_at_offset(-5 * 60)?;

        let london = new_years_eve_nyc.to_utc();
        assert_eq!(london.year(), 2023);
        assert_eq!(london.month(), 1);
        assert_eq!(london.day(), 1);
        assert_eq!(london.hour(), 4);
        assert_eq!(london.minute(), 59);
        assert_eq!(london.second(), 0);
        Ok(())
    }

    #[test]
    fn test_timestamp_fractional_seconds_scale() -> IonResult<()> {
        // Set fractional seconds as Decimal
        let timestamp_with_micro_seconds = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0)
            .with_fractional_seconds(Decimal::new(553u64, -6))
            .build_at_offset(-5 * 60)?;

        assert_eq!(
            timestamp_with_micro_seconds
                .fractional_seconds_scale()
                .unwrap(),
            6
        );

        // Set fractional seconds as Decimal with 0 coefficient and non-negative exponent
        // "Fractions whose coefficient is zero and exponent is greater than -1 are ignored."
        let timestamp_with_redundant_fractional_seconds =
            Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0)
                .with_fractional_seconds(Decimal::new(0, 6))
                .build_at_offset(-5 * 60)?;
        assert_eq!(
            timestamp_with_redundant_fractional_seconds.precision,
            Precision::Second
        );
        assert_eq!(
            timestamp_with_redundant_fractional_seconds.fractional_seconds_scale(),
            None
        );

        // Set fractional seconds with milliseconds
        let timestamp_with_milliseconds = Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0)
            .with_milliseconds(449)
            .build_at_offset(-5 * 60)?;

        assert_eq!(
            timestamp_with_milliseconds
                .fractional_seconds_scale()
                .unwrap(),
            3
        );

        // Set a fractional seconds as Decimal with low precision
        let timestamp_with_seconds =
            Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_offset(-5 * 60)?;

        // For low precision fractional_seconds_scale should return a None
        assert_eq!(timestamp_with_seconds.fractional_seconds_scale(), None);
        Ok(())
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

    #[rstest]
    #[case::timestamp_with_same_year(Timestamp::with_year(2020).build().unwrap(), Timestamp::with_year(2020).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_different_year(Timestamp::with_year(2020).build().unwrap(), Timestamp::with_year(2021).build().unwrap(), Ordering::Less)]
    #[case::timestamp_with_milliseconds(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).with_milliseconds(449).build_at_offset(5 * 60).unwrap(), Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).with_milliseconds(449).build_at_offset(5 * 60).unwrap(), Ordering::Equal)]
    #[case::timestamp_with_milliseconds_nanoseconds(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).with_milliseconds(449).build_at_offset(5 * 60).unwrap(), Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).with_nanoseconds(449000005).build_at_offset(5 * 60).unwrap(), Ordering::Less)]
    #[case::timestamp_with_fractional_seconds(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).with_fractional_seconds(Decimal::new(449u64, -3)).build_at_offset(5 * 60).unwrap(), Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).with_nanoseconds(449000000).build_at_offset(5 * 60).unwrap(), Ordering::Equal)]
    #[case::timestamp_with_different_precision(Timestamp::with_year(2020).with_month(3).build().unwrap(), Timestamp::with_year(2020).build().unwrap(), Ordering::Greater)]
    #[case::timestamp_with_same_offset(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_offset(-5 * 60).unwrap(), Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_offset(-5 * 60).unwrap(), Ordering::Equal)]
    #[case::timestamp_with_different_offset(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_offset(5 * 60).unwrap(), Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_offset(-5 * 60).unwrap(), Ordering::Less)]
    #[case::timestamp_with_unknown_offset(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_unknown_offset().unwrap(), Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_offset(-5 * 60).unwrap(), Ordering::Less)]
    #[case::timestamp_with_unknown_offset(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).with_nanoseconds(0).build_at_unknown_offset().unwrap(), Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_unknown_offset().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_unknown_offset(Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).with_nanoseconds(449000005).build_at_unknown_offset().unwrap(), Timestamp::with_ymd_hms(2021, 4, 6, 10, 15, 0).build_at_unknown_offset().unwrap(), Ordering::Greater)]
    #[case::timestamp_with_second_precison_and_year_precision(Timestamp::with_ymd(2001, 1, 1).build().unwrap(), Timestamp::with_ymd_hms(2001, 1, 1, 0, 0, 0).with_fractional_seconds(Decimal::new(00000000000000000000u128, -20)).build_at_unknown_offset().unwrap(), Ordering::Equal)]
    fn timestamp_ordering_tests(
        #[case] this: Timestamp,
        #[case] other: Timestamp,
        #[case] expected: Ordering,
    ) {
        assert_eq!(this.cmp(&other), expected)
    }

    #[test]
    fn ion_eq_fraction_seconds_mixed_mantissa() {
        let t1 = Timestamp {
            date_time: NaiveDateTime::from_str("1857-05-29T19:25:59.100").unwrap(),
            offset: Some(offset_east(60 * 60 * 23 + 60 * 59)),
            precision: Precision::Second,
            fractional_seconds: Some(Mantissa::Digits(1)),
        };
        let t2 = Timestamp {
            date_time: NaiveDateTime::from_str("1857-05-29T19:25:59").unwrap(),
            offset: Some(offset_east(60 * 60 * 23 + 60 * 59)),
            precision: Precision::Second,
            fractional_seconds: Some(Mantissa::Arbitrary(Decimal::new(1u64, -1))),
        };
        assert_eq!(t1, t2);
        assert!(t1.ion_eq(&t2));
    }

    #[test]
    fn ion_eq_fraction_seconds_mixed_mantissa_2() {
        let t1 = Timestamp {
            date_time: NaiveDateTime::from_str("2001-08-01T18:18:49.006").unwrap(),
            offset: Some(offset_east(60 * 60 + 60)),
            precision: Precision::Second,
            fractional_seconds: Some(Mantissa::Digits(5)),
        };
        let t2 = Timestamp {
            date_time: NaiveDateTime::from_str("2001-08-01T18:18:49").unwrap(),
            offset: Some(offset_east(60 * 60 + 60)),
            precision: Precision::Second,
            fractional_seconds: Some(Mantissa::Arbitrary(Decimal::new(600u64, -5))),
        };
        assert_eq!(t1, t2);
        assert!(t1.ion_eq(&t2));
    }

    #[rstest]
    #[case(Timestamp::with_year(3030).build().unwrap(), "3030T")]
    #[case(Timestamp::with_year(3030).with_month(11).build().unwrap(), "3030-11T")]
    #[case(Timestamp::with_ymd(3030, 3, 31).build().unwrap(), "3030-03-31T")]
    #[case(Timestamp::with_ymd(3030, 3, 31).with_hour_and_minute(17, 31).build_at_unknown_offset().unwrap(), "3030-03-31T17:31-00:00")]
    #[case(Timestamp::with_ymd(3030, 3, 31).with_hour_and_minute(17, 31).build_at_offset(-420).unwrap(), "3030-03-31T17:31-07:00")]
    #[case(Timestamp::with_ymd(3030, 3, 31).with_hour_and_minute(17, 31).build_utc_fields_at_offset(-420).unwrap(), "3030-03-31T10:31-07:00")]
    #[case(Timestamp::with_ymd_hms(3030, 3, 31, 17, 31, 57).build_at_offset(0).unwrap(), "3030-03-31T17:31:57+00:00")]
    #[case(Timestamp::with_ymd_hms(3030, 3, 31, 17, 31, 57).with_milliseconds(27).build_at_offset(0).unwrap(), "3030-03-31T17:31:57.027+00:00")]
    #[case(Timestamp::with_ymd_hms(3030, 3, 31, 17, 31, 57).with_microseconds(27).build_at_offset(0).unwrap(), "3030-03-31T17:31:57.000027+00:00")]
    #[case(Timestamp::with_ymd_hms(3030, 3, 31, 17, 31, 57).with_nanoseconds(27).build_at_offset(0).unwrap(), "3030-03-31T17:31:57.000000027+00:00")]
    #[case(Timestamp::with_ymd_hms(3030, 3, 31, 17, 31, 57).with_fractional_seconds(Decimal::new(27, -12)).build_at_offset(0).unwrap(), "3030-03-31T17:31:57.000000000027+00:00")]
    fn test_display(#[case] ts: Timestamp, #[case] expect: String) {
        let mut buf = Vec::new();
        write!(&mut buf, "{ts}").unwrap();
        assert_eq!(expect, String::from_utf8(buf).unwrap());
    }
}
