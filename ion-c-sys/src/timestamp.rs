// Copyright Amazon.com, Inc. or its affiliates.

//! Provides integration between `ION_TIMESTAMP` and `chrono::DateTime`.
//!
//! Specifically, models the Ion notion of a Timestamp, with [`IonDateTime`](./struct.IonDateTime.html)
//! Which combines a `DateTime` with the concept of [*precision*](./enum.TSPrecision.html) and
//! [**known** versus **unknown** *offsets*](./enum.TSOffsetKind.html).

use crate::result::*;
use crate::*;

use self::Mantissa::*;
use self::TSOffsetKind::*;
use self::TSPrecision::*;

use bigdecimal::{BigDecimal, ToPrimitive};
use chrono::{DateTime, FixedOffset, Timelike};

pub(crate) const TS_MAX_MANTISSA_DIGITS: i64 = 9;

/// The fractional part of a `Fractional` [`TSPrecision`](./enum.TSPrecision.html).
#[derive(Debug, Clone, Eq, PartialEq, PartialOrd)]
pub enum Mantissa {
    /// A kind of precision that uses digits from the nanoseconds field of the associated
    /// `DateTime` to represent the amount of mantissa.
    ///
    /// This is required for precision of nanoseconds or lower.
    Digits(u32),
    /// Specifies the mantissa precisely as a `BigDecimal` in the range `>= 0` and `< 1`.
    /// This should correspond to the nanoseconds field insofar as it is not truncated.
    ///
    /// This is only used for precision of greater than nanoseconds.
    Fraction(BigDecimal),
}

/// Precision of an [`IonDateTime`](./struct.IonDateTime.html).
///
/// All Ion timestamps are complete points in time, but they have explicit precision
/// that is either at the date components, the minute, or second (including sub-second)
/// granularity.
#[derive(Debug, Clone, Eq, PartialEq, PartialOrd)]
pub enum TSPrecision {
    /// Year-level precision (e.g. `2020T`)
    Year,
    /// Month-level precision (e.g. `2020-08T`)
    Month,
    /// Day-level precision (e.g. `2020-08-01T`)
    Day,
    /// Minute-level precision (e.g. `2020-08-01T12:34Z`)
    Minute,
    /// Second-level precision. (e.g. `2020-08-01T12:34:56Z`)
    Second,
    /// Sub-second precision (e.g. `2020-08-01T12:34:56.123456789Z`)
    Fractional(Mantissa),
}

/// The kind of offset associated with a [`IonDateTime`](./struct.IonDateTime.html).
///
/// This is generally some specific `FixedOffset` associated with the `DateTime`,
/// but in the case of a timestamp with an *unknown UTC offset*, this will be `Unknown`,
/// and the effective `FixedOffset` will be UTC+00:00--this allows an application to
/// preserve the difference between UTC+00:00 (zulu time) and UTC-00:00 which is the unknown offset.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TSOffsetKind {
    KnownOffset,
    UnknownOffset,
}

/// Higher-level wrapper over `DateTime` preserving `ION_TIMESTAMP` properties
/// that `DateTime` does not preserve on its own.
///
/// Specifically, this adds the [*precision*](./enum.TSPrecision.html) of the timestamp and
/// its associated [*kind of offset*](./enum.TSOffsetKind.html).
///
/// ## Usage
/// Generally, users will create their own `DateTime<FixedOffset>`
/// and construct an `IonDateTime` indicating the precision as follows:
/// ```
/// # use ion_c_sys::timestamp::*;
/// # use ion_c_sys::timestamp::TSPrecision::*;
/// # use ion_c_sys::timestamp::TSOffsetKind::*;
/// # use ion_c_sys::timestamp::Mantissa::*;
/// # use ion_c_sys::result::*;
/// # use chrono::*;
/// # fn main() -> IonCResult<()> {
/// // construct a DateTime with milliseconds of fractional seconds
/// use ion_c_sys::timestamp::Mantissa::Digits;
/// let dt = DateTime::parse_from_rfc3339("2020-02-27T04:15:00.123Z").unwrap();
/// // move that into an IonDateTime with the explicit milliseconds of precision
/// let ion_dt = IonDateTime::try_new(dt, Fractional(Digits(3)), KnownOffset)?;
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct IonDateTime {
    date_time: DateTime<FixedOffset>,
    precision: TSPrecision,
    offset_kind: TSOffsetKind,
}

impl IonDateTime {
    /// Constructs a new `IonDateTime` directly without validating the `Fractional` precision.
    #[inline]
    pub(crate) fn new(
        date_time: DateTime<FixedOffset>,
        precision: TSPrecision,
        offset_kind: TSOffsetKind,
    ) -> Self {
        Self {
            date_time,
            precision,
            offset_kind,
        }
    }

    /// Constructs a new `IonDateTime` from its constituent components.
    ///
    /// Note that the `Fractional` precision must match the nanoseconds field of this
    /// will fail.  Also note that the `TSOffsetKind` must be `Unknown` for precision less than
    /// a `Minute` and must correspond to UTC+00:00 in the `DateTime`.
    #[inline]
    pub fn try_new(
        date_time: DateTime<FixedOffset>,
        precision: TSPrecision,
        offset_kind: TSOffsetKind,
    ) -> IonCResult<Self> {
        match offset_kind {
            KnownOffset => {
                if precision <= Day {
                    return Err(IonCError::with_additional(
                        ion_error_code_IERR_INVALID_TIMESTAMP,
                        "Day precision or less must not have KnownOffset",
                    ));
                }
            }
            UnknownOffset => {
                if date_time.offset().utc_minus_local() != 0 {
                    return Err(IonCError::with_additional(
                        ion_error_code_IERR_INVALID_TIMESTAMP,
                        "Mismatched offset with UnknownOffset",
                    ));
                }
            }
        };
        if let Fractional(mantissa) = &precision {
            match mantissa {
                Digits(digits) => {
                    if (*digits as i64) > TS_MAX_MANTISSA_DIGITS {
                        return Err(IonCError::with_additional(
                            ion_error_code_IERR_INVALID_TIMESTAMP,
                            "Invalid digits in precision",
                        ));
                    }
                }
                Fraction(frac) => {
                    if frac < &BigDecimal::zero() || frac >= &BigDecimal::from(1) {
                        return Err(IonCError::with_additional(
                            ion_error_code_IERR_INVALID_TIMESTAMP,
                            "Mantissa outside of range",
                        ));
                    }
                    let (_, scale) = frac.as_bigint_and_exponent();
                    if scale <= TS_MAX_MANTISSA_DIGITS {
                        return Err(IonCError::with_additional(
                            ion_error_code_IERR_INVALID_TIMESTAMP,
                            "Fractional mantissa not allowed for sub-nanosecond precision",
                        ));
                    }
                    let ns = date_time.nanosecond();
                    let frac_ns = (frac * BigDecimal::from(NS_IN_SEC))
                        .abs()
                        .to_u32()
                        .ok_or_else(|| {
                            IonCError::with_additional(
                                ion_error_code_IERR_INVALID_TIMESTAMP,
                                "Invalid mantissa in precision",
                            )
                        })?;
                    if ns != frac_ns {
                        return Err(IonCError::with_additional(
                            ion_error_code_IERR_INVALID_TIMESTAMP,
                            "Fractional mantissa inconsistent in precision",
                        ));
                    }
                }
            }
        };

        Ok(Self::new(date_time, precision, offset_kind))
    }

    /// Returns a reference to the underlying `DateTime`.
    #[inline]
    pub fn as_datetime(&self) -> &DateTime<FixedOffset> {
        &(self.date_time)
    }

    /// Returns the precision of this `IonDateTime`.
    #[inline]
    pub fn precision(&self) -> &TSPrecision {
        &(self.precision)
    }

    /// Returns the offset of this `IonDateTime`.
    #[inline]
    pub fn offset_kind(&self) -> TSOffsetKind {
        self.offset_kind
    }

    /// Consumes the underlying components of this `IonDateTime` into a `DateTime`.
    #[inline]
    pub fn into_datetime(self) -> DateTime<FixedOffset> {
        self.date_time
    }
}

#[cfg(test)]
mod test_iondt {
    use super::*;

    use rstest::rstest;

    fn frac(lit: &str) -> Mantissa {
        Fraction(BigDecimal::parse_bytes(lit.as_bytes(), 10).unwrap())
    }

    #[rstest(
        dt_lit,
        precision,
        offset_kind,
        error,
        case::year("2020-01-01T00:01:00.1234567Z", Year, UnknownOffset, None),
        case::month("2020-01-01T00:01:00.1234567Z", Month, UnknownOffset, None),
        case::day("2020-01-01T00:01:00.1234567Z", Day, UnknownOffset, None),
        case::year_bad_known_offset(
            "2020-01-01T00:01:00.1234567Z",
            Year,
            KnownOffset,
            Some(ion_error_code_IERR_INVALID_TIMESTAMP),
        ),
        case::month_bad_known_offset(
            "2020-01-01T00:01:00.1234567Z",
            Month,
            KnownOffset,
            Some(ion_error_code_IERR_INVALID_TIMESTAMP),
        ),
        case::day_bad_known_offset(
            "2020-01-01T00:01:00.1234567Z",
            Day,
            KnownOffset,
            Some(ion_error_code_IERR_INVALID_TIMESTAMP),
        ),
        case::minute("2020-01-01T00:01:00.1234567Z", Minute, KnownOffset, None),
        case::second("2020-01-01T00:01:00.1234567Z", Second, KnownOffset, None),
        case::second_unknown_offset("2020-01-01T00:01:00.1234567Z", Second, UnknownOffset, None),
        case::second_bad_unknown_offset(
            "2020-01-01T00:01:00.1234567-00:15",
            Second,
            UnknownOffset,
            Some(ion_error_code_IERR_INVALID_TIMESTAMP),
        ),
        case::fractional_digits(
            "2020-01-01T00:01:00.1234567Z",
            Fractional(Digits(3)),
            KnownOffset,
            None,
        ),
        case::fractional_digits_too_big(
            "2020-01-01T00:01:00.1234567Z",
            Fractional(Digits(10)),
            KnownOffset,
            Some(ion_error_code_IERR_INVALID_TIMESTAMP),
        ),
        case::fractional_mantissa_neg(
            "2020-01-01T00:01:00.1234567Z",
            Fractional(frac("-0.1234567")),
            KnownOffset,
            Some(ion_error_code_IERR_INVALID_TIMESTAMP),
        ),
        case::fractional_mantissa_not_fractional(
            "2020-01-01T00:01:00.1234567Z",
            Fractional(frac("1.234567")),
            KnownOffset,
            Some(ion_error_code_IERR_INVALID_TIMESTAMP),
        ),
        case::fractional_mantissa_too_small(
            "2020-01-01T00:01:00.1234567Z",
            Fractional(frac("0.1234567")),
            KnownOffset,
            Some(ion_error_code_IERR_INVALID_TIMESTAMP),
        ),
        case::fractional_mantissa_more_precision(
            "2020-01-01T00:01:00.1234567Z",
            Fractional(frac("0.1234567001234567")),
            KnownOffset,
            None,
        ),
        case::fractional_mantissa_mismatch_digits(
            "2020-01-01T00:01:00.1234567Z",
            Fractional(frac("0.123456789")),
            KnownOffset,
            Some(ion_error_code_IERR_INVALID_TIMESTAMP),
        )
    )]
    fn try_new_precision(
        dt_lit: &str,
        precision: TSPrecision,
        offset_kind: TSOffsetKind,
        error: Option<i32>,
    ) -> IonCResult<()> {
        let dt = DateTime::parse_from_rfc3339(dt_lit).unwrap();
        let res = IonDateTime::try_new(dt, precision, offset_kind);
        match res {
            Ok(_) => {
                assert_eq!(None, error);
            }
            Err(actual) => {
                if let Some(expected_code) = error {
                    assert_eq!(expected_code, actual.code, "Testing expected error codes");
                } else {
                    assert!(false, "Expected no error, but got: {:?}", actual);
                }
            }
        }
        Ok(())
    }
}
