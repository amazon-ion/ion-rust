//! Types related to [`Decimal`], the in-memory representation of an Ion decimal value.

use std::cmp::Ordering;

use crate::decimal::coefficient::{Coefficient, Sign};
use crate::ion_data::{IonEq, IonOrd};
use crate::result::{IonError, IonFailure};
use crate::{Int, IonResult, UInt};
use num_traits::Zero;
use std::convert::{TryFrom, TryInto};
use std::fmt::{Display, Formatter};
use std::ops::Neg;

pub mod coefficient;

/// An arbitrary-precision Decimal type with a distinct representation of negative zero (`-0`).
///
/// A `Decimal` can be thought of as a `(coefficient, exponent)` pair, and its value can be
/// calculated using the formula `coefficient * 10^exponent`.
///
/// ```
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// use ion_rs::{Int, Decimal, UInt};
/// use ion_rs::decimal::coefficient::Sign;
/// // Equivalent to: 1225 * 10^-2, or 12.25
/// let decimal = Decimal::new(1225, -2);
/// // The coefficient can be viewed as a sign/magnitude pair...
/// assert_eq!(decimal.coefficient().sign(), Sign::Positive);
/// assert_eq!(decimal.coefficient().magnitude(), UInt::from(1225u64));
/// // ...or, if it is not negative zero, by converting it into an Int.
/// let coefficient: Int = decimal.coefficient().try_into().expect("`decimal` is not negative zero");
/// assert_eq!(coefficient, Int::from(1225));
///
/// assert_eq!(decimal.exponent(), -2);
/// # Ok(())
/// # }
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Decimal {
    // A Coefficient is a `(Sign, UInt)` pair supporting integers of arbitrary size
    pub(crate) coefficient: Coefficient,
    pub(crate) exponent: i64,
}

impl Decimal {
    pub const ZERO: Decimal = Decimal {
        coefficient: Coefficient::ZERO,
        exponent: 0,
    };

    pub const NEGATIVE_ZERO: Decimal = Decimal {
        coefficient: Coefficient::NEGATIVE_ZERO,
        exponent: 0,
    };

    /// Constructs a new Decimal with the provided components. The value of the decimal is:
    ///    `coefficient * 10^exponent`
    pub fn new<C: Into<Coefficient>, E: Into<i64>>(coefficient: C, exponent: E) -> Decimal {
        let coefficient = coefficient.into();
        let exponent = exponent.into();
        Decimal {
            coefficient,
            exponent,
        }
    }

    /// Returns this `Decimal`'s coefficient.
    pub fn coefficient(&self) -> &Coefficient {
        &self.coefficient
    }

    /// Returns this `Decimal`'s exponent.
    pub fn exponent(&self) -> i64 {
        self.exponent
    }

    /// Returns scale of the Decimal value
    /// If zero or positive, a scale indicates the number of digits to the right of the decimal point.
    /// If negative, the unscaled value of the number is multiplied by ten to the power of the negation of the scale.
    /// For example, a scale of -3 means the unscaled value is multiplied by 1000.
    pub fn scale(&self) -> i64 {
        self.exponent.neg()
    }

    /// Returns the number of digits in the non-scaled integer representation of the decimal.
    pub fn precision(&self) -> u64 {
        self.coefficient.number_of_decimal_digits() as u64
    }

    /// Constructs a Decimal with the value `-0d0`. This is provided as a convenience method
    /// because Rust will ignore a unary minus when it is applied to an zero literal (`-0`).
    pub fn negative_zero() -> Decimal {
        Decimal::negative_zero_with_exponent(0)
    }

    /// Constructs a Decimal with a coefficient of `-0` and the specified exponent. This function
    /// is provided as a convenience method because Rust will ignore a unary minus when it is
    /// applied to a zero literal (`-0`).
    pub fn negative_zero_with_exponent(exponent: i64) -> Decimal {
        let coefficient = Coefficient::negative_zero();
        Decimal {
            coefficient,
            exponent,
        }
    }

    /// Returns `true` if this Decimal is a zero of any sign or exponent.
    pub fn is_zero(&self) -> bool {
        self.coefficient.magnitude().is_zero()
    }

    /// Returns true if this Decimal's coefficient has a negative sign AND a magnitude greater than
    /// zero. Otherwise, returns false. (Negative zero returns false.)
    pub fn is_less_than_zero(&self) -> bool {
        self.coefficient.sign() == Sign::Negative && self.coefficient.magnitude().data > 0
    }

    /// Semantically identical to `self >= Decimal::new(1, 0)`, but much cheaper to compute.
    pub(crate) fn is_greater_than_or_equal_to_one(&self) -> bool {
        // If the coefficient has a magnitude of zero, the Decimal is a zero of some precision
        // and so is not >= 1.
        if self.coefficient.is_zero() {
            return false;
        }

        // If the coefficient is non-zero, look at the exponent. A non-negative exponent means the
        // value has to be >= 1.
        if self.exponent >= 0 {
            return true;
        }

        // If the exponent is negative, we have to see whether if its magnitude outweighs the
        // magnitude of the coefficient.
        let num_coefficient_decimal_digits = self.coefficient.number_of_decimal_digits() as u64;
        num_coefficient_decimal_digits > self.exponent.unsigned_abs()
    }

    // Determines whether the first decimal value is greater than, equal to, or less than
    // the second decimal value.
    fn compare(d1: &Decimal, d2: &Decimal) -> Ordering {
        if d1.is_zero() && d2.is_zero() {
            // Ignore the sign/exponent if they're both some flavor of zero.
            return Ordering::Equal;
        }
        // Even if the exponents are wildly different, disagreement in the coefficient's signs
        // still tells us which value is bigger.
        let sign_cmp = d1.coefficient.sign().cmp(&d2.coefficient.sign());
        if sign_cmp != Ordering::Equal {
            return sign_cmp;
        }

        // If the signs are the same, compare their magnitudes.
        let ordering = Decimal::compare_magnitudes(d1, d2);

        if d1.coefficient.sign() == Sign::Positive {
            // If the values are both positive, use the magnitudes' ordering.
            ordering
        } else {
            // If the values are both negative, reverse the magnitudes' ordering.
            // For example: -100 has a greater magnitude (i.e. absolute value) than -99,
            //              but -99 is the larger number.
            ordering.reverse()
        }
    }

    // Compare the magnitudes (absolute values) of the provided decimal values.
    fn compare_magnitudes(d1: &Decimal, d2: &Decimal) -> Ordering {
        // If the exponents match, we can compare the two coefficients directly.
        if d1.exponent == d2.exponent {
            return d1.coefficient.magnitude().cmp(&d2.coefficient.magnitude());
        }

        // If the exponents don't match, we need to scale one of the magnitudes to match the other
        // for comparison. For example, when comparing 16e3 and 1600e1, we can't compare the
        // magnitudes (16 and 1600) directly. Instead, we need to multiply 16 by 10^2 to compensate
        // for the difference in their exponents (3-1). Then we'll be comparing 1600 to 1600,
        // and can safely conclude that they are equal.
        if d1.exponent > d2.exponent {
            Self::compare_scaled_coefficients(d1, d2)
        } else {
            Self::compare_scaled_coefficients(d2, d1).reverse()
        }
    }

    // Scales up the coefficient associated with a greater exponent and compares it with the
    // other coefficient. `d1` must have a larger exponent than `d2`.
    fn compare_scaled_coefficients(d1: &Decimal, d2: &Decimal) -> Ordering {
        let exponent_delta = d1.exponent - d2.exponent;
        // d1 has a larger exponent, so scale up its coefficient to match d2's exponent.
        // For example, when comparing these values of d1 and d2:
        //     d1 =  8 * 10^3
        //     d2 = 80 * 10^2
        // d1 has the larger exponent (3). We need to scale its coefficient up to d2's 10^2 scale.
        // We do this by multiplying it times 10^exponent_delta, which is 1 in this case.
        // This lets us compare 80 and 80, determining that the decimals are equal.
        let mut scaled_coefficient: u128 = d1.coefficient.magnitude().data;
        scaled_coefficient *= 10u128.pow(exponent_delta as u32);
        UInt::from(scaled_coefficient).cmp(&d2.coefficient.magnitude())
    }
}

impl PartialEq for Decimal {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Decimal {}

impl IonEq for Decimal {
    fn ion_eq(&self, other: &Self) -> bool {
        self.exponent == other.exponent && self.coefficient == other.coefficient
    }
}

impl IonOrd for Decimal {
    // Numerical order (least to greatest) and then by number of significant figures (least to greatest)
    fn ion_cmp(&self, other: &Self) -> Ordering {
        let sign_cmp = self.coefficient.sign().cmp(&other.coefficient.sign());
        if sign_cmp != Ordering::Equal {
            return sign_cmp;
        }

        // If the signs are the same, compare their magnitudes.
        let ordering = Decimal::compare_magnitudes(self, other);
        if ordering != Ordering::Equal {
            return match self.coefficient.sign() {
                Sign::Negative => ordering.reverse(),
                Sign::Positive => ordering,
            };
        };
        // Finally, compare the number of significant figures.
        // Since we know the numeric value is the same, we only need to look at the exponents here.
        self.exponent.cmp(&other.exponent).reverse()
    }
}

impl PartialOrd for Decimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Decimal {
    fn cmp(&self, other: &Self) -> Ordering {
        Decimal::compare(self, other)
    }
}

macro_rules! impl_decimal_from_unsigned_primitive_integer {
    ($($t:ty),*) => ($(
        impl From<$t> for Decimal {
            fn from(value: $t) -> Self {
                Decimal::new(value as u64, 0)
            }
        }
    )*)
}
impl_decimal_from_unsigned_primitive_integer!(u8, u16, u32, u64, usize);

macro_rules! impl_decimal_from_signed_primitive_integer {
    ($($t:ty),*) => ($(
        impl From<$t> for Decimal {
            fn from(value: $t) -> Self {
                Decimal::new(Coefficient::new(value), 0)
            }
        }
    )*)
}
impl_decimal_from_signed_primitive_integer!(i8, i16, i32, i64, isize);

impl From<Int> for Decimal {
    fn from(value: Int) -> Self {
        Decimal::new(value, 0)
    }
}

impl TryFrom<f32> for Decimal {
    type Error = IonError;

    fn try_from(value: f32) -> Result<Self, Self::Error> {
        // Defer to the f64 implementation of `TryInto`
        (value as f64).try_into()
    }
}

impl TryFrom<f64> for Decimal {
    type Error = IonError;
    /// Attempts to create a Decimal from an f64. Returns an Error if the f64 being
    /// converted is a special value, including:
    ///   * Infinity
    ///   * Negative infinity
    ///   * NaN (not-a-number)
    ///
    /// Otherwise, returns Ok.
    ///
    /// Because Decimal can represent negative zero, f64::neg_zero() IS supported.
    ///
    /// NOTE: While the resulting decimal will be a very close approximation of the original f64's
    ///       value, this is an inherently lossy operation. Floating point values do not encode a
    ///       precision. When converting an f64 to a Decimal, a precision for the new Decimal must
    ///       be chosen somewhat arbitrarily. Do NOT rely on the precision of the resulting Decimal.
    ///       This implementation may change without notice.
    fn try_from(value: f64) -> Result<Self, Self::Error> {
        // === Special `f64` values ===

        if value.is_infinite() {
            if value.is_sign_negative() {
                return IonResult::illegal_operation(
                    "Cannot convert f64 negative infinity to Decimal.",
                );
            } else {
                return IonResult::illegal_operation("Cannot convert f64 infinity to Decimal.");
            }
        } else if value.is_nan() {
            return IonResult::illegal_operation(
                "Cannot convert f64 NaN (not-a-number) to Decimal.",
            );
        }

        // === The signed and unsigned zero cases ===

        // You can't use the `log10` operation on a zero value, so check for these cases explicitly.
        if value == 0f64 {
            //    ^- Positive and negative zero are mathematically equivalent,
            //       so we can use `==` here to check for both.
            if value.is_sign_negative() {
                return Ok(Decimal::NEGATIVE_ZERO);
            }
            return Ok(Decimal::ZERO);
        }

        // === Split the value into its int and fraction components ===

        // Isolate the integral portion of the f64. (e.g. 3.14 -> 3.0)
        let f64_int = value.trunc();
        //                  ^^^^^^
        // The `trunc()` method discards the fractional part of the value, returning its integer
        // component as an `f64`.

        // Isolate the fractional portion of the value. (e.g. 3.14 -> 0.14)
        let f64_fract = value.fract();
        //                    ^^^^^^
        // The `fract()` method returns the fractional part of the value as an f64.

        // === The general case ===

        // Due to the nature of IEEE-754 `f64` encoding, the value's integral component can be an
        // integer outside the integer range supported by `i128`. Starting at (2^53 + 1), an `f64`
        // will start skipping over one or more integers as its representational precision breaks down.
        // An `i128` can precisely represent more integers than an `f64` can, but because `f64` can
        // "skip" regions of large numbers, the `f64` has a wider range of integers it can represent.
        //
        // Our coefficient will be stored in an `Int` with 128 bits, allowing us to store up to 38
        // decimal places of precision.
        const MAX_DECIMAL_DIGITS: u32 = 38;
        // If the total number of digits in the f64 exceed 38, we'll need to truncate the coefficient
        // at 38 digits and increase the exponent (i.e. the number of trailing zeros) to approximate
        // what was lost.
        //
        // For example, this 40 digit number:
        //
        //    1234567890_1234567890_1234567890_1234567890
        //
        // would be turned into a decimal whose coefficient was:
        //
        //    1234567890_1234567890_1234567890_12345678XX
        //                               discarded ----^^
        //
        // and its exponent would be increased by 2 to retain the scale of discarded digits.

        // Store a copy of the value as an i128
        let integral_value = f64_int as i128;
        // Determine how many decimal digits comprise the integral portion
        let num_integral_decimal_digits = f64_int.abs().log10().floor() as u32 + 1;

        // Check to see if the fractional part of the value is zero; if so, the value is an integer.
        if f64_fract.is_zero() {
            // If the f64 is an integer value, we can convert it to a decimal trivially.
            // For very large integer values, we need to set the exponent to capture any scale
            // that the coefficient alone was not able to store.
            let exponent = (num_integral_decimal_digits as i64 - MAX_DECIMAL_DIGITS as i64).max(0);
            return Ok(Decimal::new(integral_value, exponent));
        }

        // The number of fractional digits we'll retain is the smaller of:
        //   * the number of digits _not_ occupied by the integral portion of the number
        //     OR
        //   * the number of fractional digits an f64 can represent
        let num_fractional_digits =
            (MAX_DECIMAL_DIGITS - num_integral_decimal_digits).min(f64::DIGITS);
        //                                                         ^^^^^^^^^^^
        // `f64::DIGITS` is the number of base 10 digits of fractional precision in an `f64`: 15

        // Shift `num_fractional_digits` fractional digits into the integer portion of the f64.
        let coefficient_f64 = value * 10f64.powi(num_fractional_digits as i32);
        let coefficient = coefficient_f64 as i128;

        let exponent = -(num_fractional_digits as i64);
        Ok(Decimal::new(coefficient, exponent))
    }
}

impl Display for Decimal {
    #[rustfmt::skip] // https://github.com/rust-lang/rustfmt/issues/3255
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // Inspired by the formatting conventions of Java's BigDecimal.toString()
        const WIDE_NUMBER: usize = 6; // if you think about it, six is a lot 🙃

        let digits = &*self.coefficient.magnitude().to_string();
        let len = digits.len();
        // The index of the decimal point, relative to the magnitude representation
        //       0123                                                       01234
        // Given ABCDd-2, the decimal gets inserted at position 2, yielding AB.CD
        let dot_index = len as i64 + self.exponent;

        if self.coefficient.sign() == Sign::Negative {
            write!(f, "-").unwrap();
        };

        if self.exponent == 0 && len > WIDE_NUMBER { // e.g. A.BCDEFGd6
            write!(f, "{}.{}d{}", &digits[0..1], &digits[1..len], (dot_index - 1))
        } else if self.exponent == 0 { // e.g. ABC.
            write!(f, "{}.", &digits)
        } else if self.exponent >= 0 { // e.g. ABCd1
            write!(f, "{}d{}", &digits, self.exponent)
        } else { // exponent < 0, there is a fractional component
            if dot_index > 0 { // e.g. A.BC or AB.C
                let dot_index = dot_index as usize;
                write!(f, "{}.{}", &digits[0..dot_index], &digits[dot_index..len])
            } else if dot_index > -(WIDE_NUMBER as i64) { // e.g. 0.ABC or 0.000ABC
                let width = dot_index.unsigned_abs() as usize + len;
                write!(f, "0.{digits:0>width$}", width = width, digits = digits)
            } else { // e.g. A.BCd-12
                write!(f, "{}.{}d{}", &digits[0..1], &digits[1..len], (dot_index - 1))
            }
        }
    }
}

#[cfg(test)]
mod decimal_tests {
    use crate::decimal::coefficient::Coefficient;
    use crate::result::IonResult;
    use crate::{Decimal, Int};

    use num_traits::Float;
    use std::cmp::Ordering;
    use std::convert::TryInto;
    use std::fmt::Write;

    use crate::ion_data::IonEq;

    use rstest::*;

    #[rstest]
    #[case(Decimal::new(123, 1), "123d1")]
    #[case(Decimal::new(123, 0), "123.")]
    #[case(Decimal::new(-123,  0),"-123.")]
    #[case(Decimal::new( 123, -1),  "12.3")]
    #[case(Decimal::new( 123, -3),   "0.123")]
    #[case(Decimal::new(-123, -5),  "-0.00123")]
    #[case(Decimal::new( 123, -5),   "0.00123")]
    #[case(Decimal::new( 123, -10),  "1.23d-8")]
    #[case(Decimal::new(-123, -10), "-1.23d-8")]
    fn test_display(#[case] decimal: Decimal, #[case] expected: &str) {
        let mut buffer = String::new();
        write!(buffer, "{decimal}").unwrap();
        assert_eq!(buffer.as_str(), expected);
    }

    #[test]
    fn test_decimal_eq_negative_zeros() {
        // Decimal zeros of any sign/exponent are mathematically equal.
        assert_eq!(Decimal::negative_zero(), Decimal::negative_zero());
        assert_eq!(
            Decimal::negative_zero_with_exponent(2),
            Decimal::negative_zero_with_exponent(7)
        );
        assert_eq!(
            Decimal::new(0, 0),
            Decimal::new(Coefficient::negative_zero(), 0)
        );
    }

    #[test]
    fn test_decimal_ion_eq_negative_zeros() {
        // To be IonEq, decimal zeros must have the same sign and exponent.
        assert!(Decimal::negative_zero().ion_eq(&Decimal::negative_zero()));
        assert!(!Decimal::negative_zero_with_exponent(2)
            .ion_eq(&Decimal::negative_zero_with_exponent(7)));
        assert!(!Decimal::new(0, 0).ion_eq(&Decimal::new(Coefficient::negative_zero(), 0)));
    }

    #[rstest]
    // Each tuple is a coefficient/exponent pair that will be used to construct a Decimal.
    // The boolean indicates whether the two Decimals are expected to be equal.
    #[case((80, 2), (80, 2), true)]
    #[case((124, -2), (1240, -3), true)]
    #[case((0, 0), (0, 0), true)]
    #[case((0, -2), (0, 3), true)]
    #[case((0, 2), (0, 5), true)]
    fn test_decimal_eq<I: Into<Coefficient>>(
        #[case] components1: (I, i64),
        #[case] components2: (I, i64),
        #[case] is_equal: bool,
    ) {
        let decimal1 = Decimal::new(components1.0.into(), components1.1);
        let decimal2 = Decimal::new(components2.0.into(), components2.1);
        assert_eq!(decimal1 == decimal2, is_equal);
    }

    #[rstest]
    // Each tuple is a coefficient/exponent pair that will be used to construct a Decimal.
    // The boolean indicates whether the two Decimals are expected to be Ion-equal.
    #[case((80, 2), (80, 2), true)]
    #[case((124, -2), (124, -2), true)]
    #[case((-124, -2), (-124, -2), true)]
    #[case((124, -2), (1240, -3), false)]
    #[case((0, 0), (0, 0), true)]
    #[case((0, -2), (0, -3), false)]
    #[case((0, -2), (0, 3), false)]
    #[case((0, -2), (0, -2), true)]
    #[case((0, 2), (0, 5), false)]
    fn test_decimal_ion_eq<I: Into<Coefficient>>(
        #[case] components1: (I, i64),
        #[case] components2: (I, i64),
        #[case] ion_eq_expected: bool,
    ) {
        let decimal1 = Decimal::new(components1.0.into(), components1.1);
        let decimal2 = Decimal::new(components2.0.into(), components2.1);
        assert_eq!(decimal1.ion_eq(&decimal2), ion_eq_expected);
    }

    #[rstest]
    // Each tuple is a coefficient/exponent pair that will be used to construct a Decimal
    // Positive numbers
    #[case((80, 3), Ordering::Equal,   (80, 3))]
    #[case((80, 3), Ordering::Greater, (79, 3))]
    #[case((80, 3), Ordering::Less,    (81, 3))]
    #[case((80, 3), Ordering::Greater, (80, 2))]
    #[case((80, 3), Ordering::Less,    (80, 4))]
    #[case((80, 3), Ordering::Equal,   (8, 4))]
    #[case((80, 3), Ordering::Equal,   (800, 2))]
    // Negative numbers
    #[case((-80, 3), Ordering::Equal,   (-80, 3))]
    #[case((-80, 3), Ordering::Less,    (-79, 3))]
    #[case((-80, 3), Ordering::Greater, (-81, 3))]
    #[case((-80, 3), Ordering::Less,    (-80, 2))]
    #[case((-80, 3), Ordering::Greater, (-80, 4))]
    #[case((-80, 3), Ordering::Equal,   (-8, 4))]
    #[case((-80, 3), Ordering::Equal,   (-800, 2))]
    // Positive zeros
    #[case((0, 3), Ordering::Equal,   (0, 3))]
    #[case((0, 3), Ordering::Greater, (-1, 3))]
    #[case((0, 3), Ordering::Less,    (1, 3))]
    #[case((0, 3), Ordering::Equal,   (0, -2))]
    #[case((0, 3), Ordering::Equal,   (0, -1))]
    #[case((0, 3), Ordering::Equal,   (0, 0))]
    #[case((0, 3), Ordering::Equal,   (0, 1))]
    #[case((0, 3), Ordering::Equal,   (0, 2))]
    // Negative zeros
    #[case((0, 3), Ordering::Equal,   (Coefficient::NEGATIVE_ZERO, -1))]
    #[case((0, 3), Ordering::Equal,   (Coefficient::NEGATIVE_ZERO, 0))]
    #[case((0, 3), Ordering::Equal,   (Coefficient::NEGATIVE_ZERO, 1))]
    #[case((Coefficient::NEGATIVE_ZERO, 3), Ordering::Equal,   (Coefficient::NEGATIVE_ZERO, -1))]
    #[case((Coefficient::NEGATIVE_ZERO, 3), Ordering::Equal,   (Coefficient::NEGATIVE_ZERO, 0))]
    #[case((Coefficient::NEGATIVE_ZERO, 3), Ordering::Equal,   (Coefficient::NEGATIVE_ZERO, 1))]
    // Other interesting numbers
    #[case((-1000, -1), Ordering::Less, (-99_999_999_999i64, -9))]
    #[case((1000, -1), Ordering::Greater, (99_999_999_999i64, -9))]
    fn test_decimal_ord<A: Into<Coefficient>, B: Into<Coefficient>>(
        #[case] components1: (A, i64),
        #[case] ordering: Ordering,
        #[case] components2: (B, i64),
    ) {
        let decimal1 = Decimal::new(components1.0.into(), components1.1);
        let decimal2 = Decimal::new(components2.0.into(), components2.1);
        assert_eq!(decimal1.cmp(&decimal2), ordering);
        // Make sure the inverse relationship holds
        assert_eq!(decimal2.cmp(&decimal1), ordering.reverse());
    }

    #[rstest]
    // Positive integers
    #[case(i32::MIN as f64, Decimal::from(i32::MIN))]
    #[case(10.0, Decimal::from(10))]
    #[case(1.0, Decimal::from(1))]
    #[case(0.0, Decimal::ZERO)]
    // The largest positive integer an f64 can precisely represent
    #[case((2i64.pow(53) - 1) as f64, Decimal::new(2i64.pow(53) - 1, 0))]
    // Negative integers
    #[case(-0.0, Decimal::NEGATIVE_ZERO)]
    #[case(-1.0, Decimal::from(-1))]
    #[case(-10.0, Decimal::from(-10))]
    #[case(i32::MAX as f64, Decimal::from(i32::MAX))]
    // The largest negative integer an f64 can precisely represent
    #[case((-(2i64.pow(53)) + 1) as f64, Decimal::new(-(2i64.pow(53)) + 1, 0))]
    // Positive floats
    #[case(8.67, Decimal::new(867, -2))]
    #[case(8.6753, Decimal::new(86753, -4))]
    #[case(8.675309, Decimal::new(8675309, -6))]
    // Negative float
    #[case(-8.67, Decimal::new(-867, -2))]
    #[case(-8.6753, Decimal::new(-86753, -4))]
    #[case(-8.675309, Decimal::new(-8675309, -6))]
    // Positive zero-with-fraction
    #[case(0.2, Decimal::new(2, -1))]
    #[case(0.24, Decimal::new(24, -2))]
    #[case(0.246, Decimal::new(246, -3))]
    #[case(0.24601, Decimal::new(24601, -5))]
    // Negative zero-with-fraction
    #[case(-0.2, Decimal::new(-2, -1))]
    #[case(-0.24, Decimal::new(-24, -2))]
    #[case(-0.246, Decimal::new(-246, -3))]
    #[case(-0.24601, Decimal::new(-24601, -5))]
    // Values with very small magnitudes
    #[case(0.000_000_000_000_001, Decimal::new(1, -15))]
    #[case(-0.000_000_000_000_001, Decimal::new(-1, -15))]
    fn test_decimal_try_from_f64_ok(#[case] value: f64, #[case] expected: Decimal) {
        let actual: Decimal = value.try_into().unwrap();
        assert_eq!(
            actual, expected,
            "float {value}: actual {actual} != expected {expected}"
        );
    }

    #[rstest]
    #[case::positive_infinity(f64::infinity())]
    #[case::negative_infinity(f64::neg_infinity())]
    #[case::nan(f64::nan())]
    fn test_decimal_try_from_f64_err(#[case] value: f64) {
        let conversion_result: IonResult<Decimal> = value.try_into();
        assert!(conversion_result.is_err());
    }

    #[rstest]
    #[case(Decimal::new(23, -3), 3)]
    #[case(Decimal::new(23, -2), 2)]
    #[case(Decimal::new(23, -1), 1)]
    #[case(Decimal::new(23, 0), 0)]
    #[case(Decimal::new(23, 1), -1)]
    #[case(Decimal::new(23, 2), -2)]
    #[case(Decimal::new(23, 3), -3)]
    #[case(Decimal::new(4, 3), -3)]
    #[case(Decimal::new(40, 3), -3)]
    #[case(Decimal::new(400, 3), -3)]
    #[case(Decimal::new(5, -4), 4)]
    #[case(Decimal::new(50, -4), 4)]
    #[case(Decimal::new(500, -4), 4)]
    #[case(Decimal::new(0, 0), 0)]
    #[case(Decimal::negative_zero(), 0)]
    #[case(Decimal::negative_zero_with_exponent(1), -1)]
    #[case(Decimal::negative_zero_with_exponent(2), -2)]
    #[case(Decimal::new(u64::MAX, -5), 5)]
    #[case(Decimal::new(u64::MAX, 0), 0)]
    fn test_scale(#[case] value: Decimal, #[case] expected: i64) {
        assert_eq!(value.scale(), expected)
    }

    #[rstest]
    #[case(Decimal::new(-24600, -3), 5)]
    #[case(Decimal::new(-24600, -2), 5)]
    #[case(Decimal::new(-24600, -1), 5)]
    #[case(Decimal::new(-24600, 0), 5)]
    #[case(Decimal::new(-24600, 1), 5)]
    #[case(Decimal::new(-24600, 2), 5)]
    #[case(Decimal::new(-24600, 3), 5)]
    #[case(Decimal::new(5, -3), 1)]
    #[case(Decimal::new(50, -3), 2)]
    #[case(Decimal::new(500, -3), 3)]
    #[case(Decimal::new(6, 3), 1)]
    #[case(Decimal::new(60, 3), 2)]
    #[case(Decimal::new(600, 3), 3)]
    #[case(Decimal::new(0, -2), 1)]
    #[case(Decimal::new(0, -1), 1)]
    #[case(Decimal::new(0, 0), 1)]
    #[case(Decimal::new(0, 1), 1)]
    #[case(Decimal::new(0, 2), 1)]
    #[case(Decimal::negative_zero_with_exponent(-2), 1)]
    #[case(Decimal::negative_zero_with_exponent(-1), 1)]
    #[case(Decimal::negative_zero(), 1)]
    #[case(Decimal::negative_zero_with_exponent(1), 1)]
    #[case(Decimal::negative_zero_with_exponent(2), 1)]
    #[case(Decimal::new(u64::MAX, 3), 20)]
    #[case(Decimal::new(i128::MAX, -2), 39)]
    fn test_precision(#[case] value: Decimal, #[case] expected: u64) {
        assert_eq!(value.precision(), expected);
    }

    #[rstest]
    #[case(0, Decimal::new(0, 0))]
    #[case(1, Decimal::new(1, 0))]
    #[case(-1, Decimal::new(-1, 0))]
    #[case(-8675309i64, Decimal::new(-8675309i64, 0))]
    #[case(8675309u32, Decimal::new(8675309u32, 0))]
    // mixed coefficient representations
    #[case(8675309i64, Decimal::new(8675309u32, 0))]
    #[case(Int::from(-8675309i64), Decimal::new(-8675309i64, 0))]
    #[case(Int::from(-8675309i128), Decimal::new(-8675309i64, 0))]
    fn decimal_from_integers(
        #[case] coefficient: impl Into<Coefficient>,
        #[case] expected: Decimal,
    ) {
        assert_eq!(Decimal::new(coefficient, 0), expected);
    }
}
