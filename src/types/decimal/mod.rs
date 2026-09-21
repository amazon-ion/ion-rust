//! Types related to [`Decimal`], the in-memory representation of an Ion decimal value.

use std::cmp::Ordering;

use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::result::{IonError, IonFailure};
use crate::{Int, IonResult};
use num_traits::Zero;
use std::convert::{TryFrom, TryInto};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Neg;

pub(crate) mod coefficient;
pub use coefficient::{Coefficient, Sign};

/// An arbitrary-precision Decimal type with a distinct representation of negative zero (`-0`).
///
/// A `Decimal` can be thought of as a `(coefficient, exponent)` pair, and its value can be
/// calculated using the formula `coefficient * 10^exponent`.
///
/// ```
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// use ion_rs::{Int, Decimal, UInt};
/// use ion_rs::decimal::Sign;
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
#[derive(Clone, Debug)]
pub struct Decimal {
    // `Coefficient` wraps a 16-byte, align-8 `OverflowingInt`, so embedding it directly here
    // yields a 24-byte, align-8 `Decimal`. An earlier representation stored the coefficient's
    // sign and magnitude as separate fields to dodge the align-16 padding of the old magnitude
    // type; that is no longer necessary now that the coefficient is align 8.
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
        Decimal {
            coefficient: coefficient.into(),
            exponent: exponent.into(),
        }
    }

    /// Returns this `Decimal`'s coefficient.
    pub fn coefficient(&self) -> Coefficient {
        self.coefficient.clone()
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
        Decimal {
            coefficient: Coefficient::NEGATIVE_ZERO,
            exponent,
        }
    }

    /// Returns `true` if this Decimal is a zero of any sign or exponent.
    pub fn is_zero(&self) -> bool {
        self.coefficient.is_zero()
    }

    /// Returns true if this Decimal's coefficient has a negative sign AND a magnitude greater than
    /// zero. Otherwise, returns false. (Negative zero returns false.)
    pub fn is_less_than_zero(&self) -> bool {
        self.coefficient.sign() == Sign::Negative && !self.coefficient.is_zero()
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
            return d1.coefficient.cmp_magnitude(&d2.coefficient);
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
        // `abs_diff` computes the difference as a `u64` without the intermediate `i64`
        // subtraction, which can overflow at the extremes of the exponent range. The caller
        // guarantees `d1.exponent > d2.exponent`, so the result is the positive delta.
        let exponent_delta = d1.exponent.abs_diff(d2.exponent);
        // d1 has a larger exponent, so scale up its coefficient to match d2's exponent.
        // For example, when comparing these values of d1 and d2:
        //     d1 =  8 * 10^3
        //     d2 = 80 * 10^2
        // d1 has the larger exponent (3). We need to scale its coefficient up to d2's 10^2 scale.
        // We do this by multiplying it times 10^exponent_delta, which is 1 in this case.
        // This lets us compare 80 and 80, determining that the decimals are equal.
        //
        // The union scales the magnitude and compares magnitudes — the sign is handled by the
        // caller (`compare`/`ion_cmp`), so comparing a *value* here would double-reverse two
        // negatives. It decides the wide-difference cases from bit widths without materializing
        // `10^exponent_delta`, and the inline fast path never allocates.
        d1.coefficient
            .cmp_magnitude_scaled(exponent_delta, &d2.coefficient)
    }

    /// Returns the integer part of `self`. This means that non-integer numbers are always
    /// truncated towards zero, maintaining the sign of the original coefficient.
    pub fn trunc(&self) -> Decimal {
        if self.exponent >= 0 {
            self.clone()
        } else {
            // Divide the coefficient's magnitude by 10^|exponent|, discarding the fractional
            // digits. The quotient carries the coefficient's sign, so a value that truncates to
            // zero keeps a negative sign as `-0` without this method setting one.
            let power = self.exponent.unsigned_abs();
            let (quotient, _remainder) = self.coefficient.div_rem_pow10(power);
            Decimal::new(quotient, 0)
        }
    }

    /// Returns the fractional part of `self`. Values with no fractional component will return
    /// zero maintaining the sign of the original coefficient.
    pub fn fract(&self) -> Decimal {
        if self.exponent >= 0 {
            Decimal::new(
                Coefficient::from_sign_and_value(self.coefficient.sign(), 0),
                0,
            )
        } else {
            // The remainder of dividing the magnitude by 10^|exponent| is the fractional part.
            // It carries the coefficient's sign, so an integral value keeps a negative sign as
            // `-0` without this method setting one, and the exponent is preserved.
            let power = self.exponent.unsigned_abs();
            let (_quotient, remainder) = self.coefficient.div_rem_pow10(power);
            Decimal::new(remainder, self.exponent)
        }
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

impl IonDataOrd for Decimal {
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

impl IonDataHash for Decimal {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        state.write_i8(self.coefficient.sign() as i8);
        self.coefficient.magnitude().hash(state);
        state.write_i64(self.exponent);
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
            write!(f, "{}.", digits)
        } else if self.exponent >= 0 { // e.g. ABCd1
            write!(f, "{}d{}", digits, self.exponent)
        } else { // exponent < 0, there is a fractional component
            if dot_index > 0 { // e.g. A.BC or AB.C
                let dot_index = dot_index as usize;
                write!(f, "{}.{}", &digits[0..dot_index], &digits[dot_index..len])
            } else if dot_index > -(WIDE_NUMBER as i64) { // e.g. 0.ABC or 0.000ABC
                let width = dot_index.unsigned_abs() as usize + len;
                write!(f, "0.{digits:0>width$}")
            } else { // e.g. A.BCd-12
                write!(f, "{}.{}d{}", &digits[0..1], &digits[1..len], (dot_index - 1))
            }
        }
    }
}

#[cfg(feature = "bigdecimal")]
mod bigdecimal {
    use crate::result::IonFailure;
    use crate::{Decimal, IonError, IonResult};
    use bigdecimal::BigDecimal;
    use num_traits::ToPrimitive;

    impl TryInto<BigDecimal> for Decimal {
        type Error = IonError;

        /// Attempts to create a BigDecimal from a Decimal. Returns an Error if the Decimal being
        /// converted is a special value (negative zero) or has a magnitude no representable as u128.
        fn try_into(self) -> Result<BigDecimal, Self::Error> {
            if self.coefficient().is_negative_zero() {
                return IonResult::illegal_operation("Cannot convert negative zero to BigDecimal.");
            }
            let bigint = self
                .coefficient()
                .as_int()
                .expect("coefficient is not negative zero; checked above")
                .to_bigint();
            Ok(BigDecimal::new(bigint, self.scale()))
        }
    }

    impl TryFrom<BigDecimal> for Decimal {
        type Error = IonError;

        /// Attempts to create a Decimal from a BigDecimal. Returns an Error if the BigDecimal cannot be
        /// represented as a Decimal in this library.
        fn try_from(value: BigDecimal) -> Result<Self, Self::Error> {
            let (coeff, exponent) = value.into_bigint_and_exponent();
            let Some(data) = coeff.to_i128() else {
                return IonResult::illegal_operation("Cannot represent coefficient as i128.");
            };

            Ok(Decimal::new(data, -exponent))
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::Decimal;
        use bigdecimal::BigDecimal;
        use rstest::*;

        #[fixture]
        /// We use this function to represent when we don't expect to have a value to interact with.
        /// In a less safe language this would be a "null object" or "pebble object" but here we'll just
        /// document the expectation.
        fn no_such_decimal() -> Decimal {
            Decimal::NEGATIVE_ZERO
        }

        #[rstest]
        #[case("123e1", Decimal::new(123, 1))]
        #[case("123.", Decimal::new(123, 0))]
        #[case("-123.", Decimal::new(-123,  0))]
        #[case("12.3", Decimal::new( 123, -1))]
        #[case("0.123", Decimal::new( 123, -3))]
        #[case("-0.00123", Decimal::new(-123, -5))]
        #[case("0.00123", Decimal::new( 123, -5))]
        #[case("1.23e-8", Decimal::new( 123, -10))]
        #[case("-1.23e-8", Decimal::new(-123, -10))]
        #[case::out_of_double("9_007_199_254_740_993", Decimal::new(9_007_199_254_740_993i128, 0))]
        #[should_panic]
        #[case::coeff_too_large(
            "1427247692705959881058285969449495136382746624",
            no_such_decimal()
        )]
        /// Effectively tests TryFrom<BigDecimal> for Decimal. The only failure cases should be when
        /// the coefficient is larger i128
        fn try_from_bigdecimal_for_decimal(#[case] input: BigDecimal, #[case] expected: Decimal) {
            let actual = Decimal::try_from(input).unwrap();
            assert_eq!(actual, expected);
        }

        #[fixture]
        /// We use this function to represent when we don't expect to have a value to interact with.
        /// In a less safe language this would be a "null object" or "pebble object" but here we'll just
        /// document the expectation.
        fn no_such_bigdecimal() -> BigDecimal {
            0.into()
        }

        #[rstest]
        #[case(Decimal::new(123, 1), "123e1")]
        #[case(Decimal::new(123, 0), "123.")]
        #[case(Decimal::new(-123,  0),"-123.")]
        #[case(Decimal::new( 123, -1),  "12.3")]
        #[case(Decimal::new( 123, -3),   "0.123")]
        #[case(Decimal::new(-123, -5),  "-0.00123")]
        #[case(Decimal::new( 123, -5),   "0.00123")]
        #[case(Decimal::new( 123, -10),  "1.23e-8")]
        #[case(Decimal::new(-123, -10), "-1.23e-8")]
        #[should_panic]
        #[case::negative_zero(Decimal::NEGATIVE_ZERO, no_such_bigdecimal())]
        /// Effectively tests TryFrom<Decimal> for BigDecimal. The only failure cases should be when
        /// the coefficient is larger i128
        fn try_into_bigdecimal_for_decimal(#[case] input: Decimal, #[case] expected: BigDecimal) {
            let actual: BigDecimal = Decimal::try_into(input).unwrap();
            assert_eq!(actual, expected);
        }

        #[test]
        fn convert_large_coefficient_decimal_to_bigdecimal() {
            use crate::decimal::Coefficient;
            use crate::Int;
            // 2^128 + 1 is a valid Ion decimal coefficient that exceeds u128::MAX.
            let mut bytes = vec![1u8];
            bytes.extend(vec![0u8; 16]);
            bytes[16] = 1;
            let big_int = Int::from_le_signed_bytes(&bytes);
            let d = Decimal::new(Coefficient::new(big_int), 0i64);
            let result: Result<BigDecimal, _> = d.try_into();
            assert!(result.is_ok());
        }
    }
}

#[cfg(test)]
mod decimal_tests {
    use crate::decimal::{Coefficient, Sign};
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

    #[rstest]
    #[case(Decimal::new(1, 0), Decimal::new(1, 0))]
    #[case(Decimal::new(15, -1), Decimal::new(1, 0))]
    #[case(Decimal::new(105, -1), Decimal::new(10, 0))]
    #[case(Decimal::new(-5, -1), Decimal::new(0, 0))]
    #[case(Decimal::new(-5, -1), Decimal::NEGATIVE_ZERO)]
    #[case(Decimal::NEGATIVE_ZERO, Decimal::NEGATIVE_ZERO)]
    #[case(Decimal::new(0, -5), Decimal::new(0, 0))]
    #[case(Decimal::new(Coefficient::from_sign_and_value(Sign::Negative, 0), -5), Decimal::new(0, 0))]
    fn decimal_trunc(#[case] value: Decimal, #[case] expected: Decimal) {
        assert_eq!(value.trunc(), expected);
    }

    #[rstest]
    #[case(Decimal::new(1, 0), Decimal::new(0, 0))]
    #[case(Decimal::new(15, -1), Decimal::new(5, -1))]
    #[case(Decimal::new(105, -1), Decimal::new(5, -1))]
    fn decimal_fract(#[case] value: Decimal, #[case] expected: Decimal) {
        assert_eq!(value.fract(), expected);
    }

    #[test]
    fn decimal_cmp_arbitrary_precision() {
        use crate::ion_data::IonDataHash;
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;

        // A value that exceeds i128: 2^128 + 42
        let mut bytes = vec![0u8; 18];
        bytes[0] = 42;
        bytes[16] = 1;
        let big_value = Int::from_le_signed_bytes(&bytes);

        let mut bytes2 = vec![0u8; 18];
        bytes2[16] = 2;
        let bigger_value = Int::from_le_signed_bytes(&bytes2);

        let d1 = Decimal::new(Coefficient::new(big_value.clone()), 0i64);
        let d2 = Decimal::new(Coefficient::new(big_value), 0i64);
        let small = Decimal::new(1i64, 0i64);
        let zero = Decimal::new(0i64, 0i64);

        // Equality
        assert_eq!(d1, d2);

        // Ordering: big > small
        assert_eq!(d1.cmp(&small), Ordering::Greater);
        assert_eq!(small.cmp(&d1), Ordering::Less);

        // Ordering: big > zero
        assert_eq!(d1.cmp(&zero), Ordering::Greater);

        // is_zero
        assert!(!d1.is_zero());
        assert!(zero.is_zero());

        // Hash consistency
        let hash = |d: &Decimal| {
            let mut h = DefaultHasher::new();
            d.ion_data_hash(&mut h);
            h.finish()
        };
        assert_eq!(hash(&d1), hash(&d2));

        // Different big magnitudes
        let d3 = Decimal::new(Coefficient::new(bigger_value), 0i64);
        assert_eq!(d1.cmp(&d3), Ordering::Less);
        assert_eq!(d3.cmp(&d1), Ordering::Greater);
    }

    #[test]
    fn compare_decimals_with_large_exponent_difference() {
        // 1e40 and 1e0 are both valid Ion decimals. Comparing them requires scaling
        // one coefficient by 10^40, which exceeds i128::MAX.
        let d1 = Decimal::new(1i64, 40i64);
        let d2 = Decimal::new(1i64, 0i64);
        assert_eq!(d1.cmp(&d2), Ordering::Greater);
    }

    #[test]
    fn trunc_decimal_with_large_negative_exponent() {
        // 1e-40 is a valid Ion decimal. trunc() should return 0.
        let d = Decimal::new(1i64, -40i64);
        assert_eq!(d.trunc(), Decimal::new(0i64, 0i64));
    }

    #[test]
    fn fract_decimal_with_large_negative_exponent() {
        // 1e-39 is a valid Ion decimal. fract() should return the value itself
        // since the integer part is zero.
        let d = Decimal::new(1i64, -39i64);
        assert_eq!(d.fract(), Decimal::new(1i64, -39i64));
    }
}
