use std::cmp::Ordering;

use bigdecimal::{BigDecimal, Signed};
use num_bigint::{BigInt, BigUint, ToBigUint};

use crate::result::{illegal_operation, IonError};
use crate::types::coefficient::{Coefficient, Sign};
use crate::types::magnitude::Magnitude;
use std::convert::{TryFrom, TryInto};
use std::fmt::{Display, Formatter};

/// An arbitrary-precision Decimal type with a distinct representation of negative zero (`-0`).
#[derive(Clone, Debug)]
pub struct Decimal {
    // A Coefficient is a Sign/Magnitude pair supporting integers of arbitrary size
    pub(crate) coefficient: Coefficient,
    pub(crate) exponent: i64,
}

impl Decimal {
    /// Constructs a new Decimal with the provided components. The value of the decimal is
    ///    (coefficient * 10^exponent) * (if sign == Sign::Negative { -1 } else { 1 })
    pub fn new<I: Into<Coefficient>>(coefficient: I, exponent: i64) -> Decimal {
        let coefficient = coefficient.into();
        Decimal {
            coefficient,
            exponent,
        }
    }

    /// Returns scale of the Decimal value
    /// A scale indicates the number of digits to the right of the decimal point.
    pub fn scale(&self) -> i64 {
        if self.exponent > 0 {
            return 0;
        }
        self.exponent.abs()
    }

    /// Returns the number of digits in the non-scaled integer representation of the decimal.
    pub fn digits(&self) -> u64 {
        if self.exponent > 0 {
            return self.coefficient.digits() + self.exponent as u64;
        }
        self.coefficient.digits()
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

    // Determines whether the first decimal value is greater than, equal to, or less than
    // the second decimal value.
    // TODO: This currently uses the rules for Ion equivalence to determine if two values are equal.
    //       This leads to potentially surprising behavior around zeros; in particular, -0 and 0
    //       are not equal, and zeros with different exponents are not equal. We need to offer a
    //       separate method for testing Ion equivalence.
    //       See: https://github.com/amzn/ion-rust/issues/220
    fn compare(d1: &Decimal, d2: &Decimal) -> Ordering {
        // Even if the exponents are wildly different, disagreement in the coefficient's signs
        // still tells us which value is bigger. (This approach causes `-0` to be considered less
        // than `0`; see the to-do comment on this method.)
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
            return d1.coefficient.magnitude().cmp(d2.coefficient.magnitude());
        }

        // If the exponents don't match, we need to scale one of the magnitudes to match the other
        // for comparison. For example, when comparing 16e3 and 1600e1, we can't compare the
        // magnitudes (16 and 1600) directly. Instead, we need to multiply 16 by 10^2 to compensate
        // for the difference in their exponents (3-1). Then we'll be comparing 1600 to 1600,
        // and can safely conclude that they are equal.

        // But first, a detour: Decimal zeros are a special case because we can't scale them via
        // multiplication.
        if *d1.coefficient.magnitude() == Magnitude::U64(0)
            && *d2.coefficient.magnitude() == Magnitude::U64(0)
        {
            // Ion only considers zeros with the same sign to be equal if their exponents are
            // equal. We already know the exponents are different, but we still need to decide
            // between Ordering::Greater and Ordering::Less. We can order the zeros by comparing
            // their exponents.
            return d1.exponent.cmp(&d2.exponent);
        }

        // Scale and compare the coefficients
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
        let mut scaled_coefficient: BigUint = d1.coefficient.magnitude().to_biguint().unwrap();
        scaled_coefficient *= 10u64.pow(exponent_delta as u32);
        Magnitude::BigUInt(scaled_coefficient).cmp(d2.coefficient.magnitude())
    }
}

impl PartialEq for Decimal {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Decimal {}

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
                let sign = if value < 0 {Sign::Negative} else {Sign::Positive};
                // Discard the sign and convert the value to a u64.
                let magnitude: u64 = value.checked_abs()
                        .and_then(|v| Some(v.abs() as u64))
                        // If .abs() fails, it's because <$t>::MIN.abs() cannot be represented
                        // as a $t. We can handle this case by simply using <$>::MAX + 1
                        .unwrap_or_else(|| (<$t>::MAX as u64) + 1);
                let coefficient = Coefficient::new(sign, magnitude);
                Decimal::new(coefficient, 0)
            }
        }
    )*)
}
impl_decimal_from_signed_primitive_integer!(i8, i16, i32, i64, isize);

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
        if value.is_infinite() {
            if value.is_sign_negative() {
                return illegal_operation("Cannot convert f64 negative infinity to Decimal.");
            } else {
                return illegal_operation("Cannot convert f64 infinity to Decimal.");
            }
        } else if value.is_nan() {
            return illegal_operation("Cannot convert f64 NaN (not-a-number) to Decimal.");
        }

        // You can't use the `log10` operation on a zero value, so check for these cases explicitly.
        if value == 0f64 {
            //    ^- Positive and negative zero are mathematically equivalent,
            //       so we can use `==` here to check for both.
            if value.is_sign_negative() {
                return Ok(Decimal::negative_zero());
            }
            return Ok(Decimal::new(0, 0));
        }

        // If the f64 is an integer value, we can convert it to a decimal trivially.
        // The `fract()` method returns the fractional part of the value. If fract() returns zero,
        // then `value` is an integer.
        if value.fract() == 0f64 {
            // The `trunc()` method returns the integer part of the value.
            // We can use i64's Into implementation to convert it to a Decimal.
            // This will produce a Decimal with an exponent of zero.
            return Ok((value.trunc() as i64).into());
        }

        // If the f64 is not a round number, attempt to preserve as many decimal places of precision
        // as possible.

        // f64::DIGITS is the number of base 10 digits of fractional precision in an f64: 15
        const PRECISION: u32 = f64::DIGITS;
        let coefficient = value * 10f64.powi(PRECISION as i32);
        let exponent = -(PRECISION as i64);

        Ok(Decimal::new(coefficient as i64, exponent))
    }
}

impl Display for Decimal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // TODO: This is correct, but not the most human-friendly format.
        write!(f, "{}d{}", self.coefficient, self.exponent)
    }
}

/// Make a Decimal from a BigDecimal. This is a lossless operation.
impl From<BigDecimal> for Decimal {
    fn from(value: BigDecimal) -> Self {
        let sign = if value.sign() == num_bigint::Sign::Minus {
            Sign::Negative
        } else {
            Sign::Positive
        };
        let (big_int_coefficient, negative_exponent) = value.as_bigint_and_exponent();
        // Discard the BigInt coefficient's sign before converting it to a BigUint to ensure
        // the conversion succeeds.
        let magnitude: BigUint = big_int_coefficient.abs().to_biguint().unwrap();
        // From the BigInt docs: "Note that a positive exponent indicates a negative power of 10."
        let exponent = -negative_exponent;

        Decimal::new(Coefficient::new(sign, magnitude), exponent)
    }
}

impl TryFrom<Decimal> for BigDecimal {
    type Error = IonError;
    /// Attempts to create a BigDecimal from a Decimal. Returns an Error if the Decimal being
    /// converted is a negative zero, which BigDecimal cannot represent. Returns Ok otherwise.
    fn try_from(value: Decimal) -> Result<Self, Self::Error> {
        // The Coefficient type cannot be converted to a BigInt if it is a negative zero.
        let coefficient_big_int: BigInt = value.coefficient.try_into()?;
        Ok(BigDecimal::new(coefficient_big_int, -value.exponent))
    }
}

#[cfg(test)]
mod decimal_tests {
    use crate::result::IonResult;
    use crate::types::coefficient::{Coefficient, Sign};
    use crate::types::decimal::Decimal;
    use bigdecimal::BigDecimal;
    use num_bigint::BigUint;
    use num_traits::{Float, ToPrimitive};
    use std::cmp::Ordering;
    use std::convert::TryInto;
    use std::fmt::Write;

    use rstest::*;

    #[rstest]
    #[case(Decimal::new(1, 0), "1d0")]
    #[case(Decimal::new(123, -2), "123d-2")]
    #[case(Decimal::new(123, 2), "123d2")]
    #[case(Decimal::negative_zero_with_exponent(0), "-0d0")]
    #[case(Decimal::negative_zero_with_exponent(-4), "-0d-4")]
    #[case(Decimal::negative_zero_with_exponent(4), "-0d4")]
    fn test_display(#[case] decimal: Decimal, #[case] expected: &str) {
        let mut buffer = String::new();
        write!(buffer, "{}", decimal).unwrap();
        assert_eq!(buffer.as_str(), expected);
    }

    #[test]
    fn test_decimal_eq_negative_zeros() {
        assert_eq!(Decimal::negative_zero(), Decimal::negative_zero());
        assert_ne!(
            Decimal::negative_zero_with_exponent(2),
            Decimal::negative_zero_with_exponent(7)
        );
        assert_ne!(
            Decimal::new(0, 0),
            Decimal::new(Coefficient::new(Sign::Negative, 0), 0)
        );
    }

    #[rstest]
    // Each tuple is a coefficient/exponent pair that will be used to construct a Decimal.
    // The boolean indicates whether the two Decimals are expected to be equal.
    #[case((80, 2), (80, 2), true)]
    #[case((124, -2), (1240, -3), true)]
    #[case((0, 0), (0, 0), true)]
    #[case((0, -2), (0, 3), false)]
    #[case((0, 2), (0, 5), false)]
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
    // Each tuple is a coefficient/exponent pair that will be used to construct a Decimal
    #[case((80, 3), Ordering::Equal, (80, 3))]
    #[case((80, 3), Ordering::Greater, (-80, 3))]
    #[case((80, 3), Ordering::Greater, (8, 3))]
    #[case((80, 4), Ordering::Greater, (8, 3))]
    #[case((-80, 4), Ordering::Equal, (-80, 4))]
    #[case((-80, 4), Ordering::Less, (-8, 3))]
    #[case((-80, 4), Ordering::Equal, (-8, 5))]
    #[case((-1000, -1), Ordering::Less, (-99_999_999_999i64, -9))]
    #[case((1000, -1), Ordering::Greater, (99_999_999_999i64, -9))]
    fn test_decimal_ord<I: Into<Coefficient>>(
        #[case] components1: (I, i64),
        #[case] ordering: Ordering,
        #[case] components2: (I, i64),
    ) {
        let decimal1 = Decimal::new(components1.0.into(), components1.1);
        let decimal2 = Decimal::new(components2.0.into(), components2.1);
        assert_eq!(decimal1.cmp(&decimal2), ordering);
        // Make sure the inverse relationship holds
        assert_eq!(decimal2.cmp(&decimal1), ordering.reverse());
    }

    #[rstest]
    #[case(0f64, Decimal::new(0, 0))]
    #[case(f64::neg_zero(), Decimal::negative_zero())]
    #[case(1f64, Decimal::new(1, 0))]
    #[case(-1f64, Decimal::new(-1, 0))]
    #[case(10f64, Decimal::new(1, 1))]
    #[case(100f64, Decimal::new(1, 2))]
    #[case(1.5f64, Decimal::new(15, -1))]
    #[case(-1.5f64, Decimal::new(-15, -1))]
    #[case(3.141592659f64, Decimal::new(3141592659i64, -9))]
    #[case(-3.141592659f64, Decimal::new(-3141592659i64, -9))]
    fn test_decimal_try_from_f64_ok(#[case] value: f64, #[case] expected: Decimal) {
        let actual: Decimal = value.try_into().unwrap();
        assert_eq!(actual, expected);
    }

    #[rstest]
    #[case::positive_infinity(f64::infinity())]
    #[case::negative_infinity(f64::neg_infinity())]
    #[case::nan(f64::nan())]
    fn test_decimal_try_from_f64_err(#[case] value: f64) {
        let conversion_result: IonResult<Decimal> = value.try_into();
        assert!(conversion_result.is_err());
    }

    #[test]
    fn test_convert_to_big_decimal() {
        let decimal = Decimal::new(-24601, -3);
        let big_decimal: BigDecimal = decimal.try_into().unwrap();
        let double = big_decimal.to_f64().unwrap();
        assert_eq!(-24.601, double);

        // Any form of negative zero will fail to be converted.

        let decimal = Decimal::negative_zero();
        let conversion_result: IonResult<BigDecimal> = decimal.try_into();
        assert!(conversion_result.is_err());

        let decimal = Decimal::negative_zero_with_exponent(6);
        let conversion_result: IonResult<BigDecimal> = decimal.try_into();
        assert!(conversion_result.is_err());

        let decimal = Decimal::negative_zero_with_exponent(-6);
        let conversion_result: IonResult<BigDecimal> = decimal.try_into();
        assert!(conversion_result.is_err());
    }

    #[test]
    fn test_convert_from_big_decimal() {
        let big_decimal: BigDecimal = BigDecimal::new((-24601).into(), 3);
        let actual: Decimal = big_decimal.into();
        let expected = Decimal::new(-24601, -3);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_scale() {
        let decimal_value = Decimal::new(-24601, -3);
        assert_eq!(decimal_value.scale(), 3)
    }

    #[rstest]
    #[case(Decimal::new(-24601, -3), 5)]
    #[case(Decimal::new(u64::MAX, -3), 20)]
    #[case(Decimal::new(BigUint::from(u64::MAX), 3), 23)]
    #[case(Decimal::new(BigUint::from(u128::MAX), -2), 39)]
    fn test_digits(#[case] value: Decimal, #[case] expected: u64) {
        assert_eq!(value.digits(), expected);
    }
}
