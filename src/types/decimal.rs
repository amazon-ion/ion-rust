use std::cmp::Ordering;

use bigdecimal::{BigDecimal, Signed};
use num_bigint::{BigInt, BigUint, ToBigUint};

use crate::result::IonError;
use crate::types::coefficient::{Coefficient, Sign};
use crate::types::magnitude::Magnitude;
use std::convert::{TryFrom, TryInto};

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
            return d1.coefficient.magnitude().cmp(&d2.coefficient.magnitude());
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
        Magnitude::BigUInt(scaled_coefficient).cmp(&d2.coefficient.magnitude())
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
        Some(self.cmp(&other))
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
    use num_traits::ToPrimitive;
    use std::cmp::Ordering;
    use std::convert::TryInto;

    use rstest::*;

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
}
