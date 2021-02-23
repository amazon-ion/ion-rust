use std::cmp::Ordering;

use bigdecimal::{BigDecimal, Signed};
use num_bigint::{BigInt, BigUint, ToBigUint};

use crate::types::coefficient::{Coefficient, Sign};
use crate::types::magnitude::Magnitude;
use std::convert::{TryFrom, TryInto};

/// An arbitrary-precision Decimal type with a distinct representation of negative zero (`-0`).
#[derive(Clone, Debug)]
pub struct Decimal {
    // A Coefficient is a Sign/Magnitude pair supporting integers of arbitrary size
    coefficient: Coefficient,
    exponent: i64,
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

    // Used in the implementation of Ord, which compares the sign of each decimal before
    // comparing the combined value of their exponents/magnitudes.
    fn compare(d1: &Decimal, d2: &Decimal) -> Ordering {
        // Even if the exponents are wildly different, disagreement in the coefficient's signs
        // still tells which value is bigger. This approach causes `-0` to be considered less than
        // `0`, which may seem a bit quirky. However, according to the Ion data model, `-0` is not
        // equal to `0`, so saying that it's less than zero is a reasonable conclusion.
        let sign_cmp = d1.coefficient.sign().cmp(&d2.coefficient.sign());
        if sign_cmp != Ordering::Equal {
            return sign_cmp;
        }

        // If the exponents match, we can compare the two coefficients directly.
        if d1.exponent == d2.exponent {
            // We've already confirmed that the coefficients' signs match, so we can skip to
            // comparing their magnitudes.
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

        // Scale up the magnitude associated with a lesser exponent and compare it with the
        // other magnitude.
        if d1.exponent < d2.exponent {
            Self::compare_scaled_magnitudes(d1, d2)
        } else {
            Self::compare_scaled_magnitudes(d2, d1)
        }
    }

    // d1 must have a smaller exponent than d2
    fn compare_scaled_magnitudes(d1: &Decimal, d2: &Decimal) -> Ordering {
        let exponent_delta = d2.exponent - d1.exponent;
        let mut adjusted_magnitude: BigUint = d2.coefficient.magnitude().to_biguint().unwrap();
        adjusted_magnitude *= 10u64.pow(exponent_delta as u32);
        let cmp = Magnitude::BigUInt(adjusted_magnitude).cmp(&d1.coefficient.magnitude());
        cmp
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
    //TODO: There's only one possible cause of failure for this method, but it would still be nice
    //      to return an error type that's more descriptive than `()`.
    type Error = ();
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
    use crate::types::coefficient::{Coefficient, Sign};
    use crate::types::decimal::Decimal;
    use bigdecimal::BigDecimal;
    use num_traits::ToPrimitive;
    use std::convert::TryInto;

    #[test]
    fn test_decimal_eq() {
        assert_eq!(Decimal::new(80, 2), Decimal::new(8, 3));
        assert_eq!(Decimal::new(124, -2), Decimal::new(1240, -3));
        assert_eq!(Decimal::new(0, 0), Decimal::new(0, 0));
        assert_ne!(Decimal::new(0, -2), Decimal::new(0, 3));
        assert_eq!(Decimal::negative_zero(), Decimal::negative_zero());
        assert_ne!(
            Decimal::negative_zero_with_exponent(2),
            Decimal::negative_zero_with_exponent(7)
        );
        assert_ne!(Decimal::new(0, 2), Decimal::new(0, 5));
        assert_ne!(
            Decimal::new(0, 0),
            Decimal::new(Coefficient::new(Sign::Negative, 0), 0)
        );
    }

    #[test]
    fn test_decimal_ord() {
        assert!(Decimal::new(80, 3) > Decimal::new(-80, 3));
        assert!(Decimal::new(80, 3) > Decimal::new(8, 3));
        assert!(Decimal::new(80, 4) > Decimal::new(80, 3));
        assert!(Decimal::new(1240, -3) > Decimal::new(124, -3))
    }

    #[test]
    fn test_convert_to_big_decimal() {
        let decimal = Decimal::new(-24601, -3);
        let big_decimal: BigDecimal = decimal.try_into().unwrap();
        let double = big_decimal.to_f64().unwrap();
        assert_eq!(-24.601, double);

        // Any form of negative zero will fail to be converted.

        let decimal = Decimal::negative_zero();
        let conversion_result: Result<BigDecimal, ()> = decimal.try_into();
        assert!(conversion_result.is_err());

        let decimal = Decimal::negative_zero_with_exponent(6);
        let conversion_result: Result<BigDecimal, ()> = decimal.try_into();
        assert!(conversion_result.is_err());

        let decimal = Decimal::negative_zero_with_exponent(-6);
        let conversion_result: Result<BigDecimal, ()> = decimal.try_into();
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
