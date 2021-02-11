use num_bigint::{BigInt, BigUint, ToBigUint};
use bigdecimal::{ToPrimitive, BigDecimal, Signed};
use std::ops::Neg;
use std::cmp::Ordering;

/// An integer value acting as the coefficient of a [Decimal]. When possible, users should prefer
/// to represent the integer as a [u64] for efficiency. If the integer is too large to fit in a u64,
/// users may instead opt to represent it as a [BigUint] at the cost of allocations and runtime
/// complexity.
#[derive(Clone, Debug)]
pub enum Coefficient {
    U64(u64),
    BigUInt(BigUint)
}

// TODO: We currently model Decimal as a (Sign, Coefficient, Exponent) tuple. Modeling the
//       Coefficient as being separate from the Sign value means that we can't convert signed
//       integer types (i32, i64, etc) into a Coefficient via traits. Coefficient should be
//       a combination of a sign and magnitude, not just the magnitude.

impl Coefficient {
    /// Compares a [u64] integer with a [BigUint] to see if they are equal. This method never
    /// allocates. It will always prefer to downgrade a BigUint and compare the two integers as
    /// u64 values. If this is not possible, then the two numbers cannot possibly be equal anyway.
    fn cross_representation_eq(c1: u64, c2: &BigUint) -> bool {
        // Try to downgrade the BigUint first since that's cheaper than upgrading the u64.
        if let Some(downgraded_c2) = c2.to_u64() {
            // If the conversion succeeds, compare the resulting values.
            return c1 == downgraded_c2;
        }
        // Otherwise, the two values couldn't possibly be equal.
        false
    }
}

impl PartialEq for Coefficient {
    fn eq(&self, other: &Self) -> bool {
        use Coefficient::*;
        match (self, other) {
            (U64(c1), U64(c2)) => c1 == c2,
            (BigUInt(c1), BigUInt(c2)) => c1 == c2,
            (U64(c1), BigUInt(c2)) => Coefficient::cross_representation_eq(*c1, &c2),
            (BigUInt(c1), U64(c2)) => Coefficient::cross_representation_eq(*c2, &c1)
        }
    }
}

impl Eq for Coefficient {}

impl PartialOrd for Coefficient {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Coefficient {
    fn cmp(&self, other: &Self) -> Ordering {
        use Coefficient::*;
        match (self, other) {
            (U64(c1), U64(c2)) => c1.cmp(c2),
            (BigUInt(c1), BigUInt(c2)) => c1.cmp(c2),
            // TODO: These methods should attempt to downgrade the BigUint first to see if
            //       allocations can be avoided.
            (U64(c1), BigUInt(c2)) => BigUint::from(*c1).cmp(c2),
            (BigUInt(c1), U64(c2)) => c1.cmp(&BigUint::from(*c2)),
        }
    }
}

// This macro makes it possible to turn unsigned int primitives into a Coefficient using `.into()`.
macro_rules! impl_coefficient_from_small_unsigned_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Coefficient {
            fn from(value: $t) -> Coefficient {
                Coefficient::U64(value as u64)
            }
        }
    )*)
}
//TODO: Remove i32, i64. Currently used for testing.
impl_coefficient_from_small_unsigned_int_types!(u8, u16, u32, u64, usize, i32, i64,);

impl From<BigUint> for Coefficient {
    fn from(value: BigUint) -> Self {
        Coefficient::BigUInt(value)
    }
}

impl ToBigUint for Coefficient {
    fn to_biguint(&self) -> Option<BigUint> {
        use Coefficient::*;
        match self {
            U64(c) => Some(BigUint::from(*c)),
            BigUInt(c) => Some(c.clone())
        }
    }
}

/// Indicates whether the Decimal value is less than 0 (negative) or not (positive).
/// When the Decimal's magnitude is zero, the Sign can be used to distinguish between -0 and 0.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Sign {
    Negative,
    Positive,
}

/// An arbitrary-precision Decimal type with a distinct representation of negative zero (`-0`).
#[derive(Clone, Debug)]
pub struct Decimal {
    sign: Sign,
    coefficient: Coefficient,
    exponent: i64,
}

impl Decimal {
    /// Constructs a new Decimal with the provided components. The value of the decimal is
    ///    (coefficient * 10^exponent) * (if sign == Sign::Negative { -1 } else { 1 })
    pub fn new<I: Into<Coefficient>>(sign: Sign, coefficient: I, exponent: i64) -> Decimal {
        let coefficient = coefficient.into();
        Decimal {
            sign,
            coefficient,
            exponent
        }
    }

    fn compare_magnitudes(d1: &Decimal, d2: &Decimal) -> Ordering {
        if d1.exponent == d2.exponent {
            return d1.coefficient.cmp(&d2.coefficient);
        } else if d1.coefficient == Coefficient::from(0)
               && d2.coefficient == Coefficient::from(0) {
            // Zeros are only equal if their exponents are equal.
            return d1.exponent.cmp(&d2.exponent);
        } else if d1.exponent < d2.exponent {
            Self::compare_magnitudes_helper(d1, d2)
        } else {
            Self::compare_magnitudes_helper(d2, d1)
        }
    }

    // d2 must have a greater exponent than d1
    fn compare_magnitudes_helper(d1: &Decimal, d2: &Decimal) -> Ordering {
        let exponent_delta = (d1.exponent - d2.exponent).abs();
        let mut adjusted_coefficient = d2.coefficient.to_biguint().unwrap();
        adjusted_coefficient *= 10u64.pow(exponent_delta as u32);
        let cmp = Coefficient::from(adjusted_coefficient).cmp(&d1.coefficient);
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
        let sign_cmp = self.sign.cmp(&other.sign);
        if sign_cmp != Ordering::Equal {
            return sign_cmp;
        }

        Decimal::compare_magnitudes(self, other)
    }
}

macro_rules! impl_decimal_from_signed_primitive_integer {
    ($($t:ty),*) => ($(
        impl From<$t> for Decimal {
            fn from(value: $t) -> Self {
                let sign = if value < 0 {Sign::Negative} else {Sign::Positive};
                Decimal::new(sign, value as u64, 0)
            }
        }
    )*)
}
impl_decimal_from_signed_primitive_integer!(i8, i16, i32, i64, isize);

macro_rules! impl_decimal_from_unsigned_primitive_integer {
    ($($t:ty),*) => ($(
        impl From<$t> for Decimal {
            fn from(value: $t) -> Self {
                Decimal::new(Sign::Positive, value as u64, 0)
            }
        }
    )*)
}
impl_decimal_from_unsigned_primitive_integer!(u8, u16, u32, u64, usize);

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
        let coefficient: BigUint = big_int_coefficient.abs().to_biguint().unwrap();
        // From the BigInt docs: "Note that a positive exponent indicates a negative power of 10."
        let exponent = -negative_exponent;

        Decimal::new(sign, coefficient, exponent)
    }
}

/// Make a BigDecimal from a Decimal. BigDecimal doesn't have a distinct -0, so this is technically
/// a lossy operation.
impl From<Decimal> for BigDecimal {
    fn from(value: Decimal) -> Self {
        let mut coefficient: BigInt = match value.coefficient {
            Coefficient::U64(c) => c.into(),
            Coefficient::BigUInt(c) => c.into(),
        };
        if value.sign == Sign::Negative {
            coefficient = coefficient.neg();
        }
        // BigDecimal uses 'scale' rather than 'exponent' in its API, which is a count of the
        // number of decimal places. It's effectively `exponent * -1`.
        let exponent = -value.exponent;
        BigDecimal::new(coefficient, exponent)
    }
}

#[cfg(test)]
mod coefficient_tests {
    use bigdecimal::{BigDecimal, ToPrimitive};
    use crate::types::decimal::{Coefficient, Decimal, Sign};
    use num_bigint::BigUint;

    fn eq_test<I1, I2>(c1: I1, c2: I2) where I1: Into<Coefficient>, I2: Into<Coefficient> {
        let c1 = c1.into();
        let c2 = c2.into();
        assert_eq!(c1, c2);
    }

    #[test]
    fn test_coefficient_eq() {
        eq_test(0u64, 0u64);
        eq_test(0u64, BigUint::from(0u64));
        eq_test(BigUint::from(0u64), 0u64);
        eq_test(BigUint::from(0u64), BigUint::from(0u64));

        eq_test(u64::MAX, u64::MAX);
        eq_test(u64::MAX, BigUint::from(u64::MAX));
        eq_test(BigUint::from(u64::MAX), u64::MAX);
        eq_test(BigUint::from(u64::MAX), BigUint::from(u64::MAX));

        eq_test(BigUint::from(u128::MAX), BigUint::from(u128::MAX));
    }

    #[test]
    fn test_convert_to_big_decimal() {
        let decimal = Decimal::new(Sign::Negative, 24601, -3);
        let big_decimal: BigDecimal = decimal.into();
        let double = big_decimal.to_f64().unwrap();
        assert_eq!(-24.601, double);
    }

    #[test]
    fn test_convert_from_big_decimal() {
        let big_decimal: BigDecimal = BigDecimal::new((-24601).into(), 3);
        let actual: Decimal = big_decimal.into();
        let expected = Decimal::new(Sign::Negative, 24601, -3);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_negative_zero_eq() {
        let neg_zero = Decimal::new(Sign::Negative, 0, 0);
        let pos_zero = Decimal::new(Sign::Positive, 0, 0);
        assert_eq!(neg_zero.clone(), neg_zero.clone());
        assert_ne!(neg_zero.clone(), pos_zero.clone());
        assert_eq!(pos_zero.clone(), pos_zero.clone());
    }
}

#[cfg(test)]
mod decimal_tests {
    use crate::types::decimal::{Decimal, Sign};

    #[test]
    fn test_decimal_eq() {
        assert_eq!(
            Decimal::new(Sign::Positive, 80, 2),
            Decimal::new(Sign::Positive, 8, 3)
        );
        assert_eq!(
            Decimal::new(Sign::Positive, 124, -2),
            Decimal::new(Sign::Positive, 1240, -3)
        );
        assert_eq!(
            Decimal::new(Sign::Positive, 0, 0),
            Decimal::new(Sign::Positive, 0, 0)
        );
        assert_eq!(
            Decimal::new(Sign::Negative, 0, 0),
            Decimal::new(Sign::Negative, 0, 0)
        );
        assert_ne!(
            Decimal::new(Sign::Positive, 0, 2),
            Decimal::new(Sign::Positive, 0, 5)
        );
        assert_ne!(
            Decimal::new(Sign::Positive, 0, 0),
            Decimal::new(Sign::Negative, 0, 0)
        );
    }

    #[test]
    fn test_decimal_ord() {
        assert!(
            Decimal::new(Sign::Positive, 80, 3) >
            Decimal::new(Sign::Negative, 80, 3)
        );
        assert!(
            Decimal::new(Sign::Positive, 80, 3) >
            Decimal::new(Sign::Positive, 8, 3)
        );
        assert!(
            Decimal::new(Sign::Positive, 80, 4) >
            Decimal::new(Sign::Positive, 80, 3)
        );
        assert!(
            Decimal::new(Sign::Positive, 1240, -3) >
            Decimal::new(Sign::Positive, 124, -3)
        )
    }
}