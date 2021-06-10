use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use crate::result::{illegal_operation, IonError};
use crate::types::magnitude::Magnitude;
use std::convert::TryFrom;
use std::ops::{MulAssign, Neg};

/// Indicates whether the Coefficient's magnitude is less than 0 (negative) or not (positive).
/// When the magnitude is zero, the Sign can be used to distinguish between -0 and 0.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Sign {
    Negative,
    Positive,
}

/// A signed integer that can be used as the coefficient of a Decimal value. This type does not
/// consider `0` and `-0` to be equal and supports magnitudes of arbitrary size.
// These trait derivations rely closely on the manual implementations of PartialEq and Ord on
// [Magnitude].
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct Coefficient {
    sign: Sign,
    magnitude: Magnitude,
}

impl Coefficient {
    pub(crate) fn new<I: Into<Magnitude>>(sign: Sign, magnitude: I) -> Self {
        let magnitude = magnitude.into();
        Coefficient { sign, magnitude }
    }

    pub(crate) fn sign(&self) -> Sign {
        self.sign
    }

    pub(crate) fn magnitude(&self) -> &Magnitude {
        &self.magnitude
    }

    pub(crate) fn negative_zero() -> Self {
        Coefficient {
            sign: Sign::Negative,
            magnitude: Magnitude::U64(0),
        }
    }

    pub(crate) fn is_negative_zero(&self) -> bool {
        match (self.sign, &self.magnitude) {
            (Sign::Negative, Magnitude::U64(0)) => true,
            (Sign::Negative, Magnitude::BigUInt(b)) if b.is_zero() => true,
            _ => false,
        }
    }

    /// If the value can fit in an i64, return it as such. This is useful for
    /// inline representations.
    pub(crate) fn as_i64(&self) -> Option<i64> {
        match self.magnitude {
            Magnitude::U64(unsigned) => match i64::try_from(unsigned) {
                Ok(signed) => match self.sign {
                    Sign::Negative => Some(signed.neg()), // cannot overflow (never `MIN`)
                    Sign::Positive => Some(signed),
                },
                Err(_) => None,
            },
            Magnitude::BigUInt(_) => None,
        }
    }
}

// This macro makes it possible to turn unsigned integers into a Coefficient using `.into()`.
macro_rules! impl_coefficient_from_unsigned_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Coefficient {
            fn from(value: $t) -> Coefficient {
                Coefficient::new(Sign::Positive, value)
            }
        }
    )*)
}
impl_coefficient_from_unsigned_int_types!(u8, u16, u32, u64, u128, usize, BigUint);

// This macro makes it possible to turn signed integers into a Coefficient using `.into()`.
macro_rules! impl_coefficient_from_signed_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Coefficient {
            fn from(value: $t) -> Coefficient {
                let sign = if value < <$t>::zero() { Sign::Negative } else { Sign::Positive };
                Coefficient::new(sign, value)
            }
        }
    )*)
}
impl_coefficient_from_signed_int_types!(i8, i16, i32, i64, i128, isize);

// `BigInt` can't represent -0, so this is technically a lossy operation.
impl TryFrom<Coefficient> for BigInt {
    type Error = IonError;

    /// Attempts to create a BigInt from a Coefficient. Returns an Error if the Coefficient being
    /// converted is a negative zero, which BigInt cannot represent. Returns Ok otherwise.
    fn try_from(value: Coefficient) -> Result<Self, Self::Error> {
        if value.is_negative_zero() {
            illegal_operation("Cannot convert negative zero Decimal to BigDecimal")?;
        }
        let mut big_int: BigInt = match value.magnitude {
            Magnitude::U64(m) => m.into(),
            Magnitude::BigUInt(m) => m.into(),
        };
        if value.sign == Sign::Negative {
            big_int.mul_assign(-1);
        }
        Ok(big_int)
    }
}

#[cfg(test)]
mod coefficient_tests {
    use num_bigint::BigUint;

    use crate::types::coefficient::Coefficient;
    use crate::types::decimal::Decimal;

    fn eq_test<I1, I2>(c1: I1, c2: I2)
    where
        I1: Into<Coefficient>,
        I2: Into<Coefficient>,
    {
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
    fn test_negative_zero_eq() {
        let neg_zero = Decimal::new(Coefficient::negative_zero(), 0);
        let pos_zero = Decimal::new(0, 0);
        assert_eq!(neg_zero.clone(), neg_zero.clone());
        assert_ne!(neg_zero.clone(), pos_zero.clone());
        assert_eq!(pos_zero.clone(), pos_zero.clone());
    }
}
