use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use crate::result::{IonError, IonFailure};
use crate::types::integer::UIntData;
use crate::types::UInt;
use crate::IonResult;
use std::convert::TryFrom;
use std::fmt::{Display, Formatter};
use std::ops::{MulAssign, Neg};

/// Indicates whether the Coefficient's magnitude is less than 0 (negative) or not (positive).
/// When the magnitude is zero, the Sign can be used to distinguish between -0 and 0.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Sign {
    Negative,
    Positive,
}

/// A simple wrapper type around a [`UInt`]. Users are not expected to construct
/// instances of `Magnitude` directly; it is provided for conversion ergonomics.
///
/// Signed integer types cannot implement `Into<UInt>`. Instead, they implement
/// `TryInto<UInt>` and report an error if the input integer is negative.
///
/// Signed integers can infallibly implement `Into<Magnitude>` by using their
/// absolute value.
pub struct Magnitude(UInt);

impl Magnitude {
    fn new<I: Into<UInt>>(value: I) -> Self {
        Magnitude(value.into())
    }
}

impl From<UInt> for Magnitude {
    fn from(value: UInt) -> Self {
        Magnitude(value)
    }
}

impl From<Magnitude> for UInt {
    fn from(value: Magnitude) -> Self {
        value.0
    }
}

impl From<BigUint> for Magnitude {
    fn from(value: BigUint) -> Self {
        let uint: UInt = value.into();
        Magnitude(uint)
    }
}

macro_rules! impl_magnitude_from_small_unsigned_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Magnitude {
            fn from(value: $t) -> Magnitude {
                let uint: UInt = value.into();
                Magnitude(uint)
            }
        }
    )*)
}

impl_magnitude_from_small_unsigned_int_types!(u8, u16, u32, u64, u128, usize);

macro_rules! impl_magnitude_from_small_signed_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Magnitude {
            fn from(value: $t) -> Magnitude {
                let uint: UInt = (value.unsigned_abs() as u64).into();
                Magnitude(uint)
            }
        }
    )*)
}

impl_magnitude_from_small_signed_int_types!(i8, i16, i32, i64, isize);

/// A signed integer that can be used as the coefficient of a Decimal value. This type does not
/// consider `0` and `-0` to be equal and supports magnitudes of arbitrary size.
// These trait derivations rely closely on the manual implementations of PartialEq and Ord on
// [Magnitude].
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct Coefficient {
    pub(crate) sign: Sign,
    pub(crate) magnitude: UInt,
}

impl Coefficient {
    pub(crate) fn new<I: Into<Magnitude>>(sign: Sign, magnitude: I) -> Self {
        let magnitude: Magnitude = magnitude.into();
        let magnitude: UInt = magnitude.into();
        Coefficient { sign, magnitude }
    }

    pub(crate) fn sign(&self) -> Sign {
        self.sign
    }

    pub(crate) fn magnitude(&self) -> &UInt {
        &self.magnitude
    }

    /// Returns the number of digits in the base-10 representation of the coefficient
    pub(crate) fn number_of_decimal_digits(&self) -> u64 {
        self.magnitude.number_of_decimal_digits()
    }

    /// Constructs a new Coefficient that represents negative zero.
    pub(crate) fn negative_zero() -> Self {
        Coefficient {
            sign: Sign::Negative,
            magnitude: 0u64.into(),
        }
    }

    /// Returns true if the Coefficient represents positive zero.
    pub(crate) fn is_negative_zero(&self) -> bool {
        match (self.sign, &self.magnitude.data) {
            (Sign::Negative, UIntData::U64(0)) => true,
            (Sign::Negative, UIntData::BigUInt(b)) if b.is_zero() => true,
            _ => false,
        }
    }

    /// Returns true if the Coefficient represents positive zero.
    pub(crate) fn is_positive_zero(&self) -> bool {
        match (self.sign, &self.magnitude.data) {
            (Sign::Positive, UIntData::U64(0)) => true,
            (Sign::Positive, UIntData::BigUInt(b)) if b.is_zero() => true,
            _ => false,
        }
    }

    /// Returns true if the Coefficient represents a zero of any sign.
    pub(crate) fn is_zero(&self) -> bool {
        match (self.sign, &self.magnitude.data) {
            (_, UIntData::U64(0)) => true,
            (_, UIntData::BigUInt(b)) if b.is_zero() => true,
            _ => false,
        }
    }

    /// If the value can fit in an i64, return it as such. This is useful for
    /// inline representations.
    pub(crate) fn as_i64(&self) -> Option<i64> {
        match &self.magnitude.data {
            UIntData::U64(unsigned) => match i64::try_from(*unsigned) {
                Ok(signed) => match self.sign {
                    Sign::Negative => Some(signed.neg()), // cannot overflow (never `MIN`)
                    Sign::Positive => Some(signed),
                },
                Err(_) => None,
            },
            UIntData::BigUInt(_) => None,
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
                Coefficient::new(sign, value.unsigned_abs())
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
            IonResult::illegal_operation("Cannot convert negative zero Decimal to BigInt")?;
        }
        let mut big_int: BigInt = match value.magnitude.data {
            UIntData::U64(m) => m.into(),
            UIntData::BigUInt(m) => m.into(),
        };
        if value.sign == Sign::Negative {
            big_int.mul_assign(-1);
        }
        Ok(big_int)
    }
}

impl TryFrom<BigInt> for Coefficient {
    type Error = IonError;

    fn try_from(value: BigInt) -> Result<Self, Self::Error> {
        let (sign, magnitude) = value.into_parts();
        let sign = match sign {
            num_bigint::Sign::Minus => Sign::Negative,
            num_bigint::Sign::Plus => Sign::Positive,
            num_bigint::Sign::NoSign => {
                if magnitude.is_zero() {
                    Sign::Positive
                } else {
                    return IonResult::illegal_operation(
                        "Cannot convert sign-less non-zero BigInt to Decimal.",
                    );
                }
            }
        };
        Ok(Coefficient::new(sign, magnitude))
    }
}

impl Display for Coefficient {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.sign {
            Sign::Positive => {}
            Sign::Negative => write!(f, "-")?,
        };
        match &self.magnitude.data {
            UIntData::U64(m) => write!(f, "{}", *m),
            UIntData::BigUInt(m) => write!(f, "{m}"),
        }
    }
}

#[cfg(test)]
mod coefficient_tests {
    use crate::ion_data::IonEq;
    use num_bigint::BigUint;

    use crate::types::{Coefficient, Decimal};

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
        assert_eq!(neg_zero, neg_zero);
        assert!(neg_zero.ion_eq(&neg_zero));

        assert_eq!(neg_zero, pos_zero);
        assert!(!neg_zero.ion_eq(&pos_zero));

        assert_eq!(pos_zero, pos_zero);
        assert!(pos_zero.ion_eq(&pos_zero));
    }
}
