use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use crate::result::{IonError, IonFailure};
use crate::types::decimal::magnitude::Magnitude;
use crate::types::integer::UIntData;
use crate::IonResult;
use crate::{Int, UInt};
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

    pub fn sign(&self) -> Sign {
        self.sign
    }

    pub fn magnitude(&self) -> &UInt {
        &self.magnitude
    }

    pub fn is_negative(&self) -> bool {
        self.sign == Sign::Negative
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

    /// Returns true if the Coefficient represents negative zero.
    pub fn is_negative_zero(&self) -> bool {
        self.is_zero_with_sign(Sign::Negative)
    }

    /// Returns true if the Coefficient represents positive zero.
    pub fn is_positive_zero(&self) -> bool {
        self.is_zero_with_sign(Sign::Positive)
    }

    pub(crate) fn is_zero_with_sign(&self, test_sign: Sign) -> bool {
        match (self.sign, &self.magnitude.data) {
            (sign, UIntData::U64(0)) if sign == test_sign => true,
            (sign, UIntData::BigUInt(b)) if sign == test_sign && b.is_zero() => true,
            _ => false,
        }
    }

    /// Returns true if the Coefficient represents a zero of any sign.
    pub fn is_zero(&self) -> bool {
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
impl_coefficient_from_unsigned_int_types!(u8, u16, u32, u64, u128, usize, UInt, BigUint);

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
impl_coefficient_from_signed_int_types!(i8, i16, i32, i64, i128, isize, Int);

// `BigInt` can't represent -0, so this is technically a lossy operation.
impl TryFrom<Coefficient> for BigInt {
    type Error = IonError;

    /// Attempts to create a BigInt from a Coefficient. Returns an Error if the Coefficient being
    /// converted is a negative zero, which BigInt cannot represent. Returns Ok otherwise.
    fn try_from(value: Coefficient) -> Result<Self, Self::Error> {
        if value.is_negative_zero() {
            IonResult::illegal_operation("cannot convert negative zero Coefficient to BigInt")?;
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

impl TryFrom<Coefficient> for Int {
    type Error = IonError;

    fn try_from(value: Coefficient) -> Result<Self, Self::Error> {
        if value.is_negative_zero() {
            return IonResult::illegal_operation("cannot convert negative zero Coefficient to Int");
        }
        if value.is_negative() {
            return Ok(Int::from(value.magnitude).neg());
        }
        Ok(Int::from(value.magnitude))
    }
}

impl TryFrom<&Coefficient> for Int {
    type Error = IonError;

    fn try_from(value: &Coefficient) -> Result<Self, Self::Error> {
        value.clone().try_into()
    }
}

impl TryFrom<Coefficient> for UInt {
    type Error = IonError;

    fn try_from(value: Coefficient) -> Result<Self, Self::Error> {
        if value.is_negative() {
            return IonResult::illegal_operation("cannot convert a negative Coefficient to a UInt");
        }
        Ok(value.magnitude)
    }
}

impl TryFrom<&Coefficient> for UInt {
    type Error = IonError;

    fn try_from(value: &Coefficient) -> Result<Self, Self::Error> {
        value.clone().try_into()
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
                        "cannot convert sign-less non-zero BigInt to Decimal",
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
    use crate::Int;
    use num_bigint::{BigInt, BigUint};
    use std::ops::Neg;
    use std::str::FromStr;

    use super::*;
    use crate::{Decimal, UInt};

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

    #[test]
    fn is_negative_zero() {
        assert!(Coefficient::negative_zero().is_negative_zero());
        assert!(!Coefficient::new(Sign::Positive, 0).is_negative_zero());
        assert!(!Coefficient::new(Sign::Positive, 5).is_negative_zero());
    }

    #[test]
    fn is_positive_zero() {
        assert!(Coefficient::new(Sign::Positive, 0).is_positive_zero());
        assert!(!Coefficient::new(Sign::Positive, 5).is_positive_zero());
        assert!(!Coefficient::negative_zero().is_positive_zero());
    }

    #[test]
    fn is_negative() {
        assert!(Coefficient::negative_zero().is_negative());
        assert!(Coefficient::new(Sign::Negative, 5).is_negative());
        assert!(!Coefficient::new(Sign::Positive, 5).is_negative());
    }

    #[test]
    fn sign() {
        assert_eq!(Coefficient::negative_zero().sign(), Sign::Negative);
        assert_eq!(Coefficient::new(Sign::Positive, 0).sign(), Sign::Positive);
        assert_eq!(Coefficient::new(Sign::Negative, 5).sign(), Sign::Negative);
        assert_eq!(Coefficient::new(Sign::Positive, 5).sign(), Sign::Positive);
    }

    #[test]
    fn magnitude() {
        assert_eq!(Coefficient::negative_zero().magnitude(), &UInt::from(0u32));
        assert_eq!(
            Coefficient::new(Sign::Positive, 0).magnitude(),
            &UInt::from(0u32)
        );
        assert_eq!(
            Coefficient::new(Sign::Negative, 5).magnitude(),
            &UInt::from(5u32)
        );
        assert_eq!(
            Coefficient::new(Sign::Positive, 5).magnitude(),
            &UInt::from(5u32)
        );
    }

    #[test]
    fn convert_to_int() {
        // i64
        assert_eq!(
            Int::try_from(Coefficient::new(Sign::Positive, 5)),
            Ok(Int::from(5))
        );
        assert_eq!(
            Int::try_from(Coefficient::new(Sign::Negative, 5)),
            Ok(Int::from(-5))
        );

        // BigInt
        let enormous_int = BigInt::from_str("1234567890123456789012345678901234567890").unwrap();
        assert_eq!(
            Int::try_from(Coefficient::new(Sign::Positive, enormous_int.clone())),
            Ok(Int::from(enormous_int.clone()))
        );
        assert_eq!(
            Int::try_from(Coefficient::new(Sign::Negative, enormous_int.clone())),
            Ok(Int::from(enormous_int.neg()))
        );

        // Zeros
        assert_eq!(
            Int::try_from(Coefficient::new(Sign::Positive, 0)),
            Ok(Int::from(0))
        );
        assert!(Int::try_from(Coefficient::negative_zero()).is_err());
    }
}
