//! A representation of a decimal value's coefficient.

use std::convert::TryFrom;
use std::fmt::{Display, Formatter};

use num_traits::Zero;

use crate::result::{IonError, IonFailure};
use crate::types::CountDecimalDigits;
use crate::IonResult;
use crate::{Int, UInt};

/// Indicates whether the `Coefficient`'s magnitude is less than 0 (negative) or not (positive).
/// When the magnitude is zero, the `Sign` can be used to distinguish between -0 and 0.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Sign {
    Negative = -1,
    Positive = 1,
}

/// A signed integer that can be used as the coefficient of a [`Decimal`](crate::Decimal) value.
///
/// Unlike `Int`, this type preserves the distinction between `0` and `-0`. When tested for mathematical
/// equality using [`PartialEq::eq`], [`Coefficient::ZERO`] and [`Coefficient::NEGATIVE_ZERO`] will be
/// considered equal. When tested for Ion data equality using [`IonData::eq`](crate::IonData::eq),
/// they will be considered unequal.
///
/// While the Ion specification allows this type to be of arbitrary size, this implementation currently
/// supports coefficients in the integer range supported by `i128`.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct Coefficient {
    /// This field exists solely to preserve the distinction between `0` and `-0`.
    /// It will agree with the sign information in the `magnitude` field in all cases *except*
    /// when the coefficient is `-0`.
    sign: Sign,
    magnitude: Int,
}

impl Coefficient {
    pub const ZERO: Coefficient = Coefficient {
        sign: Sign::Positive,
        magnitude: Int::ZERO,
    };

    pub const NEGATIVE_ZERO: Coefficient = Coefficient {
        sign: Sign::Negative,
        magnitude: Int::ZERO,
    };

    pub(crate) fn new<I: Into<Int>>(value: I) -> Self {
        let value: Int = value.into();
        let sign = if value.is_negative() {
            Sign::Negative
        } else {
            Sign::Positive
        };
        Coefficient {
            sign,
            magnitude: value,
        }
    }

    pub fn sign(&self) -> Sign {
        self.sign
    }

    pub fn magnitude(&self) -> UInt {
        self.magnitude.unsigned_abs()
    }

    pub fn is_negative(&self) -> bool {
        self.sign == Sign::Negative
    }

    /// Returns the number of digits in the base-10 representation of the coefficient
    pub(crate) fn number_of_decimal_digits(&self) -> u32 {
        self.magnitude.count_decimal_digits()
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
        self.sign == test_sign && self.magnitude.is_zero()
    }

    /// Returns true if the Coefficient represents a zero of any sign.
    pub fn is_zero(&self) -> bool {
        self.magnitude().is_zero()
    }

    /// If the value can be represented as an `i128`, return it as such.
    /// If the coefficient is negative zero or outside the range of an `i128`, returns `None`.
    pub(crate) fn as_int(&self) -> Option<Int> {
        if self.is_negative_zero() {
            // Returning an unsigned zero would be lossy.
            return None;
        }
        Some(self.magnitude)
    }
}

// This macro makes it possible to turn unsigned integers into a Coefficient using `.into()`.
macro_rules! impl_coefficient_from_unsigned_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Coefficient {
            fn from(value: $t) -> Coefficient {
                Coefficient::new(value)
            }
        }
    )*)
}
impl_coefficient_from_unsigned_int_types!(u8, u16, u32, u64, usize);

// This macro makes it possible to turn signed integers into a Coefficient using `.into()`.
macro_rules! impl_coefficient_from_signed_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Coefficient {
            fn from(value: $t) -> Coefficient {
                Coefficient::new(value)
            }
        }
    )*)
}
impl_coefficient_from_signed_int_types!(i8, i16, i32, i64, i128, isize, Int);

impl TryFrom<Coefficient> for Int {
    type Error = IonError;

    fn try_from(value: Coefficient) -> Result<Self, Self::Error> {
        if value.is_negative_zero() {
            return IonResult::illegal_operation("cannot convert negative zero Coefficient to Int");
        }
        Ok(value.magnitude)
    }
}

impl TryFrom<&Coefficient> for Int {
    type Error = IonError;

    fn try_from(value: &Coefficient) -> Result<Self, Self::Error> {
        (*value).try_into()
    }
}

impl TryFrom<Coefficient> for UInt {
    type Error = IonError;

    fn try_from(value: Coefficient) -> Result<Self, Self::Error> {
        if value.is_negative() {
            return IonResult::illegal_operation("cannot convert a negative Coefficient to a UInt");
        }
        Ok(value.magnitude.unsigned_abs())
    }
}

impl TryFrom<&Coefficient> for UInt {
    type Error = IonError;

    fn try_from(value: &Coefficient) -> Result<Self, Self::Error> {
        (*value).try_into()
    }
}

impl Display for Coefficient {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.sign {
            Sign::Positive => {}
            Sign::Negative => write!(f, "-")?,
        };
        write!(f, "{}", self.magnitude)
    }
}

#[cfg(test)]
mod coefficient_tests {
    use std::ops::Neg;

    use crate::ion_data::IonEq;
    use crate::Int;
    use crate::{Decimal, UInt};

    use super::*;

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
        eq_test(0u64, 0i64);
        eq_test(0i128, 0u64);
        eq_test(0i128, 0i64);

        eq_test(u64::MAX, u64::MAX);
        eq_test(u64::MAX, i128::from(u64::MAX));
        eq_test(i128::from(u64::MAX), u64::MAX);
        eq_test(i128::from(u64::MAX), i128::from(u64::MAX));

        eq_test(i128::MAX, i128::MAX);
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
        assert!(!Coefficient::new(0).is_negative_zero());
        assert!(!Coefficient::new(5).is_negative_zero());
    }

    #[test]
    fn is_positive_zero() {
        assert!(Coefficient::new(0).is_positive_zero());
        assert!(!Coefficient::new(5).is_positive_zero());
        assert!(!Coefficient::negative_zero().is_positive_zero());
    }

    #[test]
    fn is_negative() {
        assert!(Coefficient::negative_zero().is_negative());
        assert!(Coefficient::new(-5).is_negative());
        assert!(!Coefficient::new(5).is_negative());
    }

    #[test]
    fn sign() {
        assert_eq!(Coefficient::negative_zero().sign(), Sign::Negative);
        assert_eq!(Coefficient::new(0).sign(), Sign::Positive);
        assert_eq!(Coefficient::new(-5).sign(), Sign::Negative);
        assert_eq!(Coefficient::new(5).sign(), Sign::Positive);
    }

    #[test]
    fn magnitude() {
        assert_eq!(Coefficient::negative_zero().magnitude(), UInt::from(0u32));
        assert_eq!(Coefficient::new(0).magnitude(), UInt::from(0u32));
        assert_eq!(Coefficient::new(-5).magnitude(), UInt::from(5u32));
        assert_eq!(Coefficient::new(5).magnitude(), UInt::from(5u32));
    }

    #[test]
    fn convert_to_int() {
        // i64
        assert_eq!(Int::try_from(Coefficient::new(5)), Ok(Int::from(5)));
        assert_eq!(Int::try_from(Coefficient::new(-5)), Ok(Int::from(-5)));

        let enormous_int = Int::try_from(12345678901234567890123456789u128).unwrap();
        assert_eq!(
            Int::try_from(Coefficient::new(enormous_int)),
            Ok(enormous_int)
        );
        assert_eq!(
            Int::try_from(Coefficient::new(enormous_int.neg())),
            Ok(enormous_int.neg())
        );

        // Zeros
        assert_eq!(Int::try_from(Coefficient::new(0)), Ok(Int::from(0)));
        assert!(Int::try_from(Coefficient::negative_zero()).is_err());
    }

    #[test]
    fn test_casting_sign() {
        assert_eq!(-1, Sign::Negative as i8);
        assert_eq!(1, Sign::Positive as i8);
    }
}
