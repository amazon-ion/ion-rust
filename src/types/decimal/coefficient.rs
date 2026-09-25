//! A representation of a decimal value's coefficient.

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::{Debug, Display, Formatter};

use crate::result::{IonError, IonFailure};
use crate::types::overflowing_int::OverflowingInt;
use crate::IonResult;
use crate::{Int, UInt};

/// Indicates whether the `Coefficient`'s magnitude is less than 0 (negative) or not (positive).
/// When the magnitude is zero, the `Sign` can be used to distinguish between -0 and 0.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Sign {
    Negative = -1,
    Positive = 1,
}

/// A signed integer that can be used as the coefficient of a [`Decimal`](crate::Decimal) value.
///
/// Unlike `Int`, this type preserves the distinction between `0` and `-0`, which Ion requires:
/// `0d0` and `-0d0` are distinct values. Equality is **structural** — the sign always
/// participates — so [`Coefficient::ZERO`] and [`Coefficient::NEGATIVE_ZERO`] are **not** equal
/// under [`PartialEq::eq`]. The numeric equality that treats the two zeros as equal lives on
/// [`Decimal`](crate::Decimal), through its own `PartialEq`/[`IonEq`](crate::IonData) split.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Coefficient {
    repr: OverflowingInt,
}

impl Coefficient {
    pub const ZERO: Coefficient = Coefficient {
        repr: OverflowingInt::ZERO,
    };

    pub const NEGATIVE_ZERO: Coefficient = Coefficient {
        repr: OverflowingInt::NEGATIVE_ZERO,
    };

    pub(crate) fn new<I: Into<Int>>(value: I) -> Self {
        Coefficient {
            repr: OverflowingInt::from(value.into()),
        }
    }

    /// Builds a coefficient with the given `sign` and the magnitude of `magnitude`, applying the
    /// sign explicitly. A zero magnitude keeps `sign`, so this is the route that constructs a
    /// negative zero from a zero result.
    pub(crate) fn from_sign_and_value(sign: Sign, magnitude: impl Into<Int>) -> Self {
        Coefficient {
            repr: OverflowingInt::from(magnitude.into()).with_sign(sign),
        }
    }

    pub fn sign(&self) -> Sign {
        self.repr.sign()
    }

    pub fn magnitude(&self) -> UInt {
        UInt::from(self.repr.magnitude_ref())
    }

    /// Returns true when the sign is negative. This is a **sign-only** query: it is true for
    /// negative zero.
    pub fn is_negative(&self) -> bool {
        self.repr.sign() == Sign::Negative
    }

    /// Returns the number of digits in the base-10 representation of the coefficient
    pub(crate) fn number_of_decimal_digits(&self) -> u32 {
        self.repr.magnitude_ref().number_of_decimal_digits()
    }

    /// Constructs a new Coefficient that represents negative zero.
    pub(crate) fn negative_zero() -> Self {
        Coefficient {
            repr: OverflowingInt::NEGATIVE_ZERO,
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
        self.repr.sign() == test_sign && self.repr.is_zero()
    }

    /// Returns true if the Coefficient represents a zero of any sign.
    pub fn is_zero(&self) -> bool {
        self.repr.is_zero()
    }

    /// Returns the coefficient as an `Int`, or `None` for negative zero.
    ///
    /// This is a **lossless** query, not a value query: an `Int` cannot represent negative zero,
    /// and returning a plain zero would silently drop the sign. The binary writer relies on the
    /// `None` case to emit the negative-zero coefficient subfield, so this contract is
    /// load-bearing on the write path.
    pub(crate) fn as_int(&self) -> Option<Int> {
        Int::try_from(&self.repr).ok()
    }

    /// Splits the coefficient at `10^k`, returning `(quotient, remainder)`.
    ///
    /// Both results carry this coefficient's sign. A zero quotient or remainder keeps a negative sign as `-0`.
    pub(crate) fn div_rem_pow10(&self, k: u64) -> (Coefficient, Coefficient) {
        let (quotient, remainder) = self.repr.div_rem_pow10(k);
        (
            Coefficient { repr: quotient },
            Coefficient { repr: remainder },
        )
    }

    /// Compares this coefficient's magnitude scaled by `10^k` against `other`'s magnitude,
    /// ignoring sign. `Decimal`'s unequal-exponent comparison routes through this; the union
    /// decides the extreme cases from bit widths and only materializes `10^k` when the two
    /// magnitudes are close enough that neither dominates, so inline operands never allocate.
    pub(crate) fn cmp_magnitude_scaled(&self, k: u64, other: &Coefficient) -> Ordering {
        self.repr.cmp_magnitude_scaled(k, &other.repr)
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
impl_coefficient_from_unsigned_int_types!(u8, u16, u32, u64, u128, usize, UInt);

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
        match value.as_int() {
            Some(int) => Ok(int),
            None => IonResult::illegal_operation("cannot convert negative zero Coefficient to Int"),
        }
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
        // `is_negative` is true for negative zero, so `-0` is rejected here as well.
        if value.is_negative() {
            return IonResult::illegal_operation("cannot convert a negative Coefficient to a UInt");
        }
        Ok(value.magnitude())
    }
}

impl TryFrom<&Coefficient> for UInt {
    type Error = IonError;

    fn try_from(value: &Coefficient) -> Result<Self, Self::Error> {
        value.clone().try_into()
    }
}

impl Display for Coefficient {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.repr)
    }
}

impl Debug for Coefficient {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Coefficient({self})")
    }
}

#[cfg(test)]
mod coefficient_tests {
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

        let enormous_int = Int::from(12345678901234567890123456789u128);
        assert_eq!(
            Int::try_from(Coefficient::new(enormous_int.clone())),
            Ok(enormous_int.clone())
        );
        assert_eq!(
            Int::try_from(Coefficient::new(enormous_int.clone().neg())),
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

    #[test]
    fn display_and_debug_negative_heap_coefficient_single_sign() {
        // 2^128 exceeds i128, so the magnitude is heap-backed. `Display` must render exactly one
        // leading '-', not the doubled sign the baseline produced by formatting an
        // already-signed magnitude.
        let mut bytes = vec![0u8; 18];
        bytes[16] = 1;
        let magnitude = Int::from_le_signed_bytes(&bytes);
        let c = Coefficient::from_sign_and_value(Sign::Negative, magnitude);
        let shown = format!("{c}");
        assert_eq!(shown, "-340282366920938463463374607431768211456");
        assert!(!shown.starts_with("--"));
        // `Debug` wraps the same rendering, so it must not double the sign either.
        assert_eq!(
            format!("{c:?}"),
            "Coefficient(-340282366920938463463374607431768211456)"
        );
    }
}
