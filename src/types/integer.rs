use crate::result::{decoding_error, IonError};
use crate::value::Element;
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};
use std::ops::{Add, Neg};

/// Provides convenient integer accessors for integer values that are like [`Integer`]
pub trait IntAccess {
    /// Returns the value as an `i64` if it can be represented as such.
    ///
    /// ## Usage
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::owned::*;
    /// # use ion_rs::value::borrowed::*;
    /// # use ion_rs::types::integer::*;
    /// # use num_bigint::*;
    /// let big_int = Integer::BigInt(BigInt::from(100));
    /// let i64_int = Integer::I64(100);
    /// assert_eq!(big_int.as_i64(), i64_int.as_i64());
    ///
    /// // works on element too
    /// let big_elem: OwnedElement = OwnedValue::Integer(big_int).into();
    /// let i64_elem: BorrowedElement = BorrowedValue::Integer(i64_int).into();
    ///
    /// assert_eq!(big_elem.as_i64(), i64_elem.as_i64());
    /// ```
    fn as_i64(&self) -> Option<i64>;

    /// Returns a reference as a [`BigInt`] if it is represented as such.  Note that this
    /// method may return `None` if the underlying representation *is not* stored in a [`BigInt`]
    /// such as if it is represented as an `i64` so it is somewhat asymmetric with respect
    /// to [`IntAccess::as_i64`].
    ///
    /// ## Usage
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::owned::*;
    /// # use ion_rs::value::borrowed::*;
    /// # use ion_rs::types::integer::*;
    /// # use num_bigint::*;
    /// # use std::str::FromStr;
    /// let big_int = Integer::BigInt(BigInt::from(100));
    /// assert_eq!(BigInt::from_str("100").unwrap(), *big_int.as_big_int().unwrap());
    /// let i64_int = Integer::I64(100);
    /// assert_eq!(None, i64_int.as_big_int());
    ///
    /// // works on element too
    /// let big_elem: BorrowedElement = BorrowedValue::Integer(big_int).into();
    /// assert_eq!(BigInt::from_str("100").unwrap(), *big_elem.as_big_int().unwrap());
    /// let i64_elem: OwnedElement = OwnedValue::Integer(i64_int).into();
    /// assert_eq!(None, i64_elem.as_big_int());
    /// ```
    fn as_big_int(&self) -> Option<&BigInt>;
}

/// Represents a UInt of any size. Used for reading binary integers and symbol IDs.
///
/// Equality tests do NOT compare across storage types; U64(1) is not the same as BigUInt(1).
#[derive(Debug, Clone, PartialEq)]
pub enum UInteger {
    U64(u64),
    BigUInt(BigUint),
}

impl From<UInteger> for Integer {
    fn from(value: UInteger) -> Self {
        match value {
            UInteger::U64(uint) => {
                if let Ok(signed) = i64::try_from(uint) {
                    // The u64 was successfully converted to an i64
                    Integer::I64(signed)
                } else {
                    // The u64 was slightly too big to be represented as an i64; it required the
                    // 64th bit to store the magnitude. Up-convert it to a BigInt.
                    big_integer_from_u64(uint)
                }
            }
            UInteger::BigUInt(big_uint) => big_integer_from_big_uint(big_uint),
        }
    }
}

#[inline(never)]
fn big_integer_from_u64(value: u64) -> Integer {
    Integer::BigInt(BigInt::from(value))
}

#[inline(never)]
fn big_integer_from_big_uint(value: BigUint) -> Integer {
    Integer::BigInt(BigInt::from(value))
}

impl TryFrom<&UInteger> for i64 {
    type Error = IonError;

    fn try_from(value: &UInteger) -> Result<Self, Self::Error> {
        match value {
            UInteger::U64(uint) => i64::try_from(*uint).or_else(|_| {
                decoding_error(format!(
                    "Unsigned integer {:?} was too large to be represented as an i64.",
                    uint
                ))
            }),
            UInteger::BigUInt(big_uint) => i64::try_from(big_uint).or_else(|_| {
                decoding_error(format!(
                    "Unsigned integer {:?} was too large to be represented as an i64.",
                    big_uint
                ))
            }),
        }
    }
}

impl TryFrom<&UInteger> for usize {
    type Error = IonError;

    fn try_from(value: &UInteger) -> Result<Self, Self::Error> {
        match value {
            UInteger::U64(uint) => usize::try_from(*uint).or_else(|_| {
                decoding_error(format!(
                    "Unsigned integer {:?} was too large to be represented as an usize.",
                    uint
                ))
            }),
            UInteger::BigUInt(big_uint) => usize::try_from(big_uint).or_else(|_| {
                decoding_error(format!(
                    "Unsigned integer {:?} was too large to be represented as an usize.",
                    big_uint
                ))
            }),
        }
    }
}

/// Container for either an integer that can fit in a 64-bit word or an arbitrarily sized
/// [`BigInt`].
///
/// See [`IntAccess`] for common operations.
#[derive(Debug, Clone)]
pub enum Integer {
    I64(i64),
    BigInt(BigInt),
}

impl IntAccess for Integer {
    #[inline]
    fn as_i64(&self) -> Option<i64> {
        match &self {
            Integer::I64(i) => Some(*i),
            Integer::BigInt(big) => big.to_i64(),
        }
    }

    #[inline]
    fn as_big_int(&self) -> Option<&BigInt> {
        match &self {
            Integer::I64(_) => None,
            Integer::BigInt(big) => Some(big),
        }
    }
}

impl PartialEq for Integer {
    fn eq(&self, other: &Self) -> bool {
        use Integer::*;
        match self {
            I64(my_i64) => match other {
                I64(other_i64) => my_i64 == other_i64,
                BigInt(other_bi) => Some(*my_i64) == other_bi.to_i64(),
            },
            BigInt(my_bi) => match other {
                I64(other_i64) => my_bi.to_i64() == Some(*other_i64),
                BigInt(other_bi) => my_bi == other_bi,
            },
        }
    }
}

impl Eq for Integer {}

impl Neg for Integer {
    type Output = Self;

    fn neg(self) -> Self::Output {
        use Integer::*;
        match self {
            I64(value) => I64(-value),
            BigInt(value) => BigInt(-value),
        }
    }
}

impl Add<Self> for Integer {
    type Output = Integer;

    fn add(self, rhs: Self) -> Self::Output {
        // The alias 'Big' differentiates the enum variant from the wrapped 'BigInt' type
        use Integer::{BigInt as Big, I64};
        match (self, rhs) {
            (I64(this), I64(that)) => {
                // Try to add the i64s together; if they overflow, upconvert to BigInts
                match this.checked_add(that) {
                    Some(result) => I64(result),
                    None => Big(BigInt::from(this).add(BigInt::from(that))),
                }
            }
            (I64(this), Big(that)) => Big(BigInt::from(this).add(that)),
            (Big(this), I64(that)) => Big(this.add(&BigInt::from(that))),
            (Big(this), Big(that)) => Big(this.add(&that)),
        }
    }
}

impl Zero for Integer {
    fn zero() -> Self {
        Integer::I64(0)
    }

    fn is_zero(&self) -> bool {
        match self {
            Integer::I64(value) => *value == 0i64,
            Integer::BigInt(value) => value.is_zero(),
        }
    }
}

impl<T> IntAccess for T
where
    T: Element,
{
    fn as_i64(&self) -> Option<i64> {
        match self.as_integer() {
            Some(any) => any.as_i64(),
            _ => None,
        }
    }

    fn as_big_int(&self) -> Option<&BigInt> {
        match self.as_integer() {
            Some(any) => any.as_big_int(),
            _ => None,
        }
    }
}

#[cfg(test)]
mod integer_tests {
    use num_bigint::BigInt;
    use num_traits::Zero;
    // The 'Big' alias helps distinguish between the enum variant and the wrapped numeric type
    use crate::types::integer::Integer::{self, BigInt as Big, I64};

    #[test]
    fn is_zero() {
        assert!(I64(0).is_zero());
        assert!(Big(BigInt::from(0)).is_zero());
        assert!(!I64(55).is_zero());
        assert!(!Big(BigInt::from(55)).is_zero());
        assert!(!I64(-55).is_zero());
        assert!(!Big(BigInt::from(-55)).is_zero());
    }

    #[test]
    fn zero() {
        assert!(Integer::zero().is_zero());
    }

    #[test]
    fn add() {
        assert_eq!(I64(0) + I64(0), I64(0));
        assert_eq!(I64(5) + I64(7), I64(12));
        assert_eq!(I64(-5) + I64(7), I64(2));
        assert_eq!(I64(100) + Big(BigInt::from(1000)), Big(BigInt::from(1100)));
        assert_eq!(Big(BigInt::from(100)) + I64(1000), Big(BigInt::from(1100)));
        assert_eq!(
            Big(BigInt::from(100)) + Big(BigInt::from(1000)),
            Big(BigInt::from(1100))
        );
    }
}
