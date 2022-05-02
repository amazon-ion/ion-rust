use crate::result::{decoding_error, IonError};
use crate::value::Element;
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;
use std::ops::Neg;

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
                    Integer::BigInt(BigInt::from(uint))
                }
            }
            UInteger::BigUInt(big_uint) => Integer::BigInt(BigInt::from(big_uint)),
        }
    }
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
