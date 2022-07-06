use crate::result::{decoding_error, IonError};
use crate::value::Element;
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};
use std::cmp::Ordering;
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
#[derive(Debug, Clone)]
pub enum UInteger {
    U64(u64),
    BigUInt(BigUint),
}

impl UInteger {
    /// Compares a [u64] integer with a [BigUint] to see if they are equal. This method never
    /// allocates. It will always prefer to downgrade a BigUint and compare the two integers as
    /// u64 values. If this is not possible, then the two numbers cannot be equal anyway.
    fn cross_representation_eq(m1: u64, m2: &BigUint) -> bool {
        UInteger::cross_representation_cmp(m1, m2) == Ordering::Equal
    }

    /// Compares a [u64] integer with a [BigUint]. This method never allocates. It will always
    /// prefer to downgrade a BigUint and compare the two integers as u64 values. If this is
    /// not possible, then the BigUint is larger than the u64.
    fn cross_representation_cmp(m1: u64, m2: &BigUint) -> Ordering {
        // Try to downgrade the BigUint first since that's cheaper than upgrading the u64.
        if let Some(downgraded_m2) = m2.to_u64() {
            // If the conversion succeeds, compare the resulting values.
            return m1.cmp(&downgraded_m2);
        }
        // Otherwise, the BigUint must be larger than the u64.
        Ordering::Less
    }
}

impl PartialEq for UInteger {
    fn eq(&self, other: &Self) -> bool {
        use UInteger::*;
        match (self, other) {
            (U64(m1), U64(m2)) => m1 == m2,
            (BigUInt(m1), BigUInt(m2)) => m1 == m2,
            (U64(m1), BigUInt(m2)) => UInteger::cross_representation_eq(*m1, m2),
            (BigUInt(m1), U64(m2)) => UInteger::cross_representation_eq(*m2, m1),
        }
    }
}

impl Eq for UInteger {}

impl PartialOrd for UInteger {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UInteger {
    fn cmp(&self, other: &Self) -> Ordering {
        use UInteger::*;
        match (self, other) {
            (U64(m1), U64(m2)) => m1.cmp(m2),
            (BigUInt(m1), BigUInt(m2)) => m1.cmp(m2),
            (U64(m1), BigUInt(m2)) => UInteger::cross_representation_cmp(*m1, m2),
            (BigUInt(m1), U64(m2)) => UInteger::cross_representation_cmp(*m2, m1).reverse(),
        }
    }
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

impl Integer {
    /// Compares a [i64] integer with a [BigInt] to see if they are equal. This method never
    /// allocates. It will always prefer to downgrade a BigUint and compare the two integers as
    /// u64 values. If this is not possible, then the two numbers cannot be equal anyway.
    fn cross_representation_eq(m1: i64, m2: &BigInt) -> bool {
        Integer::cross_representation_cmp(m1, m2) == Ordering::Equal
    }

    /// Compares a [i64] integer with a [BigInt]. This method never allocates. It will always
    /// prefer to downgrade a BigUint and compare the two integers as u64 values. If this is
    /// not possible, then the BigUint is larger than the u64.
    fn cross_representation_cmp(m1: i64, m2: &BigInt) -> Ordering {
        // Try to downgrade the BigUint first since that's cheaper than upgrading the u64.
        if let Some(downgraded_m2) = m2.to_i64() {
            // If the conversion succeeds, compare the resulting values.
            return m1.cmp(&downgraded_m2);
        }
        // Otherwise, the BigUint must be larger than the u64.
        Ordering::Less
    }
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
        match (self, other) {
            (I64(m1), I64(m2)) => m1 == m2,
            (BigInt(m1), BigInt(m2)) => m1 == m2,
            (I64(m1), BigInt(m2)) => Integer::cross_representation_eq(*m1, m2),
            (BigInt(m1), I64(m2)) => Integer::cross_representation_eq(*m2, m1),
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

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Integer {
    fn cmp(&self, other: &Self) -> Ordering {
        use Integer::*;
        match (self, other) {
            (I64(m1), I64(m2)) => m1.cmp(m2),
            (BigInt(m1), BigInt(m2)) => m1.cmp(m2),
            (I64(m1), BigInt(m2)) => Integer::cross_representation_cmp(*m1, m2),
            (BigInt(m1), I64(m2)) => Integer::cross_representation_cmp(*m2, m1).reverse(),
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

// Trivial conversion to Integer::I64 from integers that can safely be converted to an i64
macro_rules! impl_integer_i64_from {
    ($($t:ty),*) => ($(
        impl From<$t> for Integer {
            fn from(value: $t) -> Integer {
                let i64_value = i64::from(value);
                Integer::I64(i64_value)
            }
        }
    )*)
}
impl_integer_i64_from!(u8, u16, u32, i8, i16, i32, i64);

// Conversion to Integer from integer types that may or may not fit in an i64
macro_rules! impl_integer_from {
    ($($t:ty),*) => ($(
        impl From<$t> for Integer {
            fn from(value: $t) -> Integer {
                match i64::try_from(value) {
                    Ok(i64_value) => Integer::I64(i64_value),
                    Err(_) => Integer::BigInt(BigInt::from(value))
                }
            }
        }
    )*)
}

impl_integer_from!(isize, usize, u64);

impl From<BigUint> for Integer {
    fn from(value: BigUint) -> Self {
        let big_int = BigInt::from(value);
        Integer::BigInt(big_int)
    }
}

impl From<BigInt> for Integer {
    fn from(value: BigInt) -> Self {
        Integer::BigInt(value)
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
    use num_bigint::BigUint;
    use num_traits::Zero;
    // The 'Big' alias helps distinguish between the enum variant and the wrapped numeric type
    use crate::types::integer::Integer::{self, BigInt as Big, I64};
    use crate::types::integer::UInteger;
    use rstest::*;
    use std::cmp::Ordering;

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

    #[rstest]
    #[case::i64(Integer::I64(5), Integer::I64(4), Ordering::Greater)]
    #[case::i64_equal(Integer::I64(-5), Integer::I64(-5), Ordering::Equal)]
    #[case::i64_gt_big_int(Integer::I64(4), Integer::BigInt(BigInt::from(3)), Ordering::Greater)]
    #[case::i64_eq_big_int(Integer::I64(3), Integer::BigInt(BigInt::from(3)), Ordering::Equal)]
    #[case::i64_lt_big_int(Integer::I64(-3), Integer::BigInt(BigInt::from(5)), Ordering::Less)]
    #[case::big_int(
        Integer::BigInt(BigInt::from(1100)),
        Integer::BigInt(BigInt::from(-1005)),
        Ordering::Greater
    )]
    #[case::big_int(
        Integer::BigInt(BigInt::from(1100)),
        Integer::BigInt(BigInt::from(1100)),
        Ordering::Equal
    )]
    fn integer_ordering_tests(
        #[case] this: Integer,
        #[case] other: Integer,
        #[case] expected: Ordering,
    ) {
        assert_eq!(this.cmp(&other), expected)
    }

    #[rstest]
    #[case::u64(UInteger::U64(5), UInteger::U64(4), Ordering::Greater)]
    #[case::u64_equal(UInteger::U64(5), UInteger::U64(5), Ordering::Equal)]
    #[case::u64_gt_big_uint(
        UInteger::U64(4),
        UInteger::BigUInt(BigUint::from(3u64)),
        Ordering::Greater
    )]
    #[case::u64_lt_big_uint(
        UInteger::U64(3),
        UInteger::BigUInt(BigUint::from(5u64)),
        Ordering::Less
    )]
    #[case::u64_eq_big_uint(
        UInteger::U64(3),
        UInteger::BigUInt(BigUint::from(3u64)),
        Ordering::Equal
    )]
    #[case::big_uint(
        UInteger::BigUInt(BigUint::from(1100u64)),
        UInteger::BigUInt(BigUint::from(1005u64)),
        Ordering::Greater
    )]
    #[case::big_uint(
        UInteger::BigUInt(BigUint::from(1005u64)),
        UInteger::BigUInt(BigUint::from(1005u64)),
        Ordering::Equal
    )]
    fn unsigned_integer_ordering_tests(
        #[case] this: UInteger,
        #[case] other: UInteger,
        #[case] expected: Ordering,
    ) {
        assert_eq!(this.cmp(&other), expected)
    }
}
