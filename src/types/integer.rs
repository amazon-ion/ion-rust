use crate::element::Element;
use crate::ion_data::{IonEq, IonOrd};
use crate::result::{decoding_error, IonError};
use num_bigint::{BigInt, BigUint, ToBigUint};
use num_traits::{ToPrimitive, Zero};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::ops::{Add, Neg};

/// Provides convenient integer accessors for integer values that are like [`Int`]
pub trait IntAccess {
    /// Returns the value as an `i64` if it can be represented as such.
    ///
    /// ## Usage
    /// ```
    /// # use ion_rs::element::*;
    /// # use ion_rs::element::*;
    /// # use ion_rs::types::*;
    /// # use num_bigint::*;
    /// let big_int = Int::BigInt(BigInt::from(100));
    /// let i64_int = Int::I64(100);
    /// assert_eq!(big_int.as_i64(), i64_int.as_i64());
    ///
    /// // works on element too
    /// let big_elem: Element = big_int.into();
    /// let i64_elem: Element = i64_int.into();
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
    /// # use ion_rs::element::*;
    /// # use ion_rs::element::*;
    /// # use ion_rs::types::*;
    /// # use num_bigint::*;
    /// # use std::str::FromStr;
    /// let big_int = Int::BigInt(BigInt::from(100));
    /// assert_eq!(
    ///     BigInt::from_str("100").unwrap(),
    ///     *big_int.as_big_int().unwrap()
    /// );
    /// let i64_int = Int::I64(100);
    /// assert_eq!(None, i64_int.as_big_int());
    ///
    /// // works on element too
    /// let big_elem: Element = big_int.into();
    /// assert_eq!(
    ///     BigInt::from_str("100").unwrap(),
    ///     *big_elem.as_big_int().unwrap()
    /// );
    /// let i64_elem: Element = i64_int.into();
    /// assert_eq!(None, i64_elem.as_big_int());
    /// ```
    fn as_big_int(&self) -> Option<&BigInt>;
}

/// Represents a UInt of any size. Used for reading binary integers and symbol Ids.
/// Used to represent the unsigned magnitude of Decimal values and fractional seconds.
#[derive(Debug, Clone)]
pub enum UInt {
    U64(u64),
    BigUInt(BigUint),
}

impl UInt {
    /// Compares a [u64] integer with a [BigUint] to see if they are equal. This method never
    /// allocates. It will always prefer to downgrade a BigUint and compare the two integers as
    /// u64 values. If this is not possible, then the two numbers cannot be equal anyway.
    fn cross_representation_eq(m1: u64, m2: &BigUint) -> bool {
        UInt::cross_representation_cmp(m1, m2) == Ordering::Equal
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

    /// Returns the number of digits in the base-10 representation of the UInteger.
    pub(crate) fn number_of_decimal_digits(&self) -> u64 {
        match self {
            UInt::U64(u64_value) => super::num_decimal_digits_in_u64(*u64_value),
            UInt::BigUInt(big_uint_value) => UInt::calculate_big_uint_digits(big_uint_value),
        }
    }

    fn calculate_big_uint_digits(int: &BigUint) -> u64 {
        if int.is_zero() {
            return 1;
        }
        let mut digits = 0;
        let mut dividend = int.to_owned();
        let ten: BigUint = BigUint::from(10u64);
        while dividend > BigUint::zero() {
            dividend /= &ten;
            digits += 1;
        }
        digits
    }
}

impl PartialEq for UInt {
    fn eq(&self, other: &Self) -> bool {
        use UInt::*;
        match (self, other) {
            (U64(m1), U64(m2)) => m1 == m2,
            (BigUInt(m1), BigUInt(m2)) => m1 == m2,
            (U64(m1), BigUInt(m2)) => UInt::cross_representation_eq(*m1, m2),
            (BigUInt(m1), U64(m2)) => UInt::cross_representation_eq(*m2, m1),
        }
    }
}

impl Eq for UInt {}

impl PartialOrd for UInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UInt {
    fn cmp(&self, other: &Self) -> Ordering {
        use UInt::*;
        match (self, other) {
            (U64(m1), U64(m2)) => m1.cmp(m2),
            (BigUInt(m1), BigUInt(m2)) => m1.cmp(m2),
            (U64(m1), BigUInt(m2)) => UInt::cross_representation_cmp(*m1, m2),
            (BigUInt(m1), U64(m2)) => UInt::cross_representation_cmp(*m2, m1).reverse(),
        }
    }
}

impl From<UInt> for Int {
    fn from(value: UInt) -> Self {
        match value {
            UInt::U64(uint) => {
                if let Ok(signed) = i64::try_from(uint) {
                    // The u64 was successfully converted to an i64
                    Int::I64(signed)
                } else {
                    // The u64 was slightly too big to be represented as an i64; it required the
                    // 64th bit to store the magnitude. Up-convert it to a BigInt.
                    big_integer_from_u64(uint)
                }
            }
            UInt::BigUInt(big_uint) => big_integer_from_big_uint(big_uint),
        }
    }
}

impl From<BigUint> for UInt {
    fn from(value: BigUint) -> Self {
        // prefer a compact representation for the magnitude
        match value.to_u64() {
            Some(unsigned) => UInt::U64(unsigned),
            None => UInt::BigUInt(value),
        }
    }
}

impl From<UInt> for BigUint {
    fn from(value: UInt) -> Self {
        use UInt::*;
        match value {
            U64(m) => BigUint::from(m),
            BigUInt(m) => m,
        }
    }
}

impl ToBigUint for UInt {
    fn to_biguint(&self) -> Option<BigUint> {
        // This implementation never fails, but the trait requires an `Option` return type.
        Some(self.clone().into())
    }
}

// This macro makes it possible to turn unsigned int primitives into a UInteger using `.into()`.
// Note that it works for both signed and unsigned ints. The resulting UInteger will be the
// absolute value of the integer being converted.
macro_rules! impl_uint_from_small_unsigned_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for UInt {
            fn from(value: $t) -> UInt {
                UInt::U64(value as u64)
            }
        }
    )*)
}

impl_uint_from_small_unsigned_int_types!(u8, u16, u32, u64, usize);

macro_rules! impl_uint_from_small_signed_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for UInt {
            fn from(value: $t) -> UInt {
                let abs_value = value.unsigned_abs();
                UInt::U64(abs_value.try_into().unwrap())
            }
        }
    )*)
}

impl_uint_from_small_signed_int_types!(i8, i16, i32, i64, isize);

impl From<u128> for UInt {
    fn from(value: u128) -> UInt {
        UInt::BigUInt(BigUint::from(value))
    }
}

impl From<i128> for UInt {
    fn from(value: i128) -> UInt {
        UInt::BigUInt(value.abs().to_biguint().unwrap())
    }
}

impl From<Int> for UInt {
    fn from(value: Int) -> Self {
        match value {
            Int::I64(i) => i.into(),
            // num_bigint::BigInt's `into_parts` consumes the BigInt and returns a
            // (sign: Sign, magnitude: BigUint) tuple. We only care about the magnitude, so we
            // extract it here with `.1` ---------------v and then convert the BigUint to a UInteger
            Int::BigInt(i) => i.into_parts().1.into(), // <-- using `.into()`
        }
    }
}

#[inline(never)]
fn big_integer_from_u64(value: u64) -> Int {
    Int::BigInt(BigInt::from(value))
}

#[inline(never)]
fn big_integer_from_big_uint(value: BigUint) -> Int {
    Int::BigInt(BigInt::from(value))
}

impl TryFrom<&UInt> for i64 {
    type Error = IonError;

    fn try_from(value: &UInt) -> Result<Self, Self::Error> {
        match value {
            UInt::U64(uint) => i64::try_from(*uint).or_else(|_| {
                decoding_error(format!(
                    "Unsigned integer {uint:?} was too large to be represented as an i64."
                ))
            }),
            UInt::BigUInt(big_uint) => i64::try_from(big_uint).or_else(|_| {
                decoding_error(format!(
                    "Unsigned integer {big_uint:?} was too large to be represented as an i64."
                ))
            }),
        }
    }
}

impl TryFrom<&UInt> for usize {
    type Error = IonError;

    fn try_from(value: &UInt) -> Result<Self, Self::Error> {
        match value {
            UInt::U64(uint) => usize::try_from(*uint).or_else(|_| {
                decoding_error(format!(
                    "Unsigned integer {uint:?} was too large to be represented as an usize."
                ))
            }),
            UInt::BigUInt(big_uint) => usize::try_from(big_uint).or_else(|_| {
                decoding_error(format!(
                    "Unsigned integer {big_uint:?} was too large to be represented as an usize."
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
pub enum Int {
    I64(i64),
    BigInt(BigInt),
}

impl Int {
    /// Compares a [i64] integer with a [BigInt] to see if they are equal. This method never
    /// allocates. It will always prefer to downgrade a BigUint and compare the two integers as
    /// u64 values. If this is not possible, then the two numbers cannot be equal anyway.
    fn cross_representation_eq(m1: i64, m2: &BigInt) -> bool {
        Int::cross_representation_cmp(m1, m2) == Ordering::Equal
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

impl IntAccess for Int {
    #[inline]
    fn as_i64(&self) -> Option<i64> {
        match &self {
            Int::I64(i) => Some(*i),
            Int::BigInt(big) => big.to_i64(),
        }
    }

    #[inline]
    fn as_big_int(&self) -> Option<&BigInt> {
        match &self {
            Int::I64(_) => None,
            Int::BigInt(big) => Some(big),
        }
    }
}

impl PartialEq for Int {
    fn eq(&self, other: &Self) -> bool {
        use Int::*;
        match (self, other) {
            (I64(m1), I64(m2)) => m1 == m2,
            (BigInt(m1), BigInt(m2)) => m1 == m2,
            (I64(m1), BigInt(m2)) => Int::cross_representation_eq(*m1, m2),
            (BigInt(m1), I64(m2)) => Int::cross_representation_eq(*m2, m1),
        }
    }
}

impl Eq for Int {}

impl IonEq for Int {
    fn ion_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl IonOrd for Int {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}

impl Neg for Int {
    type Output = Self;

    fn neg(self) -> Self::Output {
        use Int::*;
        match self {
            I64(value) => I64(-value),
            BigInt(value) => BigInt(-value),
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Self) -> Ordering {
        use Int::*;
        match (self, other) {
            (I64(m1), I64(m2)) => m1.cmp(m2),
            (BigInt(m1), BigInt(m2)) => m1.cmp(m2),
            (I64(m1), BigInt(m2)) => Int::cross_representation_cmp(*m1, m2),
            (BigInt(m1), I64(m2)) => Int::cross_representation_cmp(*m2, m1).reverse(),
        }
    }
}

impl Add<Self> for Int {
    type Output = Int;

    fn add(self, rhs: Self) -> Self::Output {
        // The alias 'Big' differentiates the enum variant from the wrapped 'BigInt' type
        use Int::{BigInt as Big, I64};
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

impl Zero for Int {
    fn zero() -> Self {
        Int::I64(0)
    }

    fn is_zero(&self) -> bool {
        match self {
            Int::I64(value) => *value == 0i64,
            Int::BigInt(value) => value.is_zero(),
        }
    }
}

impl Display for UInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self {
            UInt::U64(i) => write!(f, "{i}"),
            UInt::BigUInt(i) => write!(f, "{i}"),
        }
    }
}

// Trivial conversion to Int::I64 from integers that can safely be converted to an i64
macro_rules! impl_int_i64_from {
    ($($t:ty),*) => ($(
        impl From<$t> for Int {
            fn from(value: $t) -> Int {
                let i64_value = i64::from(value);
                Int::I64(i64_value)
            }
        }
    )*)
}
impl_int_i64_from!(u8, u16, u32, i8, i16, i32, i64);

// Conversion to Integer from integer types that may or may not fit in an i64
macro_rules! impl_int_from {
    ($($t:ty),*) => ($(
        impl From<$t> for Int {
            fn from(value: $t) -> Int {
                match i64::try_from(value) {
                    Ok(i64_value) => Int::I64(i64_value),
                    Err(_) => Int::BigInt(BigInt::from(value))
                }
            }
        }
    )*)
}

impl_int_from!(isize, usize, u64);

impl From<BigUint> for Int {
    fn from(value: BigUint) -> Self {
        let big_int = BigInt::from(value);
        Int::BigInt(big_int)
    }
}

impl From<BigInt> for Int {
    fn from(value: BigInt) -> Self {
        Int::BigInt(value)
    }
}

impl IntAccess for Element {
    fn as_i64(&self) -> Option<i64> {
        match self.as_int() {
            Some(any) => any.as_i64(),
            _ => None,
        }
    }

    fn as_big_int(&self) -> Option<&BigInt> {
        match self.as_int() {
            Some(any) => any.as_big_int(),
            _ => None,
        }
    }
}

impl Display for Int {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self {
            Int::I64(i) => write!(f, "{i}"),
            Int::BigInt(i) => write!(f, "{i}"),
        }
    }
}

#[cfg(test)]
mod integer_tests {
    use num_bigint::BigInt;
    use std::io::Write;

    use num_bigint::BigUint;
    use num_traits::Zero;
    // The 'Big' alias helps distinguish between the enum variant and the wrapped numeric type
    use crate::types::Int::{self, BigInt as Big, I64};
    use crate::types::UInt;
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
        assert!(Int::zero().is_zero());
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
    #[case::i64(Int::I64(5), Int::I64(4), Ordering::Greater)]
    #[case::i64_equal(Int::I64(-5), Int::I64(-5), Ordering::Equal)]
    #[case::i64_gt_big_int(Int::I64(4), Int::BigInt(BigInt::from(3)), Ordering::Greater)]
    #[case::i64_eq_big_int(Int::I64(3), Int::BigInt(BigInt::from(3)), Ordering::Equal)]
    #[case::i64_lt_big_int(Int::I64(-3), Int::BigInt(BigInt::from(5)), Ordering::Less)]
    #[case::big_int(
        Int::BigInt(BigInt::from(1100)),
        Int::BigInt(BigInt::from(-1005)),
        Ordering::Greater
    )]
    #[case::big_int(
        Int::BigInt(BigInt::from(1100)),
        Int::BigInt(BigInt::from(1100)),
        Ordering::Equal
    )]
    fn integer_ordering_tests(#[case] this: Int, #[case] other: Int, #[case] expected: Ordering) {
        assert_eq!(this.cmp(&other), expected)
    }

    #[rstest]
    #[case::u64(UInt::U64(5), UInt::U64(4), Ordering::Greater)]
    #[case::u64_equal(UInt::U64(5), UInt::U64(5), Ordering::Equal)]
    #[case::u64_gt_big_uint(UInt::U64(4), UInt::BigUInt(BigUint::from(3u64)), Ordering::Greater)]
    #[case::u64_lt_big_uint(UInt::U64(3), UInt::BigUInt(BigUint::from(5u64)), Ordering::Less)]
    #[case::u64_eq_big_uint(UInt::U64(3), UInt::BigUInt(BigUint::from(3u64)), Ordering::Equal)]
    #[case::big_uint(
        UInt::BigUInt(BigUint::from(1100u64)),
        UInt::BigUInt(BigUint::from(1005u64)),
        Ordering::Greater
    )]
    #[case::big_uint(
        UInt::BigUInt(BigUint::from(1005u64)),
        UInt::BigUInt(BigUint::from(1005u64)),
        Ordering::Equal
    )]
    fn unsigned_integer_ordering_tests(
        #[case] this: UInt,
        #[case] other: UInt,
        #[case] expected: Ordering,
    ) {
        assert_eq!(this.cmp(&other), expected)
    }

    #[rstest]
    #[case(UInt::U64(1), 1)] // only one test case for U64 as that's delegated to another impl
    #[case(UInt::BigUInt(BigUint::from(0u64)), 1)]
    #[case(UInt::BigUInt(BigUint::from(1u64)), 1)]
    #[case(UInt::BigUInt(BigUint::from(10u64)), 2)]
    #[case(UInt::BigUInt(BigUint::from(3117u64)), 4)]
    fn uint_decimal_digits_test(#[case] uint: UInt, #[case] expected: i32) {
        assert_eq!(uint.number_of_decimal_digits(), expected as u64)
    }

    #[rstest]
    #[case(Int::I64(5), "5")]
    #[case(Int::I64(-5), "-5")]
    #[case(Int::I64(0), "0")]
    #[case(Int::BigInt(BigInt::from(1100)), "1100")]
    #[case(Int::BigInt(BigInt::from(-1100)), "-1100")]
    fn int_display_test(#[case] value: Int, #[case] expect: String) {
        let mut buf = Vec::new();
        write!(&mut buf, "{value}").unwrap();
        assert_eq!(expect, String::from_utf8(buf).unwrap());
    }

    #[rstest]
    #[case(UInt::U64(5), "5")]
    #[case(UInt::U64(0), "0")]
    #[case(UInt::BigUInt(BigUint::from(0u64)), "0")]
    #[case(UInt::BigUInt(BigUint::from(1100u64)), "1100")]
    fn uint_display_test(#[case] value: UInt, #[case] expect: String) {
        let mut buf = Vec::new();
        write!(&mut buf, "{value}").unwrap();
        assert_eq!(expect, String::from_utf8(buf).unwrap());
    }
}
