use crate::ion_data::{IonEq, IonOrd};
use crate::result::IonFailure;
use crate::{IonError, IonResult};
use num_bigint::{BigInt, BigUint, ToBigUint};
use num_traits::{CheckedAdd, Signed, ToPrimitive, Zero};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::ops::{Add, Neg};

/// Represents an unsigned integer of any size.
#[derive(Debug, Clone)]
pub struct UInt {
    pub(crate) data: UIntData,
}

#[derive(Debug, Clone)]
pub(crate) enum UIntData {
    U64(u64),
    BigUInt(BigUint),
}

impl UInt {
    /// Attempts to convert this `UInt` to a `usize`. If the value is too large to fit,
    /// returns `None`.
    pub fn as_usize(&self) -> Option<usize> {
        usize::try_from(self).ok()
    }

    /// Attempts to convert this `UInt` to a `u64`. If the value is too large to fit,
    /// returns `None`.
    pub fn as_u64(&self) -> Option<u64> {
        u64::try_from(self).ok()
    }

    /// Attempts to convert this `UInt` to a `usize`. If the value is too large to fit,
    /// returns an [`IonError`].
    pub fn expect_usize(&self) -> IonResult<usize> {
        usize::try_from(self)
            .map_err(|_| IonError::decoding_error("UInt was too large to convert to a usize"))
    }

    /// Attempts to convert this `UInt` to a `u64`. If the value is too large to fit,
    /// returns an [`IonError`].
    pub fn expect_u64(&self) -> IonResult<u64> {
        u64::try_from(self)
            .map_err(|_| IonError::decoding_error("UInt was too large to convert to a u64"))
    }

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
        match &self.data {
            UIntData::U64(u64_value) => super::num_decimal_digits_in_u64(*u64_value),
            UIntData::BigUInt(big_uint_value) => UInt::calculate_big_uint_digits(big_uint_value),
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
        use UIntData::*;
        match (&self.data, &other.data) {
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
        use UIntData::*;
        match (&self.data, &other.data) {
            (U64(m1), U64(m2)) => m1.cmp(m2),
            (BigUInt(m1), BigUInt(m2)) => m1.cmp(m2),
            (U64(m1), BigUInt(m2)) => UInt::cross_representation_cmp(*m1, m2),
            (BigUInt(m1), U64(m2)) => UInt::cross_representation_cmp(*m2, m1).reverse(),
        }
    }
}

impl From<UIntData> for UInt {
    fn from(data: UIntData) -> Self {
        UInt { data }
    }
}

impl From<BigUint> for UInt {
    fn from(value: BigUint) -> Self {
        // prefer a compact representation for the magnitude
        match value.to_u64() {
            Some(unsigned) => UIntData::U64(unsigned).into(),
            None => UIntData::BigUInt(value).into(),
        }
    }
}

impl From<UInt> for BigUint {
    fn from(value: UInt) -> Self {
        use UIntData::*;
        match value.data {
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
                UIntData::U64(value as u64).into()
            }
        }
    )*)
}

impl_uint_from_small_unsigned_int_types!(u8, u16, u32, u64, usize);

macro_rules! impl_uint_try_from_small_signed_int_types {
    ($($t:ty),*) => ($(
        impl TryFrom<$t> for UInt {
            type Error = IonError;
            fn try_from(value: $t) -> Result<Self, Self::Error> {
                if value < 0 {
                    return IonResult::decoding_error("cannot convert a negative number to a UInt");
                }
                Ok((value.unsigned_abs() as u64).into())
            }
        }
    )*)
}

impl_uint_try_from_small_signed_int_types!(i8, i16, i32, i64, isize);

impl From<u128> for UInt {
    fn from(value: u128) -> UInt {
        UIntData::BigUInt(BigUint::from(value)).into()
    }
}

macro_rules! impl_int_types_try_from_uint {
    ($($t:ty),*) => ($(
        impl TryFrom<&UInt> for $t {
            type Error = IonError;

            fn try_from(value: &UInt) -> Result<Self, Self::Error> {
                match &value.data {
                    UIntData::U64(value) => <$t>::try_from(*value).map_err(|_| {
                        IonError::decoding_error(
                            concat!("UInt was too large to fit in a ", stringify!($t))
                        )
                    }),
                    UIntData::BigUInt(value) => <$t>::try_from(value).map_err(|_| {
                        IonError::decoding_error(
                            concat!("UInt was too large to fit in a ", stringify!($t))
                        )
                    }),
                }
            }
        }
    )*)
}

impl_int_types_try_from_uint!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

impl TryFrom<i128> for UInt {
    // If the i128 is negative, this will return the unit type.
    type Error = IonError;

    fn try_from(value: i128) -> Result<Self, Self::Error> {
        if value < 0 {
            IonResult::decoding_error("UInt was too large to fit in an i128")
        } else {
            Ok(value.unsigned_abs().to_biguint().unwrap().into())
        }
    }
}

impl TryFrom<Int> for UInt {
    // Returns the unit type if the input `Int` is negative.
    type Error = IonError;

    fn try_from(value: Int) -> Result<Self, Self::Error> {
        match value.data {
            IntData::I64(i) if i < 0 => {
                IonResult::decoding_error("cannot convert negative Int to a UInt")
            }
            IntData::I64(i) => Ok(i.unsigned_abs().into()),
            IntData::BigInt(i) if i.sign() == num_bigint::Sign::Minus => {
                IonResult::decoding_error("cannot convert negative Int to a UInt")
            }
            IntData::BigInt(i) => {
                // num_bigint::BigInt's `into_parts` consumes the BigInt and returns a
                // (sign: Sign, magnitude: BigUint) tuple.
                let (_, magnitude) = i.into_parts();
                Ok(magnitude.into())
            }
        }
    }
}

impl TryFrom<&Int> for UInt {
    type Error = IonError;

    fn try_from(value: &Int) -> Result<Self, Self::Error> {
        value.clone().try_into()
    }
}

macro_rules! impl_small_signed_int_try_from_int {
    ($($t:ty),*) => ($(
        impl TryFrom<Int> for $t {
            type Error = IonError;

            fn try_from(value: Int) -> Result<Self, Self::Error> {
                match value.data {
                    IntData::I64(small_int) => <$t>::try_from(small_int).map_err(|_| {
                        IonError::decoding_error(concat!("Int was too large to be converted to a(n) ", stringify!($t)))
                    }),
                    IntData::BigInt(big_int) => big_int.try_into().map_err(|_| {
                        IonError::decoding_error(concat!("Int was too large to be converted to a(n) ", stringify!($t)))
                    }),
                }
            }
        }
    )*)
}

impl_small_signed_int_try_from_int!(i8, i16, i32, i64, i128, isize);

macro_rules! impl_small_unsigned_int_try_from_uint {
    ($($t:ty),*) => ($(
        impl TryFrom<UInt> for $t {
            type Error = IonError;

            fn try_from(value: UInt) -> Result<Self, Self::Error> {
                match value.data {
                    UIntData::U64(small_uint) => <$t>::try_from(small_uint).map_err(|_| {
                        IonError::decoding_error(concat!("UInt was too large to be converted to a(n) ", stringify!($t)))
                    }),
                    UIntData::BigUInt(big_uint) => big_uint.try_into().map_err(|_| {
                        IonError::decoding_error(concat!("UInt was too large to be converted to a(n) ", stringify!($t)))
                    }),
                }
            }
        }
    )*)
}

impl_small_unsigned_int_try_from_uint!(u8, u16, u32, u64, u128, usize);

impl From<&Int> for BigInt {
    fn from(value: &Int) -> Self {
        value.clone().into()
    }
}

#[inline(never)]
fn big_integer_from_u64(value: u64) -> Int {
    IntData::BigInt(BigInt::from(value)).into()
}

#[inline(never)]
fn big_integer_from_big_uint(value: BigUint) -> Int {
    IntData::BigInt(BigInt::from(value)).into()
}

#[inline(never)]
fn big_integer_from_big_uint_ref(value: &BigUint) -> Int {
    big_integer_from_big_uint(value.clone())
}

/// Container for either an integer that can fit in a 64-bit word or an arbitrarily sized
/// [`BigInt`].
#[derive(Debug, Clone)]
pub(crate) enum IntData {
    I64(i64),
    BigInt(BigInt),
}

impl From<IntData> for Int {
    fn from(data: IntData) -> Self {
        Int { data }
    }
}

#[derive(Debug, Clone)]
/// A signed integer of arbitrary size.
/// ```
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// use ion_rs::{Element, Int};
///
/// let element = Element::read_one("-42")?;
///
/// // Access the element's integer value...
/// let int: &Int = element.expect_int()?;
/// // ...and convert it to an i64. `as_i64()` will return `None` if
/// // the Int is too large to fit in an i64.
/// assert_eq!(int.as_i64(), Some(-42i64));
///
/// // The `expect_i64()` is similar to `as_i64()`, but returns an
/// // `IonError` instead of `None` if the conversion cannot be completed.
/// assert_eq!(element.expect_i64()?, -42i64);
/// # Ok(())
/// # }
/// ```
pub struct Int {
    pub(crate) data: IntData,
}

impl Int {
    /// Returns a [`UInt`] representing the unsigned magnitude of this `Int`.
    pub(crate) fn unsigned_abs(&self) -> UInt {
        match &self.data {
            IntData::I64(i) => i.unsigned_abs().into(),
            IntData::BigInt(i) => i.abs().into_parts().1.into(),
        }
    }

    /// Returns `true` if this value is less than zero.
    /// If this value is greater than or equal to zero, returns `false`.
    pub fn is_negative(&self) -> bool {
        match &self.data {
            IntData::I64(i) => *i < 0,
            IntData::BigInt(i) => i.is_negative(),
        }
    }

    /// If this value is small enough to fit in an `i64`, returns `Ok(i64)`. Otherwise,
    /// returns a [`DecodingError`](IonError::Decoding).
    pub fn expect_i64(&self) -> IonResult<i64> {
        self.as_i64().ok_or_else(|| {
            IonError::decoding_error(format!("Int {self} is too large to fit in an i64."))
        })
    }

    /// If this value is small enough to fit in an `i64`, returns `Some(i64)`. Otherwise, returns
    /// `None`.
    pub fn as_i64(&self) -> Option<i64> {
        match &self.data {
            IntData::I64(i) => Some(*i),
            IntData::BigInt(big_int) => big_int.to_i64(),
        }
    }

    /// Compares an [i64] integer with a [BigInt] to see if they are equal. This method never
    /// allocates. It will always prefer to downgrade a BigUint and compare the two integers as
    /// u64 values. If this is not possible, then the two numbers cannot be equal anyway.
    fn cross_representation_eq(m1: i64, m2: &BigInt) -> bool {
        Int::cross_representation_cmp(m1, m2) == Ordering::Equal
    }

    /// Compares an [i64] integer with a [BigInt]. This method never allocates. It will always
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

impl PartialEq for Int {
    fn eq(&self, other: &Self) -> bool {
        use IntData::*;
        match (&self.data, &other.data) {
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
        use IntData::*;
        match &self.data {
            I64(value) => I64(-*value),
            BigInt(value) => BigInt(value.neg()),
        }
        .into()
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Self) -> Ordering {
        use IntData::*;
        match (&self.data, &other.data) {
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
        use IntData::{BigInt as Big, I64};
        match (&self.data, &rhs.data) {
            (I64(this), I64(that)) => {
                // Try to add the i64s together; if they overflow, upconvert to BigInts
                match this.checked_add(that) {
                    Some(result) => I64(result),
                    None => Big(BigInt::from(*this).add(BigInt::from(*that))),
                }
            }
            (I64(this), Big(that)) => Big(BigInt::from(*this).add(that)),
            (Big(this), I64(that)) => Big(this.add(&BigInt::from(*that))),
            (Big(this), Big(that)) => Big(this.add(that)),
        }
        .into()
    }
}

impl Zero for Int {
    fn zero() -> Self {
        IntData::I64(0).into()
    }

    fn is_zero(&self) -> bool {
        match &self.data {
            IntData::I64(value) => *value == 0i64,
            IntData::BigInt(value) => value.is_zero(),
        }
    }
}

impl Display for UInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self.data {
            UIntData::U64(i) => write!(f, "{i}"),
            UIntData::BigUInt(i) => write!(f, "{i}"),
        }
    }
}

// Trivial conversion to Int from integers that can safely be converted to an i64
macro_rules! impl_int_i64_from {
    ($($t:ty),*) => ($(
        impl From<$t> for Int {
            fn from(value: $t) -> Int {
                let i64_value = i64::from(value);
                IntData::I64(i64_value).into()
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
                    Ok(i64_value) => IntData::I64(i64_value),
                    Err(_) => IntData::BigInt(BigInt::from(value))
                }.into()
            }
        }
    )*)
}

impl_int_from!(isize, i128, usize, u64, u128);

impl From<UInt> for Int {
    fn from(value: UInt) -> Self {
        match value.data {
            UIntData::U64(uint) => {
                if let Ok(signed) = i64::try_from(uint) {
                    // The u64 was successfully converted to an i64
                    signed.into()
                } else {
                    // The u64 was slightly too big to be represented as an i64; it required the
                    // 64th bit to store the magnitude. Up-convert it to a BigInt.
                    big_integer_from_u64(uint)
                }
            }
            UIntData::BigUInt(big_uint) => big_integer_from_big_uint(big_uint),
        }
    }
}

impl From<&UInt> for Int {
    fn from(value: &UInt) -> Self {
        value.clone().into()
    }
}

impl From<BigUint> for Int {
    fn from(value: BigUint) -> Self {
        let big_int = BigInt::from(value);
        IntData::BigInt(big_int).into()
    }
}

impl From<BigInt> for Int {
    fn from(value: BigInt) -> Self {
        IntData::BigInt(value).into()
    }
}

impl From<Int> for BigInt {
    fn from(value: Int) -> Self {
        match value.data {
            IntData::I64(i) => i.into(),
            IntData::BigInt(i) => i,
        }
    }
}

impl Display for Int {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self.data {
            IntData::I64(i) => write!(f, "{i}"),
            IntData::BigInt(i) => write!(f, "{i}"),
        }
    }
}

#[cfg(test)]
mod integer_tests {
    use num_bigint::BigInt;
    use std::io::Write;

    use super::*;
    use crate::types::UInt;
    use num_bigint::BigUint;
    use num_traits::Zero;
    use rstest::*;
    use std::cmp::Ordering;
    use std::str::FromStr;

    #[test]
    fn is_zero() {
        assert!(Int::from(0).is_zero());
        assert!(Int::from(BigInt::from(0)).is_zero());
        assert!(!Int::from(55).is_zero());
        assert!(!Int::from(BigInt::from(55)).is_zero());
        assert!(!Int::from(-55).is_zero());
        assert!(!Int::from(BigInt::from(-55)).is_zero());
    }

    #[test]
    fn zero() {
        assert!(Int::zero().is_zero());
    }

    #[test]
    fn add() {
        assert_eq!(Int::from(0) + Int::from(0), Int::from(0));
        assert_eq!(Int::from(5) + Int::from(7), Int::from(12));
        assert_eq!(Int::from(-5) + Int::from(7), Int::from(2));
        assert_eq!(
            Int::from(100) + Int::from(BigInt::from(1000)),
            Int::from(BigInt::from(1100))
        );
        assert_eq!(
            Int::from(BigInt::from(100)) + Int::from(1000),
            Int::from(BigInt::from(1100))
        );
        assert_eq!(
            Int::from(BigInt::from(100)) + Int::from(BigInt::from(1000)),
            Int::from(BigInt::from(1100))
        );
    }

    #[rstest]
    #[case::i64(5.into(), 4.into(), Ordering::Greater)]
    #[case::i64_equal(Int::from(-5), Int::from(-5), Ordering::Equal)]
    #[case::i64_gt_big_int(Int::from(4), Int::from(BigInt::from(3)), Ordering::Greater)]
    #[case::i64_eq_big_int(Int::from(3), Int::from(BigInt::from(3)), Ordering::Equal)]
    #[case::i64_lt_big_int(Int::from(-3), Int::from(BigInt::from(5)), Ordering::Less)]
    #[case::big_int(
        Int::from(BigInt::from(1100)),
        Int::from(BigInt::from(-1005)),
        Ordering::Greater
    )]
    #[case::big_int(
        Int::from(BigInt::from(1100)),
        Int::from(BigInt::from(1100)),
        Ordering::Equal
    )]
    fn integer_ordering_tests(#[case] this: Int, #[case] other: Int, #[case] expected: Ordering) {
        assert_eq!(this.cmp(&other), expected)
    }

    #[rstest]
    #[case::u64(UInt::from(5u64), UInt::from(4u64), Ordering::Greater)]
    #[case::u64_equal(UInt::from(5u64), UInt::from(5u64), Ordering::Equal)]
    #[case::u64_gt_big_uint(UInt::from(4u64), UInt::from(BigUint::from(3u64)), Ordering::Greater)]
    #[case::u64_lt_big_uint(UInt::from(3u64), UInt::from(BigUint::from(5u64)), Ordering::Less)]
    #[case::u64_eq_big_uint(UInt::from(3u64), UInt::from(BigUint::from(3u64)), Ordering::Equal)]
    #[case::big_uint(
        UInt::from(BigUint::from(1100u64)),
        UInt::from(BigUint::from(1005u64)),
        Ordering::Greater
    )]
    #[case::big_uint(
        UInt::from(BigUint::from(1005u64)),
        UInt::from(BigUint::from(1005u64)),
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
    #[case(UInt::from(1u64), 1)] // only one test case for U64 as that's delegated to another impl
    #[case(UInt::from(BigUint::from(0u64)), 1)]
    #[case(UInt::from(BigUint::from(1u64)), 1)]
    #[case(UInt::from(BigUint::from(10u64)), 2)]
    #[case(UInt::from(BigUint::from(3117u64)), 4)]
    fn uint_decimal_digits_test(#[case] uint: UInt, #[case] expected: i32) {
        assert_eq!(uint.number_of_decimal_digits(), expected as u64)
    }

    #[rstest]
    #[case(Int::from(5), "5")]
    #[case(Int::from(-5), "-5")]
    #[case(Int::from(0), "0")]
    #[case(Int::from(BigInt::from(1100)), "1100")]
    #[case(Int::from(BigInt::from(-1100)), "-1100")]
    fn int_display_test(#[case] value: Int, #[case] expect: String) {
        let mut buf = Vec::new();
        write!(&mut buf, "{value}").unwrap();
        assert_eq!(expect, String::from_utf8(buf).unwrap());
    }

    #[rstest]
    #[case(UInt::from(5u64), "5")]
    #[case(UInt::from(0u64), "0")]
    #[case(UInt::from(BigUint::from(0u64)), "0")]
    #[case(UInt::from(BigUint::from(1100u64)), "1100")]
    fn uint_display_test(#[case] value: UInt, #[case] expect: String) {
        let mut buf = Vec::new();
        write!(&mut buf, "{value}").unwrap();
        assert_eq!(expect, String::from_utf8(buf).unwrap());
    }

    #[test]
    fn u8_from_uint() {
        assert_eq!(u8::try_from(UInt::from(0u64)), Ok(0u8));
        assert_eq!(u8::try_from(UInt::from(21u64)), Ok(21u8));
        assert_eq!(u8::try_from(UInt::from(255u64)), Ok(255u8));
        assert_eq!(u8::try_from(UInt::from(BigUint::from(255u64))), Ok(255u8));
        assert!(u8::try_from(UInt::from(999u64)).is_err())
    }

    #[test]
    fn u16_from_uint() {
        assert_eq!(u16::try_from(UInt::from(0u64)), Ok(0u16));
        assert_eq!(u16::try_from(UInt::from(999u64)), Ok(999u16));
        assert_eq!(u16::try_from(UInt::from(16500u64)), Ok(16500u16));
        assert_eq!(
            u16::try_from(UInt::from(BigUint::from(16500u64))),
            Ok(16500u16)
        );
        assert!(u16::try_from(UInt::from(128_000u64)).is_err())
    }

    #[test]
    fn u32_from_uint() {
        assert_eq!(u32::try_from(UInt::from(0u64)), Ok(0u32));
        assert_eq!(u32::try_from(UInt::from(16500u64)), Ok(16500u32));
        assert_eq!(u32::try_from(UInt::from(128_000u64)), Ok(128_000u32));
        assert_eq!(
            u32::try_from(UInt::from(BigUint::from(128_000u64))),
            Ok(128_000u32)
        );
        assert!(u32::try_from(UInt::from(5_000_000_000u64)).is_err())
    }

    #[test]
    fn u64_from_uint() {
        assert_eq!(u64::try_from(UInt::from(0u64)), Ok(0u64));
        assert_eq!(u64::try_from(UInt::from(128_000u64)), Ok(128_000u64));
        assert_eq!(
            u64::try_from(UInt::from(5_000_000_000u64)),
            Ok(5_000_000_000u64)
        );
        assert!(u64::try_from(UInt::from(
            BigUint::from_str("1_000_000_000_000_000_000_000_000_000_000").unwrap()
        ))
        .is_err())
    }

    #[test]
    fn usize_from_uint() {
        assert_eq!(usize::try_from(UInt::from(0u64)), Ok(0usize));
        assert_eq!(usize::try_from(UInt::from(16500u64)), Ok(16500usize));
        assert_eq!(usize::try_from(UInt::from(128_000u64)), Ok(128_000usize));
        assert_eq!(
            usize::try_from(UInt::from(BigUint::from(128_000u64))),
            Ok(128_000usize)
        );
        assert!(usize::try_from(UInt::from(
            BigUint::from_str("1_000_000_000_000_000_000_000_000_000_000").unwrap()
        ))
        .is_err())
    }

    #[test]
    fn as_usize() {
        assert_eq!(UInt::from(128_000u64).as_usize(), Some(128_000usize));
        assert_eq!(
            UInt::from(BigUint::from(128_000u64)).as_usize(),
            Some(128_000usize)
        );
        assert!(
            UInt::from(BigUint::from_str("1_000_000_000_000_000_000_000_000_000_000").unwrap())
                .as_usize()
                .is_none()
        )
    }

    #[test]
    fn expect_usize() {
        assert_eq!(UInt::from(128_000u64).expect_usize(), Ok(128_000usize));
        assert_eq!(
            UInt::from(BigUint::from(128_000u64)).expect_usize(),
            Ok(128_000usize)
        );
        assert!(
            UInt::from(BigUint::from_str("1_000_000_000_000_000_000_000_000_000_000").unwrap())
                .expect_usize()
                .is_err()
        )
    }

    #[test]
    fn as_u64() {
        assert_eq!(UInt::from(128_000u64).as_u64(), Some(128_000u64));
        assert_eq!(
            UInt::from(BigUint::from(128_000u64)).as_u64(),
            Some(128_000u64)
        );
        assert!(
            UInt::from(BigUint::from_str("1_000_000_000_000_000_000_000_000_000_000").unwrap())
                .as_u64()
                .is_none()
        )
    }

    #[test]
    fn expect_u64() {
        assert_eq!(UInt::from(128_000u64).expect_u64(), Ok(128_000u64));
        assert_eq!(
            UInt::from(BigUint::from(128_000u64)).expect_u64(),
            Ok(128_000u64)
        );
        assert!(
            UInt::from(BigUint::from_str("1_000_000_000_000_000_000_000_000_000_000").unwrap())
                .expect_u64()
                .is_err()
        )
    }
}
