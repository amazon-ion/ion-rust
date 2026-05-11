mod big_small;
mod int_data;

use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::result::IonFailure;
use crate::types::CountDecimalDigits;
use crate::{IonError, IonResult};
use big_small::AsBigOrSmallValue;
pub(crate) use int_data::{IntData, UIntData};
use num_bigint::BigInt;
use num_traits::Zero;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::{Add, Neg, Sub};

/// Represents an unsigned integer of any size.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UInt {
    pub(crate) data: UIntData,
}

impl UInt {
    pub const ZERO: UInt = UInt {
        data: UIntData::ZERO,
    };

    #[inline]
    pub(crate) fn new(data: impl Into<u128>) -> Self {
        Self {
            data: UIntData::from(data.into()),
        }
    }

    pub(crate) fn from_str_radix(s: &str, radix: u32) -> IonResult<Self> {
        let data = UIntData::from_str_radix(s, radix)?;
        Ok(Self { data })
    }

    pub(crate) fn from_be_bytes(bytes: &[u8]) -> UInt {
        let data = UIntData::from_be_bytes(bytes);
        Self { data }
    }

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

    /// Attempts to convert this `UInt` to a `u128`. If the value is too large to fit,
    /// returns `None`.
    pub fn as_u128(&self) -> Option<u128> {
        u128::try_from(self).ok()
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

    /// Attempts to convert this `UInt` to a `u128`. If the value is too large to fit,
    /// returns an [`IonError`].
    pub fn expect_u128(&self) -> IonResult<u128> {
        u128::try_from(self)
            .map_err(|_| IonError::decoding_error("UInt was too large to convert to a u128"))
    }

    /// Returns the number of digits in the base-10 representation of the UInteger.
    pub fn number_of_decimal_digits(&self) -> u32 {
        self.data.count_decimal_digits()
    }

    pub fn from_le_bytes(bytes: &[u8]) -> UInt {
        UInt {
            data: UIntData::from_le_bytes(bytes),
        }
    }

    pub fn to_le_bytes(&self) -> Vec<u8> {
        self.data.to_le_bytes()
    }
}

impl From<UIntData> for UInt {
    fn from(value: UIntData) -> Self {
        UInt { data: value }
    }
}

// This macro makes it possible to turn unsigned int primitives into a UInteger using `.into()`.
// Note that it works for both signed and unsigned ints. The resulting UInteger will be the
// absolute value of the integer being converted.
macro_rules! impl_uint_from_unsigned_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for UInt {
            #[inline]
            fn from(value: $t) -> UInt {
                UInt::new(value)
            }
        }
    )*)
}

impl_uint_from_unsigned_int_types!(u8, u16, u32, u64, u128);

impl From<usize> for UInt {
    #[inline]
    fn from(value: usize) -> Self {
        debug_assert!(
            mem::size_of::<usize>() <= mem::size_of::<u128>(),
            "usize cannot be cast to u128 safely on this platform"
        );
        UInt::new(value as u128)
    }
}

macro_rules! impl_uint_try_from_signed_int_types {
    ($($t:ty),*) => ($(
        impl TryFrom<$t> for UInt {
            type Error = IonError;
            fn try_from(value: $t) -> Result<Self, Self::Error> {
                if value.is_negative() {
                    return IonResult::decoding_error("cannot convert a negative number to a UInt");
                }
                Ok(UInt::from(value.unsigned_abs()))
            }
        }
    )*)
}

impl_uint_try_from_signed_int_types!(i8, i16, i32, i64, i128, isize);

macro_rules! impl_int_types_try_from_uint {
    ($($t:ty),*) => ($(
        impl TryFrom<&UInt> for $t {
            type Error = IonError;

            fn try_from(value: &UInt) -> Result<Self, Self::Error> {
                <$t>::try_from(value.clone().data).map_err(|_| {
                    IonError::decoding_error(
                            concat!("UInt was too large to fit in a ", stringify!($t))
                        )
                })
            }
        }
    )*)
}

impl_int_types_try_from_uint!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

impl TryFrom<Int> for UInt {
    // Returns the unit type if the input `Int` is negative.
    type Error = IonError;

    fn try_from(value: Int) -> Result<Self, Self::Error> {
        if value.data.is_negative() {
            return IonResult::decoding_error("cannot convert negative Int to a UInt");
        }
        Ok(value.data.unsigned_abs().into())
    }
}

impl TryFrom<&Int> for UInt {
    type Error = IonError;

    fn try_from(value: &Int) -> Result<Self, Self::Error> {
        value.clone().try_into()
    }
}

impl From<&UInt> for UInt {
    fn from(value: &UInt) -> Self {
        value.clone()
    }
}

impl From<&Int> for Int {
    fn from(value: &Int) -> Self {
        value.clone()
    }
}

macro_rules! impl_small_int_try_from_int {
    ($($t:ty),*) => ($(
        impl TryFrom<Int> for $t {
            type Error = IonError;

            fn try_from(value: Int) -> Result<Self, Self::Error> {
                <$t>::try_from(value.data).map_err(|_| {
                    IonError::decoding_error(concat!("Int was outside the range of a(n) ", stringify!($t)))
                })
            }
        }
    )*)
}

impl_small_int_try_from_int!(i8, i16, i32, i64, i128, isize);
impl_small_int_try_from_int!(u8, u16, u32, u64, u128, usize);

macro_rules! impl_small_unsigned_int_try_from_uint {
    ($($t:ty),*) => ($(
        impl TryFrom<UInt> for $t {
            type Error = IonError;

            fn try_from(value: UInt) -> Result<Self, Self::Error> {
                <$t>::try_from(value.data).map_err(|_| {
                    IonError::decoding_error(concat!("UInt was outside the range of a(n) ", stringify!($t)))
                })
            }
        }
    )*)
}

impl_small_unsigned_int_try_from_uint!(u8, u16, u32, u64, u128, usize);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub const ZERO: Int = Int {
        data: IntData::ZERO,
    };

    #[allow(unused)]
    pub(crate) fn new(data: impl Into<i128>) -> Self {
        Self {
            data: IntData::from(data.into()),
        }
    }

    /// Returns a [`UInt`] representing the unsigned magnitude of this `Int`.
    pub fn unsigned_abs(&self) -> UInt {
        self.data.unsigned_abs().into()
    }

    /// Returns `true` if this value is less than zero.
    /// If this value is greater than or equal to zero, returns `false`.
    pub fn is_negative(&self) -> bool {
        self.data.is_negative()
    }

    /// If this value is small enough to fit in an `i64`, returns `Ok(i64)`. Otherwise,
    /// returns a [`DecodingError`](IonError::Decoding).
    #[inline]
    pub fn expect_i64(&self) -> IonResult<i64> {
        self.as_i64().ok_or_else(
            #[inline(never)]
            || IonError::decoding_error(format!("Int {self} was not in the range of an i64.")),
        )
    }

    #[inline(always)]
    pub fn as_u32(&self) -> Option<u32> {
        u32::try_from(&self.data).ok()
    }

    #[inline]
    pub fn expect_u32(&self) -> IonResult<u32> {
        self.as_u32().ok_or_else(
            #[inline(never)]
            || IonError::decoding_error(format!("Int {self} was not in the range of a u32.")),
        )
    }

    #[inline(always)]
    pub fn as_u64(&self) -> Option<u64> {
        u64::try_from(&self.data).ok()
    }

    #[inline]
    pub fn expect_u64(&self) -> IonResult<u64> {
        self.as_u64().ok_or_else(
            #[inline(never)]
            || IonError::decoding_error(format!("Int {self} was not in the range of a u64.")),
        )
    }

    #[inline(always)]
    pub fn as_usize(&self) -> Option<usize> {
        usize::try_from(&self.data).ok()
    }

    #[inline]
    pub fn expect_usize(&self) -> IonResult<usize> {
        self.as_usize().ok_or_else(
            #[inline(never)]
            || IonError::decoding_error(format!("Int {self} was not in the range of a usize.")),
        )
    }

    /// If this value is small enough to fit in an `i128`, returns `Ok(i128)`. Otherwise,
    /// returns a [`DecodingError`](IonError::Decoding).
    pub fn expect_i128(&self) -> IonResult<i128> {
        self.as_i128().ok_or_else(|| {
            IonError::decoding_error(format!("Int {self} was not in the range of an i128."))
        })
    }

    /// If this value is small enough to fit in an `i64`, returns `Some(i64)`. Otherwise, returns
    /// `None`.
    pub fn as_i64(&self) -> Option<i64> {
        i64::try_from(&self.data).ok()
    }

    /// If this value is small enough to fit in an `i128`, returns `Some(i128)`. Otherwise, returns
    /// `None`.
    pub fn as_i128(&self) -> Option<i128> {
        i128::try_from(&self.data).ok()
    }

    pub fn from_le_signed_bytes(bytes: &[u8]) -> Int {
        Int {
            data: IntData::from_le_signed_bytes(bytes),
        }
    }

    pub fn to_le_signed_bytes(&self) -> Vec<u8> {
        self.data.to_le_bytes()
    }

    #[cfg_attr(not(feature = "bigdecimal"), allow(dead_code))]
    // Only used for bigdecimal conversion.
    pub(crate) fn to_bigint(&self) -> BigInt {
        self.data.as_big_value().into_owned()
    }
}

impl IonEq for Int {
    fn ion_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl IonDataOrd for Int {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}

impl IonDataHash for Int {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.hash(state)
    }
}

impl Neg for Int {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.data.neg().into()
    }
}

impl Add<Self> for Int {
    type Output = Int;

    fn add(self, rhs: Self) -> Self::Output {
        self.data.add(rhs.data).into()
    }
}

impl Sub<Self> for Int {
    type Output = Int;

    fn sub(self, rhs: Self) -> Self::Output {
        self.data.sub(rhs.data).into()
    }
}

impl Zero for Int {
    fn zero() -> Self {
        Int {
            data: IntData::ZERO,
        }
    }

    fn is_zero(&self) -> bool {
        self.data == IntData::ZERO
    }
}

impl Add<Self> for UInt {
    type Output = UInt;

    fn add(self, rhs: Self) -> Self::Output {
        self.data.add(rhs.data).into()
    }
}

impl Sub<Self> for UInt {
    type Output = UInt;

    fn sub(self, rhs: Self) -> Self::Output {
        self.data.sub(rhs.data).into()
    }
}

impl Zero for UInt {
    fn zero() -> Self {
        UInt {
            data: UIntData::ZERO,
        }
    }

    fn is_zero(&self) -> bool {
        self.data == UIntData::ZERO
    }
}

impl CountDecimalDigits for Int {
    fn count_decimal_digits(self) -> u32 {
        self.data.count_decimal_digits()
    }
}

impl CountDecimalDigits for UInt {
    fn count_decimal_digits(self) -> u32 {
        self.data.count_decimal_digits()
    }
}

impl Display for UInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.data)
    }
}

impl<T> From<T> for Int
where
    T: Into<IntData>,
{
    fn from(value: T) -> Self {
        Self { data: value.into() }
    }
}

impl From<UInt> for IntData {
    fn from(value: UInt) -> Self {
        value.data.into()
    }
}

impl From<&UInt> for Int {
    fn from(value: &UInt) -> Self {
        IntData::from(value.data.clone()).into()
    }
}

impl Display for Int {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.data)
    }
}

#[cfg(test)]
mod integer_tests {
    use std::io::Write;

    use super::*;
    use crate::types::UInt;
    use num_traits::Zero;
    use rstest::*;
    use std::cmp::Ordering;

    #[test]
    fn is_zero() {
        assert!(Int::from(0).is_zero());
        assert!(Int::from(0i128).is_zero());
        assert!(!Int::from(55).is_zero());
        assert!(!Int::from(55i128).is_zero());
        assert!(!Int::from(-55).is_zero());
        assert!(!Int::from(-55i128).is_zero());
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
        assert_eq!(Int::from(100) + Int::from(1000i128), Int::from(1100i128));
        assert_eq!(Int::from(100i128) + Int::from(1000), Int::from(1100i128));
        assert_eq!(
            Int::from(100i128) + Int::from(1000i128),
            Int::from(1100i128)
        );
    }

    #[test]
    fn sub() {
        assert_eq!(Int::from(0) - Int::from(0), Int::from(0));
        assert_eq!(Int::from(5) - Int::from(7), Int::from(-2));
        assert_eq!(Int::from(-5) - Int::from(7), Int::from(-12));
        assert_eq!(Int::from(100) - Int::from(1000i128), Int::from(-900i128));
        assert_eq!(Int::from(100i128) - Int::from(1000), Int::from(-900i128));
        assert_eq!(
            Int::from(100i128) - Int::from(1000i128),
            Int::from(-900i128)
        );
    }

    #[rstest]
    #[case::i64(5.into(), 4.into(), Ordering::Greater)]
    #[case::i64_equal(Int::from(-5), Int::from(-5), Ordering::Equal)]
    #[case::i64_gt_big_int(Int::from(4), Int::from(3i128), Ordering::Greater)]
    #[case::i64_eq_big_int(Int::from(3), Int::from(3i128), Ordering::Equal)]
    #[case::i64_lt_big_int(Int::from(-3), Int::from(5i128), Ordering::Less)]
    #[case::big_int(
        Int::from(1100i128),
        Int::from(-1005i128),
        Ordering::Greater
    )]
    #[case::big_int(Int::from(1100i128), Int::from(1100i128), Ordering::Equal)]
    #[case::big_int_lt_i64(Int::from(-9223372036854775809i128), Int::from(0), Ordering::Less)]
    #[case::big_int_gt_i64(Int::from(9223372036854775809i128), Int::from(0), Ordering::Greater)]
    #[case::i64_gt_big_int_i128(Int::from(0), Int::from(9223372036854775809i128), Ordering::Less)]
    #[case::i64_lt_big_int_i128(Int::from(0), Int::from(-9223372036854775809i128),  Ordering::Greater)]
    fn integer_ordering_tests(#[case] this: Int, #[case] other: Int, #[case] expected: Ordering) {
        assert_eq!(this.cmp(&other), expected)
    }

    #[rstest]
    #[case::u64(UInt::from(5u64), UInt::from(4u64), Ordering::Greater)]
    #[case::u64_equal(UInt::from(5u64), UInt::from(5u64), Ordering::Equal)]
    #[case::u64_gt_big_uint(UInt::from(4u64), UInt::from(3u128), Ordering::Greater)]
    #[case::u64_lt_big_uint(UInt::from(3u64), UInt::from(5u128), Ordering::Less)]
    #[case::u64_eq_big_uint(UInt::from(3u64), UInt::from(3u128), Ordering::Equal)]
    #[case::big_uint(UInt::from(1100u128), UInt::from(1005u128), Ordering::Greater)]
    #[case::big_uint(UInt::from(1005u128), UInt::from(1005u128), Ordering::Equal)]
    fn unsigned_integer_ordering_tests(
        #[case] this: UInt,
        #[case] other: UInt,
        #[case] expected: Ordering,
    ) {
        assert_eq!(this.cmp(&other), expected)
    }

    #[rstest]
    #[case(UInt::from(1u64), 1)] // only one test case for U64 as that's delegated to another impl
    #[case(UInt::from(0u128), 1)]
    #[case(UInt::from(1u128), 1)]
    #[case(UInt::from(10u128), 2)]
    #[case(UInt::from(3117u128), 4)]
    fn uint_decimal_digits_test(#[case] uint: UInt, #[case] expected: u32) {
        assert_eq!(uint.number_of_decimal_digits(), expected)
    }

    #[rstest]
    #[case(Int::from(5), "5")]
    #[case(Int::from(-5), "-5")]
    #[case(Int::from(0), "0")]
    #[case(Int::from(1100i128), "1100")]
    #[case(Int::from(-1100i128), "-1100")]
    fn int_display_test(#[case] value: Int, #[case] expect: String) {
        let mut buf = Vec::new();
        write!(&mut buf, "{value}").unwrap();
        assert_eq!(expect, String::from_utf8(buf).unwrap());
    }

    #[rstest]
    #[case(UInt::from(5u64), "5")]
    #[case(UInt::from(0u64), "0")]
    #[case(UInt::from(0u128), "0")]
    #[case(UInt::from(1100u128), "1100")]
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
        assert_eq!(u8::try_from(UInt::from(255u128)), Ok(255u8));
        assert!(u8::try_from(UInt::from(999u64)).is_err())
    }

    #[test]
    fn u16_from_uint() {
        assert_eq!(u16::try_from(UInt::from(0u64)), Ok(0u16));
        assert_eq!(u16::try_from(UInt::from(999u64)), Ok(999u16));
        assert_eq!(u16::try_from(UInt::from(16500u64)), Ok(16500u16));
        assert_eq!(u16::try_from(UInt::from(16500u128)), Ok(16500u16));
        assert!(u16::try_from(UInt::from(128_000u64)).is_err())
    }

    #[test]
    fn u32_from_uint() {
        assert_eq!(u32::try_from(UInt::from(0u64)), Ok(0u32));
        assert_eq!(u32::try_from(UInt::from(16500u64)), Ok(16500u32));
        assert_eq!(u32::try_from(UInt::from(128_000u64)), Ok(128_000u32));
        assert_eq!(u32::try_from(UInt::from(128_000u128)), Ok(128_000u32));
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
        assert!(u64::try_from(UInt::from(u128::MAX)).is_err())
    }

    #[test]
    fn usize_from_uint() {
        assert_eq!(usize::try_from(UInt::from(0u64)), Ok(0usize));
        assert_eq!(usize::try_from(UInt::from(16500u64)), Ok(16500usize));
        assert_eq!(usize::try_from(UInt::from(128_000u64)), Ok(128_000usize));
        assert_eq!(usize::try_from(UInt::from(128_000u128)), Ok(128_000usize));
        assert!(usize::try_from(UInt::from(u128::MAX)).is_err())
    }

    #[test]
    fn as_usize() {
        assert_eq!(UInt::from(128_000u64).as_usize(), Some(128_000usize));
        assert_eq!(UInt::from(128_000u128).as_usize(), Some(128_000usize));
        assert!(UInt::from(u128::MAX).as_usize().is_none())
    }

    #[test]
    fn expect_usize() {
        assert_eq!(UInt::from(128_000u64).expect_usize(), Ok(128_000usize));
        assert_eq!(UInt::from(128_000u128).expect_usize(), Ok(128_000usize));
        assert!(UInt::from(u128::MAX).expect_usize().is_err())
    }

    #[test]
    fn as_u64() {
        assert_eq!(UInt::from(128_000u64).as_u64(), Some(128_000u64));
        assert_eq!(UInt::from(128_000u128).as_u64(), Some(128_000u64));
        assert!(UInt::from(u128::MAX).as_u64().is_none())
    }

    #[test]
    fn expect_u64() {
        assert_eq!(UInt::from(128_000u64).expect_u64(), Ok(128_000u64));
        assert_eq!(UInt::from(128_000u128).expect_u64(), Ok(128_000u64));
        assert!(UInt::from(u128::MAX).expect_u64().is_err())
    }

    #[test]
    fn int_as_u64() {
        assert_eq!(Int::from(128_000i64).as_u64(), Some(128_000u64));
        assert_eq!(Int::from(0i64).as_u64(), Some(0u64));
        assert!(Int::from(-1i64).as_u64().is_none());
        assert!(Int::from(i128::MAX).as_u64().is_none());
    }

    #[test]
    fn int_expect_u64() {
        assert_eq!(Int::from(128_000i64).expect_u64(), Ok(128_000u64));
        assert_eq!(Int::from(0i64).expect_u64(), Ok(0u64));
        assert!(Int::from(-1i64).expect_u64().is_err());
        assert!(Int::from(i128::MAX).expect_u64().is_err());
    }

    // ===== Big value tests =====

    #[test]
    fn int_from_signed_bytes_le_big() {
        // 2^128 as signed LE: 17 bytes
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let big = Int::from_le_signed_bytes(&bytes);
        assert!(big.as_i128().is_none());
        assert!(!big.is_negative());
        assert!(!big.is_zero());
        assert_eq!(big.to_string(), "340282366920938463463374607431768211456");
    }

    #[test]
    fn uint_from_bytes_le_big() {
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let big = UInt::from_le_bytes(&bytes);
        assert!(big.as_u128().is_none());
        assert!(!big.is_zero());
        assert_eq!(big.to_string(), "340282366920938463463374607431768211456");
    }

    #[test]
    fn int_neg_big() {
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let big = Int::from_le_signed_bytes(&bytes);
        let neg = -big;
        assert!(neg.is_negative());
        assert_eq!(neg.to_string(), "-340282366920938463463374607431768211456");
    }

    #[test]
    fn int_from_bytes_roundtrip() {
        for v in [0i128, 1, -1, 42, -42, i128::MAX, i128::MIN] {
            let int = Int::from(v);
            let bytes = int.data.to_le_bytes();
            let roundtripped = Int::from_le_signed_bytes(&bytes);
            assert_eq!(int, roundtripped, "roundtrip failed for {v}");
        }
    }

    // ===== Cross-representation comparison tests (AC5a) =====

    #[test]
    fn int_cross_repr_eq() {
        let inline = Int::from(42i64);
        let also_inline = Int::from(42i64);
        assert_eq!(inline, also_inline);

        // Two big values that are equal
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let big1 = Int::from_le_signed_bytes(&bytes);
        let big2 = Int::from_le_signed_bytes(&bytes);
        assert_eq!(big1, big2);

        // Inline != heap
        assert_ne!(inline, big1);
    }

    #[test]
    fn int_cross_repr_ord() {
        let small = Int::from(42i64);
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let big = Int::from_le_signed_bytes(&bytes);

        // Inline < heap (positive)
        assert!(small < big);
        assert!(big > small);

        // Negative heap < inline
        let neg_big = -Int::from_le_signed_bytes(&bytes);
        assert!(neg_big < small);
        assert!(small > neg_big);
    }

    #[test]
    fn int_cross_repr_hash_consistent() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let hash = |v: &Int| {
            let mut h = DefaultHasher::new();
            v.hash(&mut h);
            h.finish()
        };

        // Equal values must have equal hashes
        let a = Int::from(42i64);
        let b = Int::from(42i64);
        assert_eq!(hash(&a), hash(&b));

        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let c = Int::from_le_signed_bytes(&bytes);
        let d = Int::from_le_signed_bytes(&bytes);
        assert_eq!(hash(&c), hash(&d));
    }

    #[test]
    fn int_ion_eq_and_ion_data_hash() {
        use crate::ion_data::{IonDataHash, IonEq};
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;

        let a = Int::from(42i64);
        let b = Int::from(42i64);
        assert!(a.ion_eq(&b));

        let ion_hash = |v: &Int| {
            let mut h = DefaultHasher::new();
            v.ion_data_hash(&mut h);
            h.finish()
        };
        assert_eq!(ion_hash(&a), ion_hash(&b));
    }

    #[test]
    fn uint_cross_repr_ord() {
        let small = UInt::from(42u64);
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let big = UInt::from_le_bytes(&bytes);
        assert!(small < big);
        assert!(big > small);
    }
}
