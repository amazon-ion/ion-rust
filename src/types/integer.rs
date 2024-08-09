use crate::ion_data::{IonEq, IonOrd};
use crate::result::IonFailure;
use crate::types::CountDecimalDigits;
use crate::{IonError, IonResult};
use num_traits::Zero;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::mem;
use std::ops::{Add, Neg};

/// Represents an unsigned integer of any size.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UInt {
    pub(crate) data: u128,
}

impl UInt {
    pub const ZERO: UInt = UInt { data: 0u128 };

    #[inline]
    pub(crate) fn new(data: impl Into<u128>) -> Self {
        Self { data: data.into() }
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
        Some(self.data)
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
    pub(crate) fn number_of_decimal_digits(&self) -> u32 {
        self.data.count_decimal_digits()
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
                <$t>::try_from(value.data).map_err(|_| {
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
        (*value).try_into()
    }
}

impl From<&UInt> for UInt {
    fn from(value: &UInt) -> Self {
        *value
    }
}

impl From<&Int> for Int {
    fn from(value: &Int) -> Self {
        *value
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub(crate) data: i128,
}

impl Int {
    pub const ZERO: Int = Int { data: 0i128 };

    pub(crate) fn new(data: impl Into<i128>) -> Self {
        Self { data: data.into() }
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
            || IonError::decoding_error(format!("Int {self} is too large to fit in an i64.")),
        )
    }

    #[inline(always)]
    pub fn as_u32(&self) -> Option<u32> {
        u32::try_from(self.data).ok()
    }

    #[inline]
    pub fn expect_u32(&self) -> IonResult<u32> {
        self.as_u32().ok_or_else(
            #[inline(never)]
            || IonError::decoding_error(format!("Int {self} is too large to fit in a u32.")),
        )
    }

    /// If this value is small enough to fit in an `i128`, returns `Ok(i128)`. Otherwise,
    /// returns a [`DecodingError`](IonError::Decoding).
    pub fn expect_i128(&self) -> IonResult<i128> {
        self.as_i128().ok_or_else(|| {
            IonError::decoding_error(format!("Int {self} is too large to fit in an i128."))
        })
    }

    /// If this value is small enough to fit in an `i64`, returns `Some(i64)`. Otherwise, returns
    /// `None`.
    pub fn as_i64(&self) -> Option<i64> {
        i64::try_from(self.data).ok()
    }

    /// If this value is small enough to fit in an `i128`, returns `Some(i128)`. Otherwise, returns
    /// `None`.
    pub fn as_i128(&self) -> Option<i128> {
        Some(self.data)
    }
}
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
        self.data.neg().into()
    }
}

impl Add<Self> for Int {
    type Output = Int;

    fn add(self, rhs: Self) -> Self::Output {
        self.data.add(rhs.data).into()
    }
}

impl Zero for Int {
    fn zero() -> Self {
        Int { data: 0i128 }
    }

    fn is_zero(&self) -> bool {
        self.data == 0
    }
}

impl Add<Self> for UInt {
    type Output = UInt;

    fn add(self, rhs: Self) -> Self::Output {
        self.data.add(rhs.data).into()
    }
}

impl Zero for UInt {
    fn zero() -> Self {
        UInt { data: 0u128 }
    }

    fn is_zero(&self) -> bool {
        self.data == 0
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

// Trivial conversion to Int from integers that can safely be converted to an i128
macro_rules! impl_int_i128_from {
    ($($t:ty),*) => ($(
        impl From<$t> for Int {
            fn from(value: $t) -> Int {
                Int {data: value as i128 }
            }
        }
    )*)
}
impl_int_i128_from!(u8, u16, u32, u64, usize, i8, i16, i32, i64, i128, isize);

// Conversion to Integer from integer types that may or may not fit in an i128
macro_rules! impl_int_try_from {
    ($($t:ty),*) => ($(
        impl TryFrom<$t> for Int {
            type Error = IonError;
            fn try_from(value: $t) -> Result<Self, Self::Error> {
                match i128::try_from(value) {
                    Ok(i128_value) => Ok(i128_value.into()),
                    Err(e) => IonResult::decoding_error(format!("could not safely convert value {} of type '{}' to Int: {e:?}", value, stringify!($t))),
                }
            }
        }
    )*)
}

impl_int_try_from!(u128);

impl TryFrom<UInt> for Int {
    type Error = IonError;

    fn try_from(value: UInt) -> Result<Self, Self::Error> {
        i128::try_from(value.data)
            .map_err(|_| IonError::decoding_error("UInt was outside the supported Int range"))
            .map(Int::new)
    }
}

impl TryFrom<&UInt> for Int {
    type Error = IonError;

    fn try_from(value: &UInt) -> Result<Self, Self::Error> {
        value.data.try_into()
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
}
