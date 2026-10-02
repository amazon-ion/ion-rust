use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::result::IonFailure;
use crate::types::decimal::Sign;
use crate::types::overflowing_int::{ByteOrder, Magnitude, OverflowingInt};
use crate::{IonError, IonResult};
use ice_code::ice as cold_path;
use num_bigint::BigInt;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::mem;

/// Represents an unsigned integer of any size.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UInt {
    // Never negative: every constructor takes an unsigned magnitude.
    repr: OverflowingInt,
}

impl UInt {
    pub const ZERO: UInt = UInt {
        repr: OverflowingInt::ZERO,
    };

    #[inline]
    pub(crate) fn new(value: impl Into<u128>) -> Self {
        Self {
            repr: OverflowingInt::from(value.into()),
        }
    }

    pub(crate) fn from_str_radix(s: &str, radix: u32) -> IonResult<Self> {
        OverflowingInt::from_str_radix(s, radix)
            .map(|repr| Self { repr })
            .ok_or_else(|| IonError::decoding_error("Invalid UInt"))
    }

    pub(crate) fn from_be_bytes(bytes: &[u8]) -> UInt {
        Self {
            repr: OverflowingInt::from_unsigned_bytes(bytes, ByteOrder::Big),
        }
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
        self.repr.magnitude_ref().number_of_decimal_digits()
    }

    pub fn from_le_bytes(bytes: &[u8]) -> UInt {
        Self {
            repr: OverflowingInt::from_unsigned_bytes(bytes, ByteOrder::Little),
        }
    }

    pub fn to_le_bytes(&self) -> Vec<u8> {
        self.repr.magnitude_le_bytes()
    }

    /// Returns `true` if this value is zero.
    pub fn is_zero(&self) -> bool {
        self.repr.is_zero()
    }
}

// This macro makes it possible to turn unsigned int primitives into a UInteger using `.into()`.
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
                value.repr.to_primitive().ok_or_else(|| {
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
    type Error = IonError;

    fn try_from(value: Int) -> Result<Self, Self::Error> {
        if value.is_negative() {
            return IonResult::decoding_error("cannot convert negative Int to a UInt");
        }
        Ok(UInt { repr: value.repr })
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
                value.repr.to_primitive().ok_or_else(|| {
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
                value.repr.to_primitive().ok_or_else(|| {
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
    // Never `-0`: no constructor takes a sign, and `neg` uses `minus`, which maps zero to `+0`.
    repr: OverflowingInt,
}

impl Int {
    pub const ZERO: Int = Int {
        repr: OverflowingInt::ZERO,
    };

    /// Borrows the underlying representation.
    pub(crate) fn as_overflowing_int(&self) -> &OverflowingInt {
        &self.repr
    }

    /// Returns a [`UInt`] representing the unsigned magnitude of this `Int`.
    #[inline]
    pub fn unsigned_abs(&self) -> UInt {
        UInt {
            repr: self.repr.abs(),
        }
    }

    /// Returns `true` if this value is less than zero.
    /// If this value is greater than or equal to zero, returns `false`.
    #[inline]
    pub fn is_negative(&self) -> bool {
        self.repr.sign() == Sign::Negative
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
        self.repr.to_primitive()
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
        self.repr.to_primitive()
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
        self.repr.to_primitive()
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
        self.repr.to_primitive()
    }

    /// If this value is small enough to fit in an `i128`, returns `Some(i128)`. Otherwise, returns
    /// `None`.
    pub fn as_i128(&self) -> Option<i128> {
        self.repr.as_i128()
    }

    pub fn from_le_signed_bytes(bytes: &[u8]) -> Int {
        Int {
            repr: OverflowingInt::from_le_signed_bytes(bytes),
        }
    }

    pub fn to_le_signed_bytes(&self) -> Vec<u8> {
        self.repr.to_le_signed_bytes()
    }

    pub(crate) fn to_bigint(&self) -> BigInt {
        self.repr.to_bigint()
    }

    /// Returns `true` if this value is zero.
    pub fn is_zero(&self) -> bool {
        self.repr.is_zero()
    }

    /// Returns the negation of this value.
    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> Self {
        Int {
            repr: self.repr.minus(),
        }
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

impl Display for UInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.repr)
    }
}

macro_rules! impl_int_from_int_types {
    ($wide:ty => $($t:ty),*) => ($(
        impl From<$t> for Int {
            #[inline]
            fn from(value: $t) -> Int {
                Int { repr: OverflowingInt::from(value as $wide) }
            }
        }
    )*)
}

impl_int_from_int_types!(i128 => i8, i16, i32, i64, i128, isize);
impl_int_from_int_types!(u128 => u8, u16, u32, u64, u128, usize);

impl From<UInt> for Int {
    fn from(value: UInt) -> Self {
        Int { repr: value.repr }
    }
}

impl From<&UInt> for Int {
    fn from(value: &UInt) -> Self {
        Int {
            repr: value.repr.clone(),
        }
    }
}

// ===== Conversions to/from the `OverflowingInt` union =====

/// Materializes a borrowed `Magnitude` as an owned [`UInt`].
impl From<Magnitude<'_>> for UInt {
    fn from(magnitude: Magnitude<'_>) -> Self {
        match magnitude {
            Magnitude::Small(magnitude) => UInt::from(magnitude),
            Magnitude::Big(magnitude) => cold_path! {
                UInt {
                    repr: OverflowingInt::from(magnitude.clone()),
                }
            },
        }
    }
}

/// Converts a signed [`Int`] into an [`OverflowingInt`], preserving sign and
/// magnitude. An `Int` never carries a negative zero, so the sign is unambiguous.
impl From<Int> for OverflowingInt {
    fn from(value: Int) -> Self {
        value.repr
    }
}

/// Converts an `OverflowingInt` into an [`Int`], preserving sign and magnitude.
/// Fails for negative zero, since `Int` has no negative zero.
impl TryFrom<&OverflowingInt> for Int {
    type Error = IonError;

    fn try_from(value: &OverflowingInt) -> Result<Self, Self::Error> {
        if value.sign() == Sign::Negative && value.is_zero() {
            return IonResult::illegal_operation("cannot convert negative zero to Int");
        }
        Ok(Int {
            repr: value.clone(),
        })
    }
}

impl Display for Int {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.repr)
    }
}

#[cfg(test)]
mod integer_tests {
    use std::io::Write;

    use super::*;
    use crate::types::UInt;
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
        assert!(Int::ZERO.is_zero());
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
        let neg = big.neg();
        assert!(neg.is_negative());
        assert_eq!(neg.to_string(), "-340282366920938463463374607431768211456");
    }

    #[test]
    fn int_from_bytes_roundtrip() {
        for v in [0i128, 1, -1, 42, -42, i128::MAX, i128::MIN] {
            let int = Int::from(v);
            let bytes = int.to_le_signed_bytes();
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
        let neg_big = Int::from_le_signed_bytes(&bytes).neg();
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

    #[test]
    fn layout() {
        assert!(size_of::<Int>() <= 16 && align_of::<Int>() <= 8);
        assert!(size_of::<UInt>() <= 16 && align_of::<UInt>() <= 8);
    }

    #[test]
    fn int_neg() {
        assert_eq!(Int::from(42).neg(), Int::from(-42));
        assert_eq!(Int::from(-42).neg(), Int::from(42));
        // `i128::MIN` negates past `i128::MAX`.
        let neg_min = Int::from(i128::MIN).neg();
        assert_eq!(neg_min.as_i128(), None);
        assert_eq!(
            u128::try_from(neg_min.clone()),
            Ok(i128::MIN.unsigned_abs())
        );
        assert_eq!(neg_min.neg(), Int::from(i128::MIN));
    }

    #[test]
    fn int_neg_zero_stays_positive() {
        let neg_zero = Int::ZERO.neg();
        assert!(!neg_zero.is_negative());
        assert_eq!(neg_zero, Int::ZERO);
        assert_eq!(hash_of(&neg_zero), hash_of(&Int::ZERO));
        assert_eq!(neg_zero.to_le_signed_bytes(), vec![0x00]);
    }

    #[rstest]
    #[case::two_pow_126("85070591730234615865843651857942052864", Int::from(1u128 << 126))]
    #[case::two_pow_126_hex("0x40000000000000000000000000000000", Int::from(1u128 << 126))]
    #[case::negative_two_pow_126(
        "-85070591730234615865843651857942052864",
        Int::from(1u128 << 126).neg()
    )]
    #[case::u128_max("340282366920938463463374607431768211455", Int::from(u128::MAX))]
    fn read_over_inline_capacity_text_int(#[case] text: &str, #[case] expected: Int) {
        let element = crate::Element::read_one(text).unwrap();
        assert_eq!(element.expect_int().unwrap(), &expected);
    }

    #[test]
    fn uint_from_str_radix() {
        assert_eq!(UInt::from_str_radix("0", 10), Ok(UInt::ZERO));
        assert_eq!(UInt::from_str_radix("FF", 16), Ok(UInt::from(255u8)));
        assert_eq!(UInt::from_str_radix("11111111", 2), Ok(UInt::from(255u8)));
        // Above the 2^126 inline limit, but within u128.
        let max = UInt::from_str_radix(&u128::MAX.to_string(), 10).unwrap();
        assert_eq!(max.as_u128(), Some(u128::MAX));
        // Above u128.
        let big = UInt::from_str_radix("340282366920938463463374607431768211456", 10).unwrap();
        assert_eq!(big.as_u128(), None);
        assert_eq!(big.to_string(), "340282366920938463463374607431768211456");
        assert!(UInt::from_str_radix("xyz", 10).is_err());
    }

    #[test]
    fn int_to_u128_above_i128_max() {
        // Accepted on both sides of `i128::MAX`.
        assert_eq!(u128::try_from(Int::from(i128::MAX)), Ok(i128::MAX as u128));
        let above = Int::from(i128::MAX as u128 + 1);
        assert_eq!(u128::try_from(above.clone()), Ok(i128::MAX as u128 + 1));
        assert_eq!(above.as_i128(), None);
        assert_eq!(u128::try_from(Int::from(u128::MAX)), Ok(u128::MAX));
        assert!(u128::try_from(Int::from(-1)).is_err());
    }

    fn hash_of<T: Hash>(value: &T) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        let mut h = DefaultHasher::new();
        value.hash(&mut h);
        h.finish()
    }

    #[test]
    fn padded_bytes_equal_unpadded() {
        let mut padded = vec![0u8; 20];
        padded[0] = 42;
        let padded = UInt::from_le_bytes(&padded);
        assert_eq!(padded, UInt::from(42u8));
        assert_eq!(hash_of(&padded), hash_of(&UInt::from(42u8)));

        let mut positive = vec![0u8; 17];
        positive[0] = 42;
        let mut negative = vec![0xFFu8; 17];
        negative[0] = 0xD6; // -42
        for (bytes, expected) in [(positive, Int::from(42)), (negative, Int::from(-42))] {
            let padded = Int::from_le_signed_bytes(&bytes);
            assert_eq!(padded, expected);
            assert_eq!(hash_of(&padded), hash_of(&expected));
        }
    }

    #[test]
    fn uint_decimal_digits_at_inline_limit_and_on_heap() {
        let inline_max = UInt::from((1u128 << 126) - 1); // 85070591730234615865843651857942052863
        assert_eq!(inline_max.number_of_decimal_digits(), 38);
        let heap_min = UInt::from(1u128 << 126); // 85070591730234615865843651857942052864
        assert_eq!(heap_min.number_of_decimal_digits(), 38);
        assert_eq!(UInt::from(u128::MAX).number_of_decimal_digits(), 39);
        let above_u128 = UInt::from_str_radix(&format!("1{}", "0".repeat(40)), 10).unwrap();
        assert_eq!(above_u128.number_of_decimal_digits(), 41);
    }

    #[test]
    fn int_unsigned_abs() {
        assert_eq!(Int::from(-5).unsigned_abs(), UInt::from(5u8));
        assert_eq!(Int::from(5).unsigned_abs(), UInt::from(5u8));
        let inline_max = (1u128 << 126) - 1;
        let heap_min = 1u128 << 126;
        assert_eq!(
            Int::from(inline_max).neg().unsigned_abs(),
            UInt::from(inline_max)
        );
        assert_eq!(
            Int::from(heap_min).neg().unsigned_abs(),
            UInt::from(heap_min)
        );
        assert_eq!(
            Int::from(i128::MIN).unsigned_abs(),
            UInt::from(i128::MIN.unsigned_abs())
        );
        let zero = Int::ZERO.unsigned_abs();
        assert_eq!(zero, UInt::ZERO);
        assert_eq!(hash_of(&zero), hash_of(&UInt::ZERO));
    }

    #[test]
    fn uint_to_int_and_back() {
        let uint = UInt::from(u128::MAX);
        let int = Int::from(uint.clone());
        assert!(!int.is_negative());
        assert_eq!(UInt::try_from(int), Ok(uint));
        assert!(UInt::try_from(Int::from(-1)).is_err());
    }
}
