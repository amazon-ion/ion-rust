use super::big_small::*;
use crate::result::IonFailure;
use crate::{IonError, IonResult};
use ice_code::ice as cold_path;
use num_bigint::{BigInt, BigUint};
use num_traits::{Num, Signed, ToPrimitive};
use std::borrow::Cow;
use std::ops::Neg;
use BigOrSmall::*;

/// Backing storage for `UInt`. Stores values up to u128 inline; larger values use `BigUint`.
///
/// The size of this type is 32 bytes. If that is a problem, we can try boxing the BigUint and/or
/// replacing BigOrSmall with a specialized union type.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct UIntData(BigOrSmall<u128, BigUint>);

impl UIntData {
    pub(crate) const ZERO: UIntData = UIntData(SmallValue(0));

    pub(crate) fn from_le_bytes(bytes: &[u8]) -> Self {
        if bytes.len() <= size_of::<u128>() {
            let mut buf = [0u8; size_of::<u128>()];
            buf[..bytes.len()].copy_from_slice(bytes);
            let v = u128::from_le_bytes(buf);
            Self(SmallValue(v))
        } else {
            cold_path! { Self(BigValue(BigUint::from_bytes_le(bytes))) }
        }
    }

    pub(crate) fn from_be_bytes(bytes: &[u8]) -> Self {
        if bytes.len() <= size_of::<u128>() {
            let mut buf = [0u8; size_of::<u128>()];
            buf[size_of::<u128>() - bytes.len()..].copy_from_slice(bytes);
            let v = u128::from_be_bytes(buf);
            Self(SmallValue(v))
        } else {
            cold_path! { UIntData(BigValue(BigUint::from_bytes_be(bytes))) }
        }
    }

    pub(crate) fn to_le_bytes(&self) -> Vec<u8> {
        match &self.0 {
            SmallValue(value) => {
                if *value == 0 {
                    return vec![0];
                }
                let bytes = value.to_le_bytes();
                let len = 16 - (value.leading_zeros() / 8) as usize;
                bytes[..len].to_vec()
            }
            BigValue(big_value) => cold_path! { big_value.to_bytes_le() },
        }
    }

    pub(crate) fn to_be_bytes(&self) -> Vec<u8> {
        match &self.0 {
            SmallValue(value) => {
                if *value == 0 {
                    return vec![0];
                }
                let bytes = value.to_be_bytes();
                let start = bytes
                    .iter()
                    .position(|&b| b != 0)
                    .unwrap_or(bytes.len() - 1);
                bytes[start..].to_vec()
            }
            BigValue(big_value) => cold_path! { big_value.to_bytes_be() },
        }
    }

    pub(crate) fn count_decimal_digits(&self) -> u32 {
        match &self.0 {
            SmallValue(value) => {
                if *value == 0 {
                    1
                } else {
                    value.ilog10() + 1
                }
            }
            BigValue(big) => cold_path! { format!("{big}").len() as u32 },
        }
    }

    pub(crate) fn from_str_radix(src: &str, radix: u32) -> IonResult<Self> {
        match u128::from_str_radix(src, radix) {
            Ok(value) => Ok(Self(SmallValue(value))),
            Err(e) => {
                cold_path!({
                    use core::num::IntErrorKind::*;
                    match e.kind() {
                        PosOverflow => BigUint::from_str_radix(src, radix)
                            .map(UIntData::from_big)
                            .map_err(|_| IonError::decoding_error("Invalid UInt")),
                        _ => Err(IonError::decoding_error("Invalid UInt")),
                    }
                })
            }
        }
    }

    /// Normalizes a BigUint into inline storage if it fits. Inherent rather than `From` to
    /// keep BigUint out of the public API.
    pub(crate) fn from_big(value: BigUint) -> Self {
        match value.to_u128() {
            Some(i) => i.into(),
            None => Self(BigValue(value)),
        }
    }
}

impl_as_big_or_small!(this: UIntData, BigUint => this.0.as_big_value(), u128 => this.0.as_small_value());

impl_display_big_small!(UIntData);

impl_std_op_big_small!(Add<UIntData> for UIntData, add, checked_add);
impl_std_op_big_small!(Sub<UIntData> for UIntData, sub, checked_sub);
impl_std_op_big_small!(Mul<UIntData> for UIntData, mul, checked_mul);
impl_std_op_big_small!(Div<UIntData> for UIntData, div, checked_div);
impl_std_op_big_small!(Rem<UIntData> for UIntData, rem, checked_rem);
impl_std_op_big_small!(Add<u128> for UIntData, add, checked_add);
impl_std_op_big_small!(Sub<u128> for UIntData, sub, checked_sub);
impl_std_op_big_small!(Mul<u128> for UIntData, mul, checked_mul);
impl_std_op_big_small!(Div<u128> for UIntData, div, checked_div);
impl_std_op_big_small!(Rem<u128> for UIntData, rem, checked_rem);

impl std::hash::Hash for UIntData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Hash the canonical LE byte representation for consistency
        self.to_le_bytes().hash(state);
    }
}

// ===== IntData =====

/// Backing storage for `Int`. Stores values in the i128 range inline; larger values use `BigInt`.
///
/// The size of this type is 32 bytes. If that is a problem, we can try boxing the BigUint and/or
/// replacing BigOrSmall with a specialized union type.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct IntData(BigOrSmall<i128, BigInt>);

impl IntData {
    pub(crate) const ZERO: IntData = IntData(SmallValue(0));

    pub(crate) fn from_le_signed_bytes(bytes: &[u8]) -> Self {
        if bytes.len() <= size_of::<i128>() {
            let pad = if bytes.last().is_some_and(|&b| b & 0x80 != 0) {
                0xFF
            } else {
                0x00
            };
            let mut buf = [pad; size_of::<i128>()];
            buf[..bytes.len()].copy_from_slice(bytes);
            Self(SmallValue(i128::from_le_bytes(buf)))
        } else {
            cold_path! { Self(BigValue(BigInt::from_signed_bytes_le(bytes))) }
        }
    }

    pub(crate) fn to_le_bytes(&self) -> Vec<u8> {
        match &self.0 {
            SmallValue(value) => {
                let bytes: [u8; 16] = value.to_le_bytes();
                let is_neg = *value < 0;
                let pad = if is_neg { 0xFF } else { 0x00 };
                let mut len = 16;
                while len > 1 && bytes[len - 1] == pad {
                    if (bytes[len - 2] & 0x80 != 0) != is_neg {
                        break;
                    }
                    len -= 1;
                }
                bytes[..len].to_vec()
            }
            BigValue(big) => cold_path! { big.to_signed_bytes_le() },
        }
    }

    pub(crate) fn is_negative(&self) -> bool {
        match &self.0 {
            SmallValue(value) => *value < 0,
            BigValue(big) => cold_path! { big.is_negative() },
        }
    }

    pub(crate) fn byte_len(&self) -> usize {
        match &self.0 {
            SmallValue(small) => {
                let sign_bits = if *small < 0 {
                    small.leading_ones()
                } else {
                    small.leading_zeros()
                };
                let num_magnitude_bits = (i128::BITS - sign_bits) as u64;
                // Calculates ⌈ (num_magnitude_bits + 1) / 8 ⌉
                (num_magnitude_bits / 8 + 1) as usize
            }
            BigValue(big) => cold_path! {{
                if big.is_positive() {
                    (big.bits() / 8 + 1) as usize
                } else {
                    // BigInt::bits() gives us the number of bits for the unsigned magnitude.
                    // Converting to 2's complement, can result in an extra bit iff the unsigned
                    // value is (2^n)-1, so when `n` is one less than a multiple of 8, using
                    // BigInt::bits() will get us the wrong number of BYTES.
                    // It is simpler and cheaper to just get the actual signed bytes representation,
                    // although this does result in allocations.
                    return big.to_signed_bytes_le().len()
                }
            }},
        }
    }

    pub(crate) fn count_decimal_digits(&self) -> u32 {
        match &self.0 {
            SmallValue(value) => {
                let abs = value.unsigned_abs();
                if abs == 0 {
                    1
                } else {
                    abs.ilog10() + 1
                }
            }
            BigValue(big) => cold_path! {{
                let s = format!("{big}");
                let s = s.strip_prefix('-').unwrap_or(&s);
                s.len() as u32
            }},
        }
    }

    pub(crate) fn unsigned_abs(&self) -> UIntData {
        match &self.0 {
            SmallValue(value) => UIntData(SmallValue(value.unsigned_abs())),
            BigValue(big) => cold_path! { UIntData::from_big(big.magnitude().clone()) },
        }
    }

    /// Normalizes a BigInt into inline storage if it fits.
    pub(crate) fn from_big(value: BigInt) -> Self {
        match value.to_i128() {
            Some(i) => i.into(),
            None => Self(BigValue(value)),
        }
    }
}
impl_as_big_or_small!(this: IntData, BigInt => this.0.as_big_value(), i128 => this.0.as_small_value());

impl_display_big_small!(IntData);

impl_std_op_big_small!(Add<IntData> for IntData, add, checked_add);
impl_std_op_big_small!(Sub<IntData> for IntData, sub, checked_sub);
impl_std_op_big_small!(Mul<IntData> for IntData, mul, checked_mul);
impl_std_op_big_small!(Div<IntData> for IntData, div, checked_div);
impl_std_op_big_small!(Rem<IntData> for IntData, rem, checked_rem);
impl_std_op_big_small!(Add<i128> for IntData, add, checked_add);
impl_std_op_big_small!(Sub<i128> for IntData, sub, checked_sub);
impl_std_op_big_small!(Mul<i128> for IntData, mul, checked_mul);
impl_std_op_big_small!(Div<i128> for IntData, div, checked_div);
impl_std_op_big_small!(Rem<i128> for IntData, rem, checked_rem);

impl Neg for IntData {
    type Output = IntData;
    fn neg(self) -> IntData {
        if let SmallValue(value) = &self.0 {
            if let Some(result) = value.checked_neg() {
                return Self(SmallValue(result));
            }
        }
        cold_path! {{
            match self.0 {
                SmallValue(small) => Self::from_big(-BigInt::from(small)),
                BigValue(big) => Self::from_big(-big),
            }
        }}
    }
}

impl std::hash::Hash for IntData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Hash the canonical LE byte representation for consistency
        self.to_le_bytes().hash(state);
    }
}

// ===== TryFrom/From impls =====

impl TryFrom<IntData> for UIntData {
    type Error = IonError;
    fn try_from(value: IntData) -> Result<Self, Self::Error> {
        if value.is_negative() {
            return IonResult::decoding_error("cannot convert negative IntData to UIntData");
        }
        Ok(value.unsigned_abs())
    }
}

impl From<UIntData> for IntData {
    fn from(value: UIntData) -> Self {
        if let SmallValue(v) = value.0 {
            if let Ok(i) = i128::try_from(v) {
                return Self(SmallValue(i));
            }
        }
        cold_path! { Self(BigValue(BigInt::from(value.as_big_value().into_owned()))) }
    }
}

/// Generates `TryFrom<Data> for primitive` impls that extract the inline value and narrow it.
macro_rules! impl_try_from_data_to_primitive {
    ($from_type:ty => $($to_type:ty),*) => ($(
        impl std::convert::TryFrom<$from_type> for $to_type {
            type Error = IonError;
            fn try_from(value: $from_type) -> Result<Self, IonError> {
                value.as_small_value()
                    .and_then(|v| <$to_type>::try_from(v).ok())
                    .ok_or_else(|| IonError::decoding_error(
                        concat!(stringify!($from_type), " value exceeds range of ", stringify!($to_type))
                    ))
            }
        }
    )*)
}

impl_try_from_data_to_primitive!(UIntData => i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);
impl_try_from_data_to_primitive!(IntData => i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);
impl_try_from_data_to_primitive!(&UIntData => i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);
impl_try_from_data_to_primitive!(&IntData => i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

macro_rules! from_primitive_for_int_data {
    ($($t:ty),*) => {$(
        impl From<$t> for IntData {
            fn from(value: $t) -> Self {
                Self(SmallValue(value as i128))
            }
        }
    )*}
}
from_primitive_for_int_data!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, usize);

impl From<u128> for IntData {
    fn from(value: u128) -> Self {
        if value <= i128::MAX as u128 {
            Self(SmallValue(value as i128))
        } else {
            Self(BigValue(value.into()))
        }
    }
}

macro_rules! from_primitive_for_uint_data {
    ($($t:ty),*) => {$(
        impl From<$t> for UIntData {
            fn from(value: $t) -> Self {
                Self(SmallValue(value as u128))
            }
        }
    )*}
}
from_primitive_for_uint_data!(u8, u16, u32, u64, u128, usize);

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use std::ops::{Neg, Sub};

    #[test]
    fn uint_inline_roundtrip() {
        for v in [0u128, 1, 42, u64::MAX as u128, u128::MAX] {
            let d = UIntData::from(v);
            assert!(matches!(d.0, SmallValue(_)));
            assert_eq!(d.try_into(), Ok(v));
        }
    }

    #[test]
    fn int_inline_roundtrip() {
        for v in [0i128, 1, -1, 42, -42, i128::MAX, i128::MIN] {
            let d = IntData::from(v);
            assert!(matches!(d.0, SmallValue(_)), "value {v} should be inline");
            assert_eq!(d.try_into(), Ok(v));
        }
    }

    #[test]
    fn int_neg() {
        assert_eq!(IntData::from(42).neg().try_into(), Ok(-42));
        assert_eq!(IntData::from(-42).neg().try_into(), Ok(42));
        assert_eq!(IntData::from(0).neg().try_into(), Ok(0));
        let neg_min = IntData::from(i128::MIN).neg();
        assert!(i128::try_from(neg_min).is_err());
    }

    #[test]
    fn int_neg_power_of_two_boundaries() {
        for v in [256i128, 65536, -256, -128, 16777216] {
            let d = IntData::from(v);
            let neg = d.neg();
            assert_eq!(neg.clone().try_into(), Ok(-v));
            assert_eq!(neg.neg().try_into(), Ok(v));
        }
        // Big: 2^128 round-trip
        let mut bytes = vec![0u8; 18];
        bytes[16] = 1;
        let big = IntData::from_le_signed_bytes(&bytes);
        let neg_big = big.clone().neg();
        assert!(neg_big.is_negative());
        let pos_again = neg_big.neg();
        assert_eq!(big, pos_again);
    }

    #[test]
    fn uint_from_bytes_le_normalizes() {
        let d = UIntData::from_le_bytes(&[42, 0, 0, 0]);
        assert!(matches!(d.0, SmallValue(_)));
        assert_eq!(d.try_into(), Ok(42));
    }

    #[test]
    fn int_from_signed_bytes_le_normalizes() {
        let d = IntData::from_le_signed_bytes(&[42]);
        assert!(matches!(d.0, SmallValue(_)));
        assert_eq!(d.try_into(), Ok(42));
        let d = IntData::from_le_signed_bytes(&[0xFE]);
        assert!(matches!(d.0, SmallValue(_)));
        assert_eq!(d.try_into(), Ok(-2));
    }

    #[test]
    fn uint_ordering() {
        assert!(UIntData::from(1u8) < UIntData::from(2u8));
        assert!(UIntData::from(42u8) < UIntData::from(u128::MAX));
    }

    #[test]
    fn int_ordering() {
        assert!(IntData::from(-1) < IntData::from(0));
        assert!(IntData::from(0) < IntData::from(1));
        assert!(IntData::from(42) < IntData::from(i128::MAX));
    }

    #[test]
    fn uint_display() {
        assert_eq!(format!("{}", UIntData::from(0u8)), "0");
        assert_eq!(format!("{}", UIntData::from(42u8)), "42");
        assert_eq!(
            format!("{}", UIntData::from(u128::MAX)),
            format!("{}", u128::MAX)
        );
    }

    #[test]
    fn int_display() {
        assert_eq!(format!("{}", IntData::from(0)), "0");
        assert_eq!(format!("{}", IntData::from(-42)), "-42");
        assert_eq!(
            format!("{}", IntData::from(i128::MAX)),
            format!("{}", i128::MAX)
        );
        assert_eq!(
            format!("{}", IntData::from(i128::MIN)),
            format!("{}", i128::MIN)
        );
    }

    #[test]
    fn uint_big_from_bytes_display() {
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let d = UIntData::from_le_bytes(&bytes);
        assert!(matches!(d.0, BigValue(_)));
        assert_eq!(format!("{d}"), "340282366920938463463374607431768211456");
        assert!(u128::try_from(d).is_err());
    }

    #[test]
    fn int_big_from_bytes_display() {
        let mut bytes = vec![0u8; 18];
        bytes[16] = 1;
        let d = IntData::from_le_signed_bytes(&bytes);
        assert!(matches!(d.0, BigValue(_)));
        assert_eq!(format!("{d}"), "340282366920938463463374607431768211456");
        let neg = d.neg();
        assert_eq!(format!("{neg}"), "-340282366920938463463374607431768211456");
    }

    #[test]
    fn hash_consistency() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let hash = |d: UIntData| {
            let mut h = DefaultHasher::new();
            d.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash(UIntData::from(42u8)), hash(UIntData::from(42u32)));
    }

    #[test]
    fn send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<UIntData>();
        assert_send_sync::<IntData>();
    }

    #[test]
    fn to_bytes_le_roundtrip() {
        for v in [0u128, 1, 42, u64::MAX as u128, u128::MAX] {
            let d = UIntData::from(v);
            let d2 = UIntData::from_le_bytes(&d.to_le_bytes());
            assert_eq!(d, d2, "UInt roundtrip failed for {v}");
        }
        for v in [0i128, 1, -1, 42, -42, i128::MAX, i128::MIN] {
            let d = IntData::from(v);
            let d2 = IntData::from_le_signed_bytes(&d.to_le_bytes());
            assert_eq!(d, d2, "Int roundtrip failed for {v}");
        }
    }

    #[test]
    fn uint_to_be_bytes() {
        assert_eq!(UIntData::from(0u8).to_be_bytes(), vec![0]);
        assert_eq!(UIntData::from(0xFFu8).to_be_bytes(), vec![0xFF]);
        assert_eq!(UIntData::from(0x0102u16).to_be_bytes(), vec![0x01, 0x02]);
        assert_eq!(
            UIntData::from(u128::MAX).to_be_bytes(),
            u128::MAX.to_be_bytes().to_vec()
        );
        let mut le = vec![0u8; 17];
        le[16] = 1;
        let big = UIntData::from_le_bytes(&le);
        let be = big.to_be_bytes();
        assert_eq!(be[0], 1);
        assert!(be[1..].iter().all(|&b| b == 0));
        assert_eq!(be.len(), 17);
    }

    #[rstest]
    #[case(0, 1)]
    #[case(1, 1)]
    #[case(127, 1)]
    #[case(128, 2)]
    #[case(256, 2)]
    #[case(-1, 1)]
    #[case(-128, 1)]
    #[case(-129, 2)]
    #[case::pos_2pow127_sub1(BigInt::from(2).pow(127).sub(1), 16)]
    #[case::pos_2pow127(BigInt::from(2).pow(127), 17)]
    #[case::pos_2pow135_sub1(BigInt::from(2).pow(135).sub(1), 17)]
    #[case::pos_2pow135(BigInt::from(2).pow(135), 18)]
    #[case::pos_2pow143_sub1(BigInt::from(2).pow(143).sub(1), 18)]
    #[case::pos_2pow143(BigInt::from(2).pow(143), 19)]
    #[case::neg_2pow127(BigInt::from(2).pow(127).neg(), 16)]
    #[case::neg_2pow127_sub1(BigInt::from(2).pow(127).neg().sub(1), 17)]
    #[case::neg_2pow135(BigInt::from(2).pow(135).neg(), 17)]
    #[case::neg_2pow135_sub1(BigInt::from(2).pow(135).neg().sub(1), 18)]
    #[case::neg_2pow143(BigInt::from(2).pow(143).neg(), 18)]
    #[case::neg_2pow143_sub1(BigInt::from(2).pow(143).neg().sub(1), 19)]
    #[trace] // <-- Displays all arguments for failed test cases
    fn int_byte_len(#[case] num: impl Into<BigInt>, #[case] expected_len: usize) {
        let int_data = IntData::from_big(num.into());
        let actual_len = int_data.byte_len();
        assert_eq!(
            actual_len, expected_len,
            "Length {} doesn't match expected {}",
            actual_len, expected_len
        );
        let to_le_bytes_len = int_data.to_le_bytes().len();
        assert_eq!(
            actual_len, to_le_bytes_len,
            "Length {} doesn't match to_le_bytes().len() ({})",
            actual_len, to_le_bytes_len
        );
    }

    #[test]
    fn int_arithmetic() {
        let a = IntData::from(100);
        let b = IntData::from(42);
        assert_eq!((a.clone() + b.clone()).try_into(), Ok(142));
        assert_eq!((a.clone() - b.clone()).try_into(), Ok(58));
        assert_eq!((a.clone() * 3).try_into(), Ok(300));
        assert_eq!((a.clone() / 10).try_into(), Ok(10));
        assert_eq!((a.clone() % 30).try_into(), Ok(10));

        // Negative
        let c = IntData::from(-50);
        assert_eq!((a.clone() + c.clone()).try_into(), Ok(50));
        assert_eq!((c.clone() - a.clone()).try_into(), Ok(-150));
    }

    #[test]
    fn uint_arithmetic() {
        let a = UIntData::from(100u8);
        let b = UIntData::from(42u8);
        assert_eq!((a.clone() + b.clone()).try_into(), Ok(142));
        assert_eq!((a.clone() - b.clone()).try_into(), Ok(58));
    }

    #[test]
    fn uint_from_str_radix() {
        assert_eq!(UIntData::from_str_radix("0", 10).unwrap().try_into(), Ok(0));
        assert_eq!(
            UIntData::from_str_radix("255", 10).unwrap().try_into(),
            Ok(255)
        );
        assert_eq!(
            UIntData::from_str_radix("FF", 16).unwrap().try_into(),
            Ok(255)
        );
        assert_eq!(
            UIntData::from_str_radix("11111111", 2).unwrap().try_into(),
            Ok(255)
        );
        // Big value exceeding u128
        let big = UIntData::from_str_radix("340282366920938463463374607431768211456", 10).unwrap();
        assert!(matches!(big.0, BigValue(_)));
        assert!(UIntData::from_str_radix("xyz", 10).is_err());
    }

    #[rstest]
    #[case::zero(0, 1)]
    #[case::one(1, 1)]
    #[case::nine(9, 1)]
    #[case::ten(10, 2)]
    #[case::ninety_nine(99, 2)]
    #[case::hundred(100, 3)]
    #[case::negative(-1, 1)]
    #[case::negative_large(-999999, 6)]
    #[case::i128_max(i128::MAX, 39)]
    #[case::i128_min(i128::MIN, 39)]
    fn int_count_decimal_digits(#[case] value: i128, #[case] expected: u32) {
        assert_eq!(IntData::from(value).count_decimal_digits(), expected);
    }

    #[test]
    fn int_count_decimal_digits_big() {
        // 2^128 = 340282366920938463463374607431768211456 (39 digits)
        let mut bytes = vec![0u8; 18];
        bytes[16] = 1;
        let big = IntData::from_le_signed_bytes(&bytes);
        assert!(matches!(big.0, BigValue(_)));
        assert_eq!(big.count_decimal_digits(), 39);
    }

    #[test]
    fn try_from_negative_int_to_uint_fails() {
        let neg = IntData::from(-1i128);
        assert!(UIntData::try_from(neg).is_err());
    }

    #[test]
    fn uint_to_int_big_value() {
        // u128::MAX doesn't fit in i128, so it should go through the BigValue path
        let uint = UIntData::from(u128::MAX);
        let int = IntData::from(uint);
        assert!(matches!(int.0, BigValue(_)));
        assert!(!int.is_negative());
    }

    #[test]
    fn uint_from_be_bytes() {
        // Empty / zero
        assert_eq!(UIntData::from_be_bytes(&[]).as_small_value(), Some(0));
        // Single byte
        assert_eq!(
            UIntData::from_be_bytes(&[0x42]).as_small_value(),
            Some(0x42)
        );
        // Multi-byte
        assert_eq!(
            UIntData::from_be_bytes(&[0x01, 0x02]).as_small_value(),
            Some(0x0102)
        );
        // 16 bytes (max inline)
        let bytes = u128::MAX.to_be_bytes();
        assert_eq!(
            UIntData::from_be_bytes(&bytes).as_small_value(),
            Some(u128::MAX)
        );
        // 17 bytes (heap)
        let mut big_bytes = vec![1u8];
        big_bytes.extend_from_slice(&[0u8; 16]);
        let big = UIntData::from_be_bytes(&big_bytes);
        assert!(matches!(big.0, BigValue(_)));
        assert_eq!(big.as_small_value(), None);
    }

    #[test]
    fn uint_count_decimal_digits_big() {
        // 2^128 has 39 digits
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let big = UIntData::from_le_bytes(&bytes);
        assert!(matches!(big.0, BigValue(_)));
        assert_eq!(big.count_decimal_digits(), 39);
    }

    #[test]
    fn uint_to_be_bytes_big() {
        let mut le_bytes = vec![0u8; 17];
        le_bytes[16] = 1; // 2^128 in LE
        let big = UIntData::from_le_bytes(&le_bytes);
        let be = big.to_be_bytes();
        assert_eq!(be[0], 1);
        assert!(be[1..].iter().all(|&b| b == 0));
        assert_eq!(be.len(), 17);
    }

    #[test]
    fn int_from_big_normalizes_small() {
        // A BigInt that fits in i128 should normalize to SmallValue
        let big = BigInt::from(42i128);
        let data = IntData::from_big(big);
        assert!(matches!(data.0, SmallValue(42)));
    }

    #[test]
    fn int_from_big_stays_big() {
        // A BigInt that doesn't fit in i128 stays as BigValue
        let big = BigInt::from(u128::MAX);
        let data = IntData::from_big(big);
        assert!(matches!(data.0, BigValue(_)));
    }

    #[test]
    fn int_heap_to_le_bytes() {
        // Create a big positive value (2^128)
        let mut bytes = vec![0u8; 18];
        bytes[16] = 1;
        let big = IntData::from_le_signed_bytes(&bytes);
        assert!(matches!(big.0, BigValue(_)));
        // Minimal signed LE for 2^128: 17 bytes (needs leading 0x00 for positive sign)
        let roundtripped = big.to_le_bytes();
        let expected: Vec<u8> = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        assert_eq!(roundtripped, expected);
    }

    #[test]
    fn int_heap_is_negative() {
        // Create a big negative value
        let mut bytes = vec![0u8; 18];
        bytes[16] = 1;
        let big = IntData::from_le_signed_bytes(&bytes);
        let neg = -big;
        assert!(matches!(neg.0, BigValue(_)));
        assert!(neg.is_negative());
    }

    #[test]
    fn int_heap_unsigned_abs() {
        let mut bytes = vec![0u8; 18];
        bytes[16] = 1;
        let big = IntData::from_le_signed_bytes(&bytes);
        let neg = -big.clone();
        let abs = neg.unsigned_abs();
        assert_eq!(abs.to_le_bytes(), big.unsigned_abs().to_le_bytes());
    }
}
