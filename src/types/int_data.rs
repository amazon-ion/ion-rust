// # Safety contract for `UIntData` and `IntData`
//
// These are 16-byte tagged unions that store either:
//   - An inline value as `[u8; 16]` in little-endian byte order (byte[0] bit 0 = 1), or
//   - A heap-allocated `(i64, Box<BigUint/BigInt>)` where the i64 is always 0.
//
// ## Tag bit
//
// The tag is byte[0] bit 0:
//   - For inline: always 1 (set explicitly during encoding via `(value << 1) | 1`)
//   - For heap: always 0 (the i64 discriminant is 0, so all its bytes are 0)
//
// ## Why the `i64` padding field exists
//
// `Box<BigUint>` / `Box<BigInt>` is only 8 bytes (a thin pointer). In a 16-byte union
// with `[u8; 16]`, the remaining 8 bytes would be uninitialized padding. Reading
// `self.inline` when the heap variant is active would then read uninitialized memory,
// which is undefined behavior — even just to check the tag bit.
//
// The `i64` field (always set to 0) ensures all 16 bytes of the heap variant are
// initialized. It occupies bytes[0..8], placing the `Box` pointer at bytes[8..16].
// Since the i64 is 0, byte[0] is guaranteed to be 0x00 on both little-endian and
// big-endian architectures, making the tag check (`byte[0] & 1 == 1`) endian-independent.
//
// ## Endian independence
//
// This works on both little-endian and big-endian architectures because:
//   - The tag is at a fixed byte position (byte[0]), not dependent on integer endianness
//   - The i64=0 discriminant guarantees bytes[0..8] are all zero regardless of endianness
//   - Inline values are stored as explicit LE bytes via to_le_bytes(), not native layout
//
// ## Normalization invariant
//
// Values that fit in the inline range are ALWAYS stored inline. This means equal values
// always have the same representation (both inline or both heap with identical BigInt).
//
// ## Unsafe access rule
//
// All `unsafe` accesses must first check `is_inline()` to determine the active variant.

use crate::result::IonFailure;
use crate::{IonError, IonResult};
use ice_code::ice as cold_path;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{Num, Signed, ToBytes, ToPrimitive, Unsigned};
use std::borrow::Cow;
use std::mem::ManuallyDrop;
use std::ops::Neg;

pub(crate) union UIntData {
    inline: [u8; 16],
    heap: ManuallyDrop<(i64, Box<BigUint>)>,
}

impl Drop for UIntData {
    fn drop(&mut self) {
        if !self.is_inline() {
            cold_path!({
                // SAFETY: heap variant active, drop the Box
                unsafe { ManuallyDrop::drop(&mut self.heap) };
            });
        }
    }
}

pub(crate) union IntData {
    inline: [u8; 16],
    heap: ManuallyDrop<(i64, Box<BigInt>)>,
}

impl Drop for IntData {
    fn drop(&mut self) {
        if !self.is_inline() {
            cold_path!({
                // SAFETY: heap variant active, drop the Box
                unsafe { ManuallyDrop::drop(&mut self.heap) };
            });
        }
    }
}

// Inline range: 127 usable bits (bit 0 of byte[0] is the tag)
const UINT_INLINE_MAX: u128 = (1u128 << 127) - 1;
const INT_INLINE_MAX: i128 = (1i128 << 126) - 1;
const INT_INLINE_MIN: i128 = -(1i128 << 126);

#[inline]
fn encode_inline(value: u128) -> [u8; 16] {
    ((value << 1) | 1).to_le_bytes()
}

#[inline]
fn decode_inline_u(bytes: &[u8; 16]) -> u128 {
    u128::from_le_bytes(*bytes) >> 1
}

#[inline]
fn encode_inline_signed(value: i128) -> [u8; 16] {
    ((value << 1) | 1).to_le_bytes()
}

#[inline]
fn decode_inline_i(bytes: &[u8; 16]) -> i128 {
    i128::from_le_bytes(*bytes) >> 1 // arithmetic shift preserves sign
}

// ===== UIntData =====

impl UIntData {
    pub(crate) const ZERO: UIntData = UIntData {
        inline: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    };

    #[inline]
    pub(crate) fn is_inline(&self) -> bool {
        // SAFETY: byte[0] is valid for both variants (inline bytes or i64 first byte)
        unsafe { self.inline[0] & 1 == 1 }
    }

    pub(crate) fn from_u128(value: u128) -> Self {
        if value <= UINT_INLINE_MAX {
            UIntData {
                inline: encode_inline(value),
            }
        } else {
            UIntData {
                heap: ManuallyDrop::new((0i64, Box::new(BigUint::from(value)))),
            }
        }
    }

    pub(crate) fn as_u128(&self) -> Option<u128> {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed inline variant
            Some(decode_inline_u(unsafe { &self.inline }))
        } else {
            cold_path!({
                // SAFETY: !is_inline() confirmed heap variant
                let big = unsafe { &self.heap.1 };
                big.to_u128()
            })
        }
    }

    pub(crate) fn expect_u128(&self) -> IonResult<u128> {
        self.as_u128()
            .ok_or_else(|| IonError::decoding_error("UInt value exceeds u128 range"))
    }

    pub(crate) fn from_le_bytes(bytes: &[u8]) -> Self {
        if bytes.len() <= 16 {
            let mut buf = [0u8; 16];
            buf[..bytes.len()].copy_from_slice(bytes);
            let v = u128::from_le_bytes(buf);
            if v <= UINT_INLINE_MAX {
                return UIntData {
                    inline: encode_inline(v),
                };
            }
        }
        cold_path!({ UIntData::from_biguint(BigUint::from_bytes_le(bytes)) })
    }

    pub(crate) fn from_be_bytes(bytes: &[u8]) -> Self {
        const BUFFER_SIZE: usize = size_of::<u128>();
        if bytes.len() <= BUFFER_SIZE {
            let mut buf = [0u8; BUFFER_SIZE];
            buf[BUFFER_SIZE - bytes.len()..].copy_from_slice(bytes);
            let v = u128::from_be_bytes(buf);
            if v <= UINT_INLINE_MAX {
                return UIntData {
                    inline: encode_inline(v),
                };
            }
        }
        cold_path!({ UIntData::from_biguint(BigUint::from_bytes_be(bytes)) })
    }

    pub(crate) fn to_le_bytes(&self) -> Vec<u8> {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_u(unsafe { &self.inline });
            if value == 0 {
                return vec![0];
            }
            let bytes = value.to_le_bytes();
            let len = 16 - (value.leading_zeros() / 8) as usize;
            bytes[..len].to_vec()
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                // BigUInt::to_le_bytes() always returns at least one byte.
                big.to_le_bytes()
            })
        }
    }

    pub(crate) fn to_be_bytes(&self) -> Vec<u8> {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_u(unsafe { &self.inline });
            if value == 0 {
                return vec![0];
            }
            let bytes = value.to_be_bytes();
            let start = bytes
                .iter()
                .position(|&b| b != 0)
                .unwrap_or(bytes.len() - 1);
            bytes[start..].to_vec()
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                // BigUInt::to_be_bytes() always returns at least one byte.
                big.to_be_bytes()
            })
        }
    }

    pub(crate) fn count_decimal_digits(&self) -> u32 {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_u(unsafe { &self.inline });
            if value == 0 {
                1
            } else {
                value.ilog10() + 1
            }
        } else {
            let s = format!("{self}");
            s.len() as u32
        }
    }

    pub(crate) fn from_str_radix(src: &str, radix: u32) -> IonResult<Self> {
        match u128::from_str_radix(src, radix) {
            Ok(value) => Ok(Self::from_u128(value)),
            Err(e) => {
                cold_path!({
                    use core::num::IntErrorKind::*;
                    match e.kind() {
                        PosOverflow => BigUint::from_str_radix(src, radix)
                            .map(UIntData::from_biguint)
                            .map_err(|_| IonError::decoding_error("Invalid UInt")),
                        _ => Err(IonError::decoding_error("Invalid UInt")),
                    }
                })
            }
        }
    }

    pub(crate) fn as_biguint(&self) -> Cow<'_, BigUint> {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_u(unsafe { &self.inline });
            Cow::Owned(value.into())
        } else {
            Cow::Borrowed(unsafe { self.heap.1.as_ref() })
        }
    }

    /// Normalizes a `BigUint` result: stores inline if it fits, otherwise heap-allocates.
    fn from_biguint(value: BigUint) -> UIntData {
        if let Some(v) = value.to_u128() {
            if v <= UINT_INLINE_MAX {
                return UIntData::from_u128(v);
            }
        }
        UIntData {
            heap: ManuallyDrop::new((0i64, Box::new(value))),
        }
    }
}

// ===== IntData =====

impl IntData {
    pub(crate) const ZERO: IntData = IntData {
        inline: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    };

    #[inline]
    pub(crate) fn is_inline(&self) -> bool {
        // SAFETY: byte[0] is valid for both variants
        unsafe { self.inline[0] & 1 == 1 }
    }

    pub(crate) fn from_i128(value: i128) -> Self {
        if (INT_INLINE_MIN..=INT_INLINE_MAX).contains(&value) {
            IntData {
                inline: encode_inline_signed(value),
            }
        } else {
            IntData {
                heap: ManuallyDrop::new((0i64, Box::new(BigInt::from(value)))),
            }
        }
    }

    pub(crate) fn as_i128(&self) -> Option<i128> {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            Some(decode_inline_i(unsafe { &self.inline }))
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                big.to_i128()
            })
        }
    }

    pub(crate) fn expect_i128(&self) -> IonResult<i128> {
        self.as_i128()
            .ok_or_else(|| IonError::decoding_error("Int value exceeds i128 range"))
    }

    pub(crate) fn from_le_signed_bytes(bytes: &[u8]) -> Self {
        if bytes.len() <= 16 {
            let pad = if bytes.last().is_some_and(|&b| b & 0x80 != 0) {
                0xFF
            } else {
                0x00
            };
            let mut buf = [pad; 16];
            buf[..bytes.len()].copy_from_slice(bytes);
            let v = i128::from_le_bytes(buf);
            if (INT_INLINE_MIN..=INT_INLINE_MAX).contains(&v) {
                return IntData {
                    inline: encode_inline_signed(v),
                };
            }
        }
        cold_path!({ IntData::from_bigint(BigInt::from_signed_bytes_le(bytes)) })
    }

    pub(crate) fn to_le_bytes(&self) -> Vec<u8> {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_i(unsafe { &self.inline });
            let bytes: [u8; 16] = value.to_le_bytes();
            let is_neg = value < 0;
            let pad = if is_neg { 0xFF } else { 0x00 };
            let mut len = 16;
            while len > 1 && bytes[len - 1] == pad {
                if (bytes[len - 2] & 0x80 != 0) != is_neg {
                    break;
                }
                len -= 1;
            }
            bytes[..len].to_vec()
        } else {
            cold_path! {
                // SAFETY: heap variant active
                unsafe { &self.heap.1 }.to_signed_bytes_le()
            }
        }
    }

    pub(crate) fn is_zero(&self) -> bool {
        if self.is_inline() {
            decode_inline_i(unsafe { &self.inline }) == 0
        } else {
            false // heap values are never zero (zero is always inline)
        }
    }

    pub(crate) fn is_negative(&self) -> bool {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            decode_inline_i(unsafe { &self.inline }) < 0
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                big.is_negative()
            })
        }
    }

    pub(crate) fn byte_len(&self) -> usize {
        self.to_le_bytes().len()
    }

    pub(crate) fn count_decimal_digits(&self) -> u32 {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_i(unsafe { &self.inline });
            let abs = value.unsigned_abs();
            if abs == 0 {
                1
            } else {
                abs.ilog10() + 1
            }
        } else {
            let s = format!("{self}");
            let s = s.strip_prefix('-').unwrap_or(&s);
            s.len() as u32
        }
    }

    pub(crate) fn unsigned_abs(&self) -> UIntData {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_i(unsafe { &self.inline });
            UIntData::from_u128(value.unsigned_abs())
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                UIntData::from_biguint(big.magnitude().clone())
            })
        }
    }
}

// ===== Neg =====

impl Neg for IntData {
    type Output = IntData;
    fn neg(mut self) -> IntData {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_i(unsafe { &self.inline });
            // wrapping_neg handles INT_INLINE_MIN correctly by overflowing to heap via from_i128
            IntData::from_i128(value.wrapping_neg())
        } else {
            cold_path!({
                // SAFETY: heap variant active. Take ownership of the Box.
                let (_, big) = unsafe { ManuallyDrop::take(&mut self.heap) };
                let negated = -(*big);
                // self's heap was taken; set it to inline zero to prevent double-free in Drop
                // SAFETY: Setting inline to a valid inline-tagged value to prevent double-free
                self.inline = unsafe { IntData::ZERO.inline };
                IntData::from_bigint(negated)
            })
        }
    }
}

// ===== Div =====

impl std::ops::Div<i128> for IntData {
    type Output = IntData;
    fn div(self, rhs: i128) -> IntData {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_i(unsafe { &self.inline });
            IntData::from_i128(value / rhs)
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                let result = big.as_ref() / BigInt::from(rhs);
                IntData::from_bigint(result)
            })
        }
    }
}

impl std::ops::Div<i128> for &IntData {
    type Output = IntData;
    fn div(self, rhs: i128) -> IntData {
        self.clone() / rhs
    }
}

impl std::ops::Div<u128> for UIntData {
    type Output = UIntData;
    fn div(self, rhs: u128) -> UIntData {
        if self.is_inline() {
            // SAFETY: is_inline() confirmed
            let value = decode_inline_u(unsafe { &self.inline });
            UIntData::from_u128(value / rhs)
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                let result = big.as_ref() / BigUint::from(rhs);
                UIntData::from_biguint(result)
            })
        }
    }
}

// ===== MulAssign / DivAssign / RemAssign =====

impl std::ops::MulAssign<i128> for IntData {
    fn mul_assign(&mut self, rhs: i128) {
        *self = self.clone() * rhs;
    }
}

impl std::ops::DivAssign<i128> for IntData {
    fn div_assign(&mut self, rhs: i128) {
        *self = self.clone() / rhs;
    }
}

impl std::ops::RemAssign<i128> for IntData {
    fn rem_assign(&mut self, rhs: i128) {
        *self = self.clone() % rhs;
    }
}

// ===== Mul =====

impl std::ops::Mul<i128> for IntData {
    type Output = IntData;
    fn mul(self, rhs: i128) -> IntData {
        if self.is_inline() {
            let value = decode_inline_i(unsafe { &self.inline });
            if let Some(result) = value.checked_mul(rhs) {
                return IntData::from_i128(result);
            }
            cold_path!({ IntData::from_bigint(BigInt::from(value) * BigInt::from(rhs)) })
        } else {
            cold_path!({
                let big = unsafe { &self.heap.1 };
                IntData::from_bigint(big.as_ref() * BigInt::from(rhs))
            })
        }
    }
}

// ===== Rem =====

impl std::ops::Rem<i128> for IntData {
    type Output = IntData;
    fn rem(self, rhs: i128) -> IntData {
        if self.is_inline() {
            let value = decode_inline_i(unsafe { &self.inline });
            IntData::from_i128(value % rhs)
        } else {
            cold_path!({
                let big = unsafe { &self.heap.1 };
                IntData::from_bigint(big.as_ref() % BigInt::from(rhs))
            })
        }
    }
}

// ===== Add / Sub for IntData =====

impl std::ops::Add for IntData {
    type Output = IntData;
    fn add(self, rhs: IntData) -> IntData {
        if self.is_inline() && rhs.is_inline() {
            // SAFETY: is_inline() confirmed for both
            let a = decode_inline_i(unsafe { &self.inline });
            let b = decode_inline_i(unsafe { &rhs.inline });
            if let Some(result) = a.checked_add(b) {
                return IntData::from_i128(result);
            }
        }
        cold_path!({ IntData::from_bigint(self.to_bigint() + rhs.to_bigint()) })
    }
}

impl std::ops::Sub for IntData {
    type Output = IntData;
    fn sub(self, rhs: IntData) -> IntData {
        if self.is_inline() && rhs.is_inline() {
            // SAFETY: is_inline() confirmed for both
            let a = decode_inline_i(unsafe { &self.inline });
            let b = decode_inline_i(unsafe { &rhs.inline });
            if let Some(result) = a.checked_sub(b) {
                return IntData::from_i128(result);
            }
        }
        cold_path!({ IntData::from_bigint(self.to_bigint() - rhs.to_bigint()) })
    }
}

impl std::ops::Add for UIntData {
    type Output = UIntData;
    fn add(self, rhs: UIntData) -> UIntData {
        if self.is_inline() && rhs.is_inline() {
            let a = decode_inline_u(unsafe { &self.inline });
            let b = decode_inline_u(unsafe { &rhs.inline });
            if let Some(result) = a.checked_add(b) {
                if result <= UINT_INLINE_MAX {
                    return UIntData {
                        inline: encode_inline(result),
                    };
                }
            }
        }
        cold_path!({
            let a = BigUint::from_bytes_le(&self.to_le_bytes());
            let b = BigUint::from_bytes_le(&rhs.to_le_bytes());
            UIntData::from_biguint(a + b)
        })
    }
}

impl std::ops::Sub for UIntData {
    type Output = UIntData;
    fn sub(self, rhs: UIntData) -> UIntData {
        if self.is_inline() && rhs.is_inline() {
            let a = decode_inline_u(unsafe { &self.inline });
            let b = decode_inline_u(unsafe { &rhs.inline });
            if let Some(result) = a.checked_sub(b) {
                return UIntData {
                    inline: encode_inline(result),
                };
            }
        }
        cold_path!({
            let a = BigUint::from_bytes_le(&self.to_le_bytes());
            let b = BigUint::from_bytes_le(&rhs.to_le_bytes());
            UIntData::from_biguint(a - b)
        })
    }
}

// ===== Clone =====

impl Clone for UIntData {
    fn clone(&self) -> Self {
        if self.is_inline() {
            UIntData {
                inline: unsafe { self.inline },
            }
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                UIntData {
                    heap: ManuallyDrop::new((0i64, big.clone())),
                }
            })
        }
    }
}

impl Clone for IntData {
    fn clone(&self) -> Self {
        if self.is_inline() {
            IntData {
                inline: unsafe { self.inline },
            }
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                IntData {
                    heap: ManuallyDrop::new((0i64, big.clone())),
                }
            })
        }
    }
}

// ===== PartialEq / Eq =====

impl PartialEq for UIntData {
    fn eq(&self, other: &Self) -> bool {
        match (self.as_u128(), other.as_u128()) {
            (Some(a), Some(b)) => a == b,
            (None, None) => cold_path!({
                // SAFETY: both heap
                let a = unsafe { &self.heap.1 };
                let b = unsafe { &other.heap.1 };
                a == b
            }),
            _ => false, // normalization guarantees this
        }
    }
}
impl Eq for UIntData {}

impl PartialEq for IntData {
    fn eq(&self, other: &Self) -> bool {
        match (self.as_i128(), other.as_i128()) {
            (Some(a), Some(b)) => a == b,
            (None, None) => cold_path!({
                // SAFETY: both heap
                let a = unsafe { &self.heap.1 };
                let b = unsafe { &other.heap.1 };
                a == b
            }),
            _ => false,
        }
    }
}
impl Eq for IntData {}

// ===== Ord =====

impl PartialOrd for UIntData {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UIntData {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (self.as_u128(), other.as_u128()) {
            (Some(a), Some(b)) => a.cmp(&b),
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => cold_path!({
                // SAFETY: both heap
                let a = unsafe { &self.heap.1 };
                let b = unsafe { &other.heap.1 };
                a.cmp(b)
            }),
        }
    }
}

impl PartialOrd for IntData {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for IntData {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.as_i128(), other.as_i128()) {
            (Some(a), Some(b)) => a.cmp(&b),
            _ => cold_path!({
                let a = self.to_bigint();
                let b = other.to_bigint();
                a.cmp(&b)
            }),
        }
    }
}

impl IntData {
    fn to_bigint(&self) -> BigInt {
        if self.is_inline() {
            BigInt::from(decode_inline_i(unsafe { &self.inline }))
        } else {
            cold_path!({
                // SAFETY: heap variant active
                unsafe { &self.heap.1 }.as_ref().clone()
            })
        }
    }

    /// Normalizes a `BigInt` result: stores inline if it fits, otherwise heap-allocates.
    fn from_bigint(value: BigInt) -> IntData {
        if let Some(v) = value.to_i128() {
            if (INT_INLINE_MIN..=INT_INLINE_MAX).contains(&v) {
                return IntData::from_i128(v);
            }
        }
        IntData {
            heap: ManuallyDrop::new((0i64, Box::new(value))),
        }
    }
}

// ===== Hash =====

impl std::hash::Hash for UIntData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Hash the canonical LE byte representation for consistency
        self.to_le_bytes().hash(state);
    }
}

impl std::hash::Hash for IntData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.to_le_bytes().hash(state);
    }
}

// ===== Debug =====

impl std::fmt::Debug for UIntData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = self.as_u128() {
            write!(f, "UIntData({v})")
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                write!(f, "UIntData({big})")
            })
        }
    }
}

impl std::fmt::Debug for IntData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = self.as_i128() {
            write!(f, "IntData({v})")
        } else {
            cold_path!({
                // SAFETY: heap variant active
                let big = unsafe { &self.heap.1 };
                write!(f, "IntData({big})")
            })
        }
    }
}

// ===== Display =====

impl std::fmt::Display for UIntData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = self.as_u128() {
            return write!(f, "{v}");
        }
        cold_path!({
            // SAFETY: heap variant active
            let big = unsafe { &self.heap.1 };
            write!(f, "{big}")
        })
    }
}

impl std::fmt::Display for IntData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = self.as_i128() {
            return write!(f, "{v}");
        }
        cold_path!({
            // SAFETY: heap variant active
            let big = unsafe { &self.heap.1 };
            write!(f, "{big}")
        })
    }
}

// ===== TryFrom impls =====

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
        if let Some(v) = value.as_u128() {
            if let Ok(i) = i128::try_from(v) {
                if (INT_INLINE_MIN..=INT_INLINE_MAX).contains(&i) {
                    return IntData::from_i128(i);
                }
            }
        }
        // Big value: convert BigUint to BigInt
        let bytes = value.to_le_bytes();
        let big = BigInt::from_bytes_le(Sign::Plus, &bytes);
        IntData {
            heap: ManuallyDrop::new((0i64, Box::new(big))),
        }
    }
}

macro_rules! impl_try_from_data {
    ($($t:ty),*) => ($(
        impl TryFrom<IntData> for $t {
            type Error = IonError;
            fn try_from(value: IntData) -> Result<Self, Self::Error> {
                value.as_i128()
                    .and_then(|v| <$t>::try_from(v).ok())
                    .ok_or_else(|| IonError::decoding_error(
                        concat!("IntData value exceeds range of ", stringify!($t))
                    ))
            }
        }
        impl TryFrom<UIntData> for $t {
            type Error = IonError;
            fn try_from(value: UIntData) -> Result<Self, Self::Error> {
                value.as_u128()
                    .and_then(|v| <$t>::try_from(v).ok())
                    .ok_or_else(|| IonError::decoding_error(
                        concat!("UIntData value exceeds range of ", stringify!($t))
                    ))
            }
        }
        impl TryFrom<&IntData> for $t {
            type Error = IonError;
            fn try_from(value: &IntData) -> Result<Self, Self::Error> {
                value.as_i128()
                    .and_then(|v| <$t>::try_from(v).ok())
                    .ok_or_else(|| IonError::decoding_error(
                        concat!("IntData value exceeds range of ", stringify!($t))
                    ))
            }
        }
        impl TryFrom<&UIntData> for $t {
            type Error = IonError;
            fn try_from(value: &UIntData) -> Result<Self, Self::Error> {
                value.as_u128()
                    .and_then(|v| <$t>::try_from(v).ok())
                    .ok_or_else(|| IonError::decoding_error(
                        concat!("UIntData value exceeds range of ", stringify!($t))
                    ))
            }
        }
    )*)
}

impl_try_from_data!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

// From number types to IntData/UIntData

impl<T> From<T> for IntData
where
    T: Signed + ToBytes<Bytes = Vec<u8>>,
{
    fn from(value: T) -> Self {
        IntData::from_le_signed_bytes(&value.to_le_bytes())
    }
}

impl<T> From<T> for UIntData
where
    T: Unsigned + ToBytes<Bytes = Vec<u8>>,
{
    fn from(value: T) -> Self {
        UIntData::from_le_bytes(&value.to_le_bytes())
    }
}

// ===== Tests =====

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uint_inline_roundtrip() {
        for v in [0u128, 1, 42, u64::MAX as u128, UINT_INLINE_MAX] {
            let d = UIntData::from_u128(v);
            assert!(d.is_inline());
            assert_eq!(d.as_u128(), Some(v));
        }
    }

    #[test]
    fn uint_heap_roundtrip() {
        let v = UINT_INLINE_MAX + 1;
        let d = UIntData::from_u128(v);
        assert!(!d.is_inline());
        assert_eq!(d.as_u128(), Some(v));
    }

    #[test]
    fn uint_u128_max() {
        let d = UIntData::from_u128(u128::MAX);
        assert!(!d.is_inline());
        assert_eq!(d.as_u128(), Some(u128::MAX));
    }

    #[test]
    fn int_inline_roundtrip() {
        for v in [0i128, 1, -1, 42, -42, INT_INLINE_MAX, INT_INLINE_MIN] {
            let d = IntData::from_i128(v);
            assert!(d.is_inline(), "value {v} should be inline");
            assert_eq!(d.as_i128(), Some(v));
        }
    }

    #[test]
    fn int_heap_roundtrip() {
        for v in [i128::MAX, i128::MIN, INT_INLINE_MAX + 1, INT_INLINE_MIN - 1] {
            let d = IntData::from_i128(v);
            assert!(!d.is_inline(), "value {v} should be heap");
            assert_eq!(d.as_i128(), Some(v));
        }
    }

    #[test]
    fn uint_clone_drop() {
        let d = UIntData::from_u128(u128::MAX);
        let d2 = d.clone();
        assert_eq!(d.as_u128(), d2.as_u128());
        drop(d);
        assert_eq!(d2.as_u128(), Some(u128::MAX));
    }

    #[test]
    fn int_neg() {
        assert_eq!(IntData::from_i128(42).neg().as_i128(), Some(-42));
        assert_eq!(IntData::from_i128(-42).neg().as_i128(), Some(42));
        assert_eq!(IntData::from_i128(0).neg().as_i128(), Some(0));
        let neg_min = IntData::from_i128(i128::MIN).neg();
        assert!(neg_min.as_i128().is_none());
    }

    #[test]
    fn int_neg_power_of_two_boundaries() {
        for v in [256i128, 65536, -256, -128, 16777216] {
            let d = IntData::from_i128(v);
            let neg = d.neg();
            assert_eq!(neg.as_i128(), Some(-v));
            assert_eq!(neg.neg().as_i128(), Some(v));
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
        assert!(d.is_inline());
        assert_eq!(d.as_u128(), Some(42));
    }

    #[test]
    fn int_from_signed_bytes_le_normalizes() {
        let d = IntData::from_le_signed_bytes(&[42]);
        assert!(d.is_inline());
        assert_eq!(d.as_i128(), Some(42));
        let d = IntData::from_le_signed_bytes(&[0xFE]);
        assert!(d.is_inline());
        assert_eq!(d.as_i128(), Some(-2));
    }

    #[test]
    fn uint_ordering() {
        assert!(UIntData::from_u128(1) < UIntData::from_u128(2));
        assert!(UIntData::from_u128(42) < UIntData::from_u128(u128::MAX));
    }

    #[test]
    fn int_ordering() {
        assert!(IntData::from_i128(-1) < IntData::from_i128(0));
        assert!(IntData::from_i128(0) < IntData::from_i128(1));
        assert!(IntData::from_i128(42) < IntData::from_i128(i128::MAX));
    }

    #[test]
    fn uint_display() {
        assert_eq!(format!("{}", UIntData::from_u128(0)), "0");
        assert_eq!(format!("{}", UIntData::from_u128(42)), "42");
        assert_eq!(
            format!("{}", UIntData::from_u128(u128::MAX)),
            format!("{}", u128::MAX)
        );
    }

    #[test]
    fn int_display() {
        assert_eq!(format!("{}", IntData::from_i128(0)), "0");
        assert_eq!(format!("{}", IntData::from_i128(-42)), "-42");
        assert_eq!(
            format!("{}", IntData::from_i128(i128::MAX)),
            format!("{}", i128::MAX)
        );
        assert_eq!(
            format!("{}", IntData::from_i128(i128::MIN)),
            format!("{}", i128::MIN)
        );
    }

    #[test]
    fn uint_big_from_bytes_display() {
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        let d = UIntData::from_le_bytes(&bytes);
        assert!(!d.is_inline());
        assert_eq!(d.as_u128(), None);
        assert_eq!(format!("{d}"), "340282366920938463463374607431768211456");
    }

    #[test]
    fn int_big_from_bytes_display() {
        let mut bytes = vec![0u8; 18];
        bytes[16] = 1;
        let d = IntData::from_le_signed_bytes(&bytes);
        assert!(!d.is_inline());
        assert_eq!(format!("{d}"), "340282366920938463463374607431768211456");
        let neg = d.neg();
        assert_eq!(format!("{neg}"), "-340282366920938463463374607431768211456");
    }

    #[test]
    fn hash_consistency() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let hash = |d: &UIntData| {
            let mut h = DefaultHasher::new();
            d.hash(&mut h);
            h.finish()
        };
        assert_eq!(
            hash(&UIntData::from_u128(42)),
            hash(&UIntData::from_u128(42))
        );
    }

    #[test]
    fn send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<UIntData>();
        assert_send_sync::<IntData>();
    }

    #[test]
    fn to_bytes_le_roundtrip() {
        for v in [
            0u128,
            1,
            42,
            u64::MAX as u128,
            UINT_INLINE_MAX,
            UINT_INLINE_MAX + 1,
            u128::MAX,
        ] {
            let d = UIntData::from_u128(v);
            let d2 = UIntData::from_le_bytes(&d.to_le_bytes());
            assert_eq!(d, d2, "UInt roundtrip failed for {v}");
        }
        for v in [
            0i128,
            1,
            -1,
            42,
            -42,
            INT_INLINE_MAX,
            INT_INLINE_MIN,
            i128::MAX,
            i128::MIN,
        ] {
            let d = IntData::from_i128(v);
            let d2 = IntData::from_le_signed_bytes(&d.to_le_bytes());
            assert_eq!(d, d2, "Int roundtrip failed for {v}");
        }
    }

    #[test]
    fn uint_to_be_bytes() {
        assert_eq!(UIntData::from_u128(0).to_be_bytes(), vec![0]);
        assert_eq!(UIntData::from_u128(0xFF).to_be_bytes(), vec![0xFF]);
        assert_eq!(UIntData::from_u128(0x0102).to_be_bytes(), vec![0x01, 0x02]);
        assert_eq!(
            UIntData::from_u128(u128::MAX).to_be_bytes(),
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

    #[test]
    fn int_byte_len() {
        assert_eq!(IntData::from_i128(0).byte_len(), 1);
        assert_eq!(IntData::from_i128(1).byte_len(), 1);
        assert_eq!(IntData::from_i128(127).byte_len(), 1);
        assert_eq!(IntData::from_i128(128).byte_len(), 2);
        assert_eq!(IntData::from_i128(-1).byte_len(), 1);
        assert_eq!(IntData::from_i128(-128).byte_len(), 1);
        assert_eq!(IntData::from_i128(-129).byte_len(), 2);
    }

    #[test]
    fn int_is_zero() {
        assert!(IntData::from_i128(0).is_zero());
        assert!(!IntData::from_i128(1).is_zero());
        assert!(!IntData::from_i128(-1).is_zero());
    }

    #[test]
    fn int_arithmetic() {
        let a = IntData::from_i128(100);
        let b = IntData::from_i128(42);
        assert_eq!((a.clone() + b.clone()).as_i128(), Some(142));
        assert_eq!((a.clone() - b.clone()).as_i128(), Some(58));
        assert_eq!((a.clone() * 3).as_i128(), Some(300));
        assert_eq!((a.clone() / 10).as_i128(), Some(10));
        assert_eq!((a.clone() % 30).as_i128(), Some(10));

        // Negative
        let c = IntData::from_i128(-50);
        assert_eq!((a.clone() + c.clone()).as_i128(), Some(50));
        assert_eq!((c.clone() - a.clone()).as_i128(), Some(-150));
    }

    #[test]
    fn int_assign_ops() {
        let mut v = IntData::from_i128(100);
        v *= 3;
        assert_eq!(v.as_i128(), Some(300));
        v /= 10;
        assert_eq!(v.as_i128(), Some(30));
        v %= 7;
        assert_eq!(v.as_i128(), Some(2));
    }

    #[test]
    fn uint_arithmetic() {
        let a = UIntData::from_u128(100);
        let b = UIntData::from_u128(42);
        assert_eq!((a.clone() + b.clone()).as_u128(), Some(142));
        assert_eq!((a.clone() - b.clone()).as_u128(), Some(58));
    }

    #[test]
    fn uint_from_str_radix() {
        assert_eq!(
            UIntData::from_str_radix("0", 10).unwrap().as_u128(),
            Some(0)
        );
        assert_eq!(
            UIntData::from_str_radix("255", 10).unwrap().as_u128(),
            Some(255)
        );
        assert_eq!(
            UIntData::from_str_radix("FF", 16).unwrap().as_u128(),
            Some(255)
        );
        assert_eq!(
            UIntData::from_str_radix("11111111", 2).unwrap().as_u128(),
            Some(255)
        );
        // Big value exceeding u128
        let big = UIntData::from_str_radix("340282366920938463463374607431768211456", 10).unwrap();
        assert!(!big.is_inline());
        assert!(UIntData::from_str_radix("xyz", 10).is_err());
    }
}
