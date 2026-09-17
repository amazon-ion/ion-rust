//! A compact, immutable sign-magnitude integer used to back the crate's numeric
//! types.
//!
//! [`OverflowingInt`] is a 16-byte tagged union, aligned to at most 8. It stores
//! a sign-magnitude integer inline when the magnitude fits in 126 bits and
//! heap-allocates a [`BigUint`] beyond that. Avoiding align 16 is the point of
//! the type: an inline `i128` (or a `Box<BigInt>` paired with a sign field)
//! forces align 16, which pads every enclosing enum. This type is align 8 on
//! common targets and align 4 on 32-bit ABIs where `u64` aligns to 4 (e.g.
//! `i686`); the invariant it upholds is only that it is never align 16.
//!
//! # Invariants
//!
//! Everything `unsafe` in this module rests on three properties, all enforced by
//! construction rather than by callers:
//!
//! 1. **Tag agreement** — bit 63 of the word at offset 0 always identifies the
//!    active variant (1 = inline, 0 = heap). Both variants keep a
//!    fully-initialized `u64` at offset 0 that this type controls, so the tag is
//!    read through the dedicated `tag` arm and never by materializing the `Box`
//!    as an integer. The sign shares this word at bit 62 in both variants, so the
//!    tag and sign reads are identical code on either arm.
//! 2. **Canonicality** — a magnitude is heap-backed **iff** it does not fit
//!    inline. Every constructor demotes a value that fits. This is what makes
//!    comparison, hashing, and the zero test correct without ever promoting a
//!    value: a heap-backed magnitude is always larger than any inline one, and
//!    is never zero.
//! 3. **Freed exactly once** — [`Drop`] lives on this type alone. Every wrapper
//!    relies on drop glue and implements no `Drop` of its own, so there is
//!    exactly one place that can free the heap allocation.
//!
//! The type is **immutable**: no `&mut self` method exists other than `Drop`,
//! and no accessor lends out a `&mut` into the payload. That is what reduces the
//! first two invariants to a construction-time obligation.
//!
//! Sign semantics follow the General Decimal Arithmetic Specification
//! (<https://speleotrove.com/decimal/decarith.html>) reduced to an integer with
//! no exponent and no rounding context: a negative zero is represented
//! faithfully and never normalized away; deciding whether `-0` is *meaningful*
//! belongs to the wrapper.

// This type has no non-test consumer yet; the numeric wrapper types built on it
// are added separately. `pub(crate)` items reachable only from tests still trip
// `dead_code`, so the module carries a blanket allow until those consumers land,
// at which point it is narrowed to per-item allows.
#![allow(dead_code)]

use crate::types::decimal::Sign;
use ice_code::ice as cold_path;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{Pow, ToPrimitive};
use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::mem::ManuallyDrop;

/// Number of magnitude bits available inline. The offset-0 word spends its top
/// two bits — bit 63 on the tag and bit 62 on the sign — leaving 126 magnitude
/// bits across the two words, two short of an `i128`.
const INLINE_MAGNITUDE_BITS: u32 = 126;

/// How many magnitude bits `words[0]` carries: 64 bits minus the 2 overhead bits
/// at the top (bit 63 tag, bit 62 sign). `words[1]` carries the remaining 64, so
/// the two words hold `62 + 64 == 126` magnitude bits. The magnitude is split at
/// this bit.
const INLINE_LOW_MAGNITUDE_BITS: u32 = 62;

// The low/high split must account for exactly the inline capacity, or the
// encode/decode pair below would silently corrupt magnitudes.
const _: () = assert!(INLINE_LOW_MAGNITUDE_BITS + 64 == INLINE_MAGNITUDE_BITS);

/// Bit index of the tag within the offset-0 word (1 = inline, 0 = heap). Shared
/// by both variants; see the module invariants.
const TAG_BIT: u32 = 63;

/// Bit index of the sign within the offset-0 word (1 = negative). Shared by both
/// variants, so the sign read is variant-independent.
const SIGN_BIT: u32 = 62;

// The tag and sign must sit above the low magnitude bits `words[0]` carries, or
// they would collide with the magnitude and silently corrupt the value.
const _: () = assert!(SIGN_BIT == INLINE_LOW_MAGNITUDE_BITS && TAG_BIT == SIGN_BIT + 1);
// The tag must be the most-significant bit. `PartialEq`'s raw-`words` fast path
// relies on `words[0]` having no bit above the tag (see its SAFETY comment).
const _: () = assert!(TAG_BIT == u64::BITS - 1);

/// Mask selecting the low magnitude bits carried in `words[0]` (bits `0..=61`).
const INLINE_LOW_MAGNITUDE_MASK: u64 = (1u64 << INLINE_LOW_MAGNITUDE_BITS) - 1;

/// The exclusive upper bound on an inline magnitude: `2^126`.
const INLINE_LIMIT: u128 = 1u128 << INLINE_MAGNITUDE_BITS;

/// Maps a sign to its packed bit (1 = negative). The one place this mapping is
/// spelled, shared by every constructor.
#[inline]
fn sign_bit(sign: Sign) -> u64 {
    u64::from(matches!(sign, Sign::Negative))
}

/// A 16-byte sign-magnitude integer, aligned to at most 8. See the module
/// documentation for the layout and the invariants this type owns.
#[repr(C)]
pub(crate) union OverflowingInt {
    /// The tag word alone. Every tag *and* sign read goes through this arm (they
    /// share bits 63 and 62 of the offset-0 word in both variants), never through
    /// `words` by value — reading `words` while the heap variant is active would
    /// materialize the `Box` as an integer.
    tag: u64,
    /// Inline variant (tag bit == 1): `words[0]` holds the tag (bit 63), the sign
    /// (bit 62), and the low 62 magnitude bits (bits `0..=61`); `words[1]` holds
    /// the high 64 magnitude bits.
    words: [u64; 2],
    /// Heap variant (tag bit == 0).
    heap: ManuallyDrop<HeapValue>,
}

/// The heap payload. Field order is deliberate: `meta` first, so offset 0 is
/// always a fully-initialized `u64` this type controls, independent of pointer
/// representation, width, and endianness.
#[repr(C)]
struct HeapValue {
    /// Bit 63: always 0 (the heap tag). Bit 62: sign (1 = negative). Same tag and
    /// sign placement as the inline word, so both are read by the same code.
    meta: u64,
    /// The magnitude. Always `>= 2^126` by canonicality, and therefore never
    /// zero.
    value: Box<BigUint>,
}

// `raw0` reads the offset-0 `u64` of whichever variant is active; for the heap
// variant that soundness rests on `meta` being `HeapValue`'s first field. Pin it
// so a field reorder fails the build rather than silently reading pointer bytes.
const _: () = assert!(std::mem::offset_of!(HeapValue, meta) == 0);

impl HeapValue {
    /// Builds a heap payload with the tag clear (bit 63 == 0) and the sign in
    /// bit 62 — the same encoding as the inline word. This is the only place that
    /// *computes* `meta` from a `Sign` (`Clone` copies an already-valid `meta`):
    /// because the tag and sign are now adjacent, a stray shift here would make a
    /// heap value read as inline (`is_inline` true), which is UB rather than a
    /// wrong answer, so the invariant is checked on every construction.
    #[inline]
    fn new(sign: Sign, value: Box<BigUint>) -> Self {
        let meta = sign_bit(sign) << SIGN_BIT;
        debug_assert_eq!(meta >> TAG_BIT, 0, "heap meta must leave the tag bit clear");
        HeapValue { meta, value }
    }
}

/// A borrowed view of a magnitude, for comparison and byte emission without
/// allocating. MUST NOT appear in a public signature.
pub(crate) enum Magnitude<'a> {
    Small(u128),
    Big(&'a BigUint),
}

impl OverflowingInt {
    /// Positive zero.
    // Inline: tag = 1 (bit 63), sign = positive (bit 62 = 0), magnitude = 0.
    pub(crate) const ZERO: Self = Self {
        words: [1 << TAG_BIT, 0],
    };

    /// Negative zero. Meaningful to `Coefficient`; forbidden by `IntData`.
    // Inline: tag = 1 (bit 63), sign = negative (bit 62 = 1), magnitude = 0.
    pub(crate) const NEGATIVE_ZERO: Self = Self {
        words: [(1 << TAG_BIT) | (1 << SIGN_BIT), 0],
    };

    // ===== Construction =====

    /// Builds the inline variant. The caller guarantees `magnitude < 2^126`.
    #[inline]
    fn from_inline(sign: Sign, magnitude: u128) -> Self {
        debug_assert!(magnitude < INLINE_LIMIT, "magnitude does not fit inline");
        // Mask in the `u128` domain: `magnitude < 2^126` does NOT bound `magnitude
        // as u64`, so masking after the cast is what keeps magnitude bits 62/63
        // out of the sign/tag positions. This mask is load-bearing, not redundant.
        let low = (magnitude & INLINE_LOW_MAGNITUDE_MASK as u128) as u64;
        // `words[0]`: bits 0..=61 the low magnitude bits, bit 62 the sign, bit 63
        // the tag. `words[1]` holds the high magnitude bits.
        let w0 = low | (sign_bit(sign) << SIGN_BIT) | (1 << TAG_BIT);
        let w1 = (magnitude >> INLINE_LOW_MAGNITUDE_BITS) as u64;
        Self { words: [w0, w1] }
    }

    /// Builds a value from a sign and a `u128` magnitude, storing it inline when
    /// it fits (`magnitude < 2^126`) and promoting to the heap variant otherwise
    /// — a `u128` reaches up to `2^128 - 1`, above the inline limit.
    pub(crate) fn from_sign_and_magnitude(sign: Sign, magnitude: u128) -> Self {
        if magnitude < INLINE_LIMIT {
            Self::from_inline(sign, magnitude)
        } else {
            cold_path! { Self::from_sign_and_big_magnitude(sign, BigUint::from(magnitude)) }
        }
    }

    /// Builds a value from a sign and an arbitrary-precision magnitude. Demotes
    /// to the inline variant whenever the magnitude fits, preserving
    /// canonicality — including a non-minimal `BigUint` zero, which demotes to
    /// inline positive/negative zero.
    pub(crate) fn from_sign_and_big_magnitude(sign: Sign, magnitude: BigUint) -> Self {
        if let Some(small) = magnitude.to_u128() {
            if small < INLINE_LIMIT {
                return Self::from_inline(sign, small);
            }
        }
        cold_path! {{
            Self {
                heap: ManuallyDrop::new(HeapValue::new(sign, Box::new(magnitude))),
            }
        }}
    }

    /// Returns a copy of `self` with the given sign, preserving the
    /// representation and never normalizing a zero. This is the one operation
    /// that *sets* a sign rather than deriving one from a magnitude; the wrapper
    /// that must not produce `-0` guards zero at its own call site.
    pub(crate) fn with_sign(&self, sign: Sign) -> Self {
        if self.is_inline() {
            // SAFETY: the inline variant is active (tag bit == 1).
            let magnitude = unsafe { self.inline_magnitude() };
            Self::from_inline(sign, magnitude)
        } else {
            cold_path! {{
                // SAFETY: the heap variant is active (tag bit == 0).
                let heap = unsafe { self.heap_ref() };
                Self {
                    heap: ManuallyDrop::new(HeapValue::new(sign, heap.value.clone())),
                }
            }}
        }
    }

    // ===== Raw layout access =====

    /// The word at offset 0: `words[0]` for the inline variant, `meta` for the
    /// heap variant. Reading it never touches pointer bytes.
    #[inline]
    fn raw0(&self) -> u64 {
        // SAFETY: both variants keep a fully-initialized `u64` at offset 0 that
        // this type controls. Reading offset 0 alone never materializes the
        // `Box`, so no provenance question arises.
        unsafe { self.tag }
    }

    #[inline]
    fn is_inline(&self) -> bool {
        (self.raw0() >> TAG_BIT) & 1 == 1
    }

    /// Reconstructs the inline magnitude from the two words.
    ///
    /// # Safety
    ///
    /// The inline variant must be active (tag bit == 1). Reading `words` by
    /// value is sound only then, because neither word carries pointer provenance
    /// in the inline variant.
    #[inline]
    unsafe fn inline_magnitude(&self) -> u128 {
        let w = unsafe { self.words };
        ((w[0] & INLINE_LOW_MAGNITUDE_MASK) as u128) | ((w[1] as u128) << INLINE_LOW_MAGNITUDE_BITS)
    }

    /// Borrows the heap payload.
    ///
    /// # Safety
    ///
    /// The heap variant must be active (tag bit == 0).
    #[inline]
    unsafe fn heap_ref(&self) -> &HeapValue {
        unsafe { &self.heap }
    }

    // ===== Accessors =====

    /// The sign. Positive for either zero unless the value is a `-0` built
    /// through [`Self::NEGATIVE_ZERO`] or [`Self::with_sign`].
    pub(crate) fn sign(&self) -> Sign {
        // The sign is bit 62 of the offset-0 word in both variants, so this reads
        // it the same way regardless of the tag — no tag-dependent branch, no
        // `Box` materialized.
        let negative = (self.raw0() >> SIGN_BIT) & 1 == 1;
        if negative {
            Sign::Negative
        } else {
            Sign::Positive
        }
    }

    /// Whether the value is zero of either sign. Correct by canonicality: a
    /// heap-backed magnitude is never zero, so only the inline word is read.
    pub(crate) fn is_zero(&self) -> bool {
        if self.is_inline() {
            // SAFETY: the inline variant is active.
            unsafe { self.inline_magnitude() == 0 }
        } else {
            cold_path! { false }
        }
    }

    /// The magnitude as a `u128` when it fits, ignoring the sign. Factored
    /// through `magnitude_ref` so the tag dispatch and its cold marking live in
    /// one place, matching `magnitude_as_big`.
    fn magnitude_as_u128(&self) -> Option<u128> {
        match self.magnitude_ref() {
            Magnitude::Small(magnitude) => Some(magnitude),
            Magnitude::Big(big) => big.to_u128(),
        }
    }

    /// The value as an `i128` when it fits. Whether it fits depends on the sign,
    /// since the signed range is asymmetric: `i128::MIN`'s magnitude is `2^127`,
    /// which no unsigned fit test accepts.
    pub(crate) fn as_i128(&self) -> Option<i128> {
        let magnitude = self.magnitude_as_u128()?;
        match self.sign() {
            Sign::Positive => i128::try_from(magnitude).ok(),
            Sign::Negative => {
                // `i128::MIN`'s magnitude is `(i128::MAX as u128) + 1`. Casting
                // that magnitude to `i128` wraps to `i128::MIN`, whose negation
                // wraps back to `i128::MIN` — exactly the value we want. Any
                // larger magnitude does not fit.
                if magnitude <= (i128::MAX as u128) + 1 {
                    Some((magnitude as i128).wrapping_neg())
                } else {
                    None
                }
            }
        }
    }

    /// The value as a `u128` when it fits. A negative non-zero value never fits;
    /// a negative zero has value `0` and fits.
    pub(crate) fn as_u128(&self) -> Option<u128> {
        if matches!(self.sign(), Sign::Negative) && !self.is_zero() {
            return None;
        }
        self.magnitude_as_u128()
    }

    /// The bit width of the magnitude (`0` for zero). Allocation-free on both
    /// arms, which is what lets the scaling guards and byte-length calculations
    /// avoid a conversion.
    pub(crate) fn bits(&self) -> u64 {
        if self.is_inline() {
            // SAFETY: the inline variant is active.
            let magnitude = unsafe { self.inline_magnitude() };
            (u128::BITS - magnitude.leading_zeros()) as u64
        } else {
            cold_path! { unsafe { self.heap_ref() }.value.bits() }
        }
    }

    /// A borrowed view of the magnitude, for comparison and byte emission. MUST
    /// NOT appear in a public signature.
    pub(crate) fn magnitude_ref(&self) -> Magnitude<'_> {
        if self.is_inline() {
            // SAFETY: the inline variant is active.
            Magnitude::Small(unsafe { self.inline_magnitude() })
        } else {
            cold_path! {{
                // SAFETY: the heap variant is active.
                let heap = unsafe { self.heap_ref() };
                Magnitude::Big(&heap.value)
            }}
        }
    }

    // ===== Sign-only arithmetic =====

    /// The absolute value: `+0` for either zero (decArith `abs`).
    pub(crate) fn abs(&self) -> Self {
        self.with_sign(Sign::Positive)
    }

    /// Unary negation, defined by decArith as `subtract('0', x)`: negating
    /// **either** zero yields `+0`, and negating a non-zero value flips the sign.
    /// This is **not** a bare sign flip.
    pub(crate) fn minus(&self) -> Self {
        if self.is_zero() {
            self.with_sign(Sign::Positive)
        } else {
            let flipped = match self.sign() {
                Sign::Negative => Sign::Positive,
                Sign::Positive => Sign::Negative,
            };
            self.with_sign(flipped)
        }
    }

    // ===== Scaling by a power of ten =====

    /// `self * 10^k`, preserving `self`'s sign. A zero receiver scales to zero
    /// (keeping its sign) without materializing `10^k`. A non-zero product
    /// promotes to the heap when it exceeds `u128` rather than panicking or
    /// wrapping.
    ///
    /// **Unlike [`Self::div_rem_pow10`] and [`Self::cmp_magnitude_scaled`], this
    /// is NOT hostile-`k`-safe.** A multiply's result genuinely has `~k` decimal
    /// digits, so there is nothing to short-circuit: a large `k` materializes a
    /// proportionally large `10^k`. The caller MUST bound `k` (e.g. by a decimal
    /// exponent range). The consuming wrappers do — they reach a power of ten
    /// only through the two guarded operations above, never through an untrusted
    /// exponent here.
    pub(crate) fn mul_pow10(&self, k: u64) -> Self {
        if self.is_zero() {
            // Zero magnitude: `0 * 10^k == 0`. Keep the sign and representation.
            return self.clone();
        }
        let sign = self.sign();
        if let Magnitude::Small(magnitude) = self.magnitude_ref() {
            // Fast path: stay in `u128` when `10^k` and the product both fit.
            if let Some(product) = pow10_u128(k).and_then(|p| magnitude.checked_mul(p)) {
                return Self::from_sign_and_magnitude(sign, product);
            }
        }
        cold_path! {{
            let scaled = self.magnitude_as_big() * pow10_big(k);
            Self::from_sign_and_big_magnitude(sign, scaled)
        }}
    }

    /// `(self / 10^k, self % 10^k)`, both carrying `self`'s sign (the remainder
    /// takes the dividend's sign, per decArith). Division by zero is unreachable
    /// by construction: `10^k` is never zero.
    ///
    /// Short-circuits without materializing `10^k` when the magnitude is provably
    /// narrower than `10^k` (quotient zero, remainder `self`), which also makes a
    /// hostile `k` cheap.
    pub(crate) fn div_rem_pow10(&self, k: u64) -> (Self, Self) {
        let sign = self.sign();
        // `10^k >= 8^k = 2^(3k)`, so a magnitude of at most `3k` bits is strictly
        // less than `10^k`: the quotient is zero and the remainder is `self`.
        // Also covers a zero receiver (0 bits) and any hostile `k`.
        if (self.bits() as u128) <= 3 * (k as u128) {
            return (Self::from_sign_and_magnitude(sign, 0), self.clone());
        }
        if let Magnitude::Small(magnitude) = self.magnitude_ref() {
            if let Some(divisor) = pow10_u128(k) {
                let quotient = Self::from_sign_and_magnitude(sign, magnitude / divisor);
                let remainder = Self::from_sign_and_magnitude(sign, magnitude % divisor);
                return (quotient, remainder);
            }
        }
        cold_path! {{
            let (quotient, remainder) = self.magnitude_as_big().div_rem(&pow10_big(k));
            (
                Self::from_sign_and_big_magnitude(sign, quotient),
                Self::from_sign_and_big_magnitude(sign, remainder),
            )
        }}
    }

    /// Compares `|self| * 10^k` against `|other|` — magnitudes only, signs
    /// ignored. Callers own the sign logic (see `Coefficient`'s comparison).
    ///
    /// Decides the extreme cases from bit widths alone, without materializing
    /// `10^k`, so a hostile `k` cannot force an unbounded allocation. `10^k` is
    /// materialized only when the two widths are close enough that neither side
    /// dominates — which bounds `k` by the operands' own size.
    pub(crate) fn cmp_magnitude_scaled(&self, k: u64, other: &Self) -> Ordering {
        // Zero receiver first, ahead of the width guard: `0 * 10^k == 0` for any
        // `k`, so the result is `Equal` iff `other` is also zero, else `Less`.
        if self.is_zero() {
            return if other.is_zero() {
                Ordering::Equal
            } else {
                Ordering::Less
            };
        }
        let a_bits = self.bits() as u128;
        let b_bits = other.bits() as u128;
        let k = k as u128;
        // Lower bound: `bits(|self| * 10^k) >= a_bits + 3k` (since `10^k >= 2^3k`).
        // If that lower bound already exceeds `b_bits`, the scaled value is
        // certainly greater.
        if a_bits + 3 * k > b_bits {
            return Ordering::Greater;
        }
        // Upper bound: `bits(|self| * 10^k) <= a_bits + 4k` (since `10^k < 2^4k`).
        // If that upper bound is still below `b_bits`, it is certainly less.
        if a_bits + 4 * k < b_bits {
            return Ordering::Less;
        }
        let k = k as u64;
        // Neither guard fired, so `k <= (b_bits - a_bits) / 3`: `10^k` is bounded
        // by `other`'s size. Fast path stays in `u128` where everything fits.
        if let (Some(a), Some(b)) = (self.magnitude_as_u128(), other.magnitude_as_u128()) {
            if let Some(scaled) = pow10_u128(k).and_then(|p| a.checked_mul(p)) {
                return scaled.cmp(&b);
            }
        }
        cold_path! {{
            let scaled = self.magnitude_as_big() * pow10_big(k);
            // Compare against a borrow of `other`'s magnitude — no clone.
            match other.magnitude_ref() {
                Magnitude::Small(b) => scaled.cmp(&BigUint::from(b)),
                Magnitude::Big(b) => scaled.cmp(b),
            }
        }}
    }

    /// The magnitude as an owned `BigUint`. Allocates; used only on cold paths.
    fn magnitude_as_big(&self) -> BigUint {
        match self.magnitude_ref() {
            Magnitude::Small(magnitude) => BigUint::from(magnitude),
            Magnitude::Big(big) => big.clone(),
        }
    }

    /// Magnitude comparison, ignoring sign. Allocation-free: an inline/heap pair
    /// is decided from the tag alone by canonicality (heap implies the larger
    /// magnitude).
    fn cmp_magnitude(&self, other: &Self) -> Ordering {
        match (self.is_inline(), other.is_inline()) {
            (true, true) => {
                // SAFETY: both inline variants are active.
                let a = unsafe { self.inline_magnitude() };
                let b = unsafe { other.inline_magnitude() };
                a.cmp(&b)
            }
            (true, false) => cold_path! { Ordering::Less },
            (false, true) => cold_path! { Ordering::Greater },
            (false, false) => cold_path! {{
                // SAFETY: both heap variants are active.
                let a = unsafe { self.heap_ref() };
                let b = unsafe { other.heap_ref() };
                a.value.cmp(&b.value)
            }},
        }
    }
}

/// `10^k` as a `u128`, or `None` if it does not fit.
#[inline]
fn pow10_u128(k: u64) -> Option<u128> {
    u32::try_from(k).ok().and_then(|e| 10u128.checked_pow(e))
}

/// `10^k` as a `BigUint`. Cold: callers reach it only after a width guard has
/// bounded `k` by the operands' size, so the allocation is bounded.
fn pow10_big(k: u64) -> BigUint {
    BigUint::from(10u32).pow(k)
}

impl Clone for OverflowingInt {
    fn clone(&self) -> Self {
        if self.is_inline() {
            // SAFETY: the inline variant is active; the words carry no
            // provenance and are trivially copyable.
            Self {
                words: unsafe { self.words },
            }
        } else {
            cold_path! {{
                // SAFETY: the heap variant is active.
                let heap = unsafe { self.heap_ref() };
                Self {
                    heap: ManuallyDrop::new(HeapValue {
                        meta: heap.meta,
                        value: heap.value.clone(),
                    }),
                }
            }}
        }
    }
}

impl Drop for OverflowingInt {
    fn drop(&mut self) {
        if !self.is_inline() {
            cold_path! {{
                // SAFETY: the heap variant is active and `Drop` runs exactly
                // once, so this frees the `Box` exactly once. Nothing else in the
                // crate implements `Drop` for a wrapper around this type.
                unsafe { ManuallyDrop::drop(&mut self.heap) }
            }}
        }
    }
}

impl PartialEq for OverflowingInt {
    fn eq(&self, other: &Self) -> bool {
        // Fast path: two inline values are equal iff their words are
        // bit-identical. Canonicality makes the inline encoding of a value unique
        // — tag, sign, and all 126 magnitude bits are defined, with no padding or
        // spare bits — so a bytewise compare of the pure-integer words decides it,
        // including `-0` vs `+0` (their sign bits differ).
        //
        // The `is_inline` guard is load-bearing and must not be dropped, however
        // tempting: while comparing raw bits would give the right *answer* (the
        // tag bit distinguishes inline from heap, and two heap values with equal
        // bits share the same exclusively-owned allocation), reading `words` while
        // the heap variant is active reads the boxed pointer as an integer and,
        // wherever `HeapValue` has trailing padding after the pointer (a 4-byte
        // `Box` under an ABI where `meta`'s `u64` still forces align 8 — i686, and
        // even wasm32, where the union itself has no tail padding), reads
        // uninitialized padding bytes — UB, confirmed under Miri. Two distinct heap
        // allocations of the same number fall through to `cmp`.
        if self.is_inline() && other.is_inline() {
            return unsafe { self.words == other.words };
        }
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for OverflowingInt {}

impl PartialOrd for OverflowingInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OverflowingInt {
    /// decArith `compare-total` (total order), **not** `compare`: `-0 < +0`.
    /// Sign first (negative below positive); equal signs compare magnitudes, and
    /// the magnitude comparison is **reversed** when both are negative, because a
    /// larger magnitude is a smaller number.
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.sign(), other.sign()) {
            (Sign::Negative, Sign::Positive) => Ordering::Less,
            (Sign::Positive, Sign::Negative) => Ordering::Greater,
            (Sign::Positive, Sign::Positive) => self.cmp_magnitude(other),
            (Sign::Negative, Sign::Negative) => self.cmp_magnitude(other).reverse(),
        }
    }
}

impl Hash for OverflowingInt {
    /// Sign, then magnitude — the same shape as [`Ord`]. Canonicality keeps this
    /// consistent with [`Eq`]: an inline value and a heap value can never be
    /// equal, so their differing magnitude encodings never need to agree.
    fn hash<H: Hasher>(&self, state: &mut H) {
        matches!(self.sign(), Sign::Negative).hash(state);
        match self.magnitude_ref() {
            Magnitude::Small(magnitude) => magnitude.hash(state),
            Magnitude::Big(big) => big.hash(state),
        }
    }
}

impl Debug for OverflowingInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let sign = match self.sign() {
            Sign::Negative => "-",
            Sign::Positive => "",
        };
        match self.magnitude_ref() {
            Magnitude::Small(magnitude) => {
                write!(f, "OverflowingInt::Inline({sign}{magnitude})")
            }
            Magnitude::Big(big) => write!(f, "OverflowingInt::Heap({sign}{big})"),
        }
    }
}

// ===== Conversions =====

impl From<u128> for OverflowingInt {
    fn from(value: u128) -> Self {
        Self::from_sign_and_magnitude(Sign::Positive, value)
    }
}

impl From<i128> for OverflowingInt {
    fn from(value: i128) -> Self {
        let sign = if value < 0 {
            Sign::Negative
        } else {
            Sign::Positive
        };
        Self::from_sign_and_magnitude(sign, value.unsigned_abs())
    }
}

impl From<BigUint> for OverflowingInt {
    fn from(value: BigUint) -> Self {
        Self::from_sign_and_big_magnitude(Sign::Positive, value)
    }
}

impl From<BigInt> for OverflowingInt {
    fn from(value: BigInt) -> Self {
        let (bigint_sign, magnitude) = value.into_parts();
        // A `BigInt`'s three-valued sign maps both `Plus` and `NoSign` to
        // positive; only `Minus` is negative. A `NoSign -> Negative` slip is
        // exactly the `-0` that `IntData` forbids.
        let sign = match bigint_sign {
            num_bigint::Sign::Minus => Sign::Negative,
            num_bigint::Sign::Plus | num_bigint::Sign::NoSign => Sign::Positive,
        };
        Self::from_sign_and_big_magnitude(sign, magnitude)
    }
}

// Conversions from primitives narrower than `i128`/`u128` are intentionally not
// provided: a consumer casts to `i128`/`u128` and uses those paths. That keeps
// the entry points to the two widths the inline representation is measured
// against, rather than fanning out a conversion surface with no consumer here.

// The whole `Element` byte budget rests on this size and alignment. The
// alignment is asserted as `<= 8` rather than `== 8`: the point is that the type
// is not align 16 (which would pad every enclosing enum), and `u64` aligns to 4
// rather than 8 under some 32-bit ABIs (e.g. `i686-unknown-linux-gnu`), where
// this type is correctly align 4. `#[repr(C)]` over `u64` words keeps the size
// pointer-width independent.
const _: () = assert!(size_of::<OverflowingInt>() == 16);
const _: () = assert!(align_of::<OverflowingInt>() <= 8);

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;
    use rstest::rstest;

    /// `2^126 - 1`, the largest inline magnitude.
    const MAX_INLINE: u128 = INLINE_LIMIT - 1;

    fn is_heap(value: &OverflowingInt) -> bool {
        !value.is_inline()
    }

    /// `2^bits` as a `BigUint` — a magnitude of exactly `bits + 1` bit width.
    fn big(bits: u32) -> BigUint {
        BigUint::from(1u8) << bits
    }

    #[test]
    fn size_and_alignment() {
        assert_eq!(size_of::<OverflowingInt>(), 16);
        // `<= 8`, not `== 8`: the requirement is "not align 16". `u64` aligns to
        // 4 under some 32-bit ABIs (e.g. i686), where this type is align 4.
        assert!(align_of::<OverflowingInt>() <= 8);
    }

    #[test]
    fn send_sync() {
        // Must compile with no `unsafe impl` written: a manual impl could mask a
        // genuine loss of thread-safety if the payload ever changes.
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<OverflowingInt>();
    }

    // ===== Canonicality =====

    #[test]
    fn magnitude_fitting_inline_is_demoted() {
        // A `BigUint` that fits inline must be stored inline, observed through
        // `magnitude_ref` rather than by inspecting the tag.
        let value = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(100));
        assert!(matches!(value.magnitude_ref(), Magnitude::Small(_)));
        assert!(!is_heap(&value));
    }

    #[test]
    fn non_minimal_bigint_zero_is_canonical_zero() {
        // A non-minimal `BigUint` zero is the only route by which a heap-backed
        // zero could arrive; it must demote to an inline canonical zero.
        let mut zero = BigUint::from(12345u32);
        zero.set_zero();
        let value = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, zero);
        assert!(value.is_zero());
        assert!(!is_heap(&value));
        assert_eq!(value, OverflowingInt::ZERO);
    }

    #[rstest]
    #[case(Sign::Positive)]
    #[case(Sign::Negative)]
    fn inline_heap_boundary(#[case] sign: Sign) {
        // The largest inline magnitude stays inline; the smallest heap one goes
        // to the heap — an off-by-one in either demotion predicate shows here.
        let largest_inline = OverflowingInt::from_sign_and_big_magnitude(sign, big(126) - 1u8);
        assert!(!is_heap(&largest_inline));
        // Sign and magnitude must survive at the very top of the inline range,
        // where the sign bit sits directly above the highest magnitude bit — this
        // is what makes the `sign` parameter load-bearing rather than inert.
        assert_eq!(largest_inline.magnitude_as_big(), big(126) - 1u8);
        assert_eq!(
            matches!(largest_inline.sign(), Sign::Negative),
            matches!(sign, Sign::Negative)
        );

        let smallest_heap = OverflowingInt::from_sign_and_big_magnitude(sign, big(126));
        assert!(is_heap(&smallest_heap));
        assert_eq!(smallest_heap.magnitude_as_big(), big(126));
        assert_eq!(
            matches!(smallest_heap.sign(), Sign::Negative),
            matches!(sign, Sign::Negative)
        );

        // The `u128` constructor has its own demotion predicate; pin it at the
        // same point. Exactly `INLINE_LIMIT` (`2^126`) must go to the heap, and
        // `MAX_INLINE` must stay inline.
        assert!(is_heap(&OverflowingInt::from_sign_and_magnitude(
            sign,
            INLINE_LIMIT
        )));
        assert!(!is_heap(&OverflowingInt::from_sign_and_magnitude(
            sign, MAX_INLINE
        )));
    }

    #[rstest]
    fn inline_round_trip_across_split_boundary(
        #[values(
            0,
            1,
            1u128 << 61,
            (1u128 << 62) - 1,
            1u128 << 62,
            (1u128 << 62) + 1,
            1u128 << 100,
            (1u128 << 125) - 1,
            MAX_INLINE
        )]
        magnitude: u128,
        #[values(Sign::Positive, Sign::Negative)] sign: Sign,
    ) {
        // Directly exercises the encode/decode pair (`from_inline` /
        // `inline_magnitude`) across the 62/64 word split and, crucially, with a
        // large magnitude paired with each sign — the sign bit is adjacent to the
        // top magnitude bit of `words[0]`, so a mask or shift slip would corrupt
        // one or the other only for magnitudes reaching bit 61.
        let value = OverflowingInt::from_sign_and_magnitude(sign, magnitude);
        assert!(!is_heap(&value), "magnitude {magnitude} should be inline");
        assert_eq!(
            value.magnitude_as_u128(),
            Some(magnitude),
            "magnitude round trip for {magnitude}"
        );
        assert_eq!(
            matches!(value.sign(), Sign::Negative),
            matches!(sign, Sign::Negative),
            "sign for magnitude {magnitude}"
        );
    }

    #[test]
    fn heap_value_is_not_zero() {
        // `is_zero` returns `false` on the heap arm purely by canonicality (a
        // heap magnitude is always `>= 2^126`); pin that arm, whose tag read moved
        // in this layout.
        let heap = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200));
        assert!(is_heap(&heap));
        assert!(!heap.is_zero());
    }

    // ===== Value queries =====

    #[test]
    fn as_i128_respects_signed_asymmetry() {
        // `i128::MIN`'s magnitude is `2^127`, which is heap-backed, yet the value
        // fits `i128`. The positive value of the same magnitude does not.
        let min = OverflowingInt::from_sign_and_big_magnitude(Sign::Negative, big(127));
        assert!(is_heap(&min));
        assert_eq!(min.as_i128(), Some(i128::MIN));

        let positive = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(127));
        assert_eq!(positive.as_i128(), None);

        // Just past `i128::MIN`.
        let past_min = OverflowingInt::from_sign_and_big_magnitude(Sign::Negative, big(127) + 1u8);
        assert_eq!(past_min.as_i128(), None);

        assert_eq!(OverflowingInt::from(i128::MAX).as_i128(), Some(i128::MAX));
        assert_eq!(OverflowingInt::from(i128::MIN).as_i128(), Some(i128::MIN));

        // Inline (non-heap) values also round-trip through the decode, both signs.
        let pos = OverflowingInt::from(1i128 << 100);
        let neg = OverflowingInt::from(-(1i128 << 100));
        assert!(!is_heap(&pos) && !is_heap(&neg));
        assert_eq!(pos.as_i128(), Some(1i128 << 100));
        assert_eq!(neg.as_i128(), Some(-(1i128 << 100)));
    }

    #[test]
    fn as_u128_queries() {
        assert_eq!(OverflowingInt::from(u128::MAX).as_u128(), Some(u128::MAX));
        assert_eq!(OverflowingInt::from(-5i128).as_u128(), None);
        // Negative zero has value zero and fits.
        assert_eq!(OverflowingInt::NEGATIVE_ZERO.as_u128(), Some(0));
        // A heap-backed positive value beyond `u128` does not fit.
        let huge = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(130));
        assert_eq!(huge.as_u128(), None);
        // A heap-backed value that fits `u128` still reports `Some`.
        let fits = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(126));
        assert_eq!(fits.as_u128(), Some(1u128 << 126));
        // A non-zero inline magnitude round-trips through the decode.
        let inline = OverflowingInt::from((1u128 << 62) - 1);
        assert!(!is_heap(&inline));
        assert_eq!(inline.as_u128(), Some((1u128 << 62) - 1));
    }

    // ===== Zero across every route =====

    #[test]
    fn zero_is_positive_through_every_route() {
        let mut non_minimal = BigUint::from(7u32);
        non_minimal.set_zero();
        // Named routes so a failure attributes the offending constructor — a
        // `NoSign -> Negative` slip is route-specific.
        let routes: [(&str, OverflowingInt); 6] = [
            ("ZERO", OverflowingInt::ZERO),
            ("from(0i128)", OverflowingInt::from(0i128)),
            ("from(0u128)", OverflowingInt::from(0u128)),
            ("from(BigInt::ZERO)", OverflowingInt::from(BigInt::ZERO)),
            (
                "from_sign_and_magnitude",
                OverflowingInt::from_sign_and_magnitude(Sign::Positive, 0),
            ),
            (
                "from_sign_and_big_magnitude(non-minimal)",
                OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, non_minimal),
            ),
        ];
        for (name, route) in &routes {
            assert!(matches!(route.sign(), Sign::Positive), "route {name}");
            assert_eq!(*route, OverflowingInt::ZERO, "route {name}");
            assert_ne!(*route, OverflowingInt::NEGATIVE_ZERO, "route {name}");
            // The criterion requires each route to *hash* equal to +0 too.
            assert_eq!(
                hash_of(route),
                hash_of(&OverflowingInt::ZERO),
                "route {name} hash"
            );
        }
        // -0 and +0 are unequal and must hash differently.
        assert_ne!(
            hash_of(&OverflowingInt::NEGATIVE_ZERO),
            hash_of(&OverflowingInt::ZERO)
        );
    }

    // ===== Cross-representation equality and hashing =====

    fn hash_of(value: &OverflowingInt) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn independent_heap_values_compare_and_hash_equal() {
        let a = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200));
        let b = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200));
        assert_eq!(a, b);
        assert_eq!(hash_of(&a), hash_of(&b));
    }

    #[test]
    fn mixed_representation_pair_is_never_equal() {
        let inline = OverflowingInt::from(5u128);
        let heap = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200));
        assert_ne!(inline, heap);
    }

    #[rstest]
    #[case(OverflowingInt::from(5i128), OverflowingInt::from(5i128), true)] // inline fast path
    #[case(OverflowingInt::from(5i128), OverflowingInt::from(-5i128), false)] // sign differs
    #[case(OverflowingInt::from(5i128), OverflowingInt::from(6i128), false)] // magnitude differs
    #[case(OverflowingInt::ZERO, OverflowingInt::NEGATIVE_ZERO, false)] // -0 vs +0
    #[case(
        OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200)),
        OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200)),
        true
    )] // heap slow path
    #[case(
        OverflowingInt::from(5u128),
        OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200)),
        false
    )] // mixed representation
    fn eq_agrees_with_cmp(
        #[case] a: OverflowingInt,
        #[case] b: OverflowingInt,
        #[case] expected: bool,
    ) {
        // The bitwise fast path in `eq` must never diverge from `cmp == Equal`.
        assert_eq!(a == b, expected);
        assert_eq!(a.cmp(&b) == Ordering::Equal, expected);
    }

    // ===== Ordering direction =====

    #[test]
    fn ordering_direction() {
        let neg_zero = OverflowingInt::NEGATIVE_ZERO;
        let pos_zero = OverflowingInt::ZERO;
        assert_eq!(neg_zero.cmp(&pos_zero), Ordering::Less); // -0 < +0
        assert_eq!(
            OverflowingInt::from(-5i128).cmp(&OverflowingInt::from(-3i128)),
            Ordering::Less
        ); // -5 < -3
        assert_eq!(OverflowingInt::from(-3i128).cmp(&neg_zero), Ordering::Less);
        // -3 < -0
    }

    #[rstest]
    #[case(Sign::Positive)]
    #[case(Sign::Negative)]
    fn mixed_representation_ordering_both_signs(#[case] sign: Sign) {
        // A larger magnitude is a smaller number when negative, so the
        // inline/heap ordering flips with the sign.
        let inline = OverflowingInt::from_sign_and_magnitude(sign, 5);
        let heap = OverflowingInt::from_sign_and_big_magnitude(sign, big(200));
        match sign {
            Sign::Positive => assert!(inline < heap),
            Sign::Negative => assert!(heap < inline),
        }
    }

    // ===== Re-signing =====

    #[rstest]
    #[case(OverflowingInt::from(5u128), Sign::Negative)]
    #[case(OverflowingInt::from(5u128), Sign::Positive)]
    #[case(
        OverflowingInt::from_sign_and_big_magnitude(Sign::Negative, big(200)),
        Sign::Positive
    )]
    #[case(
        OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200)),
        Sign::Negative
    )]
    fn with_sign_preserves_representation_and_magnitude(
        #[case] value: OverflowingInt,
        #[case] new_sign: Sign,
    ) {
        let was_heap = is_heap(&value);
        let expected_magnitude = value.magnitude_as_big();
        let resigned = value.with_sign(new_sign);
        // Representation, sign, and magnitude all as expected.
        assert_eq!(is_heap(&resigned), was_heap);
        assert_eq!(
            matches!(resigned.sign(), Sign::Negative),
            matches!(new_sign, Sign::Negative)
        );
        assert_eq!(resigned.magnitude_as_big(), expected_magnitude);
    }

    #[test]
    fn with_sign_never_normalizes_zero() {
        let neg_zero = OverflowingInt::ZERO.with_sign(Sign::Negative);
        assert!(neg_zero.is_zero());
        assert!(matches!(neg_zero.sign(), Sign::Negative));
        assert_eq!(neg_zero, OverflowingInt::NEGATIVE_ZERO);
    }

    // ===== abs / minus of zeros =====

    #[rstest]
    #[case(OverflowingInt::ZERO)]
    #[case(OverflowingInt::NEGATIVE_ZERO)]
    fn abs_and_minus_of_zero_are_positive(#[case] zero: OverflowingInt) {
        // decArith: `abs` and `minus` (which is `subtract('0', x)`, not a sign
        // flip) both yield `+0` for either zero. The `-0` operand exists only
        // here; the wrappers expose no route to build one.
        assert_eq!(zero.abs(), OverflowingInt::ZERO);
        assert!(matches!(zero.abs().sign(), Sign::Positive));
        assert_eq!(zero.minus(), OverflowingInt::ZERO);
        assert!(matches!(zero.minus().sign(), Sign::Positive));
    }

    #[test]
    fn minus_flips_non_zero() {
        assert_eq!(
            OverflowingInt::from(5i128).minus(),
            OverflowingInt::from(-5i128)
        );
        assert_eq!(
            OverflowingInt::from(-5i128).minus(),
            OverflowingInt::from(5i128)
        );
    }

    // ===== Scaling: mul_pow10 =====

    #[rstest]
    // A wide sweep of magnitudes and exponents. Firing late is fine; a wrong
    // answer is the defect.
    #[case(0, 0)]
    #[case(1, 5)]
    #[case(7, 12)]
    #[case(999_999, 20)]
    #[case(MAX_INLINE, 0)]
    fn mul_pow10_matches_bigint(#[case] magnitude: u128, #[case] k: u64) {
        let value = OverflowingInt::from_sign_and_magnitude(Sign::Positive, magnitude);
        let scaled = value.mul_pow10(k);
        let expected = BigUint::from(magnitude) * pow10_big(k);
        assert_eq!(scaled.magnitude_as_big(), expected);
        // Result must be canonical.
        assert_eq!(is_heap(&scaled), expected >= big(126));
    }

    #[test]
    fn mul_pow10_zero_scales_to_zero() {
        // A zero magnitude scaled by a large `k` is still zero, without
        // materializing `10^k`.
        let scaled = OverflowingInt::ZERO.mul_pow10(u64::MAX);
        assert!(scaled.is_zero());
        // Sign is preserved.
        let neg = OverflowingInt::NEGATIVE_ZERO.mul_pow10(1_000);
        assert_eq!(neg, OverflowingInt::NEGATIVE_ZERO);
    }

    #[test]
    fn mul_pow10_preserves_sign() {
        let scaled = OverflowingInt::from(-3i128).mul_pow10(2);
        assert_eq!(scaled, OverflowingInt::from(-300i128));
    }

    #[test]
    fn mul_pow10_promotes_to_heap() {
        // A 126-bit receiver at `k = 41`: `10^41` needs 136 bits, so the product
        // exceeds `u128` and must promote to the heap rather than panic or wrap.
        let receiver = OverflowingInt::from_sign_and_magnitude(Sign::Positive, MAX_INLINE);
        let scaled = receiver.mul_pow10(41);
        assert!(is_heap(&scaled));
        assert_eq!(
            scaled.magnitude_as_big(),
            BigUint::from(MAX_INLINE) * pow10_big(41)
        );
    }

    #[test]
    fn scaling_result_demotes_when_it_fits() {
        // A heap receiver whose scaled-down result fits inline must demote.
        let receiver = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200));
        let (quotient, _) = receiver.div_rem_pow10(40);
        assert!(!is_heap(&quotient));
        assert_eq!(quotient.magnitude_as_big(), big(200) / pow10_big(40));
    }

    // ===== Scaling: div_rem_pow10 =====

    #[rstest]
    #[case(0, 0)]
    #[case(12345, 2)]
    #[case(1_000_000, 6)]
    #[case(MAX_INLINE, 10)]
    fn div_rem_pow10_matches_bigint(#[case] magnitude: u128, #[case] k: u64) {
        let value = OverflowingInt::from_sign_and_magnitude(Sign::Positive, magnitude);
        let (quotient, remainder) = value.div_rem_pow10(k);
        let divisor = pow10_big(k);
        assert_eq!(
            quotient.magnitude_as_big(),
            BigUint::from(magnitude) / &divisor
        );
        assert_eq!(
            remainder.magnitude_as_big(),
            BigUint::from(magnitude) % &divisor
        );
    }

    #[test]
    fn div_rem_pow10_huge_k_is_quotient_zero() {
        // A hostile `k` short-circuits without materializing `10^k`.
        let value = OverflowingInt::from_sign_and_magnitude(Sign::Positive, MAX_INLINE);
        let (quotient, remainder) = value.div_rem_pow10(u64::MAX);
        assert!(quotient.is_zero());
        assert_eq!(remainder, value);
    }

    #[test]
    fn div_rem_pow10_carries_sign() {
        let value = OverflowingInt::from(-12345i128);
        let (quotient, remainder) = value.div_rem_pow10(2);
        assert_eq!(quotient, OverflowingInt::from(-123i128));
        assert_eq!(remainder, OverflowingInt::from(-45i128));
    }

    // ===== Scaling: cmp_magnitude_scaled =====

    #[rstest]
    // Sweep including bit length 0 (a zero receiver).
    #[case(0, 10, 5, Ordering::Less)]
    #[case(5, 0, 5, Ordering::Equal)]
    #[case(16, 3, 16000, Ordering::Equal)]
    #[case(16, 3, 15999, Ordering::Greater)]
    #[case(16, 3, 16001, Ordering::Less)]
    #[case(1, 40, 1, Ordering::Greater)]
    fn cmp_magnitude_scaled_matches_bigint(
        #[case] a: u128,
        #[case] k: u64,
        #[case] b: u128,
        #[case] expected: Ordering,
    ) {
        let lhs = OverflowingInt::from_sign_and_magnitude(Sign::Positive, a);
        let rhs = OverflowingInt::from_sign_and_magnitude(Sign::Positive, b);
        assert_eq!(lhs.cmp_magnitude_scaled(k, &rhs), expected);
        // Cross-check against the arbitrary-precision answer.
        let scaled = BigUint::from(a) * pow10_big(k);
        assert_eq!(scaled.cmp(&BigUint::from(b)), expected);
    }

    #[test]
    fn cmp_magnitude_scaled_zero_ahead_of_width_guard() {
        // The exact defect the zero-first rule catches: comparing
        // `Decimal::new(0, 10)` against `Decimal::new(5, 0)` scales the zero (it
        // carries the larger exponent). The width guard, consulted first, would
        // wrongly answer `Greater`; the correct answer is `Less`.
        let zero = OverflowingInt::ZERO;
        let five = OverflowingInt::from(5u128);
        assert_eq!(zero.cmp_magnitude_scaled(10, &five), Ordering::Less);
    }

    #[test]
    fn cmp_magnitude_scaled_huge_k_no_alloc() {
        // A near-`u64::MAX` exponent must decide from bit widths alone.
        let one = OverflowingInt::from(1u128);
        let other = OverflowingInt::from(u128::MAX);
        assert_eq!(
            one.cmp_magnitude_scaled(u64::MAX, &other),
            Ordering::Greater
        );
    }

    #[test]
    fn cmp_magnitude_scaled_ignores_sign() {
        // Magnitudes only: a negative receiver compares by magnitude.
        let neg = OverflowingInt::from(-16i128);
        let pos = OverflowingInt::from(16000u128);
        assert_eq!(neg.cmp_magnitude_scaled(3, &pos), Ordering::Equal);
    }

    #[rstest]
    // The arbitrary-precision middle band: neither width guard fires and the
    // u128 fast path is unavailable (a heap operand, or a product that overflows
    // u128), so the BigUint comparison branch runs. Cross-checked against BigUint.
    #[case(big(200), 3, big(210))] // both heap, close widths (3k=9 <= 10, 4k=12)
    #[case(big(200), 3, big(200))] // both heap, equal after scaling range
    fn cmp_magnitude_scaled_bignum_cold_path(
        #[case] a: BigUint,
        #[case] k: u64,
        #[case] b: BigUint,
    ) {
        let lhs = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, a.clone());
        let rhs = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, b.clone());
        assert!(
            is_heap(&lhs) && is_heap(&rhs),
            "operands must be heap-backed"
        );
        let expected = (&a * pow10_big(k)).cmp(&b);
        assert_eq!(lhs.cmp_magnitude_scaled(k, &rhs), expected);
    }

    #[test]
    fn cmp_magnitude_scaled_u128_overflow_forces_bignum() {
        // Inline operands whose scaled product overflows u128, widths close so no
        // guard fires (a_bits=125, b_bits=128, k=1): exercises the cold path
        // reached from a fast-path miss rather than from a heap operand.
        let a_mag = (1u128 << 125) - 1;
        let a = OverflowingInt::from(a_mag);
        let b = OverflowingInt::from(u128::MAX);
        assert!(
            a_mag.checked_mul(10).is_none(),
            "product must overflow u128"
        );
        let expected = (BigUint::from(a_mag) * pow10_big(1)).cmp(&BigUint::from(u128::MAX));
        assert_eq!(a.cmp_magnitude_scaled(1, &b), expected);
    }

    #[test]
    fn mul_pow10_heap_receiver_stays_heap() {
        // A heap receiver times 10^k stays heap and matches the BigUint product.
        let receiver = OverflowingInt::from_sign_and_big_magnitude(Sign::Negative, big(200));
        let scaled = receiver.mul_pow10(5);
        assert!(is_heap(&scaled));
        assert!(matches!(scaled.sign(), Sign::Negative));
        assert_eq!(scaled.magnitude_as_big(), big(200) * pow10_big(5));
    }

    #[test]
    fn div_rem_pow10_heap_quotient_and_remainder() {
        // A heap dividend whose quotient stays heap; assert both parts and signs.
        let value = OverflowingInt::from_sign_and_big_magnitude(Sign::Negative, big(200));
        let (quotient, remainder) = value.div_rem_pow10(1);
        assert!(is_heap(&quotient), "quotient should stay heap");
        assert!(matches!(quotient.sign(), Sign::Negative));
        assert!(matches!(remainder.sign(), Sign::Negative));
        let divisor = pow10_big(1);
        assert_eq!(quotient.magnitude_as_big(), big(200) / &divisor);
        assert_eq!(remainder.magnitude_as_big(), big(200) % &divisor);
    }

    #[rstest]
    #[case(OverflowingInt::ZERO, 0)]
    #[case(OverflowingInt::from(1u128), 1)]
    #[case(OverflowingInt::from(255u128), 8)]
    #[case(
        OverflowingInt::from_sign_and_magnitude(Sign::Positive, MAX_INLINE),
        126
    )]
    #[case(
        OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200)),
        201
    )]
    fn bits_reports_magnitude_width(#[case] value: OverflowingInt, #[case] expected: u64) {
        assert_eq!(value.bits(), expected);
    }

    // ===== Drop soundness (validated under Miri) =====

    #[test]
    #[allow(unused_assignments)] // The reassignment drops the first heap value — the point of the test.
    fn drop_through_reassignment() {
        let mut value = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200));
        value = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(210));
        assert!(is_heap(&value));
    }

    #[test]
    fn drop_through_mem_replace_and_swap() {
        let mut a = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200));
        let b = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(210));
        let old = std::mem::replace(&mut a, b);
        assert!(is_heap(&old));

        let mut x = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(220));
        let mut y = OverflowingInt::from(1u128);
        std::mem::swap(&mut x, &mut y);
        assert!(!is_heap(&x));
        assert!(is_heap(&y));
    }

    #[test]
    fn drop_through_container() {
        let values = vec![
            OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200)),
            OverflowingInt::from(1u128),
            OverflowingInt::from_sign_and_big_magnitude(Sign::Negative, big(210)),
        ];
        drop(values);
    }

    #[test]
    fn drop_clone_then_drop_both() {
        let original = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200));
        let clone = original.clone();
        assert_eq!(original, clone);
        drop(original);
        drop(clone);
    }

    #[test]
    fn drop_during_unwind() {
        // A panic while a heap value is live must still free it exactly once.
        let result = std::panic::catch_unwind(|| {
            let _value = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(200));
            panic!("unwind with a live heap value");
        });
        assert!(result.is_err());
    }

    // ===== Debug =====

    #[test]
    fn debug_output_per_arm() {
        assert_eq!(
            format!("{:?}", OverflowingInt::from(5i128)),
            "OverflowingInt::Inline(5)"
        );
        assert_eq!(
            format!("{:?}", OverflowingInt::from(-5i128)),
            "OverflowingInt::Inline(-5)"
        );
        assert_eq!(
            format!("{:?}", OverflowingInt::NEGATIVE_ZERO),
            "OverflowingInt::Inline(-0)"
        );
        let heap = OverflowingInt::from_sign_and_big_magnitude(Sign::Positive, big(126));
        assert_eq!(
            format!("{heap:?}"),
            format!("OverflowingInt::Heap({})", big(126))
        );
    }
}
