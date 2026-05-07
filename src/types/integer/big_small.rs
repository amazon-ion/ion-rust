use ice_code::ice as cold_path;
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;
use std::borrow::Cow;
use std::cmp::Ordering;

/// A value that has big and small representations. They should have equivalent semantics, although
/// the APIs might not be the same. (E.g. `int128` and `BigInt`)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BigOrSmall<S, B> {
    SmallValue(S),
    BigValue(B),
}
use BigOrSmall::*;

/// Abstraction over access to the small or big representation, regardless of which is active (and
/// regardless of whether the type has small and big variants at all).
pub(crate) trait AsBigOrSmallValue {
    type SmallType: Copy;
    type BigType: Clone;
    fn as_small_value(&self) -> Option<Self::SmallType>;
    fn as_big_value(&self) -> Cow<'_, Self::BigType>;
}

impl<S, B> PartialOrd for BigOrSmall<S, B>
where
    Self: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<S, B> Ord for BigOrSmall<S, B>
where
    B: Ord + Eq + Clone,
    S: Ord + Eq + Copy,
    Self: AsBigOrSmallValue<SmallType = S, BigType = B>,
{
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (SmallValue(this), SmallValue(that)) => this.cmp(that),
            _ => cold_path! {{ self.as_big_value().cmp(&other.as_big_value()) }},
        }
    }
}

impl<S, B> AsBigOrSmallValue for BigOrSmall<S, B>
where
    S: Copy + Into<B>,
    B: Clone,
{
    type SmallType = S;
    type BigType = B;

    fn as_small_value(&self) -> Option<Self::SmallType> {
        match self {
            SmallValue(i) => Some(*i),
            BigValue(_) => None,
        }
    }

    fn as_big_value(&self) -> Cow<'_, Self::BigType> {
        match self {
            SmallValue(value) => Cow::Owned((*value).into()),
            BigValue(big_value) => Cow::Borrowed(big_value),
        }
    }
}

/// Implements `AsBigOrSmallValue` for a wrapper type by delegating to its inner `BigOrSmall`.
/// Can also be implemented for things that do not have a Big/Small variant in order to unify
/// access over various types.
macro_rules! impl_as_big_or_small {
    ($val:ident: $self:ty, $big:ty => $big_exp:expr, $small:ty => $small_exp:expr) => {
        impl AsBigOrSmallValue for $self {
            type SmallType = $small;
            type BigType = $big;

            fn as_small_value(&self) -> Option<Self::SmallType> {
                let $val = self;
                $small_exp
            }

            fn as_big_value(&self) -> Cow<'_, Self::BigType> {
                let $val = self;
                $big_exp
            }
        }
    };
}
pub(crate) use impl_as_big_or_small;

impl_as_big_or_small!(this: u128, BigUint => Cow::Owned((*this).into()), Self => Some(*this));
impl_as_big_or_small!(this: i128, BigInt => Cow::Owned((*this).into()), Self => Some(*this));
impl_as_big_or_small!(this: BigUint, Self => Cow::Borrowed(this), u128 => this.to_u128());
impl_as_big_or_small!(this: BigInt, Self => Cow::Borrowed(this), i128 => this.to_i128());

/// Implements an arithmetic op that tries the checked primitive version first, falling back to BigInt/BigUint.
macro_rules! impl_std_op_big_small {
    ($Trait:ident<$Rhs:ty> for $T:ident, $op:ident, $checked_op:ident) => {
        impl std::ops::$Trait<$Rhs> for $T {
            type Output = $T;
            fn $op(self, rhs: $Rhs) -> $T {
                if let (Some(a), Some(b)) = (&self.as_small_value(), &rhs.as_small_value()) {
                    if let Some(result) = a.$checked_op(*b) {
                        return $T(SmallValue(result));
                    }
                }
                cold_path! {{
                    let a = self.as_big_value();
                    let b = rhs.as_big_value();
                    $T::from_big(a.as_ref().$op(b.as_ref()))
                }}
            }
        }
    };
}
pub(crate) use impl_std_op_big_small;

macro_rules! impl_display_big_small {
    ($t:ty) => {
        impl std::fmt::Display for $t {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                if let Some(small) = self.as_small_value() {
                    write!(f, "{small}")
                } else {
                    write!(f, "{}", self.as_big_value())
                }
            }
        }
    };
}
pub(crate) use impl_display_big_small;
