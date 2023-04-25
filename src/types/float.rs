use crate::ion_data::{IonEq, IonOrd};
use num_traits::Zero;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};

/// Represents an Ion `float` value, for the purpose of implementing some Ion-related traits.
///
/// Most of the time, you can use [f64] instead of this type.
#[derive(Debug, Clone, PartialOrd, PartialEq)]
pub struct Float(f64);

impl Float {
    /// Implements Ion equivalence for [f64].
    pub(crate) fn ion_eq_f64(this: &f64, that: &f64) -> bool {
        if this.is_nan() {
            return that.is_nan();
        }
        if this.is_zero() {
            return that.is_zero() && this.is_sign_negative() == that.is_sign_negative();
        }
        // For all other values, fall back to mathematical equivalence
        this == that
    }

    /// Implements Ion ordering for [f64].
    pub(crate) fn ion_cmp_f64(this: &f64, that: &f64) -> Ordering {
        this.total_cmp(that)
    }
}

impl Display for Float {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        <f64 as Display>::fmt(&self.0, f)
    }
}

impl From<f64> for Float {
    fn from(value: f64) -> Self {
        Float(value)
    }
}

impl From<Float> for f64 {
    fn from(value: Float) -> Self {
        value.0
    }
}

impl PartialEq<f64> for Float {
    fn eq(&self, other: &f64) -> bool {
        self.0 == *other
    }
}

impl IonEq for Float {
    fn ion_eq(&self, other: &Self) -> bool {
        Float::ion_eq_f64(&self.0, &other.0)
    }
}

impl IonOrd for Float {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        Float::ion_cmp_f64(&self.0, &other.0)
    }
}
