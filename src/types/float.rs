pub(crate) enum FloatRepr {
    Zero,
    // TODO: Half(f16)
    Single(f32),
    Double(f64),
}

/// Finds the smallest valid Ion encoding for a given floating point value.
pub trait SmallestFloatRepr {
    /// Returns the smallest variant of [`FloatRepr`] that can losslessly represent
    /// the implementor's data.
    fn smallest_repr(self) -> FloatRepr;
}

impl SmallestFloatRepr for f32 {
    #[inline]
    fn smallest_repr(self) -> FloatRepr {
        if self == 0f32 && self.is_sign_positive() {
            return FloatRepr::Zero;
        }

        // TODO: See if we can scale down to Half(f16)

        FloatRepr::Single(self)
    }
}

impl SmallestFloatRepr for f64 {
    #[inline]
    fn smallest_repr(self) -> FloatRepr {
        if self == 0f64 && self.is_sign_positive() {
            return FloatRepr::Zero;
        }

        // TODO: See if we can scale down to Half(f16)
        // `f64::is_finite` returns false for `NaN`, `+inf`, and `-inf`
        let is_special_value = !self.is_finite();
        let value_f32 = self as f32;
        if is_special_value || value_f32 as f64 == self {
            return FloatRepr::Single(value_f32);
        }
        FloatRepr::Double(self)
    }
}
