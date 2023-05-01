use std::ops::Deref;

/// Determines whether two values are equal according to Ion's definition of equivalence.
///
/// Ion equivalence is concerned with ensuring that no information is lost when values are written
/// to or read from a stream.
///
/// Two values may be considered equivalent by [PartialEq] but not considered equivalent by `IonEq`.
/// For example, the `f64` value `0.0` is considered equal to the `f64` value `-0.0`. However, they
/// would not be considered Ion equivalent because one cannot be substituted for the other when
/// reading or writing without losing information (namely, the value's sign: `-`).
///
/// The inverse can also happen; two values can be Ion equivalent according to [IonEq] but are not
/// considered equal according to [PartialEq]. For example: in the Ion data model, the special
/// `float` value `NaN` is considered equivalent to any other `NaN`; this is because you can always
/// substitute a `NaN` for any other `NaN` when reading or writing without losing information.
/// However, `f64::nan() == f64::nan()` is always `false` because two `Not-a-Number`s are never
/// mathematically equal.
///
/// Corner case examples:
/// * Special `float` values:
///    * `nan` and `nan` are Ion equivalent but not mathematically equivalent.
///    * `0.0e` and `-0.0e` are mathematically equivalent but not Ion equivalent.
/// * Decimal `0.0` and `-0.0` are mathematically equivalent but not Ion equivalent.
/// * Decimal `0.0` and `0.00` are mathematically equivalent but not Ion equivalent.
/// * Timestamps representing the same point in time at different precisions or at different
/// timezone offsets are not Ion equivalent.
pub trait IonEq {
    fn ion_eq(&self, other: &Self) -> bool;
}

impl<R: Deref> IonEq for R
where
    R::Target: IonEq,
{
    fn ion_eq(&self, other: &Self) -> bool {
        R::Target::ion_eq(self, other)
    }
}

impl<T: IonEq> IonEq for [T] {
    fn ion_eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for (v1, v2) in self.iter().zip(other.iter()) {
            if !v1.ion_eq(v2) {
                return false;
            }
        }
        true
    }
}

/// Checks Ion equivalence for [`f64`].
///
/// We cannot implement [`IonEq`] for [`f64`]. If [`IonEq`] is implemented directly on [`f64`], then
/// `impl<T, R> IonEq for R where T: IonEq, R: Deref<Target = T>` or any other blanket impl of
/// [`IonEq`] for a standard library trait will cause `error[E0119]: conflicting implementations of
/// trait` because [`f64`] is an external type (and "upstream crates may add a new impl of trait
/// `std::ops::Deref` for type `f64` in future versions").
///
/// Once [RFC-1210: Impl Specialization](https://rust-lang.github.io/rfcs/1210-impl-specialization.html)
/// is stable, we can move this to `impl IonEq for f64`.
pub(crate) fn ion_eq_f64(this: &f64, that: &f64) -> bool {
    use num_traits::Zero;
    if this.is_nan() {
        return that.is_nan();
    }
    if this.is_zero() {
        return that.is_zero() && this.is_sign_negative() == that.is_sign_negative();
    }
    // For all other values, fall back to mathematical equivalence
    this == that
}

/// Checks Ion equivalence for [`bool`].
///
/// See docs for [`ion_eq_f64`] for general rationale. Even though the implementation is trivial,
/// this function exists to help convey the intention of using Ion equivalence at the call site.
pub(crate) fn ion_eq_bool(this: &bool, that: &bool) -> bool {
    this == that
}
