use num_traits::Zero;

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
/// * Timestamps representing the same point in time at different precisions or at different
/// timezone offsets are not Ion equivalent.
///
// TODO: `Timestamp` and `Decimal` do not currently implement `IonEq` because their implementations
//       of `PartialEq` use Ion equivalence rules. We need to disentangle these.
// See https://github.com/amzn/ion-rust/issues/381
pub trait IonEq {
    fn ion_eq(&self, other: &Self) -> bool;
}

impl IonEq for f64 {
    fn ion_eq(&self, other: &Self) -> bool {
        if self.is_nan() {
            return other.is_nan();
        }
        if self.is_zero() {
            return other.is_zero() && self.is_sign_negative() == other.is_sign_negative();
        }
        // For all other values, fall back to mathematical equivalence
        self == other
    }
}
