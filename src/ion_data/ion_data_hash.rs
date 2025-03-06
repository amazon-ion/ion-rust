use std::hash::Hasher;
use std::ops::Deref;

/// Trait used for delegating [`Hash`] in [`IonData`](crate::IonData).
/// Implementations of [`IonDataHash`] must be consistent with [`IonEq`](crate::ion_data::IonEq).
///
/// This is _not_ the Ion Hash algorithm. Do not write any code that depends on a specific hash
/// being produced by a particular value. Do not expect that the hashes will be stable between
/// two runs of the same application. The only guarantee is that it is consistent with
/// [`IonEq`](crate::ion_data::IonEq)
///
/// This is called `IonDataHash` to avoid ambiguity with the Ion Hash algorithm and its
/// implementation in this crate.
pub(crate) trait IonDataHash {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H);
}

impl<R: Deref> IonDataHash for R
where
    R::Target: IonDataHash,
{
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        R::Target::ion_data_hash(self, state)
    }
}

impl<T: IonDataHash> IonDataHash for [T] {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.len());
        for element in self {
            T::ion_data_hash(element, state)
        }
    }
}

/// In a roundabout way, implements IonDataHash for [`f64`].
///
/// We cannot implement [`IonDataHash`] directly on [`f64`]. If [`IonDataHash`] is implemented directly
/// on [`f64`], then _any_ blanket impl of [`IonDataHash`] for a standard library trait will cause
/// `error[E0119]: conflicting implementations of trait` because [`f64`] is an external type (and
/// "upstream crates may add a new impl of trait `std::ops::Deref` for type `f64` in future versions").
pub(crate) fn ion_data_hash_f64<H: Hasher>(this: f64, state: &mut H) {
    if this.is_nan() {
        // `this` could be positive or negative, signalling or quiet NaN.
        // Ensure that all NaNs are treated equivalently, as with IonEq.
        state.write_u64(f64::NAN.to_bits())
    } else {
        state.write_u64(this.to_bits())
    }
}

/// In a roundabout way, implements IonDataHash for [`bool`].
///
/// See docs for [`crate::ion_data::ion_data_hash_f64`] for general rationale. Even though the implementation is trivial,
/// this function exists to help convey the intention of using Ion equivalence at the call site.
pub(crate) fn ion_data_hash_bool<H: Hasher>(this: bool, state: &mut H) {
    state.write_u8(this as u8)
}
