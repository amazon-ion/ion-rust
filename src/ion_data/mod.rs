mod ion_eq;
mod ion_ord;

use std::cmp::Ordering;
use std::fmt::{Display, Formatter};

pub(crate) use ion_eq::IonEq;
pub(crate) use ion_ord::IonOrd;

/// A wrapper for lifting Ion compatible data into using Ion oriented comparisons (versus the Rust
/// value semantics). This enables the default semantics to be what a Rust user expects for native
/// values, but allows a user to opt-in to Ion's structural equivalence/order.
///
/// Anything that implements [`IonEq`] can be converted into [`IonData`]. [`IonData`] itself does not
/// implement [`IonEq`] so that it is impossible to create, for example, `IonData<IonData<Element>>`.
///
/// [`Hash`] and [`Ord`] are not guaranteed to be implemented for all [`IonData`], but when they are,
/// they are required to be consistent with [`IonEq`] (and [`Eq`]).
///
/// __WARNING__—The Ion specification does _not_ define a total ordering over all Ion values. Do
/// not depend on getting any particular result from [Ord]. Use it only as an opaque total ordering
/// over all [IonData]. _The algorithm used for [Ord] may change between versions._
#[derive(Debug, Clone)]
pub struct IonData<T: IonEq>(T);

impl<T: IonEq> IonData<T> {
    /// Checks if two values are equal according to Ion's structural equivalence.
    pub fn eq<U: AsRef<T>>(a: U, b: U) -> bool {
        T::ion_eq(a.as_ref(), b.as_ref())
    }

    /// Unwraps the value.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T: IonEq> PartialEq for IonData<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ion_eq(&other.0)
    }
}

impl<T: IonEq> Eq for IonData<T> {}

impl<T: IonEq> From<T> for IonData<T> {
    fn from(value: T) -> Self {
        IonData(value)
    }
}

impl<T: IonEq> AsRef<T> for IonData<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: IonEq + Display> Display for IonData<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<T: IonEq + IonOrd> PartialOrd for IonData<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(IonOrd::ion_cmp(&self.0, &other.0))
    }
}

impl<T: IonEq + IonOrd> Ord for IonData<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        IonOrd::ion_cmp(&self.0, &other.0)
    }
}
