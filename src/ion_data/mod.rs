mod ion_eq;
mod ion_ord;

use crate::{Element, IonResult};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};

use crate::element::{Annotations, Value};
use delegate::delegate;
pub use ion_eq::IonEq;
pub(crate) use ion_ord::IonOrd;

/// A wrapper for lifting "data" to "Ion data". Anything that implements [IonEq] can be converted
/// into [IonData]. As [IonData], the semantics of [Eq] are the same as [IonEq]—that is to say, [Eq]
/// follows the rules for Ion Equivalence in the Ion specification.
///
/// [IonData] itself does not implement [IonEq] so that it is not possible to create, for example,
/// `IonData<IonData<Element>>`.
///
/// [Hash] and [Ord] are not guaranteed to be implemented for all [IonData], but when they are, they
/// are required to be consistent with [IonEq] (and [Eq]).
///
/// __WARNING__—The Ion specification does _not_ define a total ordering over all Ion values. Do
/// not depend on getting any particular result from [Ord]. Use it only as an opaque total ordering
/// over all [IonData]. _The algorithm used for [Ord] may change between versions._
#[derive(Debug, Clone)]
pub struct IonData<T: IonEq>(T);

impl<T: IonEq> IonData<T> {
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

impl IonData<Element> {
    /// Reads a single [IonData<Element>] from the provided data source.
    ///
    /// If the data source is empty, returns `Ok(None)`.
    /// If the data source has at least one value, returns `Ok(Some(IonData<Element>))`.
    /// If the data source has invalid data, returns `Err`.
    pub fn read_first<A: AsRef<[u8]>>(data: A) -> IonResult<Option<IonData<Element>>> {
        Element::read_first(data).map(|opt| opt.map(IonData))
    }

    /// Reads a single Ion [IonData<Element>] from the provided data source. If the input has invalid
    /// data or does not contain at exactly one Ion value, returns `Err(IonError)`.
    pub fn read_one<A: AsRef<[u8]>>(data: A) -> IonResult<IonData<Element>> {
        Element::read_one(data).map(IonData)
    }

    /// Reads all available [IonData<Element>]s from the provided data source.
    ///
    /// If the input has valid data, returns `Ok(Vec<IonData<Element>>)`.
    /// If the input has invalid data, returns `Err(IonError)`.
    pub fn read_all<A: AsRef<[u8]>>(data: A) -> IonResult<Vec<IonData<Element>>> {
        Element::read_all(data).map(|vec| vec.into_iter().map(IonData).collect())
    }

    delegate! {
        to self.0 {
            pub fn value(&self) -> &Value;
            pub fn annotations(&self) -> &Annotations;
        }
    }
}

impl From<IonData<Element>> for Element {
    fn from(value: IonData<Element>) -> Self {
        value.0
    }
}
