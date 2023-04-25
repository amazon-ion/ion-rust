use crate::ion_data::{IonEq, IonOrd};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};

/// Represents an Ion `bool` value, for the purpose of implementing some Ion-related traits.
///
/// Most of the time, you can use [bool] instead of this type.
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct Bool(bool);

impl Display for Bool {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        <bool as Display>::fmt(&self.0, f)
    }
}

impl From<bool> for Bool {
    fn from(value: bool) -> Self {
        Bool(value)
    }
}

impl From<Bool> for bool {
    fn from(value: Bool) -> Self {
        value.0
    }
}

impl PartialEq<bool> for Bool {
    fn eq(&self, other: &bool) -> bool {
        self.0 == *other
    }
}

impl IonEq for Bool {
    fn ion_eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl IonOrd for Bool {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}
