use crate::IonType;

/// An in-memory representation of a typed `null`.
// This type allows us to define custom behavior for `null` via trait implementations.
// For an example, see the `WriteAsIonValue` trait.
#[derive(Debug, PartialEq, Copy, Clone)]
pub struct Null(pub IonType);
