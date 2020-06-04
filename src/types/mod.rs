//! This module provides an implementation of the data types described by the
//! [Ion Data Model](http://amzn.github.io/ion-docs/docs/spec.html#the-ion-data-model)
//! section of the Ion 1.0 spec.

pub type SymbolId = usize;

mod r#type;

pub use r#type::IonType;
