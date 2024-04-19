//! This module provides an implementation of the data types described by the
//! [Ion Data Model](https://amazon-ion.github.io/ion-docs/docs/spec.html#the-ion-data-model)
//! section of the Ion 1.0 spec.

pub type SymbolId = usize;

mod bytes;
pub mod decimal;
pub(crate) mod integer;
mod list;
mod lob;
mod null;
mod sexp;
mod string;
mod r#struct;
pub(crate) mod symbol;
mod timestamp;

pub use crate::types::bytes::Bytes;
pub use decimal::Decimal;
pub use integer::{Int, UInt};
pub use list::List;
pub use lob::{Blob, Clob};
pub use null::Null;
pub use r#struct::Struct;
pub use sexp::SExp;
pub use string::Str;
pub use symbol::Symbol;
pub(crate) use timestamp::{HasFractionalSeconds, HasSeconds};
pub use timestamp::{Mantissa, Timestamp, TimestampBuilder, TimestampPrecision};

use crate::ion_data::IonOrd;
use std::cmp::Ordering;
use std::fmt;

/// Represents the Ion data type of a given value. To learn more about each data type,
/// read [the Ion Data Model](https://amazon-ion.github.io/ion-docs/docs/spec.html#the-ion-data-model)
/// section of the spec.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub enum IonType {
    Null,
    Bool,
    Int,
    Float,
    Decimal,
    Timestamp,
    Symbol,
    String,
    Clob,
    Blob,
    List,
    SExp,
    Struct,
}

impl fmt::Display for IonType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                IonType::Null => "null",
                IonType::Bool => "bool",
                IonType::Int => "int",
                IonType::Float => "float",
                IonType::Decimal => "decimal",
                IonType::Timestamp => "timestamp",
                IonType::Symbol => "symbol",
                IonType::String => "string",
                IonType::Clob => "clob",
                IonType::Blob => "blob",
                IonType::List => "list",
                IonType::SExp => "sexp",
                IonType::Struct => "struct",
            }
        )
    }
}

impl IonType {
    pub fn is_container(&self) -> bool {
        use IonType::*;
        matches!(self, List | SExp | Struct)
    }
}

impl IonOrd for IonType {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}

/// An Ion container type.
///
/// This is similar to [`ParentType`], but does not include the top level as a variant.
#[derive(Debug, PartialEq, Copy, Clone)]
pub(crate) enum ContainerType {
    /// An s-expression
    SExp,
    /// A list
    List,
    /// A struct
    Struct,
}

impl From<ContainerType> for IonType {
    fn from(value: ContainerType) -> Self {
        match value {
            ContainerType::SExp => IonType::SExp,
            ContainerType::List => IonType::List,
            ContainerType::Struct => IonType::Struct,
        }
    }
}

/// The enclosing context in which a value is found.
///
/// This is a superset of [`ContainerType`], which does not include a variant for the top
/// level.
#[derive(Debug, PartialEq, Default, Copy, Clone)]
pub(crate) enum ParentType {
    /// The value is not inside a container.
    #[default]
    TopLevel,
    /// The value is inside of an s-expression.
    SExp,
    /// The value is inside of a list.
    List,
    /// The value is inside of a struct.
    Struct,
}

impl From<ContainerType> for ParentType {
    fn from(value: ContainerType) -> Self {
        match value {
            ContainerType::SExp => ParentType::SExp,
            ContainerType::List => ParentType::List,
            ContainerType::Struct => ParentType::Struct,
        }
    }
}

#[derive(Debug, PartialEq, Default, Copy, Clone)]
pub(crate) enum ScalarType {
    #[default]
    Null,
    Bool,
    Int,
    Float,
    Decimal,
    Timestamp,
    Symbol,
    String,
    Clob,
    Blob,
}

impl From<ScalarType> for IonType {
    fn from(value: ScalarType) -> Self {
        match value {
            ScalarType::Null => IonType::Null,
            ScalarType::Bool => IonType::Bool,
            ScalarType::Int => IonType::Int,
            ScalarType::Float => IonType::Float,
            ScalarType::Decimal => IonType::Decimal,
            ScalarType::Timestamp => IonType::Timestamp,
            ScalarType::Symbol => IonType::Symbol,
            ScalarType::String => IonType::String,
            ScalarType::Clob => IonType::Clob,
            ScalarType::Blob => IonType::Blob,
        }
    }
}

/// Returns the number of base-10 digits needed to represent `value`.
fn num_decimal_digits_in_u64(value: u64) -> u64 {
    if value == 0 {
        return 1;
    }
    let log_base_ten = (value as f64).log10();
    let count = log_base_ten.ceil();
    if log_base_ten == count {
        // If ceil() didn't change the count, then `value` is an exact power of ten.
        // We need to add one to get the correct count.
        // Examples:
        //    (1).log10() ==   (1).log10().ceil() == 0
        //   (10).log10() ==  (10).log10().ceil() == 1
        //  (100).log10() == (100).log10().ceil() == 2
        count as u64 + 1
    } else {
        count as u64
    }
}
