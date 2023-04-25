//! This module provides an implementation of the data types described by the
//! [Ion Data Model](https://amazon-ion.github.io/ion-docs/docs/spec.html#the-ion-data-model)
//! section of the Ion 1.0 spec.

pub type SymbolId = usize;

pub mod coefficient;
pub mod decimal;
pub mod integer;
pub mod string;
pub mod timestamp;

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

// Represents a level into which the writer has stepped.
// A writer that has not yet called step_in() is at the top level.
#[derive(Debug, PartialEq, Default)]
pub(crate) enum ContainerType {
    #[default]
    TopLevel,
    SExpression,
    List,
    Struct,
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
