//! This module provides an implementation of the data types described by the
//! [Ion Data Model](https://amazon-ion.github.io/ion-docs/docs/spec.html#the-ion-data-model)
//! section of the Ion 1.0 spec.

// TODO: Consolidate on "symbol address" naming.
pub type SymbolId = usize;
pub type SymbolAddress = usize;

mod bytes;
pub mod decimal;
pub(crate) mod float;
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
pub use timestamp::{HasDay, HasFractionalSeconds, HasHour, HasMinute, HasMonth, HasOffset, HasSeconds, HasYear, Mantissa, Timestamp, TimestampBuilder, TimestampPrecision};

use crate::ion_data::{IonDataHash, IonDataOrd};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

/// Represents the Ion data type of a given value. To learn more about each data type,
/// read [the Ion Data Model](https://amazon-ion.github.io/ion-docs/docs/spec.html#the-ion-data-model)
/// section of the spec.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
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

impl IonDataOrd for IonType {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}

impl IonDataHash for IonType {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.hash(state)
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

pub(crate) trait CountDecimalDigits {
    fn count_decimal_digits(self) -> u32;
}

macro_rules! impl_count_decimal_digits_unsigned {
    ($($unsigned_int_type:ty),* $(,)?) => {$(
        impl CountDecimalDigits for $unsigned_int_type {
            fn count_decimal_digits(self) -> u32 {
                if self == 0 {
                    return 1;
                }
                self.ilog10() + 1
            }
        }
    )*};
}

macro_rules! impl_count_decimal_digits_signed {
    ($($signed_int_type:ty),* $(,)?) => {$(
        impl CountDecimalDigits for $signed_int_type {
            fn count_decimal_digits(self) -> u32 {
                self.unsigned_abs().count_decimal_digits()
            }
        }
    )*};
}

impl_count_decimal_digits_unsigned!(u8, u16, u32, u64, u128, usize);
impl_count_decimal_digits_signed!(i8, i16, i32, i64, i128, isize);
