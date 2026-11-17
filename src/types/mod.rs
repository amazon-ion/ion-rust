//! This module provides an implementation of the data types described by the
//! [Ion Data Model](https://amazon-ion.github.io/ion-docs/docs/spec.html#the-ion-data-model)
//! section of the Ion 1.0 spec.

// TODO: Consolidate on "symbol address" naming.
pub type SymbolId = usize;
pub type SymbolAddress = usize;

mod bytes;
pub mod decimal;
pub(crate) mod integer;
mod list;
mod lob;
mod null;
pub(crate) mod overflowing_int;
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
pub use timestamp::{Timestamp, TimestampPrecision};

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

/// A total order whose `Equal` matches `PartialEq`, except that `nan` is `Equal` to `nan`.
///
/// `PartialEq`-equal values compare `Equal`, and values that compare `Equal` are `PartialEq`-equal
/// unless they hold a `nan`. Unlike [`IonDataOrd`], it has no tie-breaks among `PartialEq`-equal
/// values, so sorting by it puts them next to each other.
pub(crate) trait PrivateOrd {
    fn private_cmp(&self, other: &Self) -> Ordering;
}

/// Implements [`PrivateOrd`] as `Ord` for types whose `Ord` is `Equal` exactly when `PartialEq`
/// holds.
macro_rules! private_ord_from_ord {
    ($($t:ty),*) => {$(
        impl PrivateOrd for $t {
            fn private_cmp(&self, other: &Self) -> Ordering {
                self.cmp(other)
            }
        }
    )*};
}

private_ord_from_ord!(bool, Int, Decimal, Timestamp, Symbol, Str, Bytes);

/// Numeric order, with `-0e0` equal to `0e0` and every `nan` equal and greatest. Not `total_cmp`,
/// which orders `-0e0` before `0e0` and tells `nan`s apart.
impl PrivateOrd for f64 {
    fn private_cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other)
            .unwrap_or_else(|| self.is_nan().cmp(&other.is_nan()))
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

#[cfg(test)]
mod private_ord_tests {
    use super::{PrivateOrd, Symbol};
    use crate::element::Value;
    use crate::{Element, IonResult};
    use std::cmp::Ordering;

    /// Values on which `PartialEq` and `IonDataOrd` disagree (decimal precision and zero signs,
    /// float zero signs and `nan`, timestamp offsets and precision), plus every Ion type, and
    /// containers holding them, including structs with repeated names.
    const VALUES: &[&str] = &[
        "null",
        "null.int",
        "null.list",
        "false",
        "true",
        "-1",
        "1",
        "18446744073709551616",
        "-0d0",
        "0d0",
        "0.0",
        "1d0",
        "1.0",
        "10d-1",
        "-0e0",
        "0e0",
        "1e0",
        "+inf",
        "nan",
        "2020T",
        "2020-01-01T00:00-00:00",
        "2020-01-01T00:00Z",
        "2020-01-01T05:00Z",
        "2020-01-01T10:00+05:00",
        "2020-01-01T05:00:00.000Z",
        "2020-01-01T23:30-05:00",
        "2020-01-02T04:30Z",
        "a",
        "'b'",
        "$0",
        "\"a\"",
        "\"b\"",
        "{{aGk=}}",
        "{{aGVsbG8=}}",
        "{{\"hi\"}}",
        "{{\"ho\"}}",
        "x::1",
        "x::1.0",
        "y::1",
        "$0::1",
        "[]",
        "[0d0, 3]",
        "[0.0, 3]",
        "[0.0, 2]",
        "[nan]",
        "[0d0, nan]",
        "[0.0, nan]",
        "[nan, 1]",
        "[nan, 2]",
        "[-0e0]",
        "[0e0]",
        "(0d0 3)",
        "(nan)",
        "{}",
        "{$0: 1}",
        "{a: 1, b: 1}",
        "{b: 1, a: 1}",
        "{a: 1, b: 2}",
        "{b: 2, a: 1}",
        "{a: [0d0, 3], a: [0.0, 2]}",
        "{a: [0d0, 2], a: [0.0, 3]}",
        "{a: [0d0, 3], a: [0.0, 3]}",
        "{a: [nan]}",
        "{a: (nan)}",
        "{a: {b: nan}}",
        "{a: {b: 0d0}, a: {b: 1}}",
        "{a: {b: 1}, a: {b: 0.0}}",
    ];

    fn values() -> IonResult<Vec<Element>> {
        VALUES.iter().map(Element::read_one).collect()
    }

    /// `PartialEq` for elements, with `nan` equal to `nan` if `nan_eq`, written out independently
    /// of `PrivateOrd`: sequences pairwise, structs by trying every pairing of their fields.
    fn reference_eq(this: &Element, that: &Element, nan_eq: bool) -> bool {
        if this.annotations() != that.annotations() {
            return false;
        }
        match (this.value(), that.value()) {
            (Value::List(these), Value::List(those)) | (Value::SExp(these), Value::SExp(those)) => {
                these.len() == those.len()
                    && these
                        .iter()
                        .zip(those.iter())
                        .all(|(a, b)| reference_eq(a, b, nan_eq))
            }
            (Value::Struct(these), Value::Struct(those)) => {
                let these: Vec<_> = these.iter().collect();
                let mut those: Vec<_> = those.iter().map(Some).collect();
                these.len() == those.len() && match_fields(&these, &mut those, nan_eq)
            }
            (Value::Float(this), Value::Float(that)) if nan_eq => {
                this == that || (this.is_nan() && that.is_nan())
            }
            (this, that) => this == that,
        }
    }

    fn match_fields(
        these: &[(&Symbol, &Element)],
        those: &mut [Option<(&Symbol, &Element)>],
        nan_eq: bool,
    ) -> bool {
        let Some(((name, value), rest)) = these.split_first() else {
            return true;
        };
        for i in 0..those.len() {
            let Some((that_name, that_value)) = those[i] else {
                continue;
            };
            if name == &that_name && reference_eq(value, that_value, nan_eq) {
                those[i] = None;
                if match_fields(rest, those, nan_eq) {
                    return true;
                }
                those[i] = Some((that_name, that_value));
            }
        }
        false
    }

    #[test]
    fn partial_eq_matches_reference() -> IonResult<()> {
        let values = values()?;
        for a in &values {
            for b in &values {
                assert_eq!(a == b, reference_eq(a, b, false), "{a} vs {b}");
            }
        }
        Ok(())
    }

    #[test]
    fn equal_exactly_when_partial_eq_or_both_nan() -> IonResult<()> {
        let values = values()?;
        for a in &values {
            for b in &values {
                assert_eq!(
                    reference_eq(a, b, true),
                    a.private_cmp(b).is_eq(),
                    "{a} vs {b}"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn total_order() -> IonResult<()> {
        let values = values()?;
        let order: Vec<Vec<Ordering>> = values
            .iter()
            .map(|a| values.iter().map(|b| a.private_cmp(b)).collect())
            .collect();
        let n = values.len();
        for a in 0..n {
            assert_eq!(order[a][a], Ordering::Equal, "{}", values[a]);
            for b in 0..n {
                let (ab, ba) = (order[a][b], order[b][a]);
                assert_eq!(ab, ba.reverse(), "{} vs {}", values[a], values[b]);
                for c in 0..n {
                    if ab.is_le() && order[b][c].is_le() {
                        assert!(
                            order[a][c].is_le(),
                            "{} <= {} <= {}",
                            values[a],
                            values[b],
                            values[c]
                        );
                    }
                }
            }
        }
        Ok(())
    }
}
