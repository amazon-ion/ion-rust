// Copyright Amazon.com, Inc. or its affiliates.
//! Implements "type qualifiers" (TQ) as per the [spec][spec].
//!
//! [spec]: https://amazon-ion.github.io/ion-hash/docs/spec.html.
use crate::binary::IonTypeCode;
use crate::element::{Element, Sequence, Struct};
use crate::{Decimal, Int, IonType, Symbol, Timestamp};

use std::slice;

// For many types, the qualifier is either 'null' or 'not null'. That's what
// these constants are for!
const QUALIFIER_NOT_NULL: u8 = 0x00;
const QUALIFIER_NULL: u8 = 0x0F;

pub(crate) struct TypeQualifier(u8);

/// From the spec:
///
/// > TQ: is a type qualifier octet consisting of a four-bit type code T
/// followed by a four-bit qualifier Q
///
/// To compute a TQ from a `T` and a `Q`, all we need to is a bitwise shift!
const fn combine(ion_type_code: IonTypeCode, q: u8) -> TypeQualifier {
    let t = ion_type_code.to_u8();
    TypeQualifier(t << 4 | q)
}

impl TypeQualifier {
    /// Computes a [`TypeQualifier`] from an [`Element`] according to the rules
    /// laid out in the spec. In many cases, the `T` is determined by the Ion
    /// binary type code.
    ///
    /// This method simply calls the appropriate `type_qualifier_$ion_type`
    /// method.
    pub(crate) fn from_element(elem: &Element) -> TypeQualifier {
        match elem.ion_type() {
            IonType::Null => type_qualifier_null(),
            IonType::Bool => type_qualifier_boolean(elem.as_bool()),
            IonType::Int => type_qualifier_integer(elem.as_int()),
            IonType::Float => type_qualifier_float(elem.as_float()),
            IonType::Decimal => type_qualifier_decimal(elem.as_decimal()),
            IonType::Timestamp => type_qualifier_timestamp(elem.as_timestamp()),
            IonType::Symbol => type_qualifier_symbol(elem.as_symbol()),
            IonType::String => type_qualifier_string(elem.as_string()),
            IonType::Clob => type_qualifier_clob(elem.as_lob()),
            IonType::Blob => type_qualifier_blob(elem.as_lob()),
            IonType::List => type_qualifier_list(elem.as_sequence()),
            IonType::SExp => type_qualifier_sexp(elem.as_sequence()),
            IonType::Struct => type_qualifier_struct(elem.as_struct()),
        }
    }

    /// Convenient transform to feed to a `Digest`.
    pub(crate) fn as_bytes(&self) -> &[u8] {
        slice::from_ref(&self.0)
    }
}

fn is_integer_positive(value: Option<&Int>) -> bool {
    value.map(|i| !i.is_negative()).unwrap_or(true)
}

/// For many types, the qualifier (see: [`TypeQualifier`]) is based on whether
/// the value is/not null.
fn qualify_nullness<T>(value: Option<T>) -> u8 {
    match value {
        Some(_) => QUALIFIER_NOT_NULL,
        None => QUALIFIER_NULL,
    }
}

pub(crate) fn type_qualifier_null() -> TypeQualifier {
    combine(IonTypeCode::NullOrNop, 0x0F)
}

pub(crate) fn type_qualifier_boolean(value: Option<bool>) -> TypeQualifier {
    let q = match value {
        None => 0x0F,
        Some(b) => match b {
            false => 0x00,
            true => 0x01,
        },
    };
    combine(IonTypeCode::Boolean, q)
}

pub(crate) fn type_qualifier_integer(any: Option<&Int>) -> TypeQualifier {
    let t = match is_integer_positive(any) {
        true => IonTypeCode::PositiveInteger,
        false => IonTypeCode::NegativeInteger,
    };
    combine(t, qualify_nullness(any))
}

pub(crate) fn type_qualifier_float(value: Option<f64>) -> TypeQualifier {
    combine(IonTypeCode::Float, qualify_nullness(value))
}

pub(crate) fn type_qualifier_decimal(value: Option<&Decimal>) -> TypeQualifier {
    combine(IonTypeCode::Decimal, qualify_nullness(value))
}

pub(crate) fn type_qualifier_timestamp(value: Option<&Timestamp>) -> TypeQualifier {
    combine(IonTypeCode::Timestamp, qualify_nullness(value))
}

pub(crate) fn type_qualifier_string(value: Option<&str>) -> TypeQualifier {
    combine(IonTypeCode::String, qualify_nullness(value))
}

pub(crate) fn type_qualifier_clob(value: Option<&[u8]>) -> TypeQualifier {
    combine(IonTypeCode::Clob, qualify_nullness(value))
}

pub(crate) fn type_qualifier_blob(value: Option<&[u8]>) -> TypeQualifier {
    combine(IonTypeCode::Blob, qualify_nullness(value))
}

pub(crate) fn type_qualifier_list(value: Option<&Sequence>) -> TypeQualifier {
    combine(IonTypeCode::List, qualify_nullness(value))
}

pub(crate) fn type_qualifier_sexp(value: Option<&Sequence>) -> TypeQualifier {
    combine(IonTypeCode::SExpression, qualify_nullness(value))
}

pub(crate) fn type_qualifier_symbol(sym: Option<&Symbol>) -> TypeQualifier {
    // Non-null symbol with unknown text has a TQ of 0x71
    if let Some(symbol) = sym {
        if symbol.text().is_none() {
            return TypeQualifier(0x71);
        }
    }
    combine(IonTypeCode::Symbol, qualify_nullness(sym))
}

pub(crate) fn type_qualifier_struct(value: Option<&Struct>) -> TypeQualifier {
    combine(IonTypeCode::Struct, qualify_nullness(value))
}
