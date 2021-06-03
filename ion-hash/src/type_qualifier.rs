// Copyright Amazon.com, Inc. or its affiliates.

use std::slice;

///! Implements "type qualifiers" (TQ) as per the [spec][spec].
///!
///! [spec]: https://amzn.github.io/ion-hash/docs/spec.html.
use ion_rs::{
    binary::IonTypeCode,
    value::{AnyInt, Element, Sequence, Struct, SymbolToken},
    IonType,
};
use num_bigint::Sign;

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
    pub(crate) fn from_element<E>(elem: &E) -> TypeQualifier
    where
        E: Element + ?Sized,
    {
        match elem.ion_type() {
            IonType::Null => type_qualifier_null(),
            IonType::Boolean => type_qualifier_boolean(elem.as_bool()),
            IonType::Integer => type_qualifier_integer(elem.as_any_int()),
            IonType::Float => type_qualifier_float(elem.as_f64()),
            /*IonType::Decimal => Decimal,
            IonType::Timestamp => Timestamp,*/
            IonType::Symbol => type_qualifier_symbol(elem.as_sym()),
            IonType::String => type_qualifier_string(elem.as_str()),
            IonType::Clob => type_qualifier_clob(elem.as_bytes()),
            IonType::Blob => type_qualifier_blob(elem.as_bytes()),
            IonType::List => type_qualifier_list(elem.as_sequence()),
            IonType::SExpression => type_qualifier_sexp(elem.as_sequence()),
            IonType::Struct => type_qualifier_struct(elem.as_struct()),
            other => unimplemented!("TypeQualifier is not implemented for {}", other),
        }
    }

    /// Convenient transform to feed to a `Digest`.
    pub(crate) fn as_bytes(&self) -> &[u8] {
        slice::from_ref(&self.0)
    }
}

fn is_anyint_positive(value: Option<&AnyInt>) -> bool {
    match value {
        None => true,
        Some(any) => match any {
            AnyInt::I64(i) => *i >= 0,
            AnyInt::BigInt(b) => !std::matches!(b.sign(), Sign::Minus),
        },
    }
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
    combine(IonTypeCode::NullOrWhitespace, 0x0F)
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

pub(crate) fn type_qualifier_integer(any: Option<&AnyInt>) -> TypeQualifier {
    let t = match is_anyint_positive(any) {
        true => IonTypeCode::PositiveInteger,
        false => IonTypeCode::NegativeInteger,
    };
    combine(t, qualify_nullness(any))
}

pub(crate) fn type_qualifier_float(value: Option<f64>) -> TypeQualifier {
    combine(IonTypeCode::Float, qualify_nullness(value))
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

pub(crate) fn type_qualifier_list<S>(value: Option<&S>) -> TypeQualifier
where
    S: Sequence + ?Sized,
{
    combine(IonTypeCode::List, qualify_nullness(value))
}

pub(crate) fn type_qualifier_sexp<S>(value: Option<&S>) -> TypeQualifier
where
    S: Sequence + ?Sized,
{
    combine(IonTypeCode::SExpression, qualify_nullness(value))
}

pub(crate) fn type_qualifier_symbol<S>(sym: Option<&S>) -> TypeQualifier
where
    S: SymbolToken + ?Sized,
{
    combine(IonTypeCode::Symbol, qualify_nullness(sym))
}

pub(crate) fn type_qualifier_struct<S>(value: Option<&S>) -> TypeQualifier
where
    S: Struct + ?Sized,
{
    combine(IonTypeCode::Struct, qualify_nullness(value))
}
