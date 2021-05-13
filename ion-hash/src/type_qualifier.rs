// Copyright Amazon.com, Inc. or its affiliates.

use std::slice;

///! Implements "type qualifiers" (TQ) as per the [spec][spec].
///!
///! [spec]: https://amzn.github.io/ion-hash/docs/spec.html.
use ion_rs::{
    binary::IonTypeCode,
    value::{AnyInt, Element},
    IonType,
};
use num_bigint::Sign;

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
    /// As much as possible, we use `const fn` to implement lookups logically.
    /// The code is authored to read like the spec, without sacrificing
    /// performance.
    pub(crate) fn from_element<E>(elem: &E) -> TypeQualifier
    where
        E: Element + ?Sized,
    {
        use IonTypeCode::*;
        match elem.ion_type() {
            IonType::Null => combine(NullOrWhitespace, 0x0F),
            IonType::Boolean => {
                let q = match elem.as_bool() {
                    None => 0x0F,
                    Some(b) => match b {
                        false => 0x00,
                        true => 0x01,
                    },
                };
                combine(Boolean, q)
            }
            IonType::Integer => {
                let any = elem.as_any_int();
                let t = match is_anyint_positive(any) {
                    true => IonTypeCode::PositiveInteger,
                    false => IonTypeCode::NegativeInteger,
                };
                let q = match any {
                    Some(_) => 0x00,
                    None => 0x0F,
                };
                combine(t, q)
            }
            /*IonType::Float => Float,
            IonType::Decimal => Decimal,
            IonType::Timestamp => Timestamp,
            IonType::Symbol => Symbol,*/
            IonType::String => {
                let q = match elem.as_str() {
                    Some(_) => 0x00,
                    None => 0x0F,
                };
                combine(String, q)
            }
            /*IonType::Clob => Clob,
            IonType::Blob => Blob,
            IonType::List => List,
            IonType::SExpression => SExpression,
            IonType::Struct => Struct,*/
            _ => todo!(),
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
