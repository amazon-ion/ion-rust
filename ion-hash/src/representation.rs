// Copyright Amazon.com, Inc. or its affiliates.

//! This file provides an extension trait [`Representation`] that is implemented
//! for Ion types found in the [`Element`] API. In the fullness of time, this
//! file should not exist as we should be using the Ion "raw" binary writer
//! instead. This implementation fills in that gap, and is focused on coverage
//! and not speed.

use crate::Markers;
use digest::{Digest, Update};
use ion_rs::{
    binary,
    value::{AnyInt, Element},
    IonType,
};

// TODO: Finish ion-rust's binary writer and factor it such that the binary
// representations can be written by the "raw" writer (ref. the Java
// implementation).
pub(crate) fn write_repr<E: Element + ?Sized, D: Digest + Update>(elem: &E, hasher: &mut D) {
    let mut hasher = escaping(hasher);

    match elem.ion_type() {
        IonType::Null | IonType::Boolean => {} // these types have no representation
        IonType::Integer => write_repr_integer(elem.as_any_int(), &mut hasher),
        IonType::Float => write_repr_float(elem.as_f64(), &mut hasher),
        IonType::Decimal | IonType::Timestamp | IonType::Symbol => todo!(),
        IonType::String => write_repr_string(elem.as_str(), &mut hasher),
        IonType::Clob | IonType::Blob | IonType::List | IonType::SExpression | IonType::Struct => {
            panic!("type {} is not yet supported", elem.ion_type())
        }
    }
}

/// Wraps an existing `Update` in an escaping one, which replaces each marker
/// byte M with ESC || M.
fn escaping<'a, U: Update>(inner: &'a mut U) -> UpdateEscaping<'a, U> {
    UpdateEscaping(inner)
}

struct UpdateEscaping<'a, U: Update>(&'a mut U);

impl<'a, U: Update> Update for UpdateEscaping<'a, U> {
    fn update(&mut self, data: impl AsRef<[u8]>) {
        for byte in data.as_ref() {
            if let Markers::B | Markers::E | Markers::ESC = *byte {
                self.0.update([0x0C]);
            }
            self.0.update([*byte]);
        }
    }
}

fn write_repr_integer<U: Update>(value: Option<&AnyInt>, hasher: &mut UpdateEscaping<'_, U>) {
    match value {
        Some(AnyInt::I64(v)) => match v {
            0 => {}
            _ => {
                let magnitude = v.abs() as u64;
                let encoded = binary::uint::encode_uint(magnitude);
                hasher.update(encoded.as_bytes())
            }
        },
        Some(AnyInt::BigInt(b)) => hasher.update(&b.magnitude().to_bytes_be()[..]),
        None => {}
    }
}

/// Floats are encoded as big-endian octets of their IEEE-754 bit patterns,
/// except for special cases: +-zero, +-inf and nan.
fn write_repr_float<U: Update>(value: Option<f64>, hasher: &mut UpdateEscaping<'_, U>) {
    match value {
        None => {}
        Some(v) => {
            // This matches positive and negative zero.
            if v == 0.0 {
                return if !v.is_sign_positive() {
                    hasher.update(&[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])
                };
            }
            if v.is_infinite() {
                return if v.is_sign_positive() {
                    hasher.update(&[0x7F, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])
                } else {
                    hasher.update(&[0xFF, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])
                };
            }

            if v.is_nan() {
                return hasher.update(&[0x7F, 0xF8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            }

            hasher.update(&v.to_be_bytes())
        }
    }
}

fn write_repr_string<U: Update>(value: Option<&str>, hasher: &mut UpdateEscaping<'_, U>) {
    match value {
        Some(s) => hasher.update(s.as_bytes()),
        None => {}
    }
}
