// Copyright Amazon.com, Inc. or its affiliates.

//! This file provides an extension trait [`Representation`] that is implemented
//! for Ion types found in the [`Element`] API. In the fullness of time, this
//! file should not exist as we should be using the Ion "raw" binary writer
//! instead. This implementation fills in that gap, and is focused on coverage
//! and not speed.

use ion_rs::{
    binary,
    value::{AnyInt, Element},
    IonType,
};

// TODO: Finish ion-rust's binary writer and factor it such that the binary
// representations can be written by the "raw" writer (ref. the Java
// implementation).
pub(crate) fn binary_repr<E: Element + ?Sized>(elem: &E) -> BinaryRepr {
    match elem.ion_type() {
        IonType::Null | IonType::Boolean => todo!(),
        IonType::Integer => elem.as_any_int().repr(),
        IonType::Float => elem.as_f64().repr(),
        IonType::Decimal | IonType::Timestamp | IonType::Symbol => todo!(),
        IonType::String => elem.as_str().repr(),
        IonType::Clob | IonType::Blob | IonType::List | IonType::SExpression | IonType::Struct => {
            todo!()
        }
    }
}

// TODO: Don't allocate all the time!
type BinaryRepr = Option<Vec<u8>>;

/// An extension trait for getting the binary representation of the various
/// types as defined in the spec.
pub trait Representation {
    fn repr(&self) -> BinaryRepr;
}

impl Representation for Option<&AnyInt> {
    fn repr(&self) -> BinaryRepr {
        match self {
            Some(AnyInt::I64(v)) => match v {
                0 => None,
                _ => {
                    let magnitude = v.abs() as u64;
                    let encoded = binary::uint::encode_uint(magnitude);
                    Some(encoded.as_bytes().into())
                }
            },
            Some(AnyInt::BigInt(b)) => Some(b.magnitude().to_bytes_be()),
            None => None,
        }
    }
}

impl Representation for Option<&str> {
    fn repr(&self) -> BinaryRepr {
        match self {
            Some(s) => Some(s.as_bytes().into()),
            None => None,
        }
    }
}

impl Representation for Option<f64> {
    /// Floats are encoded as big-endian octets of their IEEE-754 bit patterns,
    /// except for special cases: +-zero, +-inf and nan.
    fn repr(&self) -> BinaryRepr {
        match self {
            None => None,
            Some(v) => {
                // This matches positive and negative zero.
                if *v == 0.0 {
                    return if v.is_sign_positive() {
                        None
                    } else {
                        Some(vec![0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])
                    };
                }
                if v.is_infinite() {
                    return if v.is_sign_positive() {
                        Some(vec![0x7F, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])
                    } else {
                        Some(vec![0xFF, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])
                    };
                }

                if v.is_nan() {
                    return Some(vec![0x7F, 0xF8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
                }

                Some(v.to_be_bytes().into())
            }
        }
    }
}
