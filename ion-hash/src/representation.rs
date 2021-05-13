// Copyright Amazon.com, Inc. or its affiliates.

//! This file provides an extension trait [`Representation`] that is implemented
//! for Ion types found in the [`Element`] API. In the fullness of time, this
//! file should not exist as we should be using the Ion "raw" binary writer
//! instead. This implementation fills in that gap, and is focused on coverage
//! and not speed.

use ion_rs::{
    value::{AnyInt, Element},
    IonType,
};
use num_bigint::BigInt;

// TODO: Finish ion-rust's binary writer and factor it such that the binary
// representations can be written by the "raw" writer (ref. the Java
// implementation).
pub(crate) fn binary_repr<E: Element + ?Sized>(elem: &E) -> BinaryRepr {
    match elem.ion_type() {
        IonType::Null | IonType::Boolean => todo!(),
        IonType::Integer => elem.as_any_int().repr(),
        IonType::Float | IonType::Decimal | IonType::Timestamp | IonType::Symbol => todo!(),
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
        fn bigint_repr(b: &BigInt) -> Vec<u8> {
            b.magnitude().to_bytes_be()
        }

        match self {
            Some(AnyInt::I64(v)) => match v {
                0 => None,
                _ => Some(bigint_repr(&BigInt::from(*v))),
            },
            Some(AnyInt::BigInt(b)) => Some(bigint_repr(b)),
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
