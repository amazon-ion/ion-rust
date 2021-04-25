// Copyright Amazon.com, Inc. or its affiliates.

//! Implement Ion Hash as per the [spec](https://amzn.github.io/ion-hash/docs/spec.html)
//!
//! ## Examples
//! ```rust
//! use ion_rs::value::loader::{self, Loader};
//! use ion_rs::result::IonResult;
//!
//! # fn main() -> IonResult<()> {
//!   let loader = loader::loader();
//!   let elem = loader.iterate_over(b"\"hello world\"")?.next().unwrap()?;
//!   let digest = ion_hash::sha256(&elem);
//!   println!("{:?}", digest);
//! # Ok(())
//! # }
//! ```

use ion_rs::{
    value::{owned::OwnedElement, Element},
    IonType,
};

use sha2::{digest::Output, Digest, Sha256};

pub fn sha256(elem: &OwnedElement) -> Vec<u8> {
    let mut hasher = IonHasher::new(Sha256::new());
    let result = hasher.visit_element(elem);
    Vec::from(result.as_slice())
}

/// Bytes markers as per the spec.
mod markers {
    /// single byte begin marker
    pub(crate) const B: u8 = 0x0B;
    /// single byte end marker
    pub(crate) const E: u8 = 0x0E;
    /// single byte escape
    pub(crate) const ESC: u8 = 0x0C;
    /// type qualifier octet consisting of a four-bit type code T followed by a four-bit qualifier Q
    /// (this varies per type)
    pub(crate) const TQ_STRING: u8 = 0x80;
}

// TODO: In the fullness of time, we will have a IonHashReader and a
// IonHashWriter. This will allow reading/writing a value *while* computing a
// hash. For now, we provide a standalone hasher using the OwnedElement API.
pub struct IonHasher<D>
where
    D: Digest,
{
    hasher: D,
}

impl<D> IonHasher<D>
where
    D: Digest,
{
    fn new(hasher: D) -> IonHasher<D> {
        IonHasher { hasher }
    }

    fn visit_element(&mut self, elem: &OwnedElement) -> Output<D> {
        let serialized_bytes = match elem.ion_type() {
            IonType::Null => todo!(),
            IonType::Boolean => todo!(),
            IonType::Integer => todo!(),
            IonType::Float => todo!(),
            IonType::Decimal => todo!(),
            IonType::Timestamp => todo!(),
            IonType::Symbol => todo!(),
            IonType::String => self.visit_string(elem.as_str().unwrap()),
            IonType::Clob => todo!(),
            IonType::Blob => todo!(),
            IonType::List => todo!(),
            IonType::SExpression => todo!(),
            IonType::Struct => todo!(),
        };

        self.hasher.update(serialized_bytes);
        self.hasher.finalize_reset()
    }

    fn visit_string(&mut self, value: &str) -> Vec<u8> {
        let representation = value.as_bytes();
        let mut serialized_bytes = vec![markers::B, markers::TQ_STRING];
        serialized_bytes.extend(ion_hash_escape(representation));
        serialized_bytes.push(markers::E);
        serialized_bytes
    }
}

/// Replaces each marker byte M with ESC || M.
fn ion_hash_escape(representation: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(representation.len());
    for byte in representation {
        if let markers::B | markers::E | markers::ESC = *byte {
            out.push(0x0C);
        }
        out.push(*byte);
    }

    out
}

// TODO: Use the ion-hash test suite
#[cfg(test)]
mod tests {
    use super::*;
    use hex_literal::hex;
    use ion_rs::value::owned::*;

    #[test]
    fn ion_hash_sha256_string() {
        let expected = hex!("82c4010bfc9cace7f645c0a951243b9b122cb5ba21b60b3f71ea79c513c39342");
        let hello_world = OwnedElement::new(vec![], OwnedValue::String("hello world".to_string()));
        let computed = sha256(&hello_world);
        assert_eq!(expected, &computed[..]);
    }
}
