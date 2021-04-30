// Copyright Amazon.com, Inc. or its affiliates.

//! Implements the [Ion Hash specification](https://amzn.github.io/ion-hash/docs/spec.html)
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

use digest::{Digest, Output};
use ion_rs::result::{illegal_operation, IonResult};
use ion_rs::{value::Element, IonType};

// TODO: Make sha2 an optional dependency.
use sha2::Sha256;

// A `try`-like macro to workaround the Element API ergonomics. This API
// requires checking the type and then calling the appropriate getter function
// (which returns a None if you got it wrong). This macro turns the `None` into
// an `IonError`.
// TODO: Remove this once the Element API is reworked.
macro_rules! t {
    ($getter:expr) => {
        match $getter {
            Some(value) => value,
            None => illegal_operation("Missing expected value")?,
        }
    };
}

/// Utility to hash an [`Element`] using SHA-256 as the hash function.
// TODO: Make this conditional on some feature flag
pub fn sha256<E: Element>(elem: &E) -> IonResult<Vec<u8>> {
    let hasher = IonHasher::new(Sha256::new());
    let result = hasher.hash_element(elem)?;
    Ok(Vec::from(result.as_slice()))
}

/// Bytes markers as per the spec.
struct Markers;
impl Markers {
    /// single byte begin marker
    const B: u8 = 0x0B;
    /// single byte end marker
    const E: u8 = 0x0E;
    /// single byte escape
    const ESC: u8 = 0x0C;

    // type qualifier octet consisting of a four-bit type code T followed by a four-bit qualifier Q
    // (this varies per type)
    const TQ_NULL: u8 = 0x0F;
    const TQ_STRING: u8 = 0x80;
}

// TODO: In the fullness of time, we will have a IonHashReader and a
// IonHashWriter. This will allow reading/writing a value *while* computing a
// hash. For now, we provide a standalone hasher using the Element API.
/// Provides Ion hash over arbitrary [`Element`] instances with a given
/// [`Digest`] algorithm.
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
    pub fn new(hasher: D) -> Self {
        Self { hasher }
    }

    /// Computes the Ion hash over an [`Element`] recursively using this
    /// hasher's [`Digest`]
    pub fn hash_element<E: Element + ?Sized>(mut self, elem: &E) -> IonResult<Output<D>> {
        let serialized_bytes = match elem.ion_type() {
            IonType::Null => self.hash_null(),
            IonType::Boolean => todo!(),
            IonType::Integer => todo!(),
            IonType::Float => todo!(),
            IonType::Decimal => todo!(),
            IonType::Timestamp => todo!(),
            IonType::Symbol => todo!(),
            IonType::String => self.hash_string(t!(elem.as_str())),
            IonType::Clob => todo!(),
            IonType::Blob => todo!(),
            IonType::List => todo!(),
            IonType::SExpression => todo!(),
            IonType::Struct => todo!(),
        };

        // TODO: Annotations

        self.hasher.update(serialized_bytes);
        Ok(self.hasher.finalize())
    }

    fn hash_null(&mut self) -> Vec<u8> {
        vec![Markers::B, Markers::TQ_NULL, Markers::E]
    }

    fn hash_string(&mut self, value: &str) -> Vec<u8> {
        let representation = value.as_bytes();
        let mut serialized_bytes = vec![Markers::B, Markers::TQ_STRING];
        serialized_bytes.extend(ion_hash_escape(representation));
        serialized_bytes.push(Markers::E);
        serialized_bytes
    }
}

/// Replaces each marker byte M with ESC || M.
fn ion_hash_escape(representation: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(representation.len());
    for byte in representation {
        if let Markers::B | Markers::E | Markers::ESC = *byte {
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
    fn ion_hash_sha256_string() -> IonResult<()> {
        let expected = hex!("82c4010bfc9cace7f645c0a951243b9b122cb5ba21b60b3f71ea79c513c39342");
        let hello_world = OwnedElement::new(vec![], OwnedValue::String("hello world".to_string()));
        let computed = sha256(&hello_world)?;
        assert_eq!(expected, &computed[..]);
        Ok(())
    }
}
