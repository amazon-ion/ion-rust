// Copyright Amazon.com, Inc. or its affiliates.

//! Implements the [Ion Hash specification](https://amazon-ion.github.io/ion-hash/docs/spec.html)
//!
//! ## Examples
//! ```rust
//! use ion_rs::element::Element;
//! use ion_rs::result::IonResult;
//! use ion_rs::ion_hash;
//!
//! # // XXX this doc test requires an optional feature--so this makes sure we can still run tests
//! # #[cfg(feature = "sha2")]
//! # fn main() -> IonResult<()> {
//!   let elem = Element::read_one(b"\"hello world\"")?;
//!   let digest = ion_hash::sha256(&elem);
//!   println!("{:?}", digest);
//! # Ok(())
//! # }
//! # #[cfg(not(feature = "sha2"))]
//! # fn main() {}
//! ```

use digest::{self, FixedOutput, Output, Reset, Update};

use crate::element::Element;
use crate::IonResult;
use element_hasher::ElementHasher;

mod element_hasher;
mod representation;
mod type_qualifier;

#[cfg(feature = "sha2")]
use sha2::Sha256;
/// Utility to hash an [`Element`] using SHA-256 as the hash function.
#[cfg(feature = "sha2")]
pub fn sha256(elem: &Element) -> IonResult<Output<Sha256>> {
    Sha256::hash_element(elem)
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
}

/// This trait mostly exists to extend the [`Digest`](digest::Digest) trait to support Ion Hash.
/// See [`hash_element`](Self::hash_element).
pub trait IonHasher {
    type Output;

    /// Returns the Ion Hash of the given [`Element`].
    fn hash_element(elem: &Element) -> IonResult<Self::Output>;
}

/// Implements [`IonHasher`] for any type that implements [`Digest`](digest::Digest).
///
/// Note: the `Digest` trait is implemented for types that implement a set of
/// traits. You should read the `D` generic as `Digest`. The reason we list the
/// subtraits here is that implementors have much less work to do if they
/// implement the subtraits only, as the blanket impls in the `digest` crate take
/// care of assembly.
impl<D> IonHasher for D
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    type Output = digest::Output<D>;

    /// Provides Ion hash over arbitrary [`Element`] instances with a given
    /// [`Digest`](digest::Digest) algorithm.
    fn hash_element(elem: &Element) -> IonResult<Self::Output> {
        ElementHasher::new(D::default()).hash_element(elem)
    }
}
