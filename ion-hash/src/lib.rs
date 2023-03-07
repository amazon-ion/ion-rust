// Copyright Amazon.com, Inc. or its affiliates.

//! Implements the [Ion Hash specification](https://amazon-ion.github.io/ion-hash/docs/spec.html)
//!
//! ## Examples
//! ```rust
//! use ion_rs::value::reader::{self, ElementReader};
//! use ion_rs::result::IonResult;
//!
//! # fn main() -> IonResult<()> {
//!   let loader = reader::element_reader();
//!   let elem = loader.iterate_over(b"\"hello world\"")?.next().unwrap()?;
//!   let digest = ion_hash::sha256(&elem);
//!   println!("{:?}", digest);
//! # Ok(())
//! # }
//! ```

use digest::{FixedOutput, Output, Reset, Update};
use ion_rs::result::IonResult;

// TODO: Make sha2 an optional dependency.
use sha2::Sha256;

use element_hasher::ElementHasher;
use ion_rs::value::owned::Element;

mod element_hasher;
mod representation;
mod type_qualifier;

/// Utility to hash an [`Element`] using SHA-256 as the hash function.
// TODO: Make this conditional on some feature flag
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

/// This trait mostly exists to extend the [`Digest`] trait to support Ion Hash.
/// See [`hash_element`].
pub trait IonHasher {
    type Output;

    /// Returns the Ion Hash of the given [`Element`].
    fn hash_element(elem: &Element) -> IonResult<Self::Output>;
}

/// Implements [`IonHasher`] for any type that implements `Digest`.
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

    /// Provides Ion hash over arbitrary [`IonElement`] instances with a given
    /// [`Digest`] algorithm.
    fn hash_element(elem: &Element) -> IonResult<Self::Output> {
        ElementHasher::new(D::default()).hash_element(elem)
    }
}
