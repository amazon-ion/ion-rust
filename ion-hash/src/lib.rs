// Copyright Amazon.com, Inc. or its affiliates.

//! Implements the [Ion Hash specification](https://amzn.github.io/ion-hash/docs/spec.html)
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
use ion_rs::value::Element;

use representation::RepresentationEncoder;
// TODO: Make sha2 an optional dependency.
use sha2::Sha256;
use type_qualifier::TypeQualifier;

mod representation;
mod type_qualifier;

/// Utility to hash an [`Element`] using SHA-256 as the hash function.
// TODO: Make this conditional on some feature flag
pub fn sha256<E: Element + ?Sized>(elem: &E) -> IonResult<Output<Sha256>> {
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

pub trait ElementHasher<E>
where
    E: Element + ?Sized,
{
    type Output;

    fn hash_element(elem: &E) -> IonResult<Self::Output>;

    /// Implements the "serialized bytes" transform as described in the spec. The
    /// bytes are written to `hasher` (as opposed to returned) for performance
    /// reasons (avoid allocations for DSTs).
    fn update_serialized_bytes(&mut self, elem: &E) -> IonResult<()>;

    fn mark_begin(&mut self);

    fn mark_end(&mut self);

    fn update_type_qualifier_and_representation(&mut self, elem: &E) -> IonResult<()>;
}

impl<E, D> ElementHasher<E> for D
where
    E: Element + ?Sized,
    D: Update + FixedOutput + Reset + Clone + Default,
{
    type Output = digest::Output<D>;

    // TODO: In the fullness of time, we will have a IonHashReader and a
    // IonHashWriter. This will allow reading/writing a value *while* computing a
    // hash. For now, we provide a standalone hasher using the Element API.
    /// Provides Ion hash over arbitrary [`Element`] instances with a given
    /// [`Digest`] algorithm.
    ///
    /// Note that [`Digest`] *does not imply* the following traits directly, but is
    /// a *convenience* trait for these other traits with a blanked implementation.
    /// This is the reason for this is we can't go from [`Digest`] to these
    /// traits (e.g. [`Update`]) but because of a blanket implementation, we can go
    /// the other way.
    fn hash_element(elem: &E) -> IonResult<Self::Output> {
        let mut hasher = D::default();
        hasher.update_serialized_bytes(elem)?;
        Ok(hasher.finalize_fixed())
    }

    /// Implements the "serialized bytes" transform as described in the spec. The
    /// bytes are written to `hasher` (as opposed to returned) for performance
    /// reasons (avoid allocations for DSTs).
    fn update_serialized_bytes(&mut self, elem: &E) -> IonResult<()> {
        ElementHasher::<E>::mark_begin(self); // :puke:
        self.update_type_qualifier_and_representation(elem)?;
        // TODO: Annotations
        ElementHasher::<E>::mark_end(self);

        Ok(())
    }

    #[inline]
    fn mark_begin(&mut self) {
        self.update([Markers::B]);
    }

    #[inline]
    fn mark_end(&mut self) {
        self.update([Markers::E]);
    }

    fn update_type_qualifier_and_representation(&mut self, elem: &E) -> IonResult<()> {
        let tq = TypeQualifier::from_element(elem);
        self.update(tq.as_bytes());
        self.update_with_representation(elem)
    }
}
