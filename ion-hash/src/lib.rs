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

use digest::{Digest, FixedOutput, Output, Reset, Update};
use ion_rs::result::IonResult;
use ion_rs::{value::Element, IonType};

// TODO: Make sha2 an optional dependency.
use sha2::Sha256;
use type_qualifier::TypeQualifier;

mod representation;
mod type_qualifier;

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
}

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
pub struct IonHasher<D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    hasher: D,
}

impl<D> IonHasher<D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    pub fn new(hasher: D) -> Self {
        Self { hasher }
    }

    /// Computes the Ion hash over an [`Element`] recursively using this
    /// hasher's [`Digest`]
    pub fn hash_element<E: Element + ?Sized>(mut self, elem: &E) -> IonResult<Output<D>> {
        self.mark_begin();
        match elem.ion_type() {
            IonType::Null | IonType::Boolean => self.hash_no_repr(elem),
            IonType::Integer
            | IonType::Float
            | IonType::Decimal
            | IonType::Timestamp
            | IonType::Symbol
            | IonType::String
            | IonType::Clob
            | IonType::Blob
            | IonType::Struct => self.hash(elem),
            IonType::List | IonType::SExpression => todo!(),
        };
        self.mark_end();

        // TODO: Annotations

        Ok(self.hasher.finalize_fixed())
    }

    #[inline]
    fn mark_begin(&mut self) {
        self.hasher.update([Markers::B]);
    }

    #[inline]
    fn mark_end(&mut self) {
        self.hasher.update([Markers::E]);
    }

    fn hash_no_repr<E: Element + ?Sized>(&mut self, elem: &E) {
        let tq = TypeQualifier::from_element(elem);
        self.hasher.update(tq.as_bytes());
    }

    fn hash<E: Element + ?Sized>(&mut self, elem: &E) {
        self.hash_no_repr(elem);
        representation::update_with_representation(elem, &mut self.hasher);
    }
}
