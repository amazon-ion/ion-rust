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
use ion_rs::{value::Element, IonType};

// TODO: Make sha2 an optional dependency.
use sha2::Sha256;
use type_qualifier::TypeQualifier;

mod representation;
mod type_qualifier;

/// Utility to hash an [`Element`] using SHA-256 as the hash function.
// TODO: Make this conditional on some feature flag
pub fn sha256<E: Element + ?Sized>(elem: &E) -> IonResult<Output<Sha256>> {
    hash_element::<E, Sha256>(elem)
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
pub fn hash_element<E, D>(elem: &E) -> IonResult<Output<D>>
where
    E: Element + ?Sized,
    D: Update + FixedOutput + Reset + Clone + Default,
{
    let mut hasher = D::default();
    update_serialized_bytes(elem, &mut hasher)?;
    Ok(hasher.finalize_fixed())
}

/// Implements the "serialized bytes" transform as described in the spec. The
/// bytes are written to `hasher` (as opposed to returned) for performance
/// reasons (avoid allocations for DSTs).
fn update_serialized_bytes<E, D>(elem: &E, hasher: &mut D) -> IonResult<()>
where
    E: Element + ?Sized,
    D: Update + FixedOutput + Reset + Clone + Default,
{
    mark_begin(hasher);
    match elem.ion_type() {
        IonType::Null | IonType::Boolean => update_type_qualifier(elem, hasher),
        IonType::Integer
        | IonType::Float
        | IonType::Decimal
        | IonType::Timestamp
        | IonType::Symbol
        | IonType::String
        | IonType::Clob
        | IonType::Blob
        | IonType::Struct
        | IonType::List
        | IonType::SExpression => update_type_qualifier_and_representation(elem, hasher)?,
    };
    // TODO: Annotations
    mark_end(hasher);

    Ok(())
}

#[inline]
fn mark_begin<U: Update>(hasher: &mut U) {
    hasher.update([Markers::B]);
}

#[inline]
fn mark_end<U: Update>(hasher: &mut U) {
    hasher.update([Markers::E]);
}

fn update_type_qualifier<E: Element + ?Sized, U: Update>(elem: &E, hasher: &mut U) {
    let tq = TypeQualifier::from_element(elem);
    hasher.update(tq.as_bytes());
}

fn update_type_qualifier_and_representation<E, D>(elem: &E, hasher: &mut D) -> IonResult<()>
where
    E: Element + ?Sized,
    D: Update + FixedOutput + Reset + Clone + Default,
{
    update_type_qualifier(elem, hasher);
    representation::update_with_representation(elem, hasher)
}
