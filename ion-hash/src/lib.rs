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

use std::io;

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

pub trait IonHasher<E>
where
    E: Element + ?Sized,
{
    type Output;

    fn hash_element(elem: &E) -> IonResult<Self::Output>;
}

impl<E, D> IonHasher<E> for D
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
        ElementHasher::new(D::default()).hash_element(elem)
    }
}

struct ElementHasher<D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    pub(crate) digest: D,
}

impl<D> ElementHasher<D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    fn new(digest: D) -> ElementHasher<D> {
        ElementHasher { digest }
    }

    fn hash_element<E>(mut self, elem: &E) -> IonResult<Output<D>>
    where
        E: Element + ?Sized,
    {
        self.update_serialized_bytes(elem)?;
        Ok(self.digest.finalize_fixed())
    }

    /// Implements the "serialized bytes" transform as described in the spec. The
    /// bytes are written to `hasher` (as opposed to returned) for performance
    /// reasons (avoid allocations for DSTs).
    fn update_serialized_bytes<E>(&mut self, elem: &E) -> IonResult<()>
    where
        E: Element + ?Sized,
    {
        self.mark_begin();
        self.update_type_qualifier_and_representation(elem)?;
        // TODO: Annotations
        self.mark_end();

        Ok(())
    }

    #[inline]
    fn mark_begin(&mut self) {
        self.digest.update([Markers::B]);
    }

    #[inline]
    fn mark_end(&mut self) {
        self.digest.update([Markers::E]);
    }

    fn update_type_qualifier_and_representation<E>(&mut self, elem: &E) -> IonResult<()>
    where
        E: Element + ?Sized,
    {
        let tq = TypeQualifier::from_element(elem);
        self.digest.update(tq.as_bytes());
        self.update_with_representation(elem)
    }

    /// Escapes various markers as per the spec. Allocates a temporary array to
    /// do so.
    fn update_escaping(&mut self, data: impl AsRef<[u8]>) {
        let mut escaped = vec![];

        for byte in data.as_ref() {
            if let Markers::B | Markers::E | Markers::ESC = *byte {
                escaped.extend(&[Markers::ESC, *byte]);
            } else {
                escaped.extend(&[*byte]);
            }
        }

        self.digest.update(escaped);
    }
}

/// The ion-rust crate uses the `io::Write` trait as a sink for writing
/// representations. This implementation provides compatibility with the
/// `Digest` trait (represented as a set of "sub"-traits). We have no need of an
/// intermediate buffer!
impl<D> io::Write for ElementHasher<D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.update_escaping(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
