// Copyright Amazon.com, Inc. or its affiliates.

//! Provides [`ElementHasher`], a single-use IonHash implementation for an
//! [`Element`].

use std::io;

use crate::element::Element;
use crate::IonResult;
use digest::{FixedOutput, Output, Reset, Update};

use crate::ion_hash::representation::RepresentationEncoder;
use crate::ion_hash::type_qualifier::TypeQualifier;
use crate::ion_hash::Markers;

pub(crate) struct ElementHasher<D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    pub(crate) digest: D,
}

impl<D> ElementHasher<D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    pub(crate) fn new(digest: D) -> ElementHasher<D> {
        ElementHasher { digest }
    }

    pub(crate) fn hash_element(mut self, elem: &Element) -> IonResult<Output<D>> {
        self.update_serialized_bytes(elem)?;
        Ok(self.digest.finalize_fixed())
    }

    /// Implements the "serialized bytes" transform as described in the spec. The
    /// bytes are written to `hasher` (as opposed to returned) for performance
    /// reasons (avoid allocations for DSTs).
    pub(crate) fn update_serialized_bytes(&mut self, elem: &Element) -> IonResult<()> {
        let has_annotations = !elem.annotations().is_empty();
        if has_annotations {
            // s(annotated value) → B || TQ || s(annotation) || s(annotation) || ... || s(annotation) || s(value) || E
            self.mark_begin();
            self.digest.update([0xE0]);
            for ann in elem.annotations() {
                self.mark_begin();
                self.digest.update(match ann.text() {
                    None => [0x71],
                    Some(_) => [0x70],
                });
                self.write_repr_symbol(Some(ann))?;
                self.mark_end();
            }
        }

        self.mark_begin();
        self.update_type_qualifier_and_representation(elem)?;
        self.mark_end();

        if has_annotations {
            self.mark_end();
        }

        Ok(())
    }

    #[inline]
    pub(crate) fn mark_begin(&mut self) {
        self.digest.update([Markers::B]);
    }

    #[inline]
    pub(crate) fn mark_end(&mut self) {
        self.digest.update([Markers::E]);
    }

    pub(crate) fn update_type_qualifier_and_representation(
        &mut self,
        elem: &Element,
    ) -> IonResult<()> {
        let tq = TypeQualifier::from_element(elem);
        self.digest.update(tq.as_bytes());
        self.update_with_representation(elem)
    }

    /// Escapes various markers as per the spec. Allocates a temporary array to
    /// do so.
    pub(crate) fn update_escaping(&mut self, data: impl AsRef<[u8]>) {
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
