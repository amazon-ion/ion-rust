// Copyright Amazon.com, Inc. or its affiliates.

//! Provides utility to serialize Ion data from [`Element`](super::owned::Element) into common targets
//! such as byte buffers or files.

use crate::result::IonResult;

use crate::element::owned::Element;
pub use Format::*;
pub use TextKind::*;

/// Serializes [`Element`] instances into some kind of output sink.
pub trait ElementWriter {
    /// Serializes a single [`Element`] as a top-level value.
    fn write_element(&mut self, element: &Element) -> IonResult<()>;

    /// Serializes a collection of [`Element`] as a series of top-level values.
    ///
    /// This will return [`Err`] if writing any element causes a failure.
    fn write_elements<'a, I: IntoIterator<Item = &'a Element>>(
        &'a mut self,
        elements: I,
    ) -> IonResult<()> {
        for element in elements.into_iter() {
            self.write_element(element)?;
        }
        Ok(())
    }
}

/// Whether or not the text is pretty printed or serialized in a more compact representation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TextKind {
    Compact,
    Lines,
    Pretty,
}

/// Basic configuration options for [`ElementWriter`] instances.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Format {
    Text(TextKind),
    Binary,
    // TODO a mode for Json(TextKind)
}
