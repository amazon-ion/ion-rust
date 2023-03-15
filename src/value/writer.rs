// Copyright Amazon.com, Inc. or its affiliates.

//! Provides utility to serialize Ion data from [`Element`](super::owned::Element) into common targets
//! such as byte buffers or files.

use crate::result::IonResult;

use crate::value::owned::Element;
pub use Format::*;
pub use TextKind::*;

/// Serializes [`Element`] instances into some kind of output sink.
pub trait ElementWriter {
    /// The output of the writer when finishing, it could be a managed buffer,
    /// some concept of a stream, metadata about a file, or something appropriate
    /// for the destination.
    type Output;

    /// Serializes a single [`Element`] as a top-level value.
    fn write(&mut self, element: &Element) -> IonResult<()>;

    /// Serializes a collection of [`Element`] as a series of top-level values.
    ///
    /// This will return [`Err`] if writing any value causes a failure.
    fn write_all<'a, I: IntoIterator<Item = &'a Element>>(
        &'a mut self,
        elements: I,
    ) -> IonResult<()> {
        for element in elements.into_iter() {
            self.write(element)?;
        }
        Ok(())
    }

    /// Consumes this [`ElementWriter`] flushing/finishing/closing it and returns
    /// the underlying output sink.
    ///
    /// If a previous write operation returned [`Err`], this method should also return [`Err`].
    fn finish(self) -> IonResult<Self::Output>;
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
