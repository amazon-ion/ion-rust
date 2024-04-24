// Copyright Amazon.com, Inc. or its affiliates.

//! Provides utility to serialize Ion data from [`Element`] into common targets
//! such as byte buffers or files.

use crate::result::IonResult;
use crate::{Element, Value};

/// Serializes [`Element`] instances into some kind of output sink.
pub trait ElementWriter {
    /// Serializes a single [`Value`] at the current depth of the writer.
    fn write_value(&mut self, value: &Value) -> IonResult<()>;

    /// Serializes a single [`Element`] at the current depth of the writer.
    fn write_element(&mut self, element: &Element) -> IonResult<()>;

    /// Serializes a collection of [`Element`].
    ///
    /// Most commonly used to serialize a series of top-level values, but can be used to write
    /// [`Element`]s to an Ion `list` or `sexp` as well.
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
