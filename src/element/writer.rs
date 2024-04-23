// Copyright Amazon.com, Inc. or its affiliates.

//! Provides utility to serialize Ion data from [`Element`] into common targets
//! such as byte buffers or files.

use crate::result::IonResult;
use crate::{Element, TextKind, Value};

use crate::lazy::encoding::BinaryEncoding_1_1;
#[cfg(feature = "experimental-lazy-reader")]
use {
    crate::lazy::encoder::{LazyEncoder, LazyRawWriter},
    crate::lazy::encoding::{BinaryEncoding_1_0, Encoding, TextEncoding_1_0},
    std::io,
    std::marker::PhantomData,
};

/// Writer configuration to provide format and Ion version details to writer through encoding
/// This will be used to create a writer without specifying which writer methods to use
#[cfg(feature = "experimental-lazy-reader")]
#[derive(Clone, Debug)]
pub struct WriteConfig<E: Encoding> {
    pub(crate) kind: WriteConfigKind,
    phantom_data: PhantomData<E>,
}

#[cfg(feature = "experimental-lazy-reader")]
impl<E: Encoding + LazyEncoder> WriteConfig<E> {
    /// Builds a writer based on writer configuration
    pub fn build<W: io::Write>(self, output: W) -> IonResult<<E as LazyEncoder>::Writer<W>> {
        E::Writer::build(self, output)
    }
}

#[cfg(feature = "experimental-lazy-reader")]
impl WriteConfig<TextEncoding_1_0> {
    pub fn new(text_kind: TextKind) -> Self {
        Self {
            kind: WriteConfigKind::Text(TextWriteConfig { text_kind }),
            phantom_data: Default::default(),
        }
    }
}

#[cfg(feature = "experimental-lazy-reader")]
impl WriteConfig<BinaryEncoding_1_0> {
    pub fn new() -> Self {
        Self {
            kind: WriteConfigKind::Binary(BinaryWriteConfig),
            phantom_data: Default::default(),
        }
    }
}

#[cfg(feature = "experimental-lazy-reader")]
impl WriteConfig<BinaryEncoding_1_1> {
    pub fn new() -> Self {
        Self {
            kind: WriteConfigKind::Binary(BinaryWriteConfig),
            phantom_data: Default::default(),
        }
    }
}

#[cfg(feature = "experimental-lazy-reader")]
impl Default for WriteConfig<BinaryEncoding_1_0> {
    fn default() -> Self {
        Self::new()
    }
}

/// Writer configuration type enum for text and binary configuration
#[derive(Clone, Debug)]
pub(crate) enum WriteConfigKind {
    Text(TextWriteConfig),
    Binary(BinaryWriteConfig),
}

/// Text writer configuration with text kind to be used to create a writer
#[derive(Clone, Debug)]
pub(crate) struct TextWriteConfig {
    pub(crate) text_kind: TextKind,
}

/// Binary writer configuration to be used to create a writer
// TODO: Add appropriate binary configuration if required for 1.1
#[derive(Clone, Debug)]
pub(crate) struct BinaryWriteConfig;

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
