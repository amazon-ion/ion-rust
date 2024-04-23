use std::io;
use std::marker::PhantomData;

use crate::lazy::encoder::LazyRawWriter;
use crate::lazy::encoding::{
    BinaryEncoding_1_0, BinaryEncoding_1_1, Encoding, TextEncoding_1_0, TextEncoding_1_1,
};
use crate::{IonResult, TextKind};

/// Writer configuration to provide format and Ion version details to writer through encoding
/// This will be used to create a writer without specifying which writer methods to use
#[cfg(feature = "experimental-lazy-reader")]
#[derive(Clone, Debug)]
pub struct WriteConfig<E: Encoding> {
    pub(crate) kind: WriteConfigKind,
    phantom_data: PhantomData<E>,
}

#[cfg(feature = "experimental-lazy-reader")]
impl<E: Encoding> WriteConfig<E> {
    /// Builds a writer based on writer configuration
    pub fn build<W: io::Write>(self, output: W) -> IonResult<E::Writer<W>> {
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
impl WriteConfig<TextEncoding_1_1> {
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
