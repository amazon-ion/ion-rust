use std::io;
use std::marker::PhantomData;

use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::writer::IonWriter;
use crate::lazy::encoder::LazyRawWriter;
use crate::lazy::encoding::{
    BinaryEncoding_1_0, BinaryEncoding_1_1, Encoding, OutputFromBytes, TextEncoding_1_0,
    TextEncoding_1_1,
};
use crate::{IonResult, TextKind};

/// Writer configuration to provide format and Ion version details to writer through encoding
/// This will be used to create a writer without specifying which writer methods to use
#[derive(Clone, Debug)]
pub struct WriteConfig<E: Encoding> {
    pub(crate) kind: WriteConfigKind,
    phantom_data: PhantomData<E>,
}

impl<E: Encoding> WriteConfig<E> {
    pub(crate) fn encode<V: WriteAsIon>(&self, value: V) -> IonResult<E::Output> {
        let bytes = self.encode_to(value, Vec::new())?;
        Ok(E::Output::from_bytes(bytes))
    }

    pub(crate) fn encode_all<V: WriteAsIon, I: IntoIterator<Item = V>>(
        &self,
        values: I,
    ) -> IonResult<E::Output> {
        let bytes = self.encode_all_to(Vec::new(), values)?;
        Ok(E::Output::from_bytes(bytes))
    }

    pub(crate) fn encode_to<V: WriteAsIon, W: io::Write>(
        &self,
        value: V,
        output: W,
    ) -> IonResult<W> {
        let mut writer = IonWriter::with_config(self.clone(), output)?;
        writer.write(value)?;
        writer.close()
    }

    pub(crate) fn encode_all_to<V: WriteAsIon, I: IntoIterator<Item = V>, W: io::Write>(
        &self,
        output: W,
        values: I,
    ) -> IonResult<W> {
        let mut writer = IonWriter::with_config(self.clone(), output)?;
        writer.write_all(values)?;
        writer.close()
    }

    #[cfg(feature = "experimental-reader-writer")]
    pub fn build_writer<W: io::Write>(self, output: W) -> IonResult<IonWriter<E, W>> {
        IonWriter::with_config(self, output)
    }

    // When the experimental-reader-writer feature is disabled, this method is `pub(crate)` instead
    // of `pub`
    #[cfg(not(feature = "experimental-reader-writer"))]
    pub(crate) fn build_writer<W: io::Write>(self, output: W) -> IonResult<IonWriter<E, W>> {
        IonWriter::with_config(self, output)
    }

    #[cfg(feature = "experimental-tooling-apis")]
    /// Builds a writer based on writer configuration
    pub fn build_raw_writer<W: io::Write>(self, output: W) -> IonResult<E::Writer<W>> {
        E::Writer::build(self, output)
    }

    // When the experimental-tooling-apis feature is disabled, this method is `pub(crate)` instead
    // of `pub`
    #[cfg(not(feature = "experimental-tooling-apis"))]
    pub(crate) fn build_raw_writer<W: io::Write>(self, output: W) -> IonResult<E::Writer<W>> {
        E::Writer::build(self, output)
    }
}

impl WriteConfig<TextEncoding_1_0> {
    pub fn new(text_kind: TextKind) -> Self {
        Self {
            kind: WriteConfigKind::Text(TextWriteConfig { text_kind }),
            phantom_data: Default::default(),
        }
    }
}

impl WriteConfig<TextEncoding_1_1> {
    pub fn new(text_kind: TextKind) -> Self {
        Self {
            kind: WriteConfigKind::Text(TextWriteConfig { text_kind }),
            phantom_data: Default::default(),
        }
    }
}

impl WriteConfig<BinaryEncoding_1_0> {
    pub fn new() -> Self {
        Self {
            kind: WriteConfigKind::Binary(BinaryWriteConfig),
            phantom_data: Default::default(),
        }
    }
}

impl WriteConfig<BinaryEncoding_1_1> {
    pub fn new() -> Self {
        Self {
            kind: WriteConfigKind::Binary(BinaryWriteConfig),
            phantom_data: Default::default(),
        }
    }
}

impl Default for WriteConfig<TextEncoding_1_0> {
    fn default() -> Self {
        Self::new(TextKind::Compact)
    }
}

impl Default for WriteConfig<TextEncoding_1_1> {
    fn default() -> Self {
        Self::new(TextKind::Compact)
    }
}

impl Default for WriteConfig<BinaryEncoding_1_0> {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for WriteConfig<BinaryEncoding_1_1> {
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

impl From<TextEncoding_1_0> for WriteConfig<TextEncoding_1_0> {
    fn from(_encoding: TextEncoding_1_0) -> Self {
        WriteConfig::<TextEncoding_1_0>::default()
    }
}

impl From<TextEncoding_1_1> for WriteConfig<TextEncoding_1_1> {
    fn from(_encoding: TextEncoding_1_1) -> Self {
        WriteConfig::<TextEncoding_1_1>::default()
    }
}

impl From<BinaryEncoding_1_0> for WriteConfig<BinaryEncoding_1_0> {
    fn from(_encoding: BinaryEncoding_1_0) -> Self {
        WriteConfig::<BinaryEncoding_1_0>::default()
    }
}

impl From<BinaryEncoding_1_1> for WriteConfig<BinaryEncoding_1_1> {
    fn from(_encoding: BinaryEncoding_1_1) -> Self {
        WriteConfig::<BinaryEncoding_1_1>::default()
    }
}
