use std::io;
use std::marker::PhantomData;
use std::num::NonZeroU8;

use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::value_writer_config::ValueWriterConfig;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::writer::Writer;
use crate::lazy::encoding::{BinaryEncoding_1_0, Encoding, OutputFromBytes, TextEncoding_1_0};
use crate::{IonResult, TextFormat};

/// Writer configuration to provide format and Ion version details to writer through encoding
/// This will be used to create a writer without specifying which writer methods to use
#[derive(Clone, Debug)]
pub struct WriteConfig<E: Encoding> {
    kind: WriteConfigKind,
    // `None` means the default limit of `u16::MAX` levels of nested containers.
    max_depth: Option<NonZeroU8>,
    phantom_data: PhantomData<E>,
}

impl<E: Encoding> WriteConfig<E> {
    pub(crate) fn kind(&self) -> &WriteConfigKind {
        &self.kind
    }

    /// Limits how deeply values may be nested when they are encoded with this configuration, for
    /// example by [`Element::encode_as`](crate::Element::encode_as),
    /// [`Element::encode_to`](crate::Element::encode_to),
    /// [`Sequence::encode_as`](crate::Sequence::encode_as), and
    /// [`Sequence::encode_to`](crate::Sequence::encode_to). Top-level values are at depth 0 and a
    /// container's children are one level deeper than the container, so in `[[1]]` the inner list
    /// is at depth 1 and `1` is at depth 2. This permits at most `max_depth` levels of nested
    /// containers. Typed nulls such as `null.list` are not opened as containers, so they are
    /// accepted at any depth. By default, at most `u16::MAX` levels of containers may be nested.
    ///
    /// Opening a container whose children would be deeper than `max_depth` returns an encoding
    /// error, even if the container is empty.
    ///
    /// Raw writers built from this configuration do not enforce the limit.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use std::num::NonZeroU8;
    /// use ion_rs::{v1_0, Element, IonError, WriteConfig};
    ///
    /// let config = WriteConfig::<v1_0::Binary>::new().with_max_depth(NonZeroU8::new(2).unwrap());
    /// assert!(Element::read_one("[[1]]")?.encode_as(config.clone()).is_ok());
    /// assert!(matches!(
    ///     Element::read_one("[[[1]]]")?.encode_as(config),
    ///     Err(IonError::Encoding(_))
    /// ));
    ///# Ok(())
    ///# }
    /// ```
    pub fn with_max_depth(mut self, max_depth: NonZeroU8) -> Self {
        self.max_depth = Some(max_depth);
        self
    }

    /// Returns the configuration for the top-level value writer of a managed writer using this
    /// configuration.
    pub(crate) fn value_writer_config(&self) -> ValueWriterConfig {
        let remaining_depth = self
            .max_depth
            .map_or(u16::MAX, |depth| u16::from(depth.get()));
        E::default_value_writer_config().with_remaining_depth(remaining_depth)
    }

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
        let mut writer = Writer::new(self.clone(), output)?;
        writer.write(value)?;
        writer.close()
    }

    pub(crate) fn encode_all_to<V: WriteAsIon, I: IntoIterator<Item = V>, W: io::Write>(
        &self,
        output: W,
        values: I,
    ) -> IonResult<W> {
        let mut writer = Writer::new(self.clone(), output)?;
        writer.write_all(values)?;
        writer.close()
    }
}

impl WriteConfig<TextEncoding_1_0> {
    pub fn new(text_kind: TextFormat) -> Self {
        Self {
            kind: WriteConfigKind::Text(TextWriteConfig { text_kind }),
            max_depth: None,
            phantom_data: Default::default(),
        }
    }
}

impl WriteConfig<BinaryEncoding_1_0> {
    pub fn new() -> Self {
        Self {
            kind: WriteConfigKind::Binary(BinaryWriteConfig),
            max_depth: None,
            phantom_data: Default::default(),
        }
    }
}

impl Default for WriteConfig<TextEncoding_1_0> {
    fn default() -> Self {
        Self::new(TextFormat::Compact)
    }
}

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
    pub(crate) text_kind: TextFormat,
}

/// Binary writer configuration to be used to create a writer
#[derive(Clone, Debug)]
pub(crate) struct BinaryWriteConfig;

impl From<TextEncoding_1_0> for WriteConfig<TextEncoding_1_0> {
    fn from(_encoding: TextEncoding_1_0) -> Self {
        WriteConfig::<TextEncoding_1_0>::default()
    }
}

impl From<BinaryEncoding_1_0> for WriteConfig<BinaryEncoding_1_0> {
    fn from(_encoding: BinaryEncoding_1_0) -> Self {
        WriteConfig::<BinaryEncoding_1_0>::default()
    }
}
