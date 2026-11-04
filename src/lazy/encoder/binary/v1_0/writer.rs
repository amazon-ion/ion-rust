use delegate::delegate;
use std::io::Write;

use crate::binary::constants::v1_0::IVM as IVM_1_0;
use crate::lazy::encoder::binary::v1_0::value_writer::BinaryValueWriter_1_0;
use crate::lazy::encoder::binary::v1_0::DEFAULT_ENCODING_BUFFER_SIZE;
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::{
    cap_retained_buffer, LazyRawWriter, Recycle, Reusable, WriterRole, IDLE_RETAIN_CAP,
};
use crate::lazy::encoding::{BinaryEncoding_1_0, Encoding};
use crate::write_config::{BinaryWriteConfig, WriteConfig, WriteConfigKind};
use crate::{ContextWriter, IonResult};

/// A "raw"-level streaming binary Ion writer. This writer does not provide symbol table
/// management; symbol-related operations (e.g. setting field IDs and annotations or writing symbol
/// values) require a valid symbol ID to be provided by the caller.
pub struct LazyRawBinaryWriter_1_0<W: Write> {
    // The sink to which all of the writer's encoded data will be written.
    output: W,
    // Values encoded since the last flush. Containers are encoded in place, so this is the writer's
    // only scratch memory.
    encoding_buffer: Vec<u8>,
}

// Implemented only for the `Vec<u8>` instantiation: that is the only one the managed writer's
// reusable-writer API needs (`E::Writer<Vec<u8>>: Reusable`), and it is what makes re-seeding the IVM
// below infallible.
impl Reusable for LazyRawBinaryWriter_1_0<Vec<u8>> {}

impl Recycle for LazyRawBinaryWriter_1_0<Vec<u8>> {
    /// Returns this writer to its freshly-built state so it can encode another document, discarding
    /// any buffered (unflushed) content: the output buffer and the encoding buffer are emptied, either
    /// is released if it has grown past [`IDLE_RETAIN_CAP`], and -- for [`WriterRole::System`] -- the
    /// Ion 1.0 IVM that `new` emits is re-seeded.
    ///
    /// Nothing is written to any sink here, so bytes the caller wanted emitted must have been
    /// `flush`ed beforehand.
    fn recycle(&mut self, role: WriterRole) {
        self.encoding_buffer.clear();
        if self.encoding_buffer.capacity() > IDLE_RETAIN_CAP {
            // Bound retained memory: drop an oversized encoding buffer in favor of a fresh one.
            // `cap_retained_buffer` sizes its replacements for output buffers; this uses
            // `DEFAULT_ENCODING_BUFFER_SIZE` instead, so a recycled writer matches a newly built one.
            self.encoding_buffer = Vec::with_capacity(DEFAULT_ENCODING_BUFFER_SIZE);
        }
        // Discard anything still buffered. Doing this here rather than in the caller is what makes
        // the "discards unflushed content" contract self-enforcing: capping the buffer below may
        // replace it outright, and the IVM re-seed must land in an otherwise empty buffer.
        self.output.clear();
        // Bound the output buffer too; it grew to hold the largest document this writer encoded.
        // This must precede the IVM below, because replacing the buffer would drop it.
        cap_retained_buffer::<BinaryEncoding_1_0>(&mut self.output, role);
        if role == WriterRole::System {
            // A freshly built binary writer emits the IVM (see `new`); re-seed it so the reused
            // writer starts a new stream exactly as a fresh one would. Written straight to the `Vec`
            // rather than through the fallible `write_version_marker` to keep `recycle` infallible.
            // Only the system writer carries the prologue -- emitting it on the application writer
            // would corrupt the stream (<IVM><symtab><IVM><data>).
            self.output.extend_from_slice(&IVM_1_0);
        }
    }

    /// Nothing to do: a binary writer derives no state from its [`WriteConfig`]; `build` only
    /// validates that the config is a binary one.
    fn apply_config<E: Encoding>(&mut self, config: &WriteConfig<E>) {
        match config.kind() {
            // Destructured rather than matched with `_` so that a `BinaryWriteConfig` which grows a
            // field stops compiling here instead of silently leaving this writer configured for the
            // previous caller's document.
            WriteConfigKind::Binary(BinaryWriteConfig) => {}
            // Same as `build`'s: an `E`'s writer type and its config kind are chosen together, so a
            // text config can never reach the binary writer.
            WriteConfigKind::Text(_) => {
                unreachable!("Binary writer can not be configured from text encoding")
            }
        }
    }
}

impl<W: Write> LazyRawBinaryWriter_1_0<W> {
    /// Constructs a new binary writer and writes an Ion 1.0 Version Marker to output.
    pub fn new(mut output: W) -> IonResult<Self> {
        // Write the Ion 1.0 IVM
        output.write_all(&IVM_1_0)?;
        // Construct the writer
        Ok(Self {
            output,
            encoding_buffer: Vec::with_capacity(DEFAULT_ENCODING_BUFFER_SIZE),
        })
    }

    /// Writes the given Rust value to the output stream as a top-level value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        value.write_as_ion(self.value_writer())?;
        Ok(self)
    }

    /// Flushes any encoded bytes that have not already been written to the output sink, then
    /// flushes the sink.
    ///
    /// The encoding buffer keeps its grown capacity across flushes.
    pub fn flush(&mut self) -> IonResult<()> {
        if !self.encoding_buffer.is_empty() {
            // Write our top level encoding buffer's contents to the output sink.
            self.output.write_all(&self.encoding_buffer)?;
        }
        // Flush the output sink, which may have its own buffers.
        self.output.flush()?;
        self.encoding_buffer.clear();
        Ok(())
    }

    /// The number of bytes of scratch memory (excluding `output`) this writer currently retains.
    // Exposed for the reuse tests, which check whether recycling keeps or releases it.
    #[cfg(test)]
    pub(crate) fn retained_scratch_bytes(&self) -> usize {
        self.encoding_buffer.capacity()
    }

    pub(crate) fn value_writer(&mut self) -> BinaryValueWriter_1_0<'_> {
        BinaryValueWriter_1_0::new(&mut self.encoding_buffer)
    }
}

impl<W: Write> Sealed for LazyRawBinaryWriter_1_0<W> {}

impl<W: Write> LazyRawWriter<W> for LazyRawBinaryWriter_1_0<W> {
    fn new(output: W) -> IonResult<Self> {
        Self::new(output)
    }

    /// Build binary writer based on given writer configuration
    fn build<E: Encoding>(config: WriteConfig<E>, output: W) -> IonResult<Self> {
        match config.kind() {
            WriteConfigKind::Text(_) => {
                unreachable!("Text writer can not be created from binary encoding")
            }
            WriteConfigKind::Binary(_) => LazyRawBinaryWriter_1_0::new(output),
        }
    }

    fn output(&self) -> &W {
        &self.output
    }

    delegate! {
        to self {
            fn flush(&mut self) -> IonResult<()>;
        }
    }

    fn output_mut(&mut self) -> &mut W {
        &mut self.output
    }

    fn write_version_marker(&mut self) -> IonResult<()> {
        self.output.write_all(&IVM_1_0)?;
        Ok(())
    }
}

impl<W: Write> ContextWriter for LazyRawBinaryWriter_1_0<W> {
    type NestedValueWriter<'a>
        = BinaryValueWriter_1_0<'a>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for LazyRawBinaryWriter_1_0<W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        self.value_writer()
    }
}

impl<W: Write> SequenceWriter for LazyRawBinaryWriter_1_0<W> {
    type Resources = W;

    fn close(mut self) -> IonResult<Self::Resources> {
        self.flush()?;
        Ok(self.output)
    }
    // Uses the default method implementations from SequenceWriter
}

#[cfg(test)]
mod flush_tests {
    use super::LazyRawBinaryWriter_1_0;
    use crate::binary::constants::v1_0::IVM as IVM_1_0;
    use crate::lazy::encoder::LazyRawWriter;
    use crate::IonResult;
    use std::io::BufWriter;

    /// `flush` must flush the sink even when the encoding buffer is empty: `new` writes the IVM
    /// straight to the sink, so a buffered sink holds it back until it is flushed.
    #[test]
    fn flush_flushes_the_sink_when_nothing_is_buffered() -> IonResult<()> {
        let mut writer = LazyRawBinaryWriter_1_0::new(BufWriter::new(Vec::new()))?;
        // Precondition: the IVM is still held in the `BufWriter`, not yet in the `Vec`.
        assert!(
            writer.output().get_ref().is_empty(),
            "the sink passed the IVM through before `flush`"
        );
        writer.flush()?;
        assert_eq!(
            writer.output().get_ref().as_slice(),
            IVM_1_0.as_slice(),
            "`flush` did not flush the sink"
        );
        Ok(())
    }
}
