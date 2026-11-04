use delegate::delegate;
use ice_code::ice as cold_path;
#[cfg(test)]
use std::cell::Cell;
use std::io::Write;

use crate::constants::v1_0::system_symbol_ids;
use crate::element::element_writer::ElementWriter;
use crate::lazy::encoder::annotation_seq::{AnnotationSeq, AnnotationsVec};
use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{
    AnnotatableWriter, FieldWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::lazy::encoder::value_writer_config::{
    AnnotationsEncoding, FieldNameEncoding, SymbolValueEncoding, ValueWriterConfig,
};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::writer::private::{
    ManagedWriterStyle, SealedWriterConfig, StyledEncoding,
};
use crate::lazy::encoder::{
    initial_buffer_capacity, Encoder, LazyRawWriter, Recycle, Reusable, WriterRole,
    IDLE_RETAIN_CAP, IDLE_SYMBOL_RETAIN_CAP,
};
use crate::lazy::encoding::{BinaryEncoding_1_0, Encoding, TextEncoding_1_0};
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::{cold_error, IonFailure};
use crate::symbol_table::WriterSymbolTable;
use crate::text::whitespace_config::{CompactText, LinesText, PrettyText, RuntimeStyle, TextStyle};
use crate::write_config::{StyledWriteConfig, WriteConfig};
use crate::{
    ContextWriter, Decimal, Element, Int, IonResult, IonType, RawSymbolRef, Timestamp, Value,
};

/// The whitespace layout of a managed [`Writer`], as a type. By default, a writer reads the layout
/// of the [`TextFormat`] it is configured with at run time; a writer built with a marker such as
/// [`v1_0::CompactText`](crate::v1_0::CompactText) has the layout fixed at compile time. Binary
/// writers have the default style.
///
/// This trait is sealed and has no items of its own. It lets code be generic over a writer's
/// style:
///
/// ```
///# use ion_rs::IonResult;
///# #[cfg(feature = "experimental-reader-writer")]
///# fn main() -> IonResult<()> {
/// use ion_rs::{v1_0, TextFormat, Writer, WriterStyle};
///
/// fn write_greeting<S: WriterStyle>(writer: &mut Writer<v1_0::Text, Vec<u8>, S>) -> IonResult<()> {
///     writer.write("hello")?.write([1, 2])?;
///     Ok(())
/// }
///
/// let mut compact = Writer::new(v1_0::CompactText, Vec::new())?;
/// write_greeting(&mut compact)?;
/// assert_eq!(compact.close()?, b"\"hello\" [1, 2, ] ");
///
/// let mut lines = Writer::new(v1_0::Text.with_format(TextFormat::Lines), Vec::new())?;
/// write_greeting(&mut lines)?;
/// assert_eq!(lines.close()?, b"\"hello\"\n[1, 2, ]\n");
///# Ok(())
///# }
///# #[cfg(not(feature = "experimental-reader-writer"))]
///# fn main() -> IonResult<()> { Ok(()) }
/// ```
///
/// [`TextFormat`]: crate::TextFormat
// A style's raw writer is on the crate-private supertrait `ManagedWriterStyle`, and the layout on
// its supertrait `TextStyle`. `TextStyle` bounds the raw text writer, so keeping the managed
// writer's raw writer type off it leaves the raw layer with no notion of a managed writer.
pub trait WriterStyle: private::ManagedWriterStyle {}

/// A configuration of a managed [`Writer`] for the encoding `E` whose style is `S`, as
/// [`Writer::new`], [`Writer::idle`], and [`Writer::set_config`] take it:
///
/// - Every `C: Into<WriteConfig<E>>`, such as `v1_0::Binary`, `v1_0::Text`,
///   `v1_0::Text.with_format(format)`, or a [`WriteConfig`], configures a writer of the default
///   style, which reads the layout of the configured [`TextFormat`] at run time.
/// - Each marker, such as [`v1_0::CompactText`](crate::v1_0::CompactText), and the
///   [`StyledWriteConfig`](crate::v1_0::StyledWriteConfig) that its `with_max_depth` returns,
///   configures a text writer whose style is the marker, which fixes the layout at compile time.
///
/// This trait is sealed: it has no items of its own, and code outside the crate cannot implement
/// it.
///
/// ```
///# use ion_rs::IonResult;
///# #[cfg(feature = "experimental-reader-writer")]
///# fn main() -> IonResult<()> {
/// use ion_rs::{v1_0, IntoWriterConfig, Writer, WriterStyle};
///
/// fn write_one<S: WriterStyle>(config: impl IntoWriterConfig<v1_0::Text, S>) -> IonResult<Vec<u8>> {
///     let mut writer = Writer::new(config, Vec::new())?;
///     writer.write([1])?;
///     writer.close()
/// }
///
/// assert_eq!(write_one(v1_0::Text)?, b"[1, ] ");
/// assert_eq!(write_one(v1_0::PrettyText)?, b"[\n  1,\n]\n");
///# Ok(())
///# }
///# #[cfg(not(feature = "experimental-reader-writer"))]
///# fn main() -> IonResult<()> { Ok(()) }
/// ```
///
/// [`TextFormat`]: crate::TextFormat
pub trait IntoWriterConfig<E: Encoding, S>: private::SealedWriterConfig<E, S> {}

pub(crate) mod private {
    use std::io::Write;

    use crate::lazy::encoder::write_as_ion::WriteAsIon;
    use crate::lazy::encoder::LazyRawWriter;
    use crate::lazy::encoding::Encoding;
    use crate::text::whitespace_config::TextStyle;
    use crate::write_config::WriteConfig;
    use crate::IonResult;

    /// The crate-private half of [`WriterStyle`](super::WriterStyle). Code outside the crate can
    /// neither name nor implement it, but can reach its items through an `S: WriterStyle` bound.
    /// Their definitions are hidden from the docs, but `RawWriter` appears in the `Reusable`
    /// bounds of [`Writer`](super::Writer)'s reusable-writer methods. They are not a supported API.
    pub trait ManagedWriterStyle: TextStyle {
        /// The raw writer for the encoding `E` that a managed writer with this style uses.
        // `RuntimeStyle` names `E::Writer` rather than `E::StyledWriter<W, RuntimeStyle>`, so that a
        // bound on `E::Writer<Vec<u8>>` (such as `Reusable`) holds for `Writer<E, Output>` in code
        // that is generic over `E`.
        #[doc(hidden)]
        type RawWriter<E: Encoding, W: Write>: LazyRawWriter<W>;
    }

    /// The crate-private half of [`IntoWriterConfig`](super::IntoWriterConfig). Code outside the
    /// crate can neither name nor implement it, but can reach its items through an
    /// `IntoWriterConfig` bound; they are hidden from the docs and are not a supported API.
    pub trait SealedWriterConfig<E: Encoding, S> {
        /// The configuration of the writer. Its text format, if it has one, is one whose layout
        /// `S` writes.
        #[doc(hidden)]
        fn into_write_config(self) -> WriteConfig<E>;
    }

    /// The crate-private half of an [`Encoding`]'s writer support: its raw writer for each text
    /// style and how it encodes a stream whose configuration reads its layout at run time. Code
    /// outside the crate can neither name nor implement it, but can reach its items through an
    /// `E: Encoding` bound; they are hidden from the docs and are not a supported API.
    // A supertrait of `Encoding`, so that every `E: Encoding` has both. The `where Self: Encoding`
    // clause avoids a supertrait cycle with `Encoding`.
    pub trait StyledEncoding: Sized {
        /// A raw writer like [`Encoder::Writer`](crate::lazy::encoder::Encoder::Writer) whose
        /// whitespace layout is the style `S`. Encodings with no whitespace layout ignore `S`.
        #[doc(hidden)]
        type StyledWriter<W: Write, S: TextStyle>: LazyRawWriter<W>;

        /// Encodes `values` as a stream configured by `config`, which is written to `output`.
        // Not named `encode_all_to`, which every `E: Encoding` would then have twice. A method per
        // encoding rather than a `match` on the config's kind in `WriteConfig::encode_all_to`,
        // which would instantiate the binary writer once per text style.
        #[doc(hidden)]
        fn dispatch_encode_all_to<V: WriteAsIon, I: IntoIterator<Item = V>, W: Write>(
            config: &WriteConfig<Self>,
            output: W,
            values: I,
        ) -> IonResult<W>
        where
            Self: Encoding;
    }
}

impl WriterStyle for RuntimeStyle {}

impl ManagedWriterStyle for RuntimeStyle {
    type RawWriter<E: Encoding, W: Write> = E::Writer<W>;
}

// Markers and `StyledWriteConfig` must never implement `Into<WriteConfig<_>>`. If one did, both
// this impl and its marker impl would apply to it, and `Writer::new(marker, ..)` could no longer
// infer the style (E0283). `new_infers_the_encoding_and_style` pins this.
impl<E: Encoding, C: Into<WriteConfig<E>>> IntoWriterConfig<E, RuntimeStyle> for C {}

impl<E: Encoding, C: Into<WriteConfig<E>>> SealedWriterConfig<E, RuntimeStyle> for C {
    fn into_write_config(self) -> WriteConfig<E> {
        self.into()
    }
}

/// Makes the zero-sized style `$style` a managed writer style that it and its `StyledWriteConfig`
/// configure, with the text format whose layout it writes.
macro_rules! impl_static_writer_style {
    ($style:ident) => {
        impl WriterStyle for $style {}

        impl ManagedWriterStyle for $style {
            type RawWriter<E: Encoding, W: Write> = E::StyledWriter<W, Self>;
        }

        #[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
        impl $style {
            /// Returns a configuration of this style that limits how deeply values may be nested
            /// when a managed writer built with it encodes them; see
            /// [`WriteConfig::with_max_depth`].
            pub fn with_max_depth(self, max_depth: u16) -> StyledWriteConfig<Self> {
                StyledWriteConfig::new(Self::FORMAT).with_max_depth(max_depth)
            }
        }

        impl IntoWriterConfig<TextEncoding_1_0, $style> for $style {}

        impl SealedWriterConfig<TextEncoding_1_0, $style> for $style {
            fn into_write_config(self) -> WriteConfig<TextEncoding_1_0> {
                WriteConfig::<TextEncoding_1_0>::new(Self::FORMAT)
            }
        }

        impl IntoWriterConfig<TextEncoding_1_0, $style> for StyledWriteConfig<$style> {}

        impl SealedWriterConfig<TextEncoding_1_0, $style> for StyledWriteConfig<$style> {
            fn into_write_config(self) -> WriteConfig<TextEncoding_1_0> {
                // The inherent method, not this one.
                StyledWriteConfig::into_write_config(self)
            }
        }
    };
}

impl_static_writer_style!(CompactText);
impl_static_writer_style!(LinesText);
impl_static_writer_style!(PrettyText);

/// Binary has no whitespace layout, so it encodes with the configuration as it is.
impl StyledEncoding for BinaryEncoding_1_0 {
    type StyledWriter<W: Write, S: TextStyle> = <Self as Encoder>::Writer<W>;

    fn dispatch_encode_all_to<V: WriteAsIon, I: IntoIterator<Item = V>, W: Write>(
        config: &WriteConfig<Self>,
        output: W,
        values: I,
    ) -> IonResult<W> {
        encode_all_with_writer::<RuntimeStyle, _, _>(config.clone(), output, values)
    }
}

/// Text chooses, once per stream, the zero-sized style that writes the configured format. The
/// writer that encodes the stream is never exposed, so its type can depend on the format; a
/// [`Writer`] built from a run-time-styled configuration keeps [`RuntimeStyle`], because its type
/// cannot depend on a run-time value. Markers configure only managed writers, so they never reach
/// this dispatch.
///
/// This trades code size for speed: each value type encoded as text with a run-time-styled
/// configuration is compiled once per style, three times rather than once.
impl StyledEncoding for TextEncoding_1_0 {
    type StyledWriter<W: Write, S: TextStyle> = LazyRawTextWriter_1_0<W, S>;

    fn dispatch_encode_all_to<V: WriteAsIon, I: IntoIterator<Item = V>, W: Write>(
        config: &WriteConfig<Self>,
        output: W,
        values: I,
    ) -> IonResult<W> {
        let config = config.clone();
        // Each arm matches its style's `FORMAT`, so the match is exhaustive, with no wildcard,
        // only while every format has exactly one style.
        match config.text_format() {
            CompactText::FORMAT => {
                encode_all_with_writer::<CompactText, _, _>(config, output, values)
            }
            LinesText::FORMAT => encode_all_with_writer::<LinesText, _, _>(config, output, values),
            PrettyText::FORMAT => {
                encode_all_with_writer::<PrettyText, _, _>(config, output, values)
            }
        }
    }
}

#[cfg(test)]
thread_local! {
    /// The type name of the style of the writer that `encode_all_with_writer` last built on this
    /// thread.
    pub(crate) static LAST_ENCODED_STYLE: Cell<Option<&'static str>> = const { Cell::new(None) };
}

/// Encodes `values` as a stream with a managed writer of style `S` built from `config`, writing it
/// to `output`. `S` writes the layout of the text format of `config`, if it has one.
fn encode_all_with_writer<S: WriterStyle, E: Encoding, W: Write>(
    config: WriteConfig<E>,
    output: W,
    values: impl IntoIterator<Item = impl WriteAsIon>,
) -> IonResult<W> {
    #[cfg(test)]
    LAST_ENCODED_STYLE.set(Some(std::any::type_name::<S>()));
    let mut writer = Writer::<E, W, S>::from_write_config(config, output)?;
    writer.write_all(values)?;
    writer.close()
}

/// An Ion writer that maintains a symbol table and creates new entries as needed.
///
/// Unless a method states otherwise, a writer that has returned an error may have incomplete data
/// buffered. Flushing it is not guaranteed to produce a valid Ion stream.
///
/// A text writer's style `S` is the whitespace layout it writes, which comes from the configuration
/// it is built with (see [`IntoWriterConfig`]). By default, it reads the layout of the configured
/// [`TextFormat`] at run time; a writer built with a marker such as
/// [`v1_0::CompactText`](crate::v1_0::CompactText) has the layout fixed at compile time, so it does
/// not read the layout while encoding.
///
/// [`TextFormat`]: crate::TextFormat
// Note: the struct itself is generic over `Output` WITHOUT an `Output: Write` bound so that a
// sink-less `Writer<E, ()>` can be parked in a pool (e.g. thread-local) between uses, retaining its
// warm sub-writers and their scratch arenas. All encoding methods live in `impl<E, Output: Write>`;
// the idle state (`Writer<E, ()>`) exposes only `idle`/`set_config`/`attach`.
#[cfg_attr(feature = "experimental-reader-writer", visibility::make(pub))]
pub(crate) struct Writer<E: Encoding, Output, S: WriterStyle = RuntimeStyle> {
    symbols: WriterSymbolTable,
    data_writer: S::RawWriter<E, Vec<u8>>,
    directive_writer: S::RawWriter<E, Vec<u8>>,
    output: Output,
    value_writer_config: ValueWriterConfig,
}

// These aliases are used for selectively re-exporting writer types in lib.rs.
#[allow(dead_code)]
pub type TextWriter_1_0<Output> = Writer<TextEncoding_1_0, Output>;
#[allow(dead_code)]
pub type BinaryWriter_1_0<Output> = Writer<BinaryEncoding_1_0, Output>;

/// The sink-independent parts of a managed writer; see [`build_parts`].
// Named fields rather than a tuple: the two sub-writers have the same type, so a positional return
// would let a swapped destructuring compile silently.
struct WriterParts<E: Encoding, S: WriterStyle> {
    symbols: WriterSymbolTable,
    data_writer: S::RawWriter<E, Vec<u8>>,
    directive_writer: S::RawWriter<E, Vec<u8>>,
    value_writer_config: ValueWriterConfig,
}

/// Builds the sink-independent parts of a managed writer -- a fresh symbol table, the two
/// `Vec<u8>`-backed sub-writers, and the configuration for top-level values -- in the state a
/// freshly constructed writer is in before its first `flush`: the `directive_writer` holds the
/// encoding's construction prologue (an IVM for binary, nothing for text) and the `data_writer`'s
/// IVM has been erased.
///
/// [`Writer::new`] and [`Writer::idle`] differ only in the sink they bind (and, for `new`, the initial
/// `flush`), so they share this rather than each spelling the fields out and risking divergence.
///
/// The text format of `config`, if it has one, must be one whose layout `S` writes. A
/// `RuntimeStyle` raw writer reads its layout from it; a marker-styled one ignores it.
fn build_parts<E: Encoding, S: WriterStyle>(
    config: WriteConfig<E>,
) -> IonResult<WriterParts<E, S>> {
    let value_writer_config = config.value_writer_config();
    let directive_writer = S::RawWriter::<E, Vec<u8>>::build(
        config.clone(),
        Vec::with_capacity(initial_buffer_capacity::<E>(WriterRole::System)),
    )?;
    let mut data_writer = S::RawWriter::<E, Vec<u8>>::build(
        config,
        Vec::with_capacity(initial_buffer_capacity::<E>(WriterRole::Application)),
    )?;
    // Erase the IVM that's created by default; only the directive writer carries the prologue.
    data_writer.output_mut().clear();
    // TODO: LazyEncoder should define a method to construct a new symtab and/or macro table
    let symbols = WriterSymbolTable::new(E::ion_version());
    Ok(WriterParts {
        symbols,
        data_writer,
        directive_writer,
        value_writer_config,
    })
}

/// The idle (sink-less) state of a reusable managed writer. It holds warm sub-writers (each with a
/// warm scratch arena) and a fresh symbol table, but no output sink, so it can be parked in a pool.
/// Call [`Self::attach`] to bind a sink and get an active writer back.
///
/// Only encodings whose raw writer is [`Reusable`] have this API, which today means Ion 1.0 -- both
/// binary and text. For an encoding that opts out, the missing `Reusable` bound makes
/// `idle`/`attach`/`detach` resolve to nothing (E0599) rather than silently producing an invalid
/// document.
#[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
impl<E: Encoding, S: WriterStyle> Writer<E, (), S>
where
    S::RawWriter<E, Vec<u8>>: Reusable,
{
    /// Creates an idle (sink-less) writer that can be parked and reused: bind a sink with
    /// [`Self::attach`], encode, then reclaim it with [`Writer::detach`]. No bytes are emitted until
    /// a sink is attached and flushed.
    ///
    /// `config` applies to every document this writer goes on to encode and is otherwise fixed once
    /// it is built; use [`Self::set_config`] to re-configure a parked writer before attaching it to
    /// a new sink. A writer built with a marker such as
    /// [`v1_0::CompactText`](crate::v1_0::CompactText) has a different type from one built with a
    /// run-time-styled configuration, so a pool that holds both needs a slot for each style.
    pub fn idle(config: impl IntoWriterConfig<E, S>) -> IonResult<Self> {
        let WriterParts {
            symbols,
            data_writer,
            directive_writer,
            value_writer_config,
        } = build_parts::<E, S>(config.into_write_config())?;
        Ok(Writer {
            symbols,
            data_writer,
            directive_writer,
            output: (),
            value_writer_config,
        })
    }

    /// Re-configures this idle writer, which is otherwise fixed to the configuration it was built
    /// with. A pooled writer built for one caller's [`WriteConfig`] can then be handed to another's:
    /// call this before [`Self::attach`] so the next document honors the caller's configuration
    /// (e.g. `Pretty` rather than `Compact` text). This also replaces the maximum depth, so call it
    /// even for binary writers, which have no text format to change.
    ///
    /// A writer whose style is a marker such as [`v1_0::CompactText`](crate::v1_0::CompactText)
    /// accepts only that marker's configurations, so it keeps the marker's layout and only its
    /// maximum depth changes.
    pub fn set_config(&mut self, config: impl IntoWriterConfig<E, S>) {
        let config = config.into_write_config();
        self.directive_writer.apply_config(&config);
        self.data_writer.apply_config(&config);
        self.value_writer_config = config.value_writer_config();
    }

    /// Binds `output` to this idle writer and returns an active writer ready to encode.
    pub fn attach<Output: Write>(self, output: Output) -> Writer<E, Output, S> {
        // Moving the sub-writers (and so their scratch arenas) is sound: each holds its arena via an
        // `AliasableBump`, which keeps the `&Bump` captured by the arena-allocated encoding buffer
        // valid across the move.
        let (active, ()) = self.replace_output(output);
        active
    }
}

#[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
impl<E: Encoding, Output: Write, S: WriterStyle> Writer<E, Output, S>
where
    S::RawWriter<E, Vec<u8>>: Reusable,
{
    /// Returns this writer to the idle (sink-less) state along with the output sink, so the writer
    /// (and its warm sub-writers/arenas) can be parked in a pool and reused via
    /// [`Writer::<E, ()>::attach`].
    ///
    /// **This DISCARDS any un-flushed document.** Nothing is written to `output` here; call
    /// [`Self::flush`] (or [`Self::close`], if you do not need the writer back) first to emit what
    /// has been encoded so far. Detaching is deliberately infallible so that it is usable from a
    /// `Drop` impl, where an I/O error could not be reported: any writing that could fail is the
    /// caller's `flush`.
    ///
    /// The returned writer is in the same fresh-document state as [`Writer::<E, ()>::idle`], and
    /// bounds the memory it retains while parked.
    pub fn detach(mut self) -> (Writer<E, (), S>, Output) {
        // Forget the previous document's symbols (including any whose definition was still pending)
        // so the reused writer encodes a NEW, independent document.
        self.symbols
            .reset_for_reuse(IDLE_SYMBOL_RETAIN_CAP, IDLE_RETAIN_CAP);

        // Only the system role re-seeds the construction prologue; emitting one on the data writer
        // would corrupt the next document. Nothing is written to `output` -- that is `flush`'s job.
        self.directive_writer.recycle(WriterRole::System);
        self.data_writer.recycle(WriterRole::Application);

        self.replace_output(())
    }
}

// No `Output: Write` bound: this is how a writer crosses between the active (`Output: Write`) and
// idle (`Output = ()`) states.
#[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
impl<E: Encoding, Output, S: WriterStyle> Writer<E, Output, S> {
    /// Swaps this writer's output sink for `output`, returning the rebuilt writer and the sink it
    /// was holding. Everything else -- the warm sub-writers, their scratch arenas, the symbol table
    /// -- moves across untouched.
    fn replace_output<NewOutput>(self, output: NewOutput) -> (Writer<E, NewOutput, S>, Output) {
        let Writer {
            symbols,
            data_writer,
            directive_writer,
            output: previous_output,
            value_writer_config,
        } = self;
        let writer = Writer {
            symbols,
            data_writer,
            directive_writer,
            output,
            value_writer_config,
        };
        (writer, previous_output)
    }
}

#[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
impl<E: Encoding, Output: Write, S: WriterStyle> Writer<E, Output, S> {
    /// Constructs a writer for the requested encoding using the provided configuration.
    ///
    /// A text configuration with a run-time format, such as `v1_0::Text.with_format(format)`,
    /// makes a writer that reads the format's whitespace layout as it writes; for a writer
    /// specialized to one layout, pass a marker such as
    /// [`v1_0::CompactText`](crate::v1_0::CompactText), or the
    /// [`StyledWriteConfig`](crate::v1_0::StyledWriteConfig) that its `with_max_depth` returns.
    pub fn new(config: impl IntoWriterConfig<E, S>, output: Output) -> IonResult<Self> {
        Self::from_write_config(config.into_write_config(), output)
    }

    /// Constructs a writer of style `S` from `config`, whose text format, if it has one, must be one
    /// whose layout `S` writes.
    fn from_write_config(config: WriteConfig<E>, output: Output) -> IonResult<Self> {
        let WriterParts {
            symbols,
            data_writer,
            directive_writer,
            value_writer_config,
        } = build_parts::<E, S>(config)?;
        let mut writer = Writer {
            symbols,
            data_writer,
            directive_writer,
            output,
            value_writer_config,
        };
        writer.flush()?;
        Ok(writer)
    }

    pub fn output(&self) -> &Output {
        &self.output
    }

    pub fn output_mut(&mut self) -> &mut Output {
        &mut self.output
    }

    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        // This method forwards the call to the trait method implementation. It's here so
        // you can call `write()` on an ApplicationWriter without having to import SequenceWriter
        // separately.
        <Self as SequenceWriter>::write(self, value)
    }

    /// Writes bytes of previously encoded values to the output stream.
    pub fn flush(&mut self) -> IonResult<()> {
        if self.symbols.num_pending() > 0 {
            self.write_lst_append()?;
            self.symbols.reset_num_pending();
        }

        self.directive_writer.flush()?;
        self.output
            .write_all(self.directive_writer.output().as_slice())?;
        self.directive_writer.output_mut().clear();

        self.data_writer.flush()?;
        self.output
            .write_all(self.data_writer.output().as_slice())?;
        self.data_writer.output_mut().clear();

        self.output.flush()?;
        Ok(())
    }

    pub fn close(mut self) -> IonResult<Output> {
        self.flush()?;
        Ok(self.output)
    }

    #[cfg(feature = "experimental-reader-writer")]
    #[inline]
    pub fn symbol_table(&self) -> &WriterSymbolTable {
        &self.symbols
    }

    #[cfg(not(feature = "experimental-reader-writer"))]
    #[inline]
    pub(crate) fn symbol_table(&self) -> &WriterSymbolTable {
        &self.symbols
    }

    /// Helper method to encode an LST append containing pending symbols.
    fn write_lst_append(&mut self) -> IonResult<()> {
        let Self {
            symbols,
            directive_writer,
            ..
        } = self;

        let mut lst = directive_writer
            .value_writer()
            .with_annotations(system_symbol_ids::ION_SYMBOL_TABLE)?
            .struct_writer()?;

        lst.field_writer(system_symbol_ids::IMPORTS)
            .write_symbol(system_symbol_ids::ION_SYMBOL_TABLE)?;

        let mut new_symbol_list = lst.field_writer(system_symbol_ids::SYMBOLS).list_writer()?;

        new_symbol_list.write_all(symbols.pending_texts())?;
        new_symbol_list.close()?;

        lst.close()
    }
}

impl<E: Encoding, Output: Write, S: WriterStyle> ContextWriter for Writer<E, Output, S> {
    type NestedValueWriter<'a>
        = ApplicationValueWriter<
        'a,
        <S::RawWriter<E, Vec<u8>> as ContextWriter>::NestedValueWriter<'a>,
    >
    where
        Self: 'a;
}

impl<E: Encoding, Output: Write, S: WriterStyle> MakeValueWriter for Writer<E, Output, S> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        let raw_value_writer = self.data_writer.make_value_writer();
        let symbols = &mut self.symbols;

        ApplicationValueWriter {
            raw_value_writer,
            symbols,
            value_writer_config: self.value_writer_config,
        }
    }
}

impl<E: Encoding, Output: Write, S: WriterStyle> SequenceWriter for Writer<E, Output, S> {
    type Resources = Output;

    fn close(mut self) -> IonResult<Self::Resources> {
        self.flush()?;
        Ok(self.output)
    }
}

pub struct ApplicationValueWriter<'a, V: ValueWriter> {
    symbols: &'a mut WriterSymbolTable,
    raw_value_writer: V,
    value_writer_config: ValueWriterConfig,
}

impl<'a, V: ValueWriter> ApplicationValueWriter<'a, V> {
    pub(crate) fn new(
        symbols: &'a mut WriterSymbolTable,
        value_writer_config: ValueWriterConfig,
        raw_value_writer: V,
    ) -> Self {
        Self {
            symbols,
            value_writer_config,
            raw_value_writer,
        }
    }

    #[cfg(feature = "experimental-reader-writer")]
    #[inline]
    pub fn symbol_table(&self) -> &WriterSymbolTable {
        self.symbols
    }

    #[cfg(not(feature = "experimental-reader-writer"))]
    #[inline]
    pub(crate) fn symbol_table(&self) -> &WriterSymbolTable {
        self.symbols
    }
}

impl<V: ValueWriter> AnnotatableWriter for ApplicationValueWriter<'_, V> {
    type AnnotatedValueWriter<'a>
        = ApplicationValueWriter<'a, V::AnnotatedValueWriter<'a>>
    where
        Self: 'a;

    fn with_annotations<'a>(
        mut self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        let mut annotations = annotations.into_annotations_vec();
        match self.value_writer_config.annotations_encoding() {
            AnnotationsEncoding::SymbolIds => {
                // Intern all text so everything we write is a symbol ID
                self.intern_all_annotations(&mut annotations)?
            }
            AnnotationsEncoding::InlineText => {
                // Validate the symbol IDs, write the text as-is
                self.validate_all_symbol_ids(&mut annotations)?
            }
            AnnotationsEncoding::NewSymbolsAsInlineText => {
                // Map all known strings to symbol IDs, leave new text as is.
                self.map_known_symbols_to_symbol_ids(&mut annotations)?
            }
        };

        Ok(ApplicationValueWriter {
            symbols: self.symbols,
            raw_value_writer: self.raw_value_writer.with_annotations(annotations)?,
            value_writer_config: self.value_writer_config,
        })
    }
}

/// The description of the encoding error raised when opening a container whose children would be
/// deeper than the maximum depth.
const MAX_DEPTH_EXCEEDED: &str = "container nesting exceeds the configured maximum depth";

impl<V: ValueWriter> ApplicationValueWriter<'_, V> {
    /// Returns the configuration for the children of a container this writer is about to open. If
    /// they would exceed the maximum depth, returns an `Err` before `self.raw_value_writer` opens
    /// the container; field names and enclosing containers that the raw writer already encoded
    /// are not rolled back.
    #[inline]
    fn nested_container_config(&self) -> IonResult<ValueWriterConfig> {
        match self.value_writer_config.enter_container() {
            Some(config) => Ok(config),
            None => cold_path!(IonResult::encoding_error(MAX_DEPTH_EXCEEDED)),
        }
    }

    /// Converts each annotation in `annotations` to a symbol ID, adding symbols to the symbol table
    /// as necessary. If one of the annotations is a symbol ID that is not in the symbol table,
    /// returns an `Err`.
    fn intern_all_annotations<'a>(&mut self, annotations: &mut AnnotationsVec<'a>) -> IonResult<()>
    where
        Self: 'a,
    {
        for annotation in annotations {
            match annotation.as_raw_symbol_ref() {
                // The token is already a symbol ID.
                RawSymbolRef::SymbolId(sid) => {
                    if !self.symbol_table().sid_is_valid(sid) {
                        return cold_error!(
                            encoding_error,
                            "annotation symbol ID {sid} is out of range"
                        );
                    }
                }
                // The token is text...
                RawSymbolRef::Text(text) => {
                    *annotation = RawSymbolRef::SymbolId(self.symbols.get_or_add(text)?);
                }
            };
        }
        Ok(())
    }

    /// Confirms all SIDs are in the symbol table while leaving text annotations as-is.
    pub(crate) fn validate_all_symbol_ids<'a>(
        &mut self,
        annotations: &mut AnnotationsVec<'a>,
    ) -> IonResult<()>
    where
        Self: 'a,
    {
        for annotation in annotations {
            if let RawSymbolRef::SymbolId(sid) = annotation.as_raw_symbol_ref() {
                if !self.symbol_table().sid_is_valid(sid) {
                    return cold_error!(
                        encoding_error,
                        "annotation symbol ID {sid} is not in the symbol table"
                    );
                }
            }
        }
        Ok(())
    }

    /// Converts annotations with known text to their corresponding symbol ID. Annotations with
    /// text not yet in the symbol table are left as-is. If a symbol ID is not in the symbol table,
    /// returns an `Err`.
    fn map_known_symbols_to_symbol_ids<'a>(
        &mut self,
        annotations: &mut AnnotationsVec<'a>,
    ) -> IonResult<()>
    where
        Self: 'a,
    {
        for annotation in annotations {
            match annotation.as_raw_symbol_ref() {
                // The token is already a symbol ID.
                RawSymbolRef::SymbolId(sid) => {
                    if !self.symbol_table().sid_is_valid(sid) {
                        return cold_error!(
                            encoding_error,
                            "annotation symbol ID {sid} is out of range"
                        );
                    }
                }
                // The token is text...
                RawSymbolRef::Text(text) => {
                    match self.symbols.sid_for(text) {
                        Some(sid) => {
                            //...that was already in the symbol table.
                            *annotation = RawSymbolRef::SymbolId(sid);
                        }
                        None => {
                            // ...that is not in the symbol table. Leave it as-is.
                        }
                    };
                }
            };
        }
        Ok(())
    }
}

impl<'value, V: ValueWriter> ValueWriter for ApplicationValueWriter<'value, V> {
    type Encoding = V::Encoding;
    type ListWriter = ApplicationListWriter<'value, V>;
    type SExpWriter = ApplicationSExpWriter<'value, V>;
    type StructWriter = ApplicationStructWriter<'value, V>;

    delegate! {
        to self.raw_value_writer {
            fn write_null(self, ion_type: IonType) -> IonResult<()> ;
            fn write_bool(self, value: bool) -> IonResult<()>;
            fn write_i64(self, value: i64) -> IonResult<()>;
            fn write_int(self, value: &Int) -> IonResult<()>;
            fn write_f32(self, value: f32) -> IonResult<()>;
            fn write_f64(self, value: f64) -> IonResult<()>;
            fn write_decimal(self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(self, value: &Timestamp) -> IonResult<()>;
            fn write_string(self, value: impl AsRef<str>) -> IonResult<()>;
            fn write_clob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_blob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
        }
    }

    fn write_symbol(self, value: impl AsRawSymbolRef) -> IonResult<()> {
        use RawSymbolRef::*;
        use SymbolValueEncoding::*;

        let Self {
            symbols,
            raw_value_writer,
            value_writer_config,
            ..
        } = self;

        // Depending on the symbol value encoding config option, map the provided symbol reference
        // from text to SID or vice versa, performing any validation needed.
        let symbol_ref = match value.as_raw_symbol_ref() {
            SymbolId(symbol_id) => {
                // We can write the symbol ID as-is. Make sure it's in the symbol table.
                if !symbols.sid_is_valid(symbol_id) {
                    return cold_error!(
                        encoding_error,
                        "symbol value ID ${symbol_id} is not in the symbol table"
                    );
                }
                SymbolId(symbol_id)
            }
            Text(text) => {
                match value_writer_config.symbol_value_encoding() {
                    SymbolIds => SymbolId(symbols.get_or_add(text)?),
                    NewSymbolsAsInlineText => {
                        // If the text is in the symbol table, use the symbol ID. Otherwise, use the text itself.
                        match symbols.sid_for(text) {
                            Some(symbol_id) => SymbolId(symbol_id),
                            None => Text(text),
                        }
                    }
                    // We have text and we want to write text. Nothing to do.
                    InlineText => Text(text),
                }
            }
        };

        raw_value_writer.write_symbol(symbol_ref)
    }

    fn list_writer(self) -> IonResult<Self::ListWriter> {
        let config = self.nested_container_config()?;
        Ok(ApplicationListWriter::new(
            self.symbols,
            config,
            self.raw_value_writer.list_writer()?,
        ))
    }

    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        let config = self.nested_container_config()?;
        Ok(ApplicationSExpWriter::new(
            self.symbols,
            config,
            self.raw_value_writer.sexp_writer()?,
        ))
    }

    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        let config = self.nested_container_config()?;
        Ok(ApplicationStructWriter::new(
            self.symbols,
            config,
            self.raw_value_writer.struct_writer()?,
        ))
    }
}

pub struct ApplicationStructWriter<'value, V: ValueWriter> {
    symbols: &'value mut WriterSymbolTable,
    raw_struct_writer: V::StructWriter,
    value_writer_config: ValueWriterConfig,
}

impl<'value, V: ValueWriter> ApplicationStructWriter<'value, V> {
    pub(crate) fn new(
        symbols: &'value mut WriterSymbolTable,
        config: ValueWriterConfig,
        raw_struct_writer: V::StructWriter,
    ) -> Self {
        Self {
            symbols,
            raw_struct_writer,
            value_writer_config: config,
        }
    }

    // Generally useful, but currently only called in unit tests.
    #[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
    pub fn with_field_name_encoding(mut self, field_name_encoding: FieldNameEncoding) -> Self {
        self.value_writer_config = self
            .value_writer_config
            .with_field_name_encoding(field_name_encoding);
        self
    }
}

impl<V: ValueWriter> ContextWriter for ApplicationStructWriter<'_, V> {
    type NestedValueWriter<'a>
        = ApplicationValueWriter<'a, <V::StructWriter as ContextWriter>::NestedValueWriter<'a>>
    where
        Self: 'a;
}

impl<V: ValueWriter> MakeValueWriter for ApplicationStructWriter<'_, V> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        ApplicationValueWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_struct_writer.make_value_writer(),
        )
    }
}

impl<V: ValueWriter> FieldEncoder for ApplicationStructWriter<'_, V> {
    #[inline]
    fn encode_field_name(&mut self, name: impl AsRawSymbolRef) -> IonResult<()> {
        let text = match name.as_raw_symbol_ref() {
            // This is an application-level struct writer. It is expected that method calls will
            // almost always be provided text; if the user passes in a symbol ID, it means they have
            // special knowledge of the encoding environment and are bypassing the 'managed' layer.
            // We range check the SID and write it as-is. In the unusual circumstance that the user
            // has a SID at the application level and wants to write text, they can and should
            // resolve the SID in the symbol table before calling this method.
            RawSymbolRef::SymbolId(symbol_id) => {
                if !self.symbols.sid_is_valid(symbol_id) {
                    return cold_error!(
                        encoding_error,
                        "symbol ID ${symbol_id} is not in the symbol table"
                    );
                }
                return self.raw_struct_writer.encode_field_name(symbol_id);
            }
            // Otherwise, get its associated text.
            RawSymbolRef::Text(text) => text,
        };

        // From here on, we're dealing with text.

        // If the struct writer is configured to write field names as text, do that.
        if self.value_writer_config.field_name_encoding() == FieldNameEncoding::InlineText {
            return self.raw_struct_writer.encode_field_name(text);
        }

        let token: RawSymbolRef<'_> =
            if self.value_writer_config.field_name_encoding() == FieldNameEncoding::SymbolIds {
                self.symbols.get_or_add(text)?.into()
            } else {
                match self.symbols.sid_for(text) {
                    Some(sid) => sid.into(),
                    None => text.into(),
                }
            };

        // Finally, encode the field name using the selected token representation
        self.raw_struct_writer.encode_field_name(token)
    }
}

impl<V: ValueWriter> StructWriter for ApplicationStructWriter<'_, V> {
    fn field_writer<'a>(&'a mut self, name: impl Into<RawSymbolRef<'a>>) -> FieldWriter<'a, Self> {
        FieldWriter::new(name.into(), self.value_writer_config, self)
    }

    fn close(self) -> IonResult<()> {
        self.raw_struct_writer.close()
    }

    fn config(&self) -> ValueWriterConfig {
        self.value_writer_config
    }
}

pub struct ApplicationListWriter<'value, V: ValueWriter> {
    symbols: &'value mut WriterSymbolTable,
    raw_list_writer: V::ListWriter,
    value_writer_config: ValueWriterConfig,
}

impl<'value, V: ValueWriter> ApplicationListWriter<'value, V> {
    pub(crate) fn new(
        symbols: &'value mut WriterSymbolTable,
        value_writer_config: ValueWriterConfig,
        raw_list_writer: V::ListWriter,
    ) -> Self {
        Self {
            symbols,
            value_writer_config,
            raw_list_writer,
        }
    }
}

impl<V: ValueWriter> ContextWriter for ApplicationListWriter<'_, V> {
    type NestedValueWriter<'a>
        = ApplicationValueWriter<'a, <V::ListWriter as ContextWriter>::NestedValueWriter<'a>>
    where
        Self: 'a;
}

impl<V: ValueWriter> MakeValueWriter for ApplicationListWriter<'_, V> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        ApplicationValueWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_list_writer.make_value_writer(),
        )
    }
}

impl<V: ValueWriter> SequenceWriter for ApplicationListWriter<'_, V> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.raw_list_writer.close()
    }
}

pub struct ApplicationSExpWriter<'value, V: ValueWriter> {
    symbols: &'value mut WriterSymbolTable,
    raw_sexp_writer: V::SExpWriter,
    value_writer_config: ValueWriterConfig,
}

impl<'value, V: ValueWriter> ApplicationSExpWriter<'value, V> {
    pub(crate) fn new(
        symbols: &'value mut WriterSymbolTable,
        value_writer_config: ValueWriterConfig,
        raw_sexp_writer: V::SExpWriter,
    ) -> Self {
        Self {
            symbols,
            value_writer_config,
            raw_sexp_writer,
        }
    }
}

impl<V: ValueWriter> ContextWriter for ApplicationSExpWriter<'_, V> {
    type NestedValueWriter<'a>
        = ApplicationValueWriter<'a, <V::SExpWriter as ContextWriter>::NestedValueWriter<'a>>
    where
        Self: 'a;
}

impl<V: ValueWriter> MakeValueWriter for ApplicationSExpWriter<'_, V> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        ApplicationValueWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_sexp_writer.make_value_writer(),
        )
    }
}

impl<V: ValueWriter> SequenceWriter for ApplicationSExpWriter<'_, V> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.raw_sexp_writer.close()
    }
}

impl<S: SequenceWriter> ElementWriter for S {
    fn write_value(&mut self, value: &Value) -> IonResult<()> {
        self.write(value)?;
        Ok(())
    }

    fn write_element(&mut self, element: &Element) -> IonResult<()> {
        self.write(element)?;
        Ok(())
    }
}

#[cfg(test)]
mod reuse_tests {
    use super::tests::assert_depth_error;
    use super::{IntoWriterConfig, Writer, WriterStyle};
    use crate::binary::constants::v1_0::IVM;
    // `DEFAULT_BUMP_SIZE` is the binary writer's arena size, imported here (and only here) so the
    // arena tests can derive their sizes from the real arena rather than hardcoding them.
    use crate::lazy::encoder::binary::v1_0::writer::DEFAULT_BUMP_SIZE;
    use crate::lazy::encoder::{LazyRawWriter, Reusable, IDLE_RETAIN_CAP, IDLE_SYMBOL_RETAIN_CAP};
    use crate::lazy::encoding::{BinaryEncoding_1_0, TextEncoding_1_0};
    use crate::{v1_0, Element, Encoding, IonData, IonResult, TextFormat, WriteConfig};
    use bumpalo::Bump as BumpAllocator;
    use rstest::rstest;
    use rstest_reuse::{apply, template};

    /// Encodes a single document with a fresh managed writer (the non-reused baseline).
    fn encode_fresh<E: Encoding, S: WriterStyle>(
        config: impl IntoWriterConfig<E, S>,
        doc: &Element,
    ) -> IonResult<Vec<u8>> {
        let mut writer = Writer::new(config, Vec::new())?;
        writer.write(doc)?;
        writer.close()
    }

    /// The bytes a freshly built raw `E` writer leaves buffered before anything is encoded: the IVM
    /// for binary Ion 1.0, nothing for text. Derived from `LazyRawWriter::build` rather than
    /// hardcoded, so the expectation does not restate the `recycle` logic under test.
    fn construction_prologue<E: Encoding, S: WriterStyle>(
        config: impl IntoWriterConfig<E, S>,
    ) -> IonResult<Vec<u8>> {
        let raw_writer = S::RawWriter::<E, Vec<u8>>::build(config.into_write_config(), vec![])?;
        Ok(raw_writer.output().clone())
    }

    /// The capacity of a `Vec` that was requested with none and then had the binary Ion 1.0 IVM
    /// written to it. `Vec` does not specify how much it grows by, so this is measured rather than
    /// hardcoded.
    fn capacity_holding_ivm() -> usize {
        let mut buffer = Vec::<u8>::new();
        buffer.extend_from_slice(&IVM);
        buffer.capacity()
    }

    fn idle_binary_writer() -> IonResult<Writer<BinaryEncoding_1_0, ()>> {
        Writer::<BinaryEncoding_1_0, ()>::idle(v1_0::Binary)
    }

    /// The size of a freshly constructed scratch arena, computed rather than hardcoded so bumpalo's
    /// internal rounding cannot make the assertions brittle.
    fn fresh_arena_bytes() -> usize {
        BumpAllocator::with_capacity(DEFAULT_BUMP_SIZE).allocated_bytes()
    }

    /// Binary, text with a run-time style, and text with each zero-sized style: a configuration
    /// with the default maximum depth, and a function that returns a configuration of the same
    /// encoding and style with the given maximum depth.
    #[template]
    #[rstest]
    #[case::binary_1_0(
        v1_0::Binary,
        |max_depth| WriteConfig::from(v1_0::Binary).with_max_depth(max_depth)
    )]
    #[case::text_1_0(
        v1_0::Text,
        |max_depth| WriteConfig::from(v1_0::Text).with_max_depth(max_depth)
    )]
    #[case::compact_text_1_0(
        v1_0::CompactText,
        |max_depth| v1_0::CompactText.with_max_depth(max_depth)
    )]
    #[case::lines_text_1_0(
        v1_0::LinesText,
        |max_depth| v1_0::LinesText.with_max_depth(max_depth)
    )]
    #[case::pretty_text_1_0(
        v1_0::PrettyText,
        |max_depth| v1_0::PrettyText.with_max_depth(max_depth)
    )]
    fn reusable_configs<E: Encoding, S: WriterStyle, L: IntoWriterConfig<E, S>>(
        #[case] config: impl IntoWriterConfig<E, S> + Clone,
        #[case] with_max_depth: impl Fn(u16) -> L,
    ) {
    }

    /// A managed Ion 1.0 writer that is reused across DIFFERENT documents (each of which forces the
    /// binary encoding to emit its own local symbol table) must produce bytes byte-for-byte identical
    /// to a fresh writer per document, and those bytes must read back as the document that was
    /// written. This exercises both the prologue re-seed and the symbol-table reset that `detach`
    /// performs: a stale symbol table, a missing IVM, or an IVM emitted on the wrong sub-writer would
    /// corrupt every document after the first.
    #[apply(reusable_configs)]
    fn reuse_is_byte_identical_and_round_trips<
        E: Encoding,
        S: WriterStyle,
        L: IntoWriterConfig<E, S>,
    >(
        #[case] config: impl IntoWriterConfig<E, S> + Clone,
        #[case] _with_max_depth: impl Fn(u16) -> L,
    ) -> IonResult<()>
    where
        S::RawWriter<E, Vec<u8>>: Reusable,
    {
        // Two structs with disjoint text field names and symbol values, so each forces the binary
        // writer to emit its own local symbol table.
        let doc1 = Element::read_one(r#"{ alpha: sym_a, beta: sym_b }"#)?;
        let doc2 = Element::read_one(r#"{ gamma: sym_c, delta: sym_d, epsilon: sym_e }"#)?;
        // Round three repeats `doc1`: a reset that is only correct the first time would show up here.
        let rounds = [&doc1, &doc2, &doc1];

        let expected_prologue = construction_prologue(config.clone())?;

        let mut idle = Writer::<E, (), S>::idle(config.clone())?;
        for (round, doc) in rounds.into_iter().enumerate() {
            let mut writer = idle.attach(Vec::new());
            writer.write(doc)?;
            // `detach` does not write; `flush` is what emits the document to the sink.
            writer.flush()?;
            let (next_idle, bytes) = writer.detach();
            idle = next_idle;

            // The parked writer must be in the same state `new`/`idle` leave behind: the next
            // document's prologue is buffered in the directive writer and nowhere else.
            assert_eq!(
                idle.directive_writer.output(),
                &expected_prologue,
                "round {round}: the parked directive writer does not hold exactly the construction prologue"
            );
            assert!(
                idle.data_writer.output().is_empty(),
                "round {round}: the parked data writer holds bytes it should not"
            );

            let fresh = encode_fresh(config.clone(), doc)?;
            assert_eq!(
                bytes, fresh,
                "round {round}: reused bytes are not byte-identical to fresh:\n  reused: {bytes:02X?}\n  fresh:  {fresh:02X?}"
            );
            let read_back = Element::read_one(bytes)?;
            assert!(
                IonData::eq(&read_back, doc),
                "round {round}: reused writer's output did not read back as the document written:\n  read back: {read_back:?}\n  written:   {doc:?}"
            );
        }
        Ok(())
    }

    /// `detach` must release a scratch arena that grew past `IDLE_RETAIN_CAP` while encoding an
    /// unusually large value, rather than retaining it for the life of the pooled writer.
    #[test]
    fn detach_shrinks_oversized_arena() -> IonResult<()> {
        // A blob twice the retain cap; large top-level values are encoded through the bump arena.
        let big = vec![0u8; IDLE_RETAIN_CAP * 2];

        let mut writer = idle_binary_writer()?.attach(Vec::new());
        writer.write(big.as_slice())?;
        // Precondition: the value really did grow the arena past the cap. Without this the
        // post-conditions below could pass vacuously if large values stopped routing through it.
        assert!(
            writer.data_writer.allocated_bytes() > IDLE_RETAIN_CAP,
            "arena did not exceed the retain cap before detach: {} bytes",
            writer.data_writer.allocated_bytes()
        );
        writer.flush()?;

        let (idle, bytes) = writer.detach();
        assert_eq!(
            idle.data_writer.allocated_bytes(),
            fresh_arena_bytes(),
            "detach retained the oversized arena instead of replacing it with a fresh one"
        );
        // The large value still made it to the sink intact.
        assert_eq!(
            Element::read_one(bytes)?.expect_blob()?,
            big.as_slice(),
            "the large value did not survive the arena shrink"
        );

        // The writer whose arena was swapped out still encodes a correct document.
        let doc = Element::read_one(r#"{ a: 1, b: [2, 3], c: sym_c }"#)?;
        let mut writer = idle.attach(Vec::new());
        writer.write(&doc)?;
        writer.flush()?;
        let (_idle, bytes) = writer.detach();
        assert_eq!(
            bytes,
            encode_fresh(v1_0::Binary, &doc)?,
            "reuse after an arena shrink is not byte-identical to fresh"
        );
        Ok(())
    }

    /// `detach` must also bound the sub-writers' backing `Vec`s, which grow to hold the largest
    /// document encoded so far.
    #[test]
    fn detach_caps_retained_sub_writer_buffers() -> IonResult<()> {
        let big = vec![0u8; IDLE_RETAIN_CAP * 2];

        let mut writer = idle_binary_writer()?.attach(Vec::new());
        writer.write(big.as_slice())?;
        // `flush` moves the encoded value out of the arena and through the data writer's `Vec`, which
        // is what grows its capacity. Precondition: it really did grow past the cap.
        writer.flush()?;
        assert!(
            writer.data_writer.output().capacity() > IDLE_RETAIN_CAP,
            "data buffer did not exceed the retain cap before detach: {} bytes",
            writer.data_writer.output().capacity()
        );

        let (idle, _bytes) = writer.detach();
        assert!(
            idle.data_writer.output().capacity() <= IDLE_RETAIN_CAP,
            "detach retained an oversized data buffer: {} bytes",
            idle.data_writer.output().capacity()
        );
        // Only the data buffer is asserted on: this document puts nothing but a symbol table in the
        // directive buffer, so it never approaches the cap and an assertion about it would hold no
        // matter what `detach` did. `detach_retains_warm_capacity_for_a_mid_sized_document` covers the
        // directive buffer's under-cap behavior, which is the one that has content here.

        // Reuse after the buffer swap is still byte-identical, which also proves the re-seeded IVM
        // landed in the replacement buffer.
        let doc = Element::read_one(r#"{ a: 1, b: [2, 3], c: sym_c }"#)?;
        let mut writer = idle.attach(Vec::new());
        writer.write(&doc)?;
        writer.flush()?;
        let (_idle, bytes) = writer.detach();
        assert_eq!(
            bytes,
            encode_fresh(v1_0::Binary, &doc)?,
            "reuse after a buffer cap is not byte-identical to fresh"
        );
        Ok(())
    }

    /// A data buffer that `detach` replaces comes back at the capacity `build_parts` requests for
    /// it: none for binary, which copies its arena into the buffer once per flush, and 512 bytes
    /// for text, which appends to it piece by piece. A fresh text data buffer starts at that
    /// capacity; a fresh binary one is larger because it keeps the allocation `Vec` made for the
    /// IVM `build_parts` erases. The directive buffer is requested with no capacity, so a fresh one
    /// holds only what the encoding's prologue allocated. The cases spell out the requested
    /// capacities rather than naming the encodings' constants so that the test pins the policy.
    #[rstest]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    #[case::binary_1_0(v1_0::Binary, capacity_holding_ivm(), capacity_holding_ivm(), 0)]
    #[case::text_1_0(v1_0::Text, 512, 0, 512)]
    fn detach_replaces_an_oversized_data_buffer_at_the_requested_capacity<E>(
        #[case] encoding: E,
        #[case] fresh_data_capacity: usize,
        #[case] fresh_directive_capacity: usize,
        #[case] replaced_capacity: usize,
    ) -> IonResult<()>
    where
        E: Encoding + Into<WriteConfig<E>>,
        E::Writer<Vec<u8>>: Reusable,
    {
        let fresh = Writer::<E, ()>::idle(encoding)?;
        assert_eq!(fresh.data_writer.output().capacity(), fresh_data_capacity);
        assert_eq!(
            fresh.directive_writer.output().capacity(),
            fresh_directive_capacity
        );

        let big = vec![0u8; IDLE_RETAIN_CAP * 2];
        let mut writer = fresh.attach(Vec::new());
        writer.write(big.as_slice())?;
        writer.flush()?;
        // Precondition: the document grew the data buffer past the cap.
        assert!(
            writer.data_writer.output().capacity() > IDLE_RETAIN_CAP,
            "data buffer did not exceed the retain cap before detach: {} bytes",
            writer.data_writer.output().capacity()
        );

        let (idle, _bytes) = writer.detach();
        assert_eq!(idle.data_writer.output().capacity(), replaced_capacity);
        Ok(())
    }

    /// `detach` must also bound the symbol table, which grows to hold every symbol the writer has
    /// interned. Its contents are discarded on reuse either way, so retaining that capacity would be
    /// pure overhead for the life of a pooled writer.
    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn detach_caps_retained_symbol_table() -> IonResult<()> {
        // A struct with far more distinct field names than the cap allows the table to retain.
        let fields = (0..IDLE_SYMBOL_RETAIN_CAP * 2)
            .map(|i| format!("field_{i}: {i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let doc = Element::read_one(format!("{{ {fields} }}"))?;

        let mut writer = idle_binary_writer()?.attach(Vec::new());
        writer.write(&doc)?;
        writer.flush()?;
        // Precondition: the document really did grow the table past the cap.
        assert!(
            writer.symbol_table().retained_capacity() > IDLE_SYMBOL_RETAIN_CAP,
            "symbol table did not exceed the retain cap before detach: {} entries",
            writer.symbol_table().retained_capacity()
        );

        let (idle, _bytes) = writer.detach();
        assert!(
            idle.symbols.retained_capacity() <= IDLE_SYMBOL_RETAIN_CAP,
            "detach retained an oversized symbol table: {} entries",
            idle.symbols.retained_capacity()
        );

        // The writer whose table was swapped out still encodes a correct document.
        let mut writer = idle.attach(Vec::new());
        writer.write(&doc)?;
        writer.flush()?;
        let (_idle, bytes) = writer.detach();
        assert_eq!(
            bytes,
            encode_fresh(v1_0::Binary, &doc)?,
            "reuse after a symbol table cap is not byte-identical to fresh"
        );
        Ok(())
    }

    /// A single very large symbol grows the byte arena without growing the entry count, so the
    /// arena needs its own retention cap independent of `IDLE_SYMBOL_RETAIN_CAP`.
    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn detach_caps_retained_symbol_text_arena() -> IonResult<()> {
        let huge_symbol = "x".repeat(IDLE_RETAIN_CAP * 2);
        let mut writer = idle_binary_writer()?.attach(Vec::new());
        writer.symbols.get_or_add(&huge_symbol)?;
        assert!(
            writer.symbols.retained_text_capacity() > IDLE_RETAIN_CAP,
            "symbol text arena did not exceed the retain cap: {} bytes",
            writer.symbols.retained_text_capacity()
        );

        let (idle, _bytes) = writer.detach();
        assert!(
            idle.symbols.retained_text_capacity() <= IDLE_RETAIN_CAP,
            "detach retained an oversized symbol text arena: {} bytes",
            idle.symbols.retained_text_capacity()
        );
        assert_eq!(idle.symbols.sid_for(&huge_symbol), None);
        assert_eq!(idle.symbols.sid_for("$ion"), Some(1));

        let doc = Element::read_one(r#"{ a: 1, b: [2, 3], c: sym_c }"#)?;
        let mut writer = idle.attach(Vec::new());
        writer.write(&doc)?;
        writer.flush()?;
        let (_idle, bytes) = writer.detach();
        assert_eq!(
            bytes,
            encode_fresh(v1_0::Binary, &doc)?,
            "reuse after a symbol text arena cap is not byte-identical to fresh"
        );
        Ok(())
    }

    /// The flip side of the four cap tests, and the premise the whole API rests on: for a document
    /// whose arena, buffers, and symbol table all stay UNDER their caps, `detach` must leave that warm
    /// memory exactly as it found it. A regression that reallocated any of it on every `detach` would
    /// still encode correct documents -- and would make pooling pointless -- so only this test would
    /// catch it.
    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn detach_retains_warm_capacity_for_a_mid_sized_document() -> IonResult<()> {
        // Big enough to grow the arena past its initial chunk and the data buffer past a fresh
        // writer's, but far short of the cap at which either is released.
        let mid_sized_blob = vec![0u8; DEFAULT_BUMP_SIZE * 2];
        // More symbols than a fresh table is sized for, fewer than the cap at which it is released.
        let fields = (0..IDLE_SYMBOL_RETAIN_CAP / 4)
            .map(|i| format!("field_{i}: {i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let doc = Element::read_one(format!("{{ {fields} }}"))?;
        let fresh_writer = idle_binary_writer()?;
        let fresh_symbol_capacity = fresh_writer.symbols.retained_capacity();
        let fresh_symbol_text_capacity = fresh_writer.symbols.retained_text_capacity();
        let fresh_data_capacity = fresh_writer.data_writer.output().capacity();
        let fresh_directive_capacity = fresh_writer.directive_writer.output().capacity();

        let mut writer = idle_binary_writer()?.attach(Vec::new());
        writer.write(&doc)?;
        writer.write(mid_sized_blob.as_slice())?;
        // `flush` drains the buffers (leaving their capacity) and rewinds the arena, which is the
        // state `detach` finds them in.
        writer.flush()?;

        let arena_bytes = writer.data_writer.allocated_bytes();
        let data_capacity = writer.data_writer.output().capacity();
        let directive_capacity = writer.directive_writer.output().capacity();
        let symbol_capacity = writer.symbol_table().retained_capacity();
        let symbol_text_capacity = writer.symbol_table().retained_text_capacity();
        // Preconditions: this document really did leave each retained allocation warmer than a
        // fresh writer's, and left none past the cap that would (correctly) release it. Without
        // these, the assertions below could pass by measuring memory that was never warm to begin
        // with.
        assert!(
            arena_bytes > fresh_arena_bytes() && arena_bytes <= IDLE_RETAIN_CAP,
            "the document did not leave the arena warm and under the cap: {arena_bytes} bytes"
        );
        assert!(
            data_capacity > fresh_data_capacity && data_capacity <= IDLE_RETAIN_CAP,
            "the document did not leave the data buffer warm and under the cap: {data_capacity} bytes"
        );
        assert!(
            directive_capacity > fresh_directive_capacity && directive_capacity <= IDLE_RETAIN_CAP,
            "the document did not leave the directive buffer warm and under the cap: {directive_capacity} bytes"
        );
        assert!(
            symbol_capacity > fresh_symbol_capacity && symbol_capacity <= IDLE_SYMBOL_RETAIN_CAP,
            "the document did not leave the symbol table warm and under the cap: {symbol_capacity} entries"
        );
        assert!(
            symbol_text_capacity > fresh_symbol_text_capacity
                && symbol_text_capacity <= IDLE_RETAIN_CAP,
            "the document did not leave the symbol text arena warm and under the cap: {symbol_text_capacity} bytes"
        );

        let (idle, _bytes) = writer.detach();
        assert_eq!(
            idle.data_writer.allocated_bytes(),
            arena_bytes,
            "detach replaced an under-cap scratch arena instead of keeping it warm"
        );
        assert_eq!(
            idle.data_writer.output().capacity(),
            data_capacity,
            "detach replaced an under-cap data buffer instead of keeping it warm"
        );
        assert_eq!(
            idle.directive_writer.output().capacity(),
            directive_capacity,
            "detach replaced an under-cap directive buffer instead of keeping it warm"
        );
        assert_eq!(
            idle.symbols.retained_capacity(),
            symbol_capacity,
            "detach replaced an under-cap symbol table instead of keeping it warm"
        );
        assert_eq!(
            idle.symbols.retained_text_capacity(),
            symbol_text_capacity,
            "detach replaced an under-cap symbol text arena instead of keeping it warm"
        );

        // ...and the writer whose warm state was kept still encodes a correct document.
        let mut writer = idle.attach(Vec::new());
        writer.write(&doc)?;
        writer.flush()?;
        let (_idle, bytes) = writer.detach();
        assert_eq!(
            bytes,
            encode_fresh(v1_0::Binary, &doc)?,
            "reuse of a warm writer is not byte-identical to fresh"
        );
        Ok(())
    }

    /// `detach` writes nothing: a document that was never flushed is dropped, and the writer is still
    /// left in the fresh-document state that makes the NEXT document correct. Both encodings are
    /// covered because they buffer an un-flushed document in different places -- binary in its scratch
    /// arena, text directly in its output buffer -- and each `recycle` has to discard its own.
    #[apply(reusable_configs)]
    fn detach_discards_an_unflushed_document<
        E: Encoding,
        S: WriterStyle,
        L: IntoWriterConfig<E, S>,
    >(
        #[case] config: impl IntoWriterConfig<E, S> + Clone,
        #[case] _with_max_depth: impl Fn(u16) -> L,
    ) -> IonResult<()>
    where
        S::RawWriter<E, Vec<u8>>: Reusable,
    {
        let dropped = Element::read_one(r#"{ never_flushed: sym_x }"#)?;

        let mut writer = Writer::<E, (), S>::idle(config.clone())?.attach(Vec::new());
        writer.write(&dropped)?;
        let (idle, bytes) = writer.detach();
        assert!(
            bytes.is_empty(),
            "detach wrote to the sink instead of discarding the un-flushed document: {bytes:02X?}"
        );

        // Neither the discarded document's bytes nor its symbols may leak into the next one.
        let doc = Element::read_one(r#"{ a: 1, b: [2, 3], c: sym_c }"#)?;
        let mut writer = idle.attach(Vec::new());
        writer.write(&doc)?;
        writer.flush()?;
        let (_idle, bytes) = writer.detach();
        assert_eq!(
            bytes,
            encode_fresh(config, &doc)?,
            "reuse after a discarded document is not byte-identical to fresh"
        );
        Ok(())
    }

    /// A writer built by `idle` with a maximum depth enforces it in every document it encodes,
    /// including after a `detach`/`attach` cycle.
    #[apply(reusable_configs)]
    fn idle_applies_the_max_depth<E: Encoding, S: WriterStyle, L: IntoWriterConfig<E, S>>(
        #[case] _config: impl IntoWriterConfig<E, S> + Clone,
        #[case] with_max_depth: impl Fn(u16) -> L,
    ) -> IonResult<()>
    where
        S::RawWriter<E, Vec<u8>>: Reusable,
    {
        let at_max = Element::read_one("[0]")?;
        let past_max = Element::read_one("[[0]]")?;

        let mut writer = Writer::<E, (), S>::idle(with_max_depth(1))?.attach(Vec::new());
        assert_depth_error(writer.write(&past_max));
        let (idle, _discarded) = writer.detach();

        let mut writer = idle.attach(Vec::new());
        writer.write(&at_max)?;
        writer.flush()?;
        let (idle, bytes) = writer.detach();
        assert_eq!(Element::read_one(bytes)?, at_max);

        let mut writer = idle.attach(Vec::new());
        assert_depth_error(writer.write(&past_max));
        Ok(())
    }

    /// `set_config` replaces the maximum depth along with the rest of the configuration, so it can
    /// lift the limit a writer was built with.
    #[apply(reusable_configs)]
    fn set_config_lifts_the_max_depth<E: Encoding, S: WriterStyle, L: IntoWriterConfig<E, S>>(
        #[case] config: impl IntoWriterConfig<E, S> + Clone,
        #[case] with_max_depth: impl Fn(u16) -> L,
    ) -> IonResult<()>
    where
        S::RawWriter<E, Vec<u8>>: Reusable,
    {
        let doc = Element::read_one("[[0]]")?;
        let mut idle = Writer::<E, (), S>::idle(with_max_depth(1))?;
        idle.set_config(config.clone());
        let mut writer = idle.attach(Vec::new());
        writer.write(&doc)?;
        assert_eq!(writer.close()?, encode_fresh(config, &doc)?);
        Ok(())
    }

    /// `set_config` can also impose a maximum depth on a writer built without one.
    #[apply(reusable_configs)]
    fn set_config_imposes_a_max_depth<E: Encoding, S: WriterStyle, L: IntoWriterConfig<E, S>>(
        #[case] config: impl IntoWriterConfig<E, S> + Clone,
        #[case] with_max_depth: impl Fn(u16) -> L,
    ) -> IonResult<()>
    where
        S::RawWriter<E, Vec<u8>>: Reusable,
    {
        let doc = Element::read_one("[[0]]")?;
        let mut idle = Writer::<E, (), S>::idle(config)?;
        idle.set_config(with_max_depth(1));
        let mut writer = idle.attach(Vec::new());
        assert_depth_error(writer.write(&doc));
        Ok(())
    }

    /// A parked writer built for one `WriteConfig` must be able to adopt another's, in place: a pool
    /// hands whichever writer it has to whichever caller asks next.
    #[test]
    fn set_config_re_applies_the_text_format() -> IonResult<()> {
        let doc = Element::read_one(r#"{ a: 1, b: [2, 3], c: sym_c }"#)?;
        let compact = WriteConfig::<TextEncoding_1_0>::new(TextFormat::Compact);
        let pretty = WriteConfig::<TextEncoding_1_0>::new(TextFormat::Pretty);

        let mut idle = Writer::<TextEncoding_1_0, ()>::idle(compact.clone())?;
        let mut writer = idle.attach(Vec::new());
        writer.write(&doc)?;
        writer.flush()?;
        let (parked, compact_bytes) = writer.detach();
        assert_eq!(
            compact_bytes,
            encode_fresh(compact, &doc)?,
            "the compact document is not byte-identical to fresh"
        );

        // Re-configure the parked writer and encode the same document again.
        idle = parked;
        idle.set_config(pretty.clone());
        let mut writer = idle.attach(Vec::new());
        writer.write(&doc)?;
        writer.flush()?;
        let (_idle, pretty_bytes) = writer.detach();
        assert_eq!(
            pretty_bytes,
            encode_fresh(pretty, &doc)?,
            "the re-configured writer did not encode pretty text"
        );
        assert_ne!(
            compact_bytes, pretty_bytes,
            "the two text formats produced identical bytes, so this test proves nothing"
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        BinaryWriter_1_0, IntoWriterConfig, TextWriter_1_0, WriterStyle, MAX_DEPTH_EXCEEDED,
    };
    use crate::lazy::encoding::{BinaryEncoding_1_0, TextEncoding_1_0};
    use crate::text::whitespace_config::{CompactText, LinesText, PrettyText, RuntimeStyle};
    use crate::write_config::StyledWriteConfig;
    use crate::{v1_0, Element, Encoding, IonError, IonResult, TextFormat, WriteConfig, Writer};
    use rstest::rstest;
    use std::any::type_name;
    use std::io::BufWriter;

    /// A binary writer encodes text that a system symbol has with that symbol's SID, so the stream
    /// is the IVM, a local symbol table only if there is user text, and the value.
    #[rstest]
    #[case::symbol_value("name", &[0x71, 0x04])]
    #[case::ion_symbol_table_symbol_value("$ion_symbol_table", &[0x71, 0x03])]
    #[case::field_name("{name: 1}", &[0xD3, 0x84, 0x21, 0x01])]
    #[case::annotation("name::1", &[0xE4, 0x81, 0x84, 0x21, 0x01])]
    // `$ion_symbol_table::{imports: $ion_symbol_table, symbols: ["foo"]}`, then `{$10: $4}`. `foo`
    // comes first so that `name` is resolved after the user text has allocated the symbol index.
    #[case::with_user_text(
        "{foo: name}",
        &[
            0xEC, 0x81, 0x83, 0xD9, 0x86, 0x71, 0x03, 0x87, 0xB4, 0x83, b'f', b'o', b'o',
            0xD3, 0x8A, 0x71, 0x04,
        ]
    )]
    fn binary_writer_writes_system_text_by_sid(
        #[case] ion: &str,
        #[case] bytes_after_ivm: &[u8],
    ) -> IonResult<()> {
        let mut writer = Writer::new(v1_0::Binary, Vec::new())?;
        writer.write(Element::read_one(ion)?)?;
        let bytes = writer.close()?;
        let expected = [&[0xE0, 0x01, 0x00, 0xEA], bytes_after_ivm].concat();
        assert_eq!(bytes, expected, "{ion}");
        Ok(())
    }

    /// Each way of configuring `Writer::new` infers the writer's encoding and style on its own:
    /// the case expression is checked against `Writer<E, Vec<u8>, S>` with `E` and `S` unknown.
    #[rstest]
    #[case::binary(
        Writer::new(v1_0::Binary, Vec::new()),
        type_name::<BinaryEncoding_1_0>(),
        type_name::<RuntimeStyle>()
    )]
    #[case::text(
        Writer::new(v1_0::Text, Vec::new()),
        type_name::<TextEncoding_1_0>(),
        type_name::<RuntimeStyle>()
    )]
    #[case::text_with_format(
        Writer::new(v1_0::Text.with_format(TextFormat::Pretty), Vec::new()),
        type_name::<TextEncoding_1_0>(),
        type_name::<RuntimeStyle>()
    )]
    #[case::binary_write_config(
        Writer::new(WriteConfig::<v1_0::Binary>::new(), Vec::new()),
        type_name::<BinaryEncoding_1_0>(),
        type_name::<RuntimeStyle>()
    )]
    #[case::text_write_config(
        Writer::new(WriteConfig::<v1_0::Text>::new(TextFormat::Lines), Vec::new()),
        type_name::<TextEncoding_1_0>(),
        type_name::<RuntimeStyle>()
    )]
    #[case::text_writer_alias(
        TextWriter_1_0::new(v1_0::Text, Vec::new()),
        type_name::<TextEncoding_1_0>(),
        type_name::<RuntimeStyle>()
    )]
    #[case::binary_writer_alias(
        BinaryWriter_1_0::new(v1_0::Binary, Vec::new()),
        type_name::<BinaryEncoding_1_0>(),
        type_name::<RuntimeStyle>()
    )]
    #[case::compact(
        Writer::new(v1_0::CompactText, Vec::new()),
        type_name::<TextEncoding_1_0>(),
        type_name::<CompactText>()
    )]
    #[case::lines(
        Writer::new(v1_0::LinesText, Vec::new()),
        type_name::<TextEncoding_1_0>(),
        type_name::<LinesText>()
    )]
    #[case::pretty(
        Writer::new(v1_0::PrettyText, Vec::new()),
        type_name::<TextEncoding_1_0>(),
        type_name::<PrettyText>()
    )]
    #[case::styled_write_config(
        Writer::new(v1_0::CompactText.with_max_depth(4), Vec::new()),
        type_name::<TextEncoding_1_0>(),
        type_name::<CompactText>()
    )]
    fn new_infers_the_encoding_and_style<E: Encoding, S: WriterStyle>(
        #[case] writer: IonResult<Writer<E, Vec<u8>, S>>,
        #[case] expected_encoding: &str,
        #[case] expected_style: &str,
    ) -> IonResult<()> {
        writer?;
        assert_eq!(type_name::<E>(), expected_encoding);
        assert_eq!(type_name::<S>(), expected_style);
        Ok(())
    }

    /// `Writer::idle` infers the style of a marker, as `Writer::new` does. `Writer::<E, ()>` names
    /// the default style.
    #[rstest]
    #[case::text(Writer::idle(v1_0::Text), type_name::<RuntimeStyle>())]
    #[case::text_default_style(Writer::<v1_0::Text, ()>::idle(v1_0::Text), type_name::<RuntimeStyle>())]
    #[case::compact(Writer::idle(v1_0::CompactText), type_name::<CompactText>())]
    #[case::styled_write_config(
        Writer::idle(v1_0::PrettyText.with_max_depth(4)),
        type_name::<PrettyText>()
    )]
    fn idle_infers_the_style<S: WriterStyle>(
        #[case] writer: IonResult<Writer<TextEncoding_1_0, (), S>>,
        #[case] expected_style: &str,
    ) -> IonResult<()> {
        writer?;
        assert_eq!(type_name::<S>(), expected_style);
        Ok(())
    }

    #[test]
    fn flush_underlying_sink() -> IonResult<()> {
        // The final output destination
        let mut buffer: Vec<u8> = Vec::new();
        // A BufWriter that, when flushed, writes bytes to the final output destination
        let buf_writer = BufWriter::new(&mut buffer);
        // An Ion Writer that writes bytes to the buf_writer
        let mut writer = Writer::new(v1_0::Binary, buf_writer)?;
        let len_before_flush = writer.output().get_ref().len();
        // Write some data
        writer.write([1, 2, 3, 4, 5])?;
        // At this point, we've written some data but haven't flushed the inner `buf_writer`,
        // so the length of its underlying `Vec<u8>` should remain unchanged.
        assert_eq!(writer.output().get_ref().len(), len_before_flush);
        // Flush the Ion writer. This should in turn flush the buf_writer, causing bytes to be
        // written to the underlying `Vec<u8>`.
        writer.flush()?;
        // Make sure that this caused the encoded bytes to reach the `Vec<u8>`.
        assert!(writer.output().get_ref().len() > len_before_flush);
        Ok(())
    }

    /// Asserts that `result` is the encoding error raised for a container that would exceed the
    /// maximum depth.
    #[track_caller]
    pub(super) fn assert_depth_error<T>(result: IonResult<T>) {
        let result = result.map(|_| ());
        assert!(
            matches!(&result, Err(IonError::Encoding(e)) if e.to_string() == MAX_DEPTH_EXCEEDED),
            "expected a depth encoding error, got {result:?}"
        );
    }

    /// The encodings the depth tests cover. An enum rather than a generic `E: Encoding` so that
    /// rstest `#[values]` can vary the encoding alongside the other parameters.
    #[derive(Copy, Clone, Debug)]
    enum Format {
        Text,
        Binary,
    }

    /// Encodes `values` as one stream with a fresh managed writer, limited to `max_depth` if it is
    /// `Some` and otherwise using the default limit.
    fn encode_with_max_depth(
        format: Format,
        max_depth: Option<u16>,
        values: &[Element],
    ) -> IonResult<Vec<u8>> {
        fn encode<E: Encoding>(
            config: WriteConfig<E>,
            max_depth: Option<u16>,
            values: &[Element],
        ) -> IonResult<Vec<u8>> {
            let config = match max_depth {
                Some(max_depth) => config.with_max_depth(max_depth),
                None => config,
            };
            config.encode_all_to(Vec::new(), values)
        }
        match format {
            Format::Text => encode(
                WriteConfig::<TextEncoding_1_0>::new(TextFormat::Compact),
                max_depth,
                values,
            ),
            Format::Binary => encode(WriteConfig::<BinaryEncoding_1_0>::new(), max_depth, values),
        }
    }

    /// Asserts that `values` encode under `max_depth` and read back unchanged.
    fn assert_round_trips(
        format: Format,
        max_depth: Option<u16>,
        values: &[Element],
    ) -> IonResult<()> {
        let bytes = encode_with_max_depth(format, max_depth, values)?;
        let read_back: Vec<Element> = Element::read_all(bytes)?.into_iter().collect();
        assert_eq!(read_back, values);
        Ok(())
    }

    #[derive(Copy, Clone, Debug)]
    enum Container {
        List,
        SExp,
        Struct,
    }

    /// Returns a value made of `containers` levels of nested `container`s around the integer `0`,
    /// each container optionally annotated. The integer is at depth `containers`.
    fn nested(container: Container, annotated: bool, containers: usize) -> IonResult<Element> {
        let (open, close) = match container {
            Container::List => ("[", "]"),
            Container::SExp => ("(", ")"),
            Container::Struct => ("{a:", "}"),
        };
        let annotation = if annotated { "x::" } else { "" };
        let text = format!(
            "{}0{}",
            format!("{annotation}{open}").repeat(containers),
            close.repeat(containers)
        );
        Element::read_one(text)
    }

    /// Runs `f` on a thread with a stack large enough for the recursive reading and writing of
    /// values nested hundreds of levels deep in unoptimized builds.
    fn on_large_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn_scoped(scope, f)
                .unwrap()
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
        })
    }

    // The `#[values]` matrices of this test and the next are kept in sync.
    #[rstest]
    fn nesting_at_max_depth_round_trips(
        #[values(Format::Text, Format::Binary)] format: Format,
        #[values(Container::List, Container::SExp, Container::Struct)] container: Container,
        #[values(false, true)] annotated: bool,
        #[values(2, 4)] max_depth: u16,
    ) -> IonResult<()> {
        let value = nested(container, annotated, usize::from(max_depth))?;
        assert_round_trips(format, Some(max_depth), &[value])
    }

    #[rstest]
    fn nesting_past_max_depth_is_an_encoding_error(
        #[values(Format::Text, Format::Binary)] format: Format,
        #[values(Container::List, Container::SExp, Container::Struct)] container: Container,
        #[values(false, true)] annotated: bool,
        #[values(2, 4)] max_depth: u16,
    ) -> IonResult<()> {
        let value = nested(container, annotated, usize::from(max_depth) + 1)?;
        assert_depth_error(encode_with_max_depth(format, Some(max_depth), &[value]));
        Ok(())
    }

    /// With a limit of 0, scalars and typed nulls are accepted.
    #[rstest]
    fn max_depth_of_zero_accepts_scalars(
        #[values(Format::Text, Format::Binary)] format: Format,
        #[values("0", "x::sym", "null.list", "null.struct")] text: &str,
    ) -> IonResult<()> {
        assert_round_trips(format, Some(0), &[Element::read_one(text)?])
    }

    /// With a limit of 0, any container is rejected, even an empty one.
    #[rstest]
    fn max_depth_of_zero_rejects_any_container(
        #[values(Format::Text, Format::Binary)] format: Format,
        #[values("[]", "()", "{}", "x::[0]")] text: &str,
    ) -> IonResult<()> {
        let value = Element::read_one(text)?;
        assert_depth_error(encode_with_max_depth(format, Some(0), &[value]));
        Ok(())
    }

    /// With a limit of 1, scalars and a single level of containers are accepted. Typed nulls such
    /// as `null.list` are not opened as containers, so they are accepted at any depth.
    #[rstest]
    fn max_depth_of_one_accepts_a_single_level_of_containers(
        #[values(Format::Text, Format::Binary)] format: Format,
        #[values(
            "0",
            "x::sym",
            "null.list",
            "null.sexp",
            "null.struct",
            "[]",
            "[0]",
            "(0)",
            "{a: 0}",
            "x::[0]",
            "[null.list]",
            "{a: null.struct}"
        )]
        text: &str,
    ) -> IonResult<()> {
        assert_round_trips(format, Some(1), &[Element::read_one(text)?])
    }

    /// A container inside a container is rejected even if the inner container is empty.
    #[rstest]
    fn max_depth_of_one_rejects_a_nested_container(
        #[values(Format::Text, Format::Binary)] format: Format,
        #[values("[[0]]", "[[]]", "[()]", "[{}]", "(())", "{a: []}", "x::[x::[]]")] text: &str,
    ) -> IonResult<()> {
        let value = Element::read_one(text)?;
        assert_depth_error(encode_with_max_depth(format, Some(1), &[value]));
        Ok(())
    }

    /// Lists, s-expressions, and structs all count toward the same depth.
    #[rstest]
    fn container_types_share_one_depth_budget(
        #[values(Format::Text, Format::Binary)] format: Format,
    ) -> IonResult<()> {
        let value = Element::read_one("[(x::{a: [0]})]")?;
        assert_round_trips(format, Some(4), std::slice::from_ref(&value))?;
        assert_depth_error(encode_with_max_depth(format, Some(3), &[value]));
        Ok(())
    }

    /// Each sibling container gets the full depth remaining at its level.
    #[rstest]
    fn sibling_containers_each_get_the_remaining_depth(
        #[values(Format::Text, Format::Binary)] format: Format,
    ) -> IonResult<()> {
        assert_round_trips(format, Some(2), &[Element::read_one("[[0], (0), {a: 0}]")?])
    }

    /// Each top-level value written through one writer gets the full maximum depth.
    #[rstest]
    fn each_top_level_value_gets_the_max_depth(
        #[values(Format::Text, Format::Binary)] format: Format,
    ) -> IonResult<()> {
        let values: Vec<Element> = Element::read_all("[[0]] ([0]) {a: {b: 0}}")?
            .into_iter()
            .collect();
        assert_round_trips(format, Some(2), &values)
    }

    /// A managed writer built from a configuration of a zero-sized style enforces that
    /// configuration's maximum depth; the last `with_max_depth` replaces any earlier one.
    #[rstest]
    #[case::compact(v1_0::CompactText.with_max_depth(1))]
    #[case::lines(v1_0::LinesText.with_max_depth(1))]
    #[case::pretty(v1_0::PrettyText.with_max_depth(1))]
    #[case::replaced(v1_0::CompactText.with_max_depth(0).with_max_depth(1))]
    fn styled_writer_applies_the_max_depth<S: WriterStyle>(
        #[case] config: StyledWriteConfig<S>,
    ) -> IonResult<()>
    where
        StyledWriteConfig<S>: IntoWriterConfig<TextEncoding_1_0, S>,
    {
        let mut writer = Writer::new(config, Vec::new())?;
        writer.write(Element::read_one("[0]")?)?;
        assert_depth_error(writer.write(Element::read_one("[[0]]")?));
        Ok(())
    }

    /// `encode_as` enforces the maximum depth of a run-time-styled text configuration in each
    /// format.
    #[rstest]
    fn encode_as_applies_the_max_depth(
        #[values(TextFormat::Compact, TextFormat::Lines, TextFormat::Pretty)] format: TextFormat,
    ) -> IonResult<()> {
        let config = v1_0::Text.with_format(format).with_max_depth(1);
        Element::read_one("[0]")?.encode_as(config.clone())?;
        assert_depth_error(Element::read_one("[[0]]")?.encode_as(config));
        Ok(())
    }

    /// A limit above the `u8` range is enforced exactly.
    #[rstest]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn max_depth_above_u8_range_is_enforced(
        #[values(Format::Text, Format::Binary)] format: Format,
    ) -> IonResult<()> {
        on_large_stack(|| {
            let at_max = nested(Container::List, false, 300)?;
            assert_round_trips(format, Some(300), &[at_max])?;

            let past_max = nested(Container::List, false, 301)?;
            assert_depth_error(encode_with_max_depth(format, Some(300), &[past_max]));
            Ok(())
        })
    }

    #[rstest]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn default_depth_allows_deep_nesting(
        #[values(Format::Text, Format::Binary)] format: Format,
    ) -> IonResult<()> {
        on_large_stack(|| {
            let value = nested(Container::List, false, 300)?;
            assert_round_trips(format, None, &[value])
        })
    }
}
