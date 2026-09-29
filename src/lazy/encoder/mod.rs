#![allow(non_camel_case_types)]

use std::fmt::Debug;
use std::io::Write;
use value_writer::SequenceWriter;

use crate::lazy::encoding::Encoding;
use crate::write_config::WriteConfig;
use crate::IonResult;

pub mod annotate;
pub mod annotation_seq;
pub mod binary;
pub mod text;
pub mod value_writer;
pub mod value_writer_config;
pub mod write_as_ion;
pub mod writer;

/// A family of types that collectively comprise the writer API for an Ion serialization
/// format. These types operate at the 'raw' level; they do not attempt to resolve symbols
/// using the active symbol table.
// Implementations of this trait are typically unit structs that are never instantiated.
// However, many types are generic over some `E: LazyEncoder`, and having this trait
// extend 'static, Sized, Debug, Clone and Copy means that those types can #[derive(...)]
// those traits themselves without boilerplate `where` clauses.
pub trait Encoder: 'static + Sized + Debug + Clone + Copy {
    const SUPPORTS_TEXT_TOKENS: bool;
    const DEFAULT_SYMBOL_CREATION_POLICY: SymbolCreationPolicy;

    /// A writer that serializes Rust values as Ion, emitting the resulting data to an implementation
    /// of [`Write`].
    type Writer<W: Write>: LazyRawWriter<W>;
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum SymbolCreationPolicy {
    // Prefer a compact encoding; create symbol table entries for all field names, annotations,
    // and symbol values. For text Ion, this will result in less human-friendly output.
    RequireSymbolId,
    // When the encoding supports it, write whatever token (symbol ID or text) that the user provided.
    // Do not create new symbol table entries.
    WriteProvidedToken,
    // TODO: Other potential policies, such as:
    //         * Require text (if a SID doesn't map to text, it's an error)
    //         * Wait until the next `flush()` operation to add new symbol definitions in bulk.
    //         * Using a symbol detection mechanism to intern recurring symbols after `N` usages.
}

pub(crate) mod private {
    /// Prevents types outside the crate from implementing traits that extend it.
    // This trait exists only as a visibility constraint, so the compiler considers it dead code.
    #[allow(dead_code)]
    pub trait Sealed {}
}

/// Which of a managed writer's two raw sub-writers is being recycled. The system (directive)
/// writer re-seeds the encoding's construction prologue; the application (data) writer never
/// does, because emitting a second prologue mid-stream would corrupt the document.
// `pub` in this `pub(crate)` module: usable throughout the crate, unreachable from any public path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriterRole {
    /// The sub-writer that emits the stream prologue and encoding directives (symbol tables,
    /// etc.).
    System,
    /// The sub-writer that emits user data.
    Application,
}

/// The crate-internal half of [`Reusable`]: the operations a managed writer performs on a
/// sub-writer it is parking. Kept out of the public API deliberately -- `recycle` DISCARDS whatever
/// the sub-writer has buffered, so calling it at the wrong moment silently truncates the document
/// being encoded. Only [`Writer::detach`](crate::lazy::encoder::writer::Writer::detach) may call it.
// Like `WriterRole` above, this is `pub` in a `pub(crate)` module, so downstream crates can neither
// implement it nor call its methods.
pub trait Recycle {
    /// Returns this writer to its freshly-built state for `role`, discarding any buffered
    /// (unflushed) content: the output buffer and any internal scratch state are emptied,
    /// retained memory is released if it has grown past [`IDLE_RETAIN_CAP`], and -- for
    /// [`WriterRole::System`] only -- the encoding's construction prologue is re-seeded so that the
    /// next document begins exactly as a fresh writer's would.
    ///
    /// Infallible: implementations only ever exist for `Vec<u8>`-backed writers, whose writes
    /// cannot fail. Nothing is written to any sink here, so bytes the caller wanted emitted must
    /// have been `flush`ed beforehand.
    fn recycle(&mut self, role: WriterRole);

    /// Re-applies the encoding-level settings in `config` to this writer in place, i.e. without
    /// rebuilding it (which would throw away the warm scratch state that makes reuse worthwhile).
    /// Only the fields a fresh writer would derive from `config` are touched.
    fn apply_config<E: Encoding>(&mut self, config: &WriteConfig<E>);
}

/// The upper bound on the memory a parked (idle) writer may retain in any one of its buffers or
/// scratch arenas. Each of those grows to fit the largest document the writer has encoded; a pooled
/// writer can live for the rest of the process, so anything that has grown past this cap is dropped
/// in favor of a small fresh allocation instead of being held indefinitely. The cost is one
/// reallocation the next time a large document is encoded. (A future refinement could make this
/// adaptive to avoid thrashing when large documents are frequent.)
// These caps are encoding-agnostic on purpose: they describe the managed writer's parking policy, so
// they do not belong to (and must not be borrowed from) any one encoding's writer module.
pub(crate) const IDLE_RETAIN_CAP: usize = 256 * 1024;

/// The capacity given to the replacement buffer when a retained buffer exceeds [`IDLE_RETAIN_CAP`].
/// Sized to hold a typical small document -- the workload the reusable-writer API exists for --
/// without immediately reallocating.
pub(crate) const IDLE_BUFFER_CAPACITY: usize = 8 * 1024;

/// The upper bound on the number of entries a parked writer's symbol table may retain. Expressed in
/// entries rather than bytes because that is what the table's storage is sized by; at a few dozen
/// bytes per entry (one `Symbol` in the by-ID vector plus one map entry), this is the same order of
/// magnitude as [`IDLE_RETAIN_CAP`].
pub(crate) const IDLE_SYMBOL_RETAIN_CAP: usize = 1024;

/// Bounds the memory a parked (idle) writer retains in `buffer`. If `buffer` has grown past
/// [`IDLE_RETAIN_CAP`], it is replaced with a small fresh one rather than held for the (possibly very
/// long) life of a pooled writer.
///
/// The buffer must already be empty, because replacing it discards its contents; each
/// [`Recycle::recycle`] implementation clears it immediately before calling this, so the assertion
/// below is a cross-check on them.
pub(crate) fn cap_retained_buffer(buffer: &mut Vec<u8>) {
    debug_assert!(
        buffer.is_empty(),
        "a retained buffer must be drained before it is capped"
    );
    if buffer.capacity() > IDLE_RETAIN_CAP {
        *buffer = Vec::with_capacity(IDLE_BUFFER_CAPACITY);
    }
}

/// A marker for raw writers that a managed [`Writer`](writer::Writer) can park (sink-less) and reuse.
///
/// This trait is sealed and carries no callable API of its own -- the methods that make a writer
/// reusable live on crate-private supertraits, because calling them at the wrong moment would discard
/// a document mid-encode. It exists to gate the reusable-writer API (`idle`/`attach`/`detach` on
/// [`Writer`](writer::Writer)) at compile time, and is nameable so that generic code -- a writer pool,
/// say -- can repeat the bound:
///
/// ```text
/// impl<E: Encoding> MyPool<E> where E::Writer<Vec<u8>>: Reusable { /* ... */ }
/// ```
///
/// Only the Ion 1.0 raw writers implement it, so only `Writer<BinaryEncoding_1_0, _>` and
/// `Writer<TextEncoding_1_0, _>` can be reused. An encoding whose writer carries state that
/// `recycle` cannot reset must not implement it: reuse would then silently emit a document that
/// depends on definitions the stream never makes.
pub trait Reusable: private::Sealed + Recycle {}

/// An Ion writer without a symbol table.
pub trait LazyRawWriter<W: Write>: SequenceWriter<Resources = W> {
    fn new(output: W) -> IonResult<Self>
    where
        Self: Sized;

    fn build<E: Encoding>(config: WriteConfig<E>, output: W) -> IonResult<Self>
    where
        Self: Sized;
    fn flush(&mut self) -> IonResult<()>;

    fn output(&self) -> &W;

    fn output_mut(&mut self) -> &mut W;

    fn write_version_marker(&mut self) -> IonResult<()>;
}

#[cfg(test)]
mod tests {
    use crate::lazy::encoder::annotate::Annotatable;
    use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
    use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
    use crate::symbol_ref::AsSymbolRef;
    use crate::{Element, IonData, IonResult, Timestamp};

    fn writer_test(
        expected: &str,
        mut test: impl FnMut(&mut LazyRawTextWriter_1_0<&mut Vec<u8>>) -> IonResult<()>,
    ) -> IonResult<()> {
        let expected = Element::read_all(expected)?;
        let mut buffer = Vec::new();
        let mut writer = LazyRawTextWriter_1_0::new(&mut buffer)?;
        test(&mut writer)?;
        writer.flush()?;
        println!("{}", String::from_utf8_lossy(buffer.as_slice()));
        let actual = Element::read_all(buffer)?;
        assert!(
            IonData::eq(&expected, &actual),
            "expected:\n{expected:?}\nwas not Ion equal to actual:\n{actual:?}\n"
        );
        Ok(())
    }

    #[test]
    fn write_scalars() -> IonResult<()> {
        let expected = r#"
            1
            false
            3e0
            "foo"
            bar
            2023-11-09T
            {{4AEA6g==}}
            [1, 2, 3]
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            writer
                .write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write("bar".as_symbol_ref())?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?
                .write([1, 2, 3])?;
            Ok(())
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_annotated_scalars() -> IonResult<()> {
        let expected = r#"
            foo::bar::1
            quux::quuz::gary::false
            Mercury::Venus::3e0
            Earth::"foo"
            Mars::Jupiter::bar
            Saturn::2023-11-09T
            Uranus::{{4AEA6g==}}
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            writer
                .write(1.annotated_with(["foo", "bar"]))?
                .write(false.annotated_with(["quux", "quuz", "gary"]))?
                .write(3f32.annotated_with(["Mercury", "Venus"]))?
                .write("foo".annotated_with(["Earth"]))?
                .write("bar".as_symbol_ref().annotated_with(["Mars", "Jupiter"]))?
                .write(
                    Timestamp::with_ymd(2023, 11, 9)
                        .build()?
                        .annotated_with(["Saturn"]),
                )?
                .write([0xE0u8, 0x01, 0x00, 0xEA].annotated_with(["Uranus"]))?;
            Ok(())
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_list() -> IonResult<()> {
        let expected = r#"
            [
              1,
              false,
              3e0,
              "foo",
              bar,
              2023-11-09T,
              {{4AEA6g==}},
            ]
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            let mut list = writer.list_writer()?;
            list.write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write("bar".as_symbol_ref())?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?;
            list.end()
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_sexp() -> IonResult<()> {
        let expected = r#"
            (
              1
              false
              3e0
              "foo"
              bar
              2023-11-09T
              {{4AEA6g==}}
              // Nested list
              [1, 2, 3]
            )
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            let mut sexp = writer.sexp_writer()?;
            sexp.write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write("bar".as_symbol_ref())?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?
                .write([1, 2, 3])?;
            sexp.end()
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_struct() -> IonResult<()> {
        let expected = r#"
            {
              a: 1,
              b: false,
              c: 3e0,
              d: "foo",
              e: bar,
              f: 2023-11-09T,
              g: {{4AEA6g==}},
            }
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            let mut struct_ = writer.struct_writer()?;
            struct_
                .write("a", 1)?
                .write("b", false)?
                .write("c", 3f32)?
                .write("d", "foo")?
                .write("e", "bar".as_symbol_ref())?
                .write("f", Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write("g", [0xE0u8, 0x01, 0x00, 0xEA])?;
            struct_.end()
        };
        writer_test(expected, test)
    }
}
