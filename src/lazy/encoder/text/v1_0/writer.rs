use std::io::Write;

use delegate::delegate;

use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::text::v1_0::value_writer::{Separator, TextValueWriter_1_0};
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::{cap_retained_buffer, LazyRawWriter, Recycle, Reusable, WriterRole};
use crate::lazy::encoding::{Encoding, TextEncoding_1_0};
use crate::result::IonFailure;
use crate::text::whitespace_config::WhitespaceConfig;
use crate::types::ParentType;
use crate::write_config::WriteConfigKind;
use crate::{ContextWriter, IonResult, TextFormat, WriteConfig};

/// A raw text Ion 1.0 writer.
pub struct LazyRawTextWriter_1_0<W: Write> {
    pub(crate) output: W,
    pub(crate) whitespace_config: &'static WhitespaceConfig,
}

impl<W: Write> LazyRawTextWriter_1_0<W> {
    /// Constructs a new writer that will emit encoded data to the specified `output`.
    pub fn new(output: W) -> IonResult<Self> {
        <Self as LazyRawWriter<W>>::new(output)
    }

    /// Writes the provided data as a top-level value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        value.write_as_ion(self.value_writer())?;
        Ok(self)
    }

    /// Writes any pending data to the output stream and then calls [`Write::flush`] on it.
    pub fn flush(&mut self) -> IonResult<()> {
        self.output.flush()?;
        Ok(())
    }

    /// Helper method to construct this format's `ValueWriter` implementation. There's no delimiter
    /// between values at the top level, only whitespace.
    #[inline]
    fn value_writer(&mut self) -> TextValueWriter_1_0<'_, W> {
        TextValueWriter_1_0::new(self, 0, Separator::TopLevel, ParentType::TopLevel)
    }
}

// Implemented only for the `Vec<u8>` instantiation, mirroring the binary 1.0 writer: that is the only
// one the managed writer's reusable-writer API needs (`E::Writer<Vec<u8>>: Reusable`).
impl Reusable for LazyRawTextWriter_1_0<Vec<u8>> {}

impl Recycle for LazyRawTextWriter_1_0<Vec<u8>> {
    /// Discards any buffered (unflushed) content and bounds the retained output buffer; in either
    /// role, that is all: a text 1.0 writer owns no scratch state and emits no construction prologue
    /// to re-seed.
    fn recycle(&mut self, role: WriterRole) {
        // A text writer encodes straight into its output buffer, so this is where an unflushed
        // document is discarded. Like binary's, the clear lives here so the contract does not depend
        // on the caller having drained the buffer first.
        self.output.clear();
        cap_retained_buffer::<TextEncoding_1_0>(&mut self.output, role);
    }

    /// Re-derives the whitespace rules from `config`, the only state a text writer takes from it.
    fn apply_config<E: Encoding>(&mut self, config: &WriteConfig<E>) {
        match config.kind() {
            WriteConfigKind::Text(text_config) => {
                self.whitespace_config = text_config.text_kind.into()
            }
            WriteConfigKind::Binary(_) => {
                unreachable!("Text writer can not be configured from binary encoding")
            }
        }
    }
}

impl<W: Write> Sealed for LazyRawTextWriter_1_0<W> {}

impl<W: Write> SequenceWriter for LazyRawTextWriter_1_0<W> {
    type Resources = W;

    fn close(mut self) -> IonResult<Self::Resources> {
        self.flush()?;
        Ok(self.output)
    }
}

impl<W: Write> ContextWriter for LazyRawTextWriter_1_0<W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_0<'a, W>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for LazyRawTextWriter_1_0<W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        self.value_writer()
    }
}

impl<W: Write> LazyRawWriter<W> for LazyRawTextWriter_1_0<W> {
    fn new(output: W) -> IonResult<Self> {
        Self::build(
            WriteConfig::<TextEncoding_1_0>::new(TextFormat::default()),
            output,
        )
    }

    /// Build text writer based on given writer configuration. Returns an error if `config` is a
    /// binary configuration.
    fn build<E: Encoding>(config: WriteConfig<E>, output: W) -> IonResult<Self> {
        match config.kind() {
            WriteConfigKind::Text(text_config) => {
                let whitespace_config = text_config.text_kind.into();
                Ok(LazyRawTextWriter_1_0 {
                    output,
                    whitespace_config,
                })
            }
            WriteConfigKind::Binary(_) => IonResult::illegal_operation(
                "a text writer cannot be built from a binary configuration",
            ),
        }
    }

    // Delegate the trait methods to the inherent methods; this allows a version of these
    // methods to be called on the concrete type even when the trait is not in scope.
    delegate! {
        to self {
            fn flush(&mut self) -> IonResult<()>;
        }
    }

    fn output(&self) -> &W {
        &self.output
    }

    fn output_mut(&mut self) -> &mut W {
        &mut self.output
    }

    fn write_version_marker(&mut self) -> IonResult<()> {
        self.output.write_all(b"$ion_1_0")?;
        Separator::TopLevel.write(self)
    }
}

#[cfg(test)]
mod tests {
    use std::io;

    use rstest::rstest;

    use crate::element::reader::ElementReader;
    use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
    use crate::lazy::encoder::LazyRawWriter;
    use crate::lazy::encoding::{BinaryEncoding_1_0, TextEncoding_1_0};
    use crate::{
        v1_0, Annotatable, Decimal, Int, IonData, IonError, IonResult, RawSymbolRef, Reader,
        SequenceWriter, Symbol, SymbolRef, TextFormat, Timestamp, ValueWriter, WriteConfig,
    };

    #[test]
    fn write_annotated_values() -> IonResult<()> {
        const NO_ANNOTATIONS: [&str; 0] = [];
        let mut writer = LazyRawTextWriter_1_0::new(vec![])?;
        writer
            .write(1)?
            // Explicitly setting an empty annotations sequence
            .write(2.annotated_with(NO_ANNOTATIONS))?
            .write(3.annotated_with("foo"))?
            .write(4.annotated_with(["foo", "bar", "baz"]))?;
        let encoded_bytes = writer.close()?;
        let encoded_text = String::from_utf8(encoded_bytes).unwrap();
        println!("{encoded_text}");

        let expected_ion = r#"
            1
            2 // An explicitly empty annotations sequence results in an unannotated value
            foo::3
            foo::bar::baz::4
        "#;

        let mut reader = Reader::new(v1_0::Text, encoded_text)?;
        let actual = reader.read_all_elements()?;

        let mut reader = Reader::new(v1_0::Text, expected_ion)?;
        let expected = reader.read_all_elements()?;

        assert!(IonData::eq(&expected, &actual));
        Ok(())
    }

    #[rstest]
    #[case::symbol_id("$123", "'$123'")]
    #[case::trailing_letters("$123abc", "$123abc")]
    #[case::trailing_underscore("$1_2", "$1_2")]
    #[case::trailing_dollar("$1$2", "$1$2")]
    #[case::dollar_only("$", "$")]
    #[case::version_marker("$ion_1_1", "'$ion_1_1'")]
    #[case::version_marker_then_letter("$ion_1_0x", "$ion_1_0x")]
    #[case::version_marker_then_underscore("$ion_1_0_0", "$ion_1_0_0")]
    #[case::system_symbol("$ion_symbol_table", "$ion_symbol_table")]
    #[case::ion_prefix("$ion_", "$ion_")]
    fn write_dollar_symbol(#[case] text: &str, #[case] expected: &str) -> IonResult<()> {
        let mut writer = LazyRawTextWriter_1_0::new(vec![])?;
        writer.write(SymbolRef::with_text(text))?;
        let encoded_text = String::from_utf8(writer.close()?).unwrap();
        assert_eq!(encoded_text.trim(), expected);

        let element = Reader::new(v1_0::Text, encoded_text)?.read_one_element()?;
        assert_eq!(element.as_symbol().and_then(|s| s.text()), Some(text));
        Ok(())
    }

    /// An `io::Write` that accepts `capacity` bytes, recording them in `accepted`, then fails every
    /// write with `BrokenPipe`, counting the failures in `failed_writes`.
    struct FailingSink {
        capacity: usize,
        accepted: Vec<u8>,
        failed_writes: usize,
    }

    impl io::Write for FailingSink {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            if self.capacity == 0 {
                self.failed_writes += 1;
                return Err(io::ErrorKind::BrokenPipe.into());
            }
            let len = buf.len().min(self.capacity);
            self.capacity -= len;
            self.accepted.extend_from_slice(&buf[..len]);
            Ok(len)
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    type FailingWriter = LazyRawTextWriter_1_0<FailingSink>;

    /// A sink failure is reported as `IonError::Io` with the sink's `ErrorKind`, whichever part of
    /// the output was being written. The sink accepts `accepted.len()` bytes of Pretty output, so
    /// `accepted` shows that the failing write is the part the case names. The writer stops at the
    /// first failure, so the error it reports is that failure's.
    #[rstest]
    #[case::i64("", |w: &mut FailingWriter| w.write(12345).map(drop))]
    #[case::int("170", |w: &mut FailingWriter| w.write(Int::from(i128::MAX)).map(drop))]
    #[case::float("", |w: &mut FailingWriter| w.write(1.5f64).map(drop))]
    #[case::decimal("12", |w: &mut FailingWriter| w.write(Decimal::new(12345, -2)).map(drop))]
    #[case::timestamp("2000-", |w: &mut FailingWriter| w.write(Timestamp::with_ymd(2000, 1, 1).build()?).map(drop))]
    #[case::blob("{{A", |w: &mut FailingWriter| w.write([1u8, 2, 3, 4].as_slice()).map(drop))]
    #[case::clob("{{\"", |w: &mut FailingWriter| w.value_writer().write_clob(b"hello"))]
    #[case::string("\"", |w: &mut FailingWriter| w.write("hello").map(drop))]
    #[case::symbol("", |w: &mut FailingWriter| w.write(Symbol::from("foo")).map(drop))]
    #[case::symbol_id("$", |w: &mut FailingWriter| w.value_writer().write_symbol(RawSymbolRef::SymbolId(10)))]
    #[case::text_annotation("f", |w: &mut FailingWriter| w.write(1.annotated_with("foo")).map(drop))]
    #[case::symbol_id_annotation("$", |w: &mut FailingWriter| w.write(1.annotated_with(10usize)).map(drop))]
    #[case::separator("1", |w: &mut FailingWriter| w.write(1).map(drop))]
    #[case::field_name("{\n  ", |w: &mut FailingWriter| w.value_writer().write_struct([("foo", 1)]))]
    fn sink_failures_are_io_errors(
        #[case] accepted: &str,
        #[case] write: fn(&mut FailingWriter) -> IonResult<()>,
    ) -> IonResult<()> {
        let sink = FailingSink {
            capacity: accepted.len(),
            accepted: Vec::new(),
            failed_writes: 0,
        };
        let mut writer = LazyRawTextWriter_1_0::build(
            WriteConfig::<TextEncoding_1_0>::new(TextFormat::Pretty),
            sink,
        )?;
        match write(&mut writer) {
            Err(IonError::Io(error)) => {
                assert_eq!(error.source().kind(), io::ErrorKind::BrokenPipe)
            }
            other => panic!("expected an I/O error, got {other:?}"),
        }
        assert_eq!(writer.output.accepted, accepted.as_bytes());
        assert_eq!(
            writer.output.failed_writes, 1,
            "the writer kept writing after the sink failed"
        );
        Ok(())
    }

    /// Building a text writer from a binary configuration is an error.
    #[test]
    fn build_rejects_a_binary_config() {
        let result = LazyRawTextWriter_1_0::build(WriteConfig::<BinaryEncoding_1_0>::new(), vec![]);
        assert!(
            matches!(result, Err(IonError::IllegalOperation(_))),
            "expected an illegal operation error, got {:?}",
            result.as_ref().err()
        );
    }
}
