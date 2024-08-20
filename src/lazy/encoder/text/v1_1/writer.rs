use std::io::Write;

use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
use crate::lazy::encoder::text::v1_1::value_writer::TextValueWriter_1_1;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::LazyRawWriter;
use crate::lazy::encoding::{Encoding, TextEncoding_1_1};
use crate::text::whitespace_config::{
    COMPACT_WHITESPACE_CONFIG, LINES_WHITESPACE_CONFIG, PRETTY_WHITESPACE_CONFIG,
};
use crate::write_config::WriteConfigKind;
use crate::{IonEncoding, IonResult, TextFormat, WriteConfig};

// Text Ion 1.1 is a syntactic superset of Ion 1.0. The types comprising this writer implementation
// delegates nearly all of their functionality to the 1.0 text writer.

/// A raw text Ion 1.1 writer.
pub struct LazyRawTextWriter_1_1<W: Write> {
    pub(crate) writer_1_0: LazyRawTextWriter_1_0<W>,
}

impl<W: Write> SequenceWriter for LazyRawTextWriter_1_1<W> {
    type Resources = W;

    fn close(self) -> IonResult<Self::Resources> {
        self.writer_1_0.close()
    }
}

impl<W: Write> MakeValueWriter for LazyRawTextWriter_1_1<W> {
    type ValueWriter<'a> = TextValueWriter_1_1<'a, W>
    where
        Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        let value_writer_1_0 = self.writer_1_0.make_value_writer();
        TextValueWriter_1_1 { value_writer_1_0 }
    }
}

impl<W: Write> LazyRawWriter<W> for LazyRawTextWriter_1_1<W> {
    fn new(output: W) -> IonResult<Self>
    where
        Self: Sized,
    {
        Self::build(
            WriteConfig::<TextEncoding_1_1>::new(TextFormat::default()),
            output,
        )
    }

    fn build<E: Encoding>(config: WriteConfig<E>, mut output: W) -> IonResult<Self>
    where
        Self: Sized,
    {
        match &config.kind {
            WriteConfigKind::Text(text_config) => {
                let whitespace_config = match text_config.text_kind {
                    TextFormat::Compact => &COMPACT_WHITESPACE_CONFIG,
                    TextFormat::Lines => &LINES_WHITESPACE_CONFIG,
                    TextFormat::Pretty => &PRETTY_WHITESPACE_CONFIG,
                };
                write!(
                    output,
                    "$ion_1_1{}",
                    whitespace_config.space_between_top_level_values
                )?;
                Ok(LazyRawTextWriter_1_1 {
                    writer_1_0: LazyRawTextWriter_1_0 {
                        output,
                        whitespace_config,
                    },
                })
            }
            WriteConfigKind::Binary(_) => {
                unreachable!("Binary writer can not be created from text encoding")
            }
        }
    }

    fn flush(&mut self) -> IonResult<()> {
        self.writer_1_0.flush()
    }

    fn output(&self) -> &W {
        self.writer_1_0.output()
    }

    fn output_mut(&mut self) -> &mut W {
        self.writer_1_0.output_mut()
    }

    fn write_version_marker(&mut self) -> IonResult<()> {
        let space_between = self
            .writer_1_0
            .whitespace_config
            .space_between_top_level_values;
        write!(self.writer_1_0.output, "$ion_1_1{space_between}")?;
        Ok(())
    }

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Text_1_1
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::any_encoding::IonVersion;
    use crate::lazy::decoder::{LazyRawReader, LazyRawSequence, LazyRawValue};
    use crate::lazy::encoder::text::v1_1::writer::LazyRawTextWriter_1_1;
    use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter, ValueWriter};
    use crate::lazy::encoder::write_as_ion::WriteAsSExp;
    use crate::lazy::encoder::LazyRawWriter;
    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::expanded::macro_evaluator::RawEExpression;
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::text::raw::v1_1::reader::{LazyRawTextReader_1_1, MacroIdRef};
    use crate::symbol_ref::AsSymbolRef;
    use crate::{
        v1_1, Annotatable, Decimal, ElementReader, IonData, IonResult, IonType, Null, RawSymbolRef,
        Reader, Timestamp,
    };

    #[test]
    fn write_scalars() -> IonResult<()> {
        let mut writer = LazyRawTextWriter_1_1::new(vec![])?;
        writer
            .write(Null(IonType::String))?
            .write(true)?
            .write(1)?
            .write(1.5f64)?
            .write(Decimal::new(123, -2))?
            .write(Timestamp::with_ymd(2024, 4, 23).build()?)?
            .write("foo")?
            .write("foo".as_symbol_ref())?
            .write([0xEAu8, 0x01, 0x01, 0xEE])?
            .write_clob([0xEAu8, 0x01, 0x01, 0xEE])?;
        let encoded_bytes = writer.close()?;
        let encoded_text = String::from_utf8(encoded_bytes).unwrap();
        println!("{encoded_text}");

        let expected_ion = r#"
            $ion_1_1
            null.string
            true
            1
            1.5e0
            1.23
            2024-04-23T
            "foo"
            foo
            {{6gEB7g==}}
            {{"\xea\x01\x01\xee"}}
        "#;

        let mut reader = Reader::new(v1_1::Text, encoded_text)?;
        let actual = reader.read_all_elements()?;

        let mut reader = Reader::new(v1_1::Text, expected_ion)?;
        let expected = reader.read_all_elements()?;

        assert!(IonData::eq(&expected, &actual));
        Ok(())
    }

    #[test]
    fn write_list() -> IonResult<()> {
        let mut writer = LazyRawTextWriter_1_1::new(vec![])?;
        let empty_list: [i64; 0] = [];
        writer
            .write(empty_list)?
            .write([1])?
            .write([1, 2])?
            .write([[1, 2], [3, 4], [5, 6]])?;
        let encoded_bytes = writer.close()?;
        let encoded_text = String::from_utf8(encoded_bytes).unwrap();
        println!("{encoded_text}");
        let expected_ion = r#"
            $ion_1_1
            []
            [1]
            [1, 2]
            [[1, 2], [3, 4], [5, 6]]
        "#;

        let mut reader = Reader::new(v1_1::Text, encoded_text)?;
        let actual = reader.read_all_elements()?;

        let mut reader = Reader::new(v1_1::Text, expected_ion)?;
        let expected = reader.read_all_elements()?;

        assert!(IonData::eq(&expected, &actual));
        Ok(())
    }

    #[test]
    fn write_sexp() -> IonResult<()> {
        let mut writer = LazyRawTextWriter_1_1::new(vec![])?;
        let empty_sexp: [i64; 0] = [];
        writer
            .write_sexp(empty_sexp)?
            .write_sexp([1])?
            .write_sexp([1, 2])?
            .write_sexp([[1, 2].as_sexp(), [3, 4].as_sexp(), [5, 6].as_sexp()])?;
        let encoded_bytes = writer.close()?;
        let encoded_text = String::from_utf8(encoded_bytes).unwrap();
        println!("{encoded_text}");
        let expected_ion = r#"
            $ion_1_1
            ()
            (1)
            (1 2)
            ((1 2) (3 4) (5 6))
        "#;

        let mut reader = Reader::new(v1_1::Text, encoded_text)?;
        let actual = reader.read_all_elements()?;

        let mut reader = Reader::new(v1_1::Text, expected_ion)?;
        let expected = reader.read_all_elements()?;

        assert!(IonData::eq(&expected, &actual));
        Ok(())
    }

    #[test]
    fn write_struct() -> IonResult<()> {
        let mut writer = LazyRawTextWriter_1_1::new(vec![])?;
        let empty_field_list: [(&str, i64); 0] = [];
        writer
            .write_struct(empty_field_list)?
            .write_struct([("foo", 1)])?
            .write_struct([("foo", 1), ("bar", 2)])?
            .write_struct([("foo", 1), ("bar", 2), ("baz", 3)])?;

        let mut parent_struct = writer.struct_writer()?;
        parent_struct
            .field_writer("quux")
            .write_struct([("quuz", 4)])?;
        parent_struct.close()?;

        let encoded_bytes = writer.close()?;
        let encoded_text = String::from_utf8(encoded_bytes).unwrap();
        println!("{encoded_text}");
        let expected_ion = r#"
            $ion_1_1
            {}
            {foo: 1}
            {foo: 1, bar: 2}
            {foo: 1, bar: 2, baz: 3}
            {quux: {quuz: 4}}
        "#;

        let mut reader = Reader::new(v1_1::Text, encoded_text)?;
        let actual = reader.read_all_elements()?;

        let mut reader = Reader::new(v1_1::Text, expected_ion)?;
        let expected = reader.read_all_elements()?;

        assert!(IonData::eq(&expected, &actual));
        Ok(())
    }

    #[test]
    fn test_eexp() -> IonResult<()> {
        let mut writer = LazyRawTextWriter_1_1::new(vec![])?;
        let mut macro_args = writer.eexp_writer("foo")?;
        macro_args
            .write(1)?
            .write([2, 3, 4])?
            .write("bar")?
            .write_symbol("+++")?;
        macro_args.close()?;
        let encoded_bytes = writer.close()?;

        let encoded_text = String::from_utf8(encoded_bytes).unwrap();
        println!("{encoded_text}");

        let mut reader = LazyRawTextReader_1_1::new(encoded_text.as_bytes());
        let mut context = EncodingContext::for_ion_version(IonVersion::v1_1);
        let macro_foo =
            TemplateCompiler::compile_from_text("(macro foo (x*) null)")?;
        context.macro_table.add_macro(macro_foo)?;
        let context = context.get_ref();
        let _marker = reader.next(context)?.expect_ivm()?;
        let eexp = reader.next(context)?.expect_eexp()?;
        assert_eq!(MacroIdRef::LocalName("foo"), eexp.id());
        let mut args = eexp.raw_arguments();
        let x = args.next().unwrap()?.expr().expect_arg_group()?;
        let mut x_values = x.into_iter();
        let int_value = x_values
            .next()
            .unwrap()?
            .expect_value()
            .unwrap()
            .read()?
            .expect_i64()?;
        assert_eq!(int_value, 1);
        let list_value = x_values
            .next()
            .unwrap()?
            .expect_value()?
            .read()?
            .expect_list()?;
        assert_eq!(list_value.iter().count(), 3);
        let string_value = x_values
            .next()
            .unwrap()?
            .expect_value()?
            .read()?
            .expect_string()?;
        assert_eq!(string_value, "bar");
        let symbol_value = x_values
            .next()
            .unwrap()?
            .expect_value()?
            .read()?
            .expect_symbol()?;
        assert_eq!(symbol_value, RawSymbolRef::Text("+++"));

        Ok(())
    }

    #[test]
    fn write_annotated_values() -> IonResult<()> {
        const NO_ANNOTATIONS: [&str; 0] = [];
        let mut writer = LazyRawTextWriter_1_1::new(vec![])?;
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
            $ion_1_1
            1
            2 // An explicitly empty annotations sequence results in an unannotated value
            foo::3
            foo::bar::baz::4
        "#;

        let mut reader = Reader::new(v1_1::Text, encoded_text)?;
        let actual = reader.read_all_elements()?;

        let mut reader = Reader::new(v1_1::Text, expected_ion)?;
        let expected = reader.read_all_elements()?;

        assert!(IonData::eq(&expected, &actual));
        Ok(())
    }
}
