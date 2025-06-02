use crate::lazy::encoder::annotation_seq::AnnotationSeq;
use crate::lazy::encoder::text::v1_0::value_writer::{
    TextAnnotatedValueWriter_1_0, TextContainerWriter_1_0, TextListWriter_1_0, TextSExpWriter_1_0,
    TextStructWriter_1_0, TextValueWriter_1_0,
};
use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
use crate::lazy::encoder::value_writer::internal::{
    EExpWriterInternal, FieldEncoder, MakeValueWriter,
};
use crate::lazy::encoder::value_writer::{
    AnnotatableWriter, EExpWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::lazy::expanded::macro_table::MacroRef;
use crate::lazy::expanded::template::{Parameter, SignatureIterator};
use crate::lazy::text::raw::v1_1::reader::{MacroIdLike, MacroIdRef};
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::IonFailure;
use crate::types::{ContainerType, ParentType};
use crate::{
    v1_1, ContextWriter, Decimal, Encoding, Int, IonResult, IonType, MacroTable, Timestamp,
    ValueWriterConfig,
};
use compact_str::format_compact;
use delegate::delegate;
use std::io::Write;

pub struct TextValueWriter_1_1<'value, W: Write> {
    pub(crate) value_writer_1_0: TextValueWriter_1_0<'value, W>,
    pub(crate) macros: &'value MacroTable,
}

pub struct TextAnnotatedValueWriter_1_1<'value, W: Write> {
    value_writer_1_0: TextAnnotatedValueWriter_1_0<'value, W>,
    macros: &'value MacroTable,
}

impl<'value, W: Write + 'value> AnnotatableWriter for TextValueWriter_1_1<'value, W> {
    type AnnotatedValueWriter<'a>
        = TextAnnotatedValueWriter_1_1<'a, W>
    where
        Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(TextAnnotatedValueWriter_1_1 {
            value_writer_1_0: self.value_writer_1_0.with_annotations(annotations)?,
            macros: self.macros,
        })
    }
}

impl<'value, W: Write + 'value> ValueWriter for TextValueWriter_1_1<'value, W> {
    type ListWriter = TextListWriter_1_1<'value, W>;
    type SExpWriter = TextSExpWriter_1_1<'value, W>;
    type StructWriter = TextStructWriter_1_1<'value, W>;
    type EExpWriter = TextEExpWriter_1_1<'value, W>;

    // For all of the scalars, delegate to the existing 1.0 writing logic.
    delegate! {
        to self.value_writer_1_0 {
            fn write_null(self, ion_type: IonType) -> IonResult<()>;
            fn write_bool(self, value: bool) -> IonResult<()>;
            fn write_i64(self, value: i64) -> IonResult<()>;
            fn write_int(self, value: &Int) -> IonResult<()>;
            fn write_f32(self, value: f32) -> IonResult<()>;
            fn write_f64(self, value: f64) -> IonResult<()>;
            fn write_decimal(self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(self, value: &Timestamp) -> IonResult<()>;
            fn write_string(self, value: impl AsRef<str>) -> IonResult<()>;
            fn write_symbol(self, value: impl AsRawSymbolRef) -> IonResult<()>;
            fn write_clob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_blob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
        }
    }

    fn list_writer(self) -> IonResult<Self::ListWriter> {
        Ok(TextListWriter_1_1 {
            writer_1_0: self.value_writer_1_0.list_writer()?,
            macros: self.macros,
        })
    }

    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        Ok(TextSExpWriter_1_1 {
            writer_1_0: self.value_writer_1_0.sexp_writer()?,
            macros: self.macros,
        })
    }

    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        Ok(TextStructWriter_1_1 {
            writer_1_0: self.value_writer_1_0.struct_writer()?,
            macros: self.macros,
        })
    }

    fn eexp_writer<'a>(self, macro_id: impl MacroIdLike<'a>) -> IonResult<Self::EExpWriter>
    where
        Self: 'a,
    {
        let macro_ref = macro_id.resolve(self.macros)?;
        let opening_text = match macro_id.prefer_name() {
            MacroIdRef::LocalName(name) => format_compact!("(:{} ", name),
            MacroIdRef::LocalAddress(address) => format_compact!("(:{} ", address),
            MacroIdRef::SystemAddress(system_address) => {
                format_compact!("(:$ion::{} ", system_address.as_usize())
            }
        };
        TextEExpWriter_1_1::new(
            self.value_writer_1_0.writer,
            self.value_writer_1_0.depth,
            self.value_writer_1_0.parent_type,
            // Pretend we're in a sexp for syntax purposes
            opening_text.as_str(),
            self.macros,
            macro_ref,
        )
    }
}

impl<'value, W: Write + 'value> AnnotatableWriter for TextAnnotatedValueWriter_1_1<'value, W> {
    type AnnotatedValueWriter<'a>
        = TextAnnotatedValueWriter_1_1<'a, W>
    where
        Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(TextAnnotatedValueWriter_1_1 {
            value_writer_1_0: self.value_writer_1_0.with_annotations(annotations)?,
            macros: self.macros,
        })
    }
}

impl<'value, W: Write + 'value> ValueWriter for TextAnnotatedValueWriter_1_1<'value, W> {
    type ListWriter = TextListWriter_1_1<'value, W>;
    type SExpWriter = TextSExpWriter_1_1<'value, W>;
    type StructWriter = TextStructWriter_1_1<'value, W>;
    type EExpWriter = TextEExpWriter_1_1<'value, W>;
    // For all of the scalars, delegate to the existing 1.0 writing logic.
    delegate! {
        to self.value_writer_1_0 {
            fn write_null(self, ion_type: IonType) -> IonResult<()>;
            fn write_bool(self, value: bool) -> IonResult<()>;
            fn write_i64(self, value: i64) -> IonResult<()>;
            fn write_int(self, value: &Int) -> IonResult<()>;
            fn write_f32(self, value: f32) -> IonResult<()>;
            fn write_f64(self, value: f64) -> IonResult<()>;
            fn write_decimal(self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(self, value: &Timestamp) -> IonResult<()>;
            fn write_string(self, value: impl AsRef<str>) -> IonResult<()>;
            fn write_symbol(self, value: impl AsRawSymbolRef) -> IonResult<()>;
            fn write_clob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_blob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
        }
    }

    fn list_writer(self) -> IonResult<Self::ListWriter> {
        Ok(TextListWriter_1_1 {
            writer_1_0: self.value_writer_1_0.list_writer()?,
            macros: self.macros,
        })
    }

    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        Ok(TextSExpWriter_1_1 {
            writer_1_0: self.value_writer_1_0.sexp_writer()?,
            macros: self.macros,
        })
    }

    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        Ok(TextStructWriter_1_1 {
            writer_1_0: self.value_writer_1_0.struct_writer()?,
            macros: self.macros,
        })
    }

    fn eexp_writer<'a>(self, _macro_id: impl MacroIdLike<'a>) -> IonResult<Self::EExpWriter> {
        IonResult::encoding_error("e-expressions cannot have annotations")
    }
}

pub struct TextListWriter_1_1<'value, W: Write> {
    writer_1_0: TextListWriter_1_0<'value, W>,
    macros: &'value MacroTable,
}

impl<W: Write> ContextWriter for TextListWriter_1_1<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_1<'a, W>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for TextListWriter_1_1<'_, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        TextValueWriter_1_1 {
            value_writer_1_0: self.writer_1_0.make_value_writer(),
            macros: self.macros,
        }
    }
}

impl<W: Write> SequenceWriter for TextListWriter_1_1<'_, W> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.writer_1_0.close()
    }
}

pub struct TextSExpWriter_1_1<'value, W: Write> {
    writer_1_0: TextSExpWriter_1_0<'value, W>,
    macros: &'value MacroTable,
}

impl<W: Write> ContextWriter for TextSExpWriter_1_1<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_1<'a, W>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for TextSExpWriter_1_1<'_, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        TextValueWriter_1_1 {
            value_writer_1_0: self.writer_1_0.make_value_writer(),
            macros: self.macros,
        }
    }
}

impl<W: Write> SequenceWriter for TextSExpWriter_1_1<'_, W> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.writer_1_0.close()
    }
}

pub struct TextStructWriter_1_1<'value, W: Write> {
    writer_1_0: TextStructWriter_1_0<'value, W>,
    macros: &'value MacroTable,
}

impl<W: Write> FieldEncoder for TextStructWriter_1_1<'_, W> {
    fn encode_field_name(&mut self, name: impl AsRawSymbolRef) -> IonResult<()> {
        self.writer_1_0.encode_field_name(name)
    }
}

impl<W: Write> ContextWriter for TextStructWriter_1_1<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_1<'a, W>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for TextStructWriter_1_1<'_, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        TextValueWriter_1_1 {
            value_writer_1_0: self.writer_1_0.make_value_writer(),
            macros: self.macros,
        }
    }
}

impl<W: Write> StructWriter for TextStructWriter_1_1<'_, W> {
    fn close(self) -> IonResult<()> {
        self.writer_1_0.close()
    }

    fn config(&self) -> ValueWriterConfig {
        v1_1::Text::default_value_writer_config()
    }
}

pub struct TextEExpWriter_1_1<'value, W: Write> {
    // There is no e-exp writer in 1.0 to which we can delegate,
    // but we can re-use the TextContainerWriter_1_0 for a lot of the formatting.
    container_writer: TextContainerWriter_1_0<'value, W>,
    macros: &'value MacroTable,
    signature_iter: SignatureIterator<'value>,
}

impl<'value, W: Write> TextEExpWriter_1_1<'value, W> {
    pub(crate) fn new(
        writer: &'value mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        opening_text: &str,
        macros: &'value MacroTable,
        invoked_macro: MacroRef<'value>,
    ) -> IonResult<Self> {
        let trailing_delimiter = match parent_type {
            ParentType::Struct | ParentType::List => ",",
            _ => "",
        };
        let value_delimiter = " ";

        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            // Pretend we're in a SExp for syntax purposes
            ContainerType::SExp,
            opening_text,
            value_delimiter,
            trailing_delimiter,
        )?;
        let signature_iter = invoked_macro.iter_signature();
        Ok(Self {
            container_writer,
            macros,
            signature_iter,
        })
    }
}

impl<'value, W: Write + 'value> SequenceWriter for TextEExpWriter_1_1<'value, W> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.container_writer.close(")")
    }
}

impl<'value, W: Write + 'value> ContextWriter for TextEExpWriter_1_1<'value, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_1<'a, W>
    where
        Self: 'a;
}

impl<'value, W: Write + 'value> MakeValueWriter for TextEExpWriter_1_1<'value, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        TextValueWriter_1_1 {
            value_writer_1_0: self.container_writer.value_writer(),
            macros: self.macros,
        }
    }
}

impl<'eexp, W: Write + 'eexp> EExpWriterInternal for TextEExpWriter_1_1<'eexp, W> {
    fn expect_next_parameter(&mut self) -> IonResult<&Parameter> {
        self.signature_iter.expect_next_parameter()
    }
}

impl<'eexp, W: Write + 'eexp> EExpWriter for TextEExpWriter_1_1<'eexp, W> {
    type ExprGroupWriter<'group>
        = TextExprGroupWriter<'group, W>
    where
        Self: 'group;

    fn invoked_macro(&self) -> MacroRef<'_> {
        self.signature_iter.parent_macro()
    }

    fn current_parameter(&self) -> Option<&Parameter> {
        self.signature_iter.current_parameter()
    }

    fn expr_group_writer(&mut self) -> IonResult<Self::ExprGroupWriter<'_>> {
        TextExprGroupWriter::new(
            self.container_writer.writer,
            self.container_writer.depth,
            self.container_writer.container_type.into(),
            " ",
            self.macros,
        )
    }
    // Default SequenceWriter methods
}

pub struct TextExprGroupWriter<'group, W: Write> {
    // There is no expr group writer in 1.0 to which we can delegate,
    // but we can re-use the TextContainerWriter_1_0 for a lot of the formatting.
    container_writer: TextContainerWriter_1_0<'group, W>,
    macros: &'group MacroTable,
}

impl<'group, W: Write> TextExprGroupWriter<'group, W> {
    pub(crate) fn new(
        writer: &'group mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        trailing_delimiter: &'static str,
        macros: &'group MacroTable,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth + 1,
            parent_type,
            ContainerType::SExp,
            "(::",
            " ",
            trailing_delimiter,
        )?;
        Ok(Self {
            container_writer,
            macros,
        })
    }
}

impl<W: Write> MakeValueWriter for TextExprGroupWriter<'_, W> {
    fn make_value_writer(&mut self) -> <Self as ContextWriter>::NestedValueWriter<'_> {
        TextValueWriter_1_1 {
            value_writer_1_0: self.container_writer.value_writer(),
            macros: self.macros,
        }
    }
}

impl<W: Write> SequenceWriter for TextExprGroupWriter<'_, W> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.container_writer.close(")")
    }
}

impl<W: Write> ContextWriter for TextExprGroupWriter<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_1<'a, W>
    where
        Self: 'a;
}
