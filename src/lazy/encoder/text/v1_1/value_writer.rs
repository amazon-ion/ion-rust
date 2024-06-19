use crate::lazy::encoder::annotation_seq::AnnotationSeq;
use crate::lazy::encoder::text::v1_0::value_writer::{
    TextAnnotatedValueWriter_1_0, TextContainerWriter_1_0, TextListWriter_1_0, TextSExpWriter_1_0,
    TextStructWriter_1_0, TextValueWriter_1_0,
};
use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{
    AnnotatableWriter, EExpWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::IonFailure;
use crate::types::{ContainerType, ParentType};
use crate::{Decimal, Int, IonResult, IonType, Timestamp};
use delegate::delegate;
use std::io::Write;

pub struct TextValueWriter_1_1<'value, W: Write + 'value> {
    pub(crate) value_writer_1_0: TextValueWriter_1_0<'value, W>,
}

pub struct TextAnnotatedValueWriter_1_1<'value, W: Write + 'value> {
    value_writer_1_0: TextAnnotatedValueWriter_1_0<'value, W>,
}

impl<'value, W: Write + 'value> AnnotatableWriter for TextValueWriter_1_1<'value, W> {
    type AnnotatedValueWriter<'a> = TextAnnotatedValueWriter_1_1<'a, W> where Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(TextAnnotatedValueWriter_1_1 {
            value_writer_1_0: self.value_writer_1_0.with_annotations(annotations)?,
        })
    }
}

impl<'value, W: Write + 'value> ValueWriter for TextValueWriter_1_1<'value, W> {
    type ListWriter = TextListWriter_1_1<'value, W>;
    type SExpWriter = TextSExpWriter_1_1<'value, W>;
    type StructWriter = TextStructWriter_1_1<'value, W>;
    type EExpWriter = TextEExpWriter_1_1<'value, W>;

    const IS_HUMAN_READABLE: bool = true;

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
        })
    }

    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        Ok(TextSExpWriter_1_1 {
            writer_1_0: self.value_writer_1_0.sexp_writer()?,
        })
    }

    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        Ok(TextStructWriter_1_1 {
            writer_1_0: self.value_writer_1_0.struct_writer()?,
        })
    }

    fn eexp_writer<'a>(self, macro_id: impl Into<MacroIdRef<'a>>) -> IonResult<Self::EExpWriter> {
        TextEExpWriter_1_1::new(
            self.value_writer_1_0.writer,
            self.value_writer_1_0.depth,
            self.value_writer_1_0.parent_type,
            // Pretend we're in a sexp for syntax purposes
            ContainerType::SExp,
            // TODO: Reusable buffer
            format!("(:{}", macro_id.into()).as_str(),
            " ",
            match self.value_writer_1_0.parent_type {
                ParentType::Struct | ParentType::List => ",",
                _ => "",
            },
        )
    }
}

impl<'value, W: Write + 'value> AnnotatableWriter for TextAnnotatedValueWriter_1_1<'value, W> {
    type AnnotatedValueWriter<'a> = TextAnnotatedValueWriter_1_1<'a, W> where Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(TextAnnotatedValueWriter_1_1 {
            value_writer_1_0: self.value_writer_1_0.with_annotations(annotations)?,
        })
    }
}

impl<'value, W: Write + 'value> ValueWriter for TextAnnotatedValueWriter_1_1<'value, W> {
    type ListWriter = TextListWriter_1_1<'value, W>;
    type SExpWriter = TextSExpWriter_1_1<'value, W>;
    type StructWriter = TextStructWriter_1_1<'value, W>;
    type EExpWriter = TextEExpWriter_1_1<'value, W>;
    const IS_HUMAN_READABLE: bool = true;
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
        })
    }

    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        Ok(TextSExpWriter_1_1 {
            writer_1_0: self.value_writer_1_0.sexp_writer()?,
        })
    }

    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        Ok(TextStructWriter_1_1 {
            writer_1_0: self.value_writer_1_0.struct_writer()?,
        })
    }

    fn eexp_writer<'a>(self, _macro_id: impl Into<MacroIdRef<'a>>) -> IonResult<Self::EExpWriter> {
        IonResult::encoding_error("e-expressions cannot have annotations")
    }
}

pub struct TextListWriter_1_1<'value, W: Write> {
    writer_1_0: TextListWriter_1_0<'value, W>,
}

impl<'value, W: Write> MakeValueWriter for TextListWriter_1_1<'value, W> {
    type ValueWriter<'a> = TextValueWriter_1_1<'a, W> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        TextValueWriter_1_1 {
            value_writer_1_0: self.writer_1_0.make_value_writer(),
        }
    }
}

impl<'value, W: Write> SequenceWriter for TextListWriter_1_1<'value, W> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.writer_1_0.close()
    }
}

pub struct TextSExpWriter_1_1<'value, W: Write> {
    writer_1_0: TextSExpWriter_1_0<'value, W>,
}

impl<'value, W: Write> MakeValueWriter for TextSExpWriter_1_1<'value, W> {
    type ValueWriter<'a> = TextValueWriter_1_1<'a, W> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        TextValueWriter_1_1 {
            value_writer_1_0: self.writer_1_0.make_value_writer(),
        }
    }
}

impl<'value, W: Write> SequenceWriter for TextSExpWriter_1_1<'value, W> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.writer_1_0.close()
    }
}

pub struct TextStructWriter_1_1<'value, W: Write> {
    writer_1_0: TextStructWriter_1_0<'value, W>,
}

impl<'value, W: Write> FieldEncoder for TextStructWriter_1_1<'value, W> {
    fn encode_field_name(&mut self, name: impl AsRawSymbolRef) -> IonResult<()> {
        self.writer_1_0.encode_field_name(name)
    }
}

impl<'value, W: Write> MakeValueWriter for TextStructWriter_1_1<'value, W> {
    type ValueWriter<'a> = TextValueWriter_1_1<'a, W> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        TextValueWriter_1_1 {
            value_writer_1_0: self.writer_1_0.make_value_writer(),
        }
    }
}

impl<'value, W: Write> StructWriter for TextStructWriter_1_1<'value, W> {
    const IS_HUMAN_READABLE: bool = true;
    fn close(self) -> IonResult<()> {
        self.writer_1_0.close()
    }
}

pub struct TextEExpWriter_1_1<'value, W: Write> {
    // There is no e-exp writer in 1.0 to which we can delegate,
    // but we can re-use the TextContainerWriter_1_0 for a lot of the formatting.
    container_writer: TextContainerWriter_1_0<'value, W>,
}

impl<'value, W: Write> TextEExpWriter_1_1<'value, W> {
    pub(crate) fn new(
        writer: &'value mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        container_type: ContainerType,
        opening_delimiter: &str,
        value_delimiter: &'static str,
        trailing_delimiter: &'static str,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            container_type,
            opening_delimiter,
            value_delimiter,
            trailing_delimiter,
        )?;
        Ok(Self { container_writer })
    }
}

impl<'value, W: Write + 'value> SequenceWriter for TextEExpWriter_1_1<'value, W> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.container_writer.close(")")
    }
}

impl<'value, W: Write + 'value> MakeValueWriter for TextEExpWriter_1_1<'value, W> {
    type ValueWriter<'a> = TextValueWriter_1_1<'a, W>
    where
        Self: 'a,;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        TextValueWriter_1_1 {
            value_writer_1_0: self.container_writer.value_writer(),
        }
    }
}

impl<'value, W: Write + 'value> EExpWriter for TextEExpWriter_1_1<'value, W> {
    // Default SequenceWriter methods
}
