use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::Range;

use crate::lazy::decoder::{Decoder, HasRange, HasSpan, LazyRawValueExpr};
use crate::lazy::encoder::annotation_seq::AnnotationSeq;
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{
    delegate_value_writer_to_self, AnnotatableWriter, ValueWriter,
};
use crate::lazy::encoder::value_writer::{EExpWriter, SequenceWriter, StructWriter};
use crate::lazy::expanded::e_expression::EExpArgGroup;
use crate::lazy::expanded::macro_evaluator::{
    EExpressionArgGroup, IsExhaustedIterator, RawEExpression,
};
use crate::lazy::expanded::template::ParameterEncoding;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::span::Span;
use crate::lazy::text::raw::v1_1::arg_group::EExpArg;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::{Decimal, Int, IonResult, IonType, Timestamp, ValueWriterConfig};

/// An uninhabited type that signals to the compiler that related code paths are not reachable.
#[derive(Debug, Copy, Clone)]
pub enum Never {
    // Has no variants, cannot be instantiated.
}

impl<'top> HasSpan<'top> for Never {
    fn span(&self) -> Span<'top> {
        unreachable!("<Never as HasSpan>::span")
    }
}

impl HasRange for Never {
    fn range(&self) -> Range<usize> {
        unreachable!("<Never as HasSpan>::range")
    }
}

impl SequenceWriter for Never {
    type Resources = ();

    fn close(self) -> IonResult<()> {
        unreachable!("SequenceWriter::end() in Never")
    }
}

impl FieldEncoder for Never {
    fn encode_field_name(&mut self, _name: impl AsRawSymbolRef) -> IonResult<()> {
        unreachable!("FieldEncoder::encode_field_name in Never")
    }
}

impl StructWriter for Never {
    fn close(self) -> IonResult<()> {
        unreachable!("StructWriter::end in Never")
    }

    fn config(&self) -> ValueWriterConfig {
        unreachable!("<Never as StructWriter>::config")
    }
}

impl MakeValueWriter for Never {
    type ValueWriter<'a> = Never
    where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        unreachable!("MakeValueWriter::value_writer in Never")
    }
}

impl EExpWriter for Never {}

impl AnnotatableWriter for Never {
    type AnnotatedValueWriter<'a> = Never
    where Self: 'a;

    fn with_annotations<'a>(
        self,
        _annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        unreachable!("<Never as AnnotatableWriter>::with_annotations");
    }
}

impl ValueWriter for Never {
    type ListWriter = Never;
    type SExpWriter = Never;
    type StructWriter = Never;
    type EExpWriter = Never;

    delegate_value_writer_to_self!();
}

impl<'top, D: Decoder<EExp<'top> = Self>> RawEExpression<'top, D> for Never {
    type RawArgumentsIterator = NeverEExpArgIterator<'top, D>; // Placeholder

    type ArgGroup = NeverArgGroup<'top, D>;

    fn id(self) -> MacroIdRef<'top> {
        unreachable!("<Never as RawEExpression>::id")
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator {
        unreachable!("<Never as RawEExpression>::raw_arguments")
    }
}

#[derive(Copy, Clone, Debug)]
pub struct NeverEExpArgIterator<'top, D: Decoder> {
    spooky: PhantomData<&'top D>,
    never: Never,
}

impl<'top, D: Decoder> Iterator for NeverEExpArgIterator<'top, D> {
    type Item = IonResult<EExpArg<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        unreachable!("<NeverEExpArgIterator as Iterator>::next");
    }
}

#[derive(Copy, Clone, Debug)]
pub struct NeverArgGroup<'top, D: Decoder> {
    spooky: PhantomData<&'top D>,
    never: Never,
}

impl<'top, D: Decoder> IntoIterator for NeverArgGroup<'top, D> {
    type Item = IonResult<LazyRawValueExpr<'top, D>>;
    type IntoIter = NeverArgGroupIterator<'top, D>;

    fn into_iter(self) -> Self::IntoIter {
        unreachable!("<NeverArgGroup as IntoIterator>::into_iter")
    }
}

#[derive(Copy, Clone, Debug)]
pub struct NeverArgGroupIterator<'top, D: Decoder> {
    spooky: PhantomData<&'top D>,
    never: Never,
}

impl<'top, D: Decoder> Iterator for NeverArgGroupIterator<'top, D> {
    type Item = IonResult<LazyRawValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        unreachable!("<NeverArgGroupIterator as Iterator>::next")
    }
}

impl<'top, D: Decoder> IsExhaustedIterator<'top, D> for NeverArgGroupIterator<'top, D> {
    fn is_exhausted(&self) -> bool {
        unreachable!("<NeverArgGroupIterator as EExpArgGroupIterator>::is_exhausted")
    }
}

impl<'top, D: Decoder> HasRange for NeverArgGroup<'top, D> {
    fn range(&self) -> Range<usize> {
        unreachable!("<NeverArgGroup as HasRange>::range")
    }
}

impl<'top, D: Decoder> HasSpan<'top> for NeverArgGroup<'top, D> {
    fn span(&self) -> Span<'top> {
        unreachable!("<NeverArgGroup as HasSpan>::span")
    }
}

impl<'top, D: Decoder> EExpressionArgGroup<'top, D> for NeverArgGroup<'top, D> {
    type Iterator = NeverArgGroupIterator<'top, D>;

    fn encoding(&self) -> &ParameterEncoding {
        unreachable!("<NeverArgGroup as EExpressionArgGroup>::encoding")
    }

    fn resolve(self, _context: EncodingContextRef<'top>) -> EExpArgGroup<'top, D> {
        unreachable!("<NeverArgGroup as EExpressionArgGroup>::resolve")
    }

    fn iter(self) -> Self::Iterator {
        unreachable!("<NeverArgGroup as EExpressionArgGroup>::iter")
    }
}
