#![allow(non_camel_case_types)]

use std::fmt::Debug;
use std::ops::Range;

use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator as RawBinaryAnnotationsIterator_1_0;
use crate::lazy::binary::raw::r#struct::{
    LazyRawBinaryFieldName_1_0, LazyRawBinaryStruct_1_0, RawBinaryStructIterator_1_0,
};
use crate::lazy::binary::raw::reader::LazyRawBinaryReader_1_0;
use crate::lazy::binary::raw::sequence::{
    LazyRawBinaryList_1_0, LazyRawBinarySExp_1_0, RawBinarySequenceIterator_1_0,
};
use crate::lazy::binary::raw::v1_1::e_expression::{
    BinaryEExpArgGroup, BinaryEExpArgGroupIterator, BinaryEExpression_1_1,
};
use crate::lazy::binary::raw::v1_1::r#struct::{
    LazyRawBinaryFieldName_1_1, LazyRawBinaryStruct_1_1, RawBinaryStructIterator_1_1,
};
use crate::lazy::binary::raw::v1_1::reader::LazyRawBinaryReader_1_1;
use crate::lazy::binary::raw::v1_1::sequence::{
    LazyRawBinaryList_1_1, LazyRawBinarySExp_1_1, RawBinarySequenceIterator_1_1,
};
use crate::lazy::binary::raw::v1_1::value::{
    LazyRawBinaryValue_1_1, LazyRawBinaryVersionMarker_1_1,
};
use crate::lazy::binary::raw::v1_1::RawBinaryAnnotationsIterator_1_1;
use crate::lazy::binary::raw::value::{LazyRawBinaryValue_1_0, LazyRawBinaryVersionMarker_1_0};
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, HasRange, HasSpan, LazyRawContainer, LazyRawFieldExpr, LazyRawFieldName,
    LazyRawReader, LazyRawSequence, LazyRawStruct, LazyRawValue, LazyRawValueExpr, RawValueExpr,
    RawVersionMarker,
};
use crate::lazy::encoding::{
    BinaryEncoding_1_0, BinaryEncoding_1_1, TextEncoding_1_0, TextEncoding_1_1,
};
use crate::lazy::expanded::e_expression::ArgGroup;
use crate::lazy::expanded::macro_evaluator::{
    EExpArgGroupIterator, EExpressionArgGroup, RawEExpression,
};
use crate::lazy::expanded::template::ParameterEncoding;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::raw_stream_item::LazyRawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::span::Span;
use crate::lazy::text::raw::r#struct::{
    LazyRawTextFieldName_1_0, LazyRawTextStruct_1_0, RawTextStructIterator_1_0,
};
use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
use crate::lazy::text::raw::sequence::{
    LazyRawTextList_1_0, LazyRawTextSExp_1_0, RawTextListIterator_1_0, RawTextSExpIterator_1_0,
};
use crate::lazy::text::raw::v1_1::arg_group::{
    EExpArg, EExpArgExpr, TextEExpArgGroup, TextEExpArgGroupIterator,
};
use crate::lazy::text::raw::v1_1::reader::{
    LazyRawTextFieldName_1_1, LazyRawTextList_1_1, LazyRawTextReader_1_1, LazyRawTextSExp_1_1,
    LazyRawTextStruct_1_1, MacroIdRef, RawTextSequenceCacheIterator_1_1,
    RawTextStructCacheIterator_1_1, TextEExpression_1_1,
};
use crate::lazy::text::value::{
    LazyRawTextValue_1_0, LazyRawTextValue_1_1, LazyRawTextVersionMarker_1_0,
    LazyRawTextVersionMarker_1_1, RawTextAnnotationsIterator,
};
use crate::{try_next, Encoding, IonResult, IonType, RawStreamItem, RawSymbolRef};

/// An implementation of the `LazyDecoder` trait that can read any encoding of Ion.
#[derive(Debug, Clone, Copy)]
pub struct AnyEncoding;

// This family of types avoids boxing and dynamic dispatch by using enums of the supported formats
// within each type. Trait methods are implemented by forwarding the call to the appropriate
// underlying type.
impl Decoder for AnyEncoding {
    type Reader<'data> = LazyRawAnyReader<'data>;
    type Value<'top> = LazyRawAnyValue<'top>;
    type SExp<'top> = LazyRawAnySExp<'top>;
    type List<'top> = LazyRawAnyList<'top>;
    type Struct<'top> = LazyRawAnyStruct<'top>;
    type FieldName<'top> = LazyRawAnyFieldName<'top>;
    type AnnotationsIterator<'top> = RawAnyAnnotationsIterator<'top>;
    type EExp<'top> = LazyRawAnyEExpression<'top>;
    type VersionMarker<'top> = LazyRawAnyVersionMarker<'top>;
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyVersionMarker<'top> {
    encoding: LazyRawAnyVersionMarkerKind<'top>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawAnyVersionMarkerKind<'top> {
    Text_1_0(LazyRawTextVersionMarker_1_0<'top>),
    Binary_1_0(LazyRawBinaryVersionMarker_1_0<'top>),
    Text_1_1(LazyRawTextVersionMarker_1_1<'top>),
    Binary_1_1(LazyRawBinaryVersionMarker_1_1<'top>),
}

impl<'top> LazyRawAnyVersionMarker<'top> {
    pub fn encoding(&self) -> IonEncoding {
        use crate::lazy::any_encoding::LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(_) => TextEncoding_1_0.encoding(),
            Binary_1_0(_) => BinaryEncoding_1_0.encoding(),
            Text_1_1(_) => TextEncoding_1_1.encoding(),
            Binary_1_1(_) => BinaryEncoding_1_1.encoding(),
        }
    }
}

impl<'top> HasSpan<'top> for LazyRawAnyVersionMarker<'top> {
    fn span(&self) -> Span<'top> {
        use LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(marker) => marker.span(),
            Binary_1_0(marker) => marker.span(),
            Text_1_1(marker) => marker.span(),
            Binary_1_1(marker) => marker.span(),
        }
    }
}

impl<'top> HasRange for LazyRawAnyVersionMarker<'top> {
    fn range(&self) -> Range<usize> {
        use LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(marker) => marker.range(),
            Binary_1_0(marker) => marker.range(),
            Text_1_1(marker) => marker.range(),
            Binary_1_1(marker) => marker.range(),
        }
    }
}

impl<'top> RawVersionMarker<'top> for LazyRawAnyVersionMarker<'top> {
    fn major_minor(&self) -> (u8, u8) {
        use LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(marker) => marker.major_minor(),
            Binary_1_0(marker) => marker.major_minor(),
            Text_1_1(marker) => marker.major_minor(),
            Binary_1_1(marker) => marker.major_minor(),
        }
    }

    fn stream_encoding_before_marker(&self) -> IonEncoding {
        use LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(_) => IonEncoding::Text_1_0,
            Binary_1_0(_) => IonEncoding::Binary_1_0,
            Text_1_1(_) => IonEncoding::Text_1_1,
            Binary_1_1(_) => IonEncoding::Binary_1_1,
        }
    }
}

impl<'top> From<LazyRawBinaryVersionMarker_1_0<'top>> for LazyRawAnyVersionMarker<'top> {
    fn from(value: LazyRawBinaryVersionMarker_1_0<'top>) -> Self {
        LazyRawAnyVersionMarker {
            encoding: LazyRawAnyVersionMarkerKind::Binary_1_0(value),
        }
    }
}
impl<'top> From<LazyRawBinaryVersionMarker_1_1<'top>> for LazyRawAnyVersionMarker<'top> {
    fn from(value: LazyRawBinaryVersionMarker_1_1<'top>) -> Self {
        LazyRawAnyVersionMarker {
            encoding: LazyRawAnyVersionMarkerKind::Binary_1_1(value),
        }
    }
}
impl<'top> From<LazyRawTextVersionMarker_1_0<'top>> for LazyRawAnyVersionMarker<'top> {
    fn from(value: LazyRawTextVersionMarker_1_0<'top>) -> Self {
        LazyRawAnyVersionMarker {
            encoding: LazyRawAnyVersionMarkerKind::Text_1_0(value),
        }
    }
}
impl<'top> From<LazyRawTextVersionMarker_1_1<'top>> for LazyRawAnyVersionMarker<'top> {
    fn from(value: LazyRawTextVersionMarker_1_1<'top>) -> Self {
        LazyRawAnyVersionMarker {
            encoding: LazyRawAnyVersionMarkerKind::Text_1_1(value),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyEExpression<'top> {
    encoding: LazyRawAnyEExpressionKind<'top>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawAnyEExpressionKind<'top> {
    Text_1_1(TextEExpression_1_1<'top>),
    Binary_1_1(&'top BinaryEExpression_1_1<'top>),
}

impl<'top> LazyRawAnyEExpression<'top> {
    pub fn encoding(&self) -> IonEncoding {
        use LazyRawAnyEExpressionKind::*;
        match self.encoding {
            Text_1_1(_) => TextEncoding_1_1.encoding(),
            Binary_1_1(_) => BinaryEncoding_1_1.encoding(),
        }
    }
}

impl<'top> From<TextEExpression_1_1<'top>> for LazyRawAnyEExpression<'top> {
    fn from(text_invocation: TextEExpression_1_1<'top>) -> Self {
        LazyRawAnyEExpression {
            encoding: LazyRawAnyEExpressionKind::Text_1_1(text_invocation),
        }
    }
}
impl<'top> From<&'top BinaryEExpression_1_1<'top>> for LazyRawAnyEExpression<'top> {
    fn from(binary_invocation: &'top BinaryEExpression_1_1<'top>) -> Self {
        LazyRawAnyEExpression {
            encoding: LazyRawAnyEExpressionKind::Binary_1_1(binary_invocation),
        }
    }
}

impl<'top> HasSpan<'top> for LazyRawAnyEExpression<'top> {
    fn span(&self) -> Span<'top> {
        use LazyRawAnyEExpressionKind::*;
        match self.encoding {
            Text_1_1(m) => m.span(),
            Binary_1_1(m) => m.span(),
        }
    }
}

impl<'top> HasRange for LazyRawAnyEExpression<'top> {
    fn range(&self) -> Range<usize> {
        use LazyRawAnyEExpressionKind::*;
        match self.encoding {
            Text_1_1(m) => m.range(),
            Binary_1_1(m) => m.range(),
        }
    }
}

impl<'top> RawEExpression<'top, AnyEncoding> for LazyRawAnyEExpression<'top> {
    type RawArgumentsIterator = AnyEExpArgsIterator<'top>;
    type ArgGroup = AnyEExpArgGroup<'top>;

    fn id(self) -> MacroIdRef<'top> {
        use LazyRawAnyEExpressionKind::*;
        match self.encoding {
            Text_1_1(ref m) => m.id(),
            Binary_1_1(m) => m.id(),
        }
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator {
        use LazyRawAnyEExpressionKind::*;
        match self.encoding {
            Text_1_1(e) => AnyEExpArgsIterator {
                encoding: LazyRawAnyEExpArgsIteratorKind::Text_1_1(e.raw_arguments()),
            },
            Binary_1_1(e) => AnyEExpArgsIterator {
                encoding: LazyRawAnyEExpArgsIteratorKind::Binary_1_1(e.raw_arguments()),
            },
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct AnyEExpArgGroup<'top> {
    kind: AnyEExpArgGroupKind<'top>,
}

#[derive(Copy, Clone, Debug)]
pub enum AnyEExpArgGroupKind<'top> {
    Text_1_1(TextEExpArgGroup<'top>),
    Binary_1_1(BinaryEExpArgGroup<'top>),
}

impl<'top> HasRange for AnyEExpArgGroup<'top> {
    fn range(&self) -> Range<usize> {
        match self.kind {
            AnyEExpArgGroupKind::Text_1_1(group) => group.range(),
            AnyEExpArgGroupKind::Binary_1_1(group) => group.range(),
        }
    }
}

impl<'top> HasSpan<'top> for AnyEExpArgGroup<'top> {
    fn span(&self) -> Span<'top> {
        match self.kind {
            AnyEExpArgGroupKind::Text_1_1(group) => group.span(),
            AnyEExpArgGroupKind::Binary_1_1(group) => group.span(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct AnyEExpArgGroupIterator<'top> {
    kind: AnyEExpArgGroupIteratorKind<'top>,
}

impl<
        'top,
        D: Decoder<Value<'top> = LazyRawAnyValue<'top>, EExp<'top> = LazyRawAnyEExpression<'top>>,
    > EExpArgGroupIterator<'top, D> for AnyEExpArgGroupIterator<'top>
{
    fn is_exhausted(&self) -> bool {
        match self.kind {
            AnyEExpArgGroupIteratorKind::Text_1_1(ref i) => i.is_exhausted(),
            AnyEExpArgGroupIteratorKind::Binary_1_1(ref i) => i.is_exhausted(),
        }
    }
}

impl<'top> IntoIterator for AnyEExpArgGroup<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, AnyEncoding>>;
    type IntoIter = AnyEExpArgGroupIterator<'top>;

    fn into_iter(self) -> Self::IntoIter {
        match self.kind {
            AnyEExpArgGroupKind::Text_1_1(group) => AnyEExpArgGroupIterator {
                kind: AnyEExpArgGroupIteratorKind::Text_1_1(group.into_iter()),
            },
            AnyEExpArgGroupKind::Binary_1_1(group) => AnyEExpArgGroupIterator {
                kind: AnyEExpArgGroupIteratorKind::Binary_1_1(group.into_iter()),
            },
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum AnyEExpArgGroupIteratorKind<'top> {
    Text_1_1(TextEExpArgGroupIterator<'top>),
    Binary_1_1(BinaryEExpArgGroupIterator<'top>),
}

impl<'top> Iterator for AnyEExpArgGroupIterator<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, AnyEncoding>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.kind {
            AnyEExpArgGroupIteratorKind::Text_1_1(ref mut i) => {
                Some(Ok(try_next!(i.next()).into()))
            }
            AnyEExpArgGroupIteratorKind::Binary_1_1(ref mut i) => {
                Some(Ok(try_next!(i.next()).into()))
            }
        }
    }
}

impl<'top> EExpressionArgGroup<'top, AnyEncoding> for AnyEExpArgGroup<'top> {
    type Iterator = AnyEExpArgGroupIterator<'top>;

    fn encoding(&self) -> ParameterEncoding {
        match self.kind {
            AnyEExpArgGroupKind::Text_1_1(g) => g.encoding(),
            AnyEExpArgGroupKind::Binary_1_1(g) => g.encoding(),
        }
    }

    fn resolve(self, context: EncodingContextRef<'top>) -> ArgGroup<'top, AnyEncoding> {
        ArgGroup::new(self, context)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum LazyRawAnyEExpArgsIteratorKind<'top> {
    Text_1_1(
        <TextEExpression_1_1<'top> as RawEExpression<
                'top,
                TextEncoding_1_1,
            >>::RawArgumentsIterator,
    ),
    Binary_1_1(
        <&'top BinaryEExpression_1_1<'top> as RawEExpression<
            'top,
            BinaryEncoding_1_1,
        >>::RawArgumentsIterator,
    ),
}

#[derive(Copy, Clone, Debug)]
pub struct AnyEExpArgsIterator<'top> {
    encoding: LazyRawAnyEExpArgsIteratorKind<'top>,
}

impl<'top> Iterator for AnyEExpArgsIterator<'top> {
    type Item = IonResult<EExpArg<'top, AnyEncoding>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.encoding {
            LazyRawAnyEExpArgsIteratorKind::Text_1_1(ref mut iter) => {
                let arg = try_next!(iter.next());
                use EExpArgExpr::*;
                let any_expr = match arg.expr() {
                    ValueLiteral(v) => ValueLiteral(LazyRawAnyValue::from(*v)),
                    EExp(e) => EExp(LazyRawAnyEExpression::from(*e)),
                    ArgGroup(g) => ArgGroup(AnyEExpArgGroup {
                        kind: AnyEExpArgGroupKind::Text_1_1(*g),
                    }),
                };
                Some(Ok(EExpArg::new(arg.encoding(), any_expr)))
            }
            LazyRawAnyEExpArgsIteratorKind::Binary_1_1(ref mut iter) => {
                let arg = try_next!(iter.next());
                use EExpArgExpr::*;
                let any_expr = match arg.expr() {
                    ValueLiteral(v) => ValueLiteral(LazyRawAnyValue::from(*v)),
                    EExp(e) => EExp(LazyRawAnyEExpression::from(*e)),
                    ArgGroup(g) => ArgGroup(AnyEExpArgGroup {
                        kind: AnyEExpArgGroupKind::Binary_1_1(*g),
                    }),
                };
                Some(Ok(EExpArg::new(arg.encoding(), any_expr)))
            }
        }
    }
}

// ===== Readers ======

/// A lazy raw reader that can decode both text and binary Ion.
pub struct LazyRawAnyReader<'data> {
    // If the reader encounters an IVM that changes the encoding, the new encoding will be stored
    // here until `next()` is called again, at which point the reader will be swapped out for one
    // that can read the new encoding.
    new_encoding: Option<IonEncoding>,
    encoding_reader: RawReaderKind<'data>,
}

impl<'data> LazyRawAnyReader<'data> {
    fn detect_encoding(data: &[u8]) -> IonEncoding {
        const BINARY_1_0_IVM: &[u8] = &[0xEA, 0x01, 0x00, 0xE0];

        match *data {
            [0xE0, 0x01, 0x00, 0xEA, ..] => IonEncoding::Binary_1_0,
            [0xE0, 0x01, 0x01, 0xEA, ..] => IonEncoding::Binary_1_1,
            _ => IonEncoding::Text_1_0,
        }
    }
}

impl<'data> From<RawReaderKind<'data>> for LazyRawAnyReader<'data> {
    fn from(encoding: RawReaderKind<'data>) -> Self {
        Self {
            new_encoding: None,
            encoding_reader: encoding,
        }
    }
}

pub enum RawReaderKind<'data> {
    Text_1_0(LazyRawTextReader_1_0<'data>),
    Binary_1_0(LazyRawBinaryReader_1_0<'data>),
    Text_1_1(LazyRawTextReader_1_1<'data>),
    Binary_1_1(LazyRawBinaryReader_1_1<'data>),
}

impl<'data> RawReaderKind<'data> {
    fn resume_at_offset(
        data: &'data [u8],
        stream_offset: usize,
        encoding_hint: IonEncoding,
    ) -> RawReaderKind {
        use IonEncoding::*;
        match encoding_hint {
            Text_1_0 => RawReaderKind::Text_1_0(LazyRawTextReader_1_0::resume_at_offset(
                data,
                stream_offset,
                encoding_hint,
            )),
            Binary_1_0 => RawReaderKind::Binary_1_0(LazyRawBinaryReader_1_0::resume_at_offset(
                data,
                stream_offset,
                encoding_hint,
            )),
            Text_1_1 => RawReaderKind::Text_1_1(LazyRawTextReader_1_1::resume_at_offset(
                data,
                stream_offset,
                encoding_hint,
            )),
            Binary_1_1 => RawReaderKind::Binary_1_1(LazyRawBinaryReader_1_1::resume_at_offset(
                data,
                stream_offset,
                encoding_hint,
            )),
        }
    }
}

#[derive(Default, Debug, Copy, Clone, PartialEq)]
#[non_exhaustive]
pub enum IonEncoding {
    // In the absence of a binary IVM, readers must assume Ion 1.0 text data until a
    // text Ion 1.1 version marker is found.
    #[default]
    Text_1_0,
    Binary_1_0,
    Text_1_1,
    Binary_1_1,
}

impl IonEncoding {
    pub fn is_text(&self) -> bool {
        use IonEncoding::*;
        matches!(*self, Text_1_0 | Text_1_1)
    }

    pub fn is_binary(&self) -> bool {
        use IonEncoding::*;
        matches!(*self, Binary_1_0 | Binary_1_1)
    }

    pub fn name(&self) -> &str {
        use IonEncoding::*;
        match self {
            Text_1_0 => TextEncoding_1_0::name(),
            Binary_1_0 => BinaryEncoding_1_0::name(),
            Text_1_1 => TextEncoding_1_1::name(),
            Binary_1_1 => BinaryEncoding_1_1::name(),
        }
    }

    pub fn version(&self) -> IonVersion {
        use IonEncoding::*;
        match self {
            Text_1_0 | Binary_1_0 => IonVersion::v1_0,
            Text_1_1 | Binary_1_1 => IonVersion::v1_1,
        }
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub enum IonVersion {
    #[default]
    v1_0,
    v1_1,
}

impl IonVersion {
    pub fn major_minor(&self) -> (u8, u8) {
        use IonVersion::*;
        match self {
            v1_0 => (1, 0),
            v1_1 => (1, 1),
        }
    }
}

impl<'data> From<LazyRawTextReader_1_0<'data>> for LazyRawAnyReader<'data> {
    fn from(reader: LazyRawTextReader_1_0<'data>) -> Self {
        RawReaderKind::Text_1_0(reader).into()
    }
}

impl<'data> From<LazyRawTextReader_1_1<'data>> for LazyRawAnyReader<'data> {
    fn from(reader: LazyRawTextReader_1_1<'data>) -> Self {
        RawReaderKind::Text_1_1(reader).into()
    }
}

impl<'data> From<LazyRawBinaryReader_1_0<'data>> for LazyRawAnyReader<'data> {
    fn from(reader: LazyRawBinaryReader_1_0<'data>) -> Self {
        RawReaderKind::Binary_1_0(reader).into()
    }
}

impl<'data> From<LazyRawBinaryReader_1_1<'data>> for LazyRawAnyReader<'data> {
    fn from(reader: LazyRawBinaryReader_1_1<'data>) -> Self {
        RawReaderKind::Binary_1_1(reader).into()
    }
}

impl<'data> LazyRawReader<'data, AnyEncoding> for LazyRawAnyReader<'data> {
    fn new(data: &'data [u8]) -> Self {
        Self::resume_at_offset(data, 0, IonEncoding::default())
    }

    fn resume_at_offset(data: &'data [u8], offset: usize, mut encoding_hint: IonEncoding) -> Self {
        if offset == 0 {
            // If we're at the beginning of the stream, the provided `encoding_hint` may be a
            // default. We need to inspect the bytes to see if we should override it.
            encoding_hint = Self::detect_encoding(data);
        }
        match encoding_hint {
            IonEncoding::Text_1_0 => {
                LazyRawTextReader_1_0::resume_at_offset(data, offset, encoding_hint).into()
            }
            IonEncoding::Binary_1_0 => {
                LazyRawBinaryReader_1_0::resume_at_offset(data, offset, encoding_hint).into()
            }
            IonEncoding::Text_1_1 => {
                LazyRawTextReader_1_1::resume_at_offset(data, offset, encoding_hint).into()
            }
            IonEncoding::Binary_1_1 => {
                LazyRawBinaryReader_1_1::resume_at_offset(data, offset, encoding_hint).into()
            }
        }
    }

    fn stream_data(&self) -> (&'data [u8], usize, IonEncoding) {
        use RawReaderKind::*;
        let (remaining_data, stream_offset, mut encoding) = match &self.encoding_reader {
            Text_1_0(r) => r.stream_data(),
            Binary_1_0(r) => r.stream_data(),
            Text_1_1(r) => r.stream_data(),
            Binary_1_1(r) => r.stream_data(),
        };
        // If we hit an IVM that changed the encoding but we haven't changed our reader yet,
        // we still want to report the new encoding.
        if let Some(new_encoding) = self.new_encoding {
            encoding = new_encoding;
        }
        (remaining_data, stream_offset, encoding)
    }

    fn next<'top>(
        &'top mut self,
        context: EncodingContextRef<'top>,
    ) -> IonResult<LazyRawStreamItem<'top, AnyEncoding>>
    where
        'data: 'top,
    {
        // If we previously ran into an IVM that changed the stream encoding, replace our reader
        // with one that can read the new encoding.
        if let Some(new_encoding) = self.new_encoding.take() {
            let (remaining_data, stream_offset, _) = self.stream_data();
            let new_encoding_reader =
                RawReaderKind::resume_at_offset(remaining_data, stream_offset, new_encoding);
            self.encoding_reader = new_encoding_reader;
        }

        use RawReaderKind::*;
        let item: LazyRawStreamItem<AnyEncoding> = match &mut self.encoding_reader {
            Text_1_0(r) => r.next(context)?.into(),
            Binary_1_0(r) => r.next()?.into(),
            Text_1_1(r) => r.next(context)?.into(),
            Binary_1_1(r) => r.next(context)?.into(),
        };

        // If this item is an IVM:
        //   * the encoding context will be reset, but this is handled by higher-level readers.
        //   * the encoding itself may change, and we need to handle that at this level.
        if let RawStreamItem::VersionMarker(ivm) = item {
            let ivm_old_encoding = ivm.stream_encoding_before_marker();
            let ivm_new_encoding = ivm.stream_encoding_after_marker()?;
            if ivm_new_encoding != ivm_old_encoding {
                // Save the new encoding; when `next()` is called again, we'll make a new reader.
                self.new_encoding = Some(ivm_new_encoding);
            }
        }

        Ok(item)
    }

    fn position(&self) -> usize {
        use RawReaderKind::*;
        match &self.encoding_reader {
            Text_1_0(r) => r.position(),
            Binary_1_0(r) => r.position(),
            Text_1_1(r) => r.position(),
            Binary_1_1(r) => r.position(),
        }
    }

    fn encoding(&self) -> IonEncoding {
        use RawReaderKind::*;
        // If we hit an IVM that changed the encoding but we haven't changed our reader yet,
        // we still want to report the new encoding. This is a niche case -- it can only arise
        // when the reader has hit an IVM (in which case `next()` mutably borrowed the reader
        // and `reader.encoding()` cannot be called) and then dropped the IVM. At that point,
        // the reader is available again and has moved beyond the IVM, so the new encoding is in
        // effect even though we have not encountered our first item in the new encoding.
        if let Some(new_encoding) = self.new_encoding {
            return new_encoding;
        }
        match &self.encoding_reader {
            Text_1_0(_) => IonEncoding::Text_1_0,
            Binary_1_0(_) => IonEncoding::Binary_1_0,
            Text_1_1(_) => IonEncoding::Text_1_1,
            Binary_1_1(_) => IonEncoding::Binary_1_1,
        }
    }
}

// ===== Values ======

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyValue<'top> {
    encoding: LazyRawValueKind<'top>,
}

impl<'top> LazyRawAnyValue<'top> {
    /// Returns an enum indicating the encoding that backs this lazy value.
    #[cfg(feature = "experimental-tooling-apis")]
    pub fn kind(&self) -> LazyRawValueKind<'top> {
        self.encoding
    }

    pub fn encoding(&self) -> IonEncoding {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(_) => TextEncoding_1_0.encoding(),
            Binary_1_0(_) => BinaryEncoding_1_0.encoding(),
            Text_1_1(_) => TextEncoding_1_1.encoding(),
            Binary_1_1(_) => BinaryEncoding_1_1.encoding(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawValueKind<'top> {
    Text_1_0(LazyRawTextValue_1_0<'top>),
    Binary_1_0(LazyRawBinaryValue_1_0<'top>),
    Text_1_1(LazyRawTextValue_1_1<'top>),
    Binary_1_1(&'top LazyRawBinaryValue_1_1<'top>),
}

impl<'top> From<LazyRawTextValue_1_0<'top>> for LazyRawAnyValue<'top> {
    fn from(value: LazyRawTextValue_1_0<'top>) -> Self {
        LazyRawAnyValue {
            encoding: LazyRawValueKind::Text_1_0(value),
        }
    }
}

impl<'top> From<LazyRawBinaryValue_1_0<'top>> for LazyRawAnyValue<'top> {
    fn from(value: LazyRawBinaryValue_1_0<'top>) -> Self {
        LazyRawAnyValue {
            encoding: LazyRawValueKind::Binary_1_0(value),
        }
    }
}

impl<'top> From<LazyRawTextValue_1_1<'top>> for LazyRawAnyValue<'top> {
    fn from(value: LazyRawTextValue_1_1<'top>) -> Self {
        LazyRawAnyValue {
            encoding: LazyRawValueKind::Text_1_1(value),
        }
    }
}

impl<'top> From<&'top LazyRawBinaryValue_1_1<'top>> for LazyRawAnyValue<'top> {
    fn from(value: &'top LazyRawBinaryValue_1_1<'top>) -> Self {
        LazyRawAnyValue {
            encoding: LazyRawValueKind::Binary_1_1(value),
        }
    }
}

impl<'top> From<LazyRawValueExpr<'top, TextEncoding_1_0>> for LazyRawValueExpr<'top, AnyEncoding> {
    fn from(value: LazyRawValueExpr<'top, TextEncoding_1_0>) -> Self {
        match value {
            RawValueExpr::ValueLiteral(v) => RawValueExpr::ValueLiteral(v.into()),
            RawValueExpr::EExp(_) => unreachable!("macro invocation in text Ion 1.0"),
        }
    }
}

impl<'top> From<LazyRawValueExpr<'top, BinaryEncoding_1_0>>
    for LazyRawValueExpr<'top, AnyEncoding>
{
    fn from(value: LazyRawValueExpr<'top, BinaryEncoding_1_0>) -> Self {
        match value {
            RawValueExpr::ValueLiteral(v) => RawValueExpr::ValueLiteral(v.into()),
            RawValueExpr::EExp(_) => unreachable!("macro invocation in binary Ion 1.0"),
        }
    }
}

impl<'top> From<LazyRawValueExpr<'top, TextEncoding_1_1>> for LazyRawValueExpr<'top, AnyEncoding> {
    fn from(value: LazyRawValueExpr<'top, TextEncoding_1_1>) -> Self {
        match value {
            RawValueExpr::ValueLiteral(v) => RawValueExpr::ValueLiteral(v.into()),
            RawValueExpr::EExp(m) => {
                let invocation = LazyRawAnyEExpression {
                    encoding: LazyRawAnyEExpressionKind::Text_1_1(m),
                };
                RawValueExpr::EExp(invocation)
            }
        }
    }
}

impl<'top> From<LazyRawValueExpr<'top, BinaryEncoding_1_1>>
    for LazyRawValueExpr<'top, AnyEncoding>
{
    fn from(value: LazyRawValueExpr<'top, BinaryEncoding_1_1>) -> Self {
        match value {
            RawValueExpr::ValueLiteral(v) => RawValueExpr::ValueLiteral(v.into()),
            RawValueExpr::EExp(m) => {
                let invocation = LazyRawAnyEExpression {
                    encoding: LazyRawAnyEExpressionKind::Binary_1_1(m),
                };
                RawValueExpr::EExp(invocation)
            }
        }
    }
}

impl<'top> From<RawValueRef<'top, TextEncoding_1_0>> for RawValueRef<'top, AnyEncoding> {
    fn from(value: RawValueRef<'top, TextEncoding_1_0>) -> Self {
        use RawValueRef::*;
        match value {
            Null(ion_type) => Null(ion_type),
            Bool(value) => Bool(value),
            Int(value) => Int(value),
            Float(value) => Float(value),
            Decimal(value) => Decimal(value),
            Timestamp(value) => Timestamp(value),
            String(value) => String(value),
            Symbol(value) => Symbol(value),
            Blob(value) => Blob(value),
            Clob(value) => Clob(value),
            SExp(value) => SExp(value.into()),
            List(value) => List(value.into()),
            Struct(value) => Struct(value.into()),
        }
    }
}

impl<'top> From<RawValueRef<'top, BinaryEncoding_1_0>> for RawValueRef<'top, AnyEncoding> {
    fn from(value: RawValueRef<'top, BinaryEncoding_1_0>) -> Self {
        use RawValueRef::*;
        match value {
            Null(ion_type) => Null(ion_type),
            Bool(value) => Bool(value),
            Int(value) => Int(value),
            Float(value) => Float(value),
            Decimal(value) => Decimal(value),
            Timestamp(value) => Timestamp(value),
            String(value) => String(value),
            Symbol(value) => Symbol(value),
            Blob(value) => Blob(value),
            Clob(value) => Clob(value),
            SExp(value) => SExp(value.into()),
            List(value) => List(value.into()),
            Struct(value) => Struct(value.into()),
        }
    }
}

impl<'top> From<RawValueRef<'top, TextEncoding_1_1>> for RawValueRef<'top, AnyEncoding> {
    fn from(value: RawValueRef<'top, TextEncoding_1_1>) -> Self {
        use RawValueRef::*;
        match value {
            Null(ion_type) => Null(ion_type),
            Bool(value) => Bool(value),
            Int(value) => Int(value),
            Float(value) => Float(value),
            Decimal(value) => Decimal(value),
            Timestamp(value) => Timestamp(value),
            String(value) => String(value),
            Symbol(value) => Symbol(value),
            Blob(value) => Blob(value),
            Clob(value) => Clob(value),
            SExp(value) => SExp(value.into()),
            List(value) => List(value.into()),
            Struct(value) => Struct(value.into()),
        }
    }
}

impl<'top> From<RawValueRef<'top, BinaryEncoding_1_1>> for RawValueRef<'top, AnyEncoding> {
    fn from(value: RawValueRef<'top, BinaryEncoding_1_1>) -> Self {
        use RawValueRef::*;
        match value {
            Null(ion_type) => Null(ion_type),
            Bool(value) => Bool(value),
            Int(value) => Int(value),
            Float(value) => Float(value),
            Decimal(value) => Decimal(value),
            Timestamp(value) => Timestamp(value),
            String(value) => String(value),
            Symbol(value) => Symbol(value),
            Blob(value) => Blob(value),
            Clob(value) => Clob(value),
            SExp(value) => SExp(value.into()),
            List(value) => List(value.into()),
            Struct(value) => Struct(value.into()),
        }
    }
}

impl<'top> From<LazyRawStreamItem<'top, TextEncoding_1_0>>
    for LazyRawStreamItem<'top, AnyEncoding>
{
    fn from(value: LazyRawStreamItem<'top, TextEncoding_1_0>) -> Self {
        match value {
            LazyRawStreamItem::<TextEncoding_1_0>::VersionMarker(marker) => {
                LazyRawStreamItem::<AnyEncoding>::VersionMarker(marker.into())
            }
            LazyRawStreamItem::<TextEncoding_1_0>::Value(value) => {
                LazyRawStreamItem::<AnyEncoding>::Value(value.into())
            }
            LazyRawStreamItem::<TextEncoding_1_0>::EExp(_) => {
                unreachable!("Ion 1.0 does not support macro invocations")
            }
            LazyRawStreamItem::<TextEncoding_1_0>::EndOfStream(end) => {
                LazyRawStreamItem::<AnyEncoding>::EndOfStream(end)
            }
        }
    }
}

impl<'top> From<LazyRawStreamItem<'top, BinaryEncoding_1_0>>
    for LazyRawStreamItem<'top, AnyEncoding>
{
    fn from(value: LazyRawStreamItem<'top, BinaryEncoding_1_0>) -> Self {
        match value {
            LazyRawStreamItem::<BinaryEncoding_1_0>::VersionMarker(marker) => {
                LazyRawStreamItem::<AnyEncoding>::VersionMarker(marker.into())
            }
            LazyRawStreamItem::<BinaryEncoding_1_0>::Value(value) => {
                LazyRawStreamItem::<AnyEncoding>::Value(value.into())
            }
            LazyRawStreamItem::<BinaryEncoding_1_0>::EExp(_) => {
                unreachable!("Ion 1.0 does not support macro invocations")
            }
            LazyRawStreamItem::<BinaryEncoding_1_0>::EndOfStream(end) => {
                LazyRawStreamItem::<AnyEncoding>::EndOfStream(end)
            }
        }
    }
}

impl<'top> From<LazyRawStreamItem<'top, TextEncoding_1_1>>
    for LazyRawStreamItem<'top, AnyEncoding>
{
    fn from(value: LazyRawStreamItem<'top, TextEncoding_1_1>) -> Self {
        match value {
            LazyRawStreamItem::<TextEncoding_1_1>::VersionMarker(marker) => {
                LazyRawStreamItem::<AnyEncoding>::VersionMarker(marker.into())
            }
            LazyRawStreamItem::<TextEncoding_1_1>::Value(value) => {
                LazyRawStreamItem::<AnyEncoding>::Value(value.into())
            }
            LazyRawStreamItem::<TextEncoding_1_1>::EExp(invocation) => {
                LazyRawStreamItem::<AnyEncoding>::EExp(LazyRawAnyEExpression {
                    encoding: LazyRawAnyEExpressionKind::Text_1_1(invocation),
                })
            }
            LazyRawStreamItem::<TextEncoding_1_1>::EndOfStream(end) => {
                LazyRawStreamItem::<AnyEncoding>::EndOfStream(end)
            }
        }
    }
}

impl<'top> From<LazyRawStreamItem<'top, BinaryEncoding_1_1>>
    for LazyRawStreamItem<'top, AnyEncoding>
{
    fn from(value: LazyRawStreamItem<'top, BinaryEncoding_1_1>) -> Self {
        match value {
            LazyRawStreamItem::<BinaryEncoding_1_1>::VersionMarker(marker) => {
                LazyRawStreamItem::<AnyEncoding>::VersionMarker(marker.into())
            }
            LazyRawStreamItem::<BinaryEncoding_1_1>::Value(value) => {
                LazyRawStreamItem::<AnyEncoding>::Value(value.into())
            }
            LazyRawStreamItem::<BinaryEncoding_1_1>::EExp(eexp) => {
                LazyRawStreamItem::<AnyEncoding>::EExp(eexp.into())
            }
            LazyRawStreamItem::<BinaryEncoding_1_1>::EndOfStream(end) => {
                LazyRawStreamItem::<AnyEncoding>::EndOfStream(end)
            }
        }
    }
}

impl<'top> HasSpan<'top> for LazyRawAnyValue<'top> {
    fn span(&self) -> Span<'top> {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.span(),
            Binary_1_0(v) => v.span(),
            Text_1_1(v) => v.span(),
            Binary_1_1(v) => v.span(),
        }
    }
}

impl<'top> HasRange for LazyRawAnyValue<'top> {
    fn range(&self) -> Range<usize> {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.range(),
            Binary_1_0(v) => v.range(),
            Text_1_1(v) => v.range(),
            Binary_1_1(v) => v.range(),
        }
    }
}

impl<'top> LazyRawValue<'top, AnyEncoding> for LazyRawAnyValue<'top> {
    fn ion_type(&self) -> IonType {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.ion_type(),
            Binary_1_0(v) => v.ion_type(),
            Text_1_1(v) => v.ion_type(),
            Binary_1_1(v) => v.ion_type(),
        }
    }

    fn is_null(&self) -> bool {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.is_null(),
            Binary_1_0(v) => v.is_null(),
            Text_1_1(v) => v.is_null(),
            Binary_1_1(v) => v.is_null(),
        }
    }

    fn has_annotations(&self) -> bool {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.has_annotations(),
            Binary_1_0(v) => v.has_annotations(),
            Text_1_1(v) => v.has_annotations(),
            Binary_1_1(v) => v.has_annotations(),
        }
    }

    fn annotations(&self) -> RawAnyAnnotationsIterator<'top> {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Text_1_0(v.annotations()),
            },
            Binary_1_0(v) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Binary_1_0(v.annotations()),
            },
            Text_1_1(v) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Text_1_1(v.annotations()),
            },
            Binary_1_1(v) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Binary_1_1(v.annotations()),
            },
        }
    }

    fn read(&self) -> IonResult<RawValueRef<'top, AnyEncoding>> {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => Ok(v.read()?.into()),
            Binary_1_0(v) => Ok(v.read()?.into()),
            Text_1_1(v) => Ok(v.read()?.into()),
            Binary_1_1(v) => Ok(v.read()?.into()),
        }
    }

    fn annotations_span(&self) -> Span<'top> {
        match &self.encoding {
            LazyRawValueKind::Text_1_0(v) => v.annotations_span(),
            LazyRawValueKind::Binary_1_0(v) => v.annotations_span(),
            LazyRawValueKind::Text_1_1(v) => v.annotations_span(),
            LazyRawValueKind::Binary_1_1(v) => v.annotations_span(),
        }
    }

    fn value_span(&self) -> Span<'top> {
        match &self.encoding {
            LazyRawValueKind::Text_1_0(v) => v.value_span(),
            LazyRawValueKind::Binary_1_0(v) => v.value_span(),
            LazyRawValueKind::Text_1_1(v) => v.value_span(),
            LazyRawValueKind::Binary_1_1(v) => v.value_span(),
        }
    }
}

// ===== Annotations =====

pub struct RawAnyAnnotationsIterator<'top> {
    encoding: RawAnnotationsIteratorKind<'top>,
}

pub enum RawAnnotationsIteratorKind<'top> {
    Text_1_0(RawTextAnnotationsIterator<'top>),
    Binary_1_0(RawBinaryAnnotationsIterator_1_0<'top>),
    Text_1_1(RawTextAnnotationsIterator<'top>),
    Binary_1_1(RawBinaryAnnotationsIterator_1_1<'top>),
}

impl<'top> Iterator for RawAnyAnnotationsIterator<'top> {
    type Item = IonResult<RawSymbolRef<'top>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.encoding {
            RawAnnotationsIteratorKind::Text_1_0(i) => i.next(),
            RawAnnotationsIteratorKind::Binary_1_0(i) => i.next(),
            RawAnnotationsIteratorKind::Text_1_1(i) => i.next(),
            RawAnnotationsIteratorKind::Binary_1_1(i) => i.next(),
        }
    }
}

// ===== Lists ======

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyList<'top> {
    encoding: LazyRawListKind<'top>,
}

impl<'top> LazyRawAnyList<'top> {
    pub fn as_value(&self) -> LazyRawAnyValue<'top> {
        use LazyRawListKind::*;
        match self.encoding {
            Text_1_0(l) => l.as_value().into(),
            Binary_1_0(l) => l.as_value().into(),
            Text_1_1(l) => l.as_value().into(),
            Binary_1_1(l) => l.as_value().into(),
        }
    }
}

impl<'top> LazyRawAnyList<'top> {
    pub fn kind(&self) -> LazyRawListKind<'top> {
        self.encoding
    }
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawListKind<'top> {
    Text_1_0(LazyRawTextList_1_0<'top>),
    Binary_1_0(LazyRawBinaryList_1_0<'top>),
    Text_1_1(LazyRawTextList_1_1<'top>),
    Binary_1_1(LazyRawBinaryList_1_1<'top>),
}

impl<'top> LazyContainerPrivate<'top, AnyEncoding> for LazyRawAnyList<'top> {
    fn from_value(value: LazyRawAnyValue<'top>) -> Self {
        match value.encoding {
            LazyRawValueKind::Text_1_0(v) => LazyRawAnyList {
                encoding: LazyRawListKind::Text_1_0(LazyRawTextList_1_0::from_value(v)),
            },
            LazyRawValueKind::Binary_1_0(v) => LazyRawAnyList {
                encoding: LazyRawListKind::Binary_1_0(LazyRawBinaryList_1_0::from_value(v)),
            },
            LazyRawValueKind::Text_1_1(v) => LazyRawAnyList {
                encoding: LazyRawListKind::Text_1_1(LazyRawTextList_1_1::from_value(v)),
            },
            LazyRawValueKind::Binary_1_1(v) => LazyRawAnyList {
                encoding: LazyRawListKind::Binary_1_1(LazyRawBinaryList_1_1::from_value(v)),
            },
        }
    }
}

pub struct RawAnyListIterator<'data> {
    encoding: RawAnyListIteratorKind<'data>,
}

pub enum RawAnyListIteratorKind<'data> {
    Text_1_0(RawTextListIterator_1_0<'data>),
    Binary_1_0(RawBinarySequenceIterator_1_0<'data>),
    Text_1_1(RawTextSequenceCacheIterator_1_1<'data>),
    Binary_1_1(RawBinarySequenceIterator_1_1<'data>),
}

impl<'data> Iterator for RawAnyListIterator<'data> {
    type Item = IonResult<LazyRawValueExpr<'data, AnyEncoding>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.encoding {
            RawAnyListIteratorKind::Text_1_0(i) => i
                .next()
                .map(|value_result| value_result.map(|value| value.into())),
            RawAnyListIteratorKind::Binary_1_0(i) => i
                .next()
                .map(|value_result| value_result.map(|value| value.into())),
            RawAnyListIteratorKind::Text_1_1(i) => i
                .next()
                .map(|value_result| value_result.map(|value| value.into())),
            RawAnyListIteratorKind::Binary_1_1(i) => i
                .next()
                .map(|value_result| value_result.map(|value| value.into())),
        }
    }
}

impl<'top> LazyRawContainer<'top, AnyEncoding> for LazyRawAnyList<'top> {
    fn as_value(&self) -> <AnyEncoding as Decoder>::Value<'top> {
        match &self.encoding {
            LazyRawListKind::Text_1_0(s) => s.as_value().into(),
            LazyRawListKind::Binary_1_0(s) => s.as_value().into(),
            LazyRawListKind::Text_1_1(s) => s.as_value().into(),
            LazyRawListKind::Binary_1_1(s) => s.as_value().into(),
        }
    }
}

impl<'top> LazyRawSequence<'top, AnyEncoding> for LazyRawAnyList<'top> {
    type Iterator = RawAnyListIterator<'top>;

    fn annotations(&self) -> <AnyEncoding as Decoder>::AnnotationsIterator<'top> {
        self.as_value().annotations()
    }

    fn ion_type(&self) -> IonType {
        match &self.encoding {
            LazyRawListKind::Text_1_0(s) => s.ion_type(),
            LazyRawListKind::Binary_1_0(s) => s.ion_type(),
            LazyRawListKind::Text_1_1(s) => s.ion_type(),
            LazyRawListKind::Binary_1_1(s) => s.ion_type(),
        }
    }

    fn iter(&self) -> Self::Iterator {
        match &self.encoding {
            LazyRawListKind::Text_1_0(s) => RawAnyListIterator {
                encoding: RawAnyListIteratorKind::Text_1_0(s.iter()),
            },
            LazyRawListKind::Binary_1_0(s) => RawAnyListIterator {
                encoding: RawAnyListIteratorKind::Binary_1_0(s.iter()),
            },
            LazyRawListKind::Text_1_1(s) => RawAnyListIterator {
                encoding: RawAnyListIteratorKind::Text_1_1(s.iter()),
            },
            LazyRawListKind::Binary_1_1(s) => RawAnyListIterator {
                encoding: RawAnyListIteratorKind::Binary_1_1(s.iter()),
            },
        }
    }
}

impl<'data> From<LazyRawTextList_1_0<'data>> for LazyRawAnyList<'data> {
    fn from(value: LazyRawTextList_1_0<'data>) -> Self {
        LazyRawAnyList {
            encoding: LazyRawListKind::Text_1_0(value),
        }
    }
}

impl<'data> From<LazyRawBinaryList_1_0<'data>> for LazyRawAnyList<'data> {
    fn from(value: LazyRawBinaryList_1_0<'data>) -> Self {
        LazyRawAnyList {
            encoding: LazyRawListKind::Binary_1_0(value),
        }
    }
}

impl<'data> From<LazyRawTextList_1_1<'data>> for LazyRawAnyList<'data> {
    fn from(value: LazyRawTextList_1_1<'data>) -> Self {
        LazyRawAnyList {
            encoding: LazyRawListKind::Text_1_1(value),
        }
    }
}

impl<'data> From<LazyRawBinaryList_1_1<'data>> for LazyRawAnyList<'data> {
    fn from(value: LazyRawBinaryList_1_1<'data>) -> Self {
        LazyRawAnyList {
            encoding: LazyRawListKind::Binary_1_1(value),
        }
    }
}

// ===== SExps =====

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnySExp<'data> {
    encoding: LazyRawSExpKind<'data>,
}

impl<'top> LazyRawAnySExp<'top> {
    pub fn kind(&self) -> LazyRawSExpKind<'top> {
        self.encoding
    }
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawSExpKind<'data> {
    Text_1_0(LazyRawTextSExp_1_0<'data>),
    Binary_1_0(LazyRawBinarySExp_1_0<'data>),
    Text_1_1(LazyRawTextSExp_1_1<'data>),
    Binary_1_1(LazyRawBinarySExp_1_1<'data>),
}

impl<'top> LazyRawContainer<'top, AnyEncoding> for LazyRawAnySExp<'top> {
    fn as_value(&self) -> <AnyEncoding as Decoder>::Value<'top> {
        use LazyRawSExpKind::*;
        match self.encoding {
            Text_1_0(s) => s.as_value().into(),
            Binary_1_0(s) => s.as_value().into(),
            Text_1_1(s) => s.as_value().into(),
            Binary_1_1(s) => s.as_value().into(),
        }
    }
}

impl<'data> LazyContainerPrivate<'data, AnyEncoding> for LazyRawAnySExp<'data> {
    fn from_value(value: LazyRawAnyValue<'data>) -> Self {
        match value.encoding {
            LazyRawValueKind::Text_1_0(v) => LazyRawAnySExp {
                encoding: LazyRawSExpKind::Text_1_0(LazyRawTextSExp_1_0::from_value(v)),
            },
            LazyRawValueKind::Binary_1_0(v) => LazyRawAnySExp {
                encoding: LazyRawSExpKind::Binary_1_0(LazyRawBinarySExp_1_0::from_value(v)),
            },
            LazyRawValueKind::Text_1_1(v) => LazyRawAnySExp {
                encoding: LazyRawSExpKind::Text_1_1(LazyRawTextSExp_1_1::from_value(v)),
            },
            LazyRawValueKind::Binary_1_1(v) => LazyRawAnySExp {
                encoding: LazyRawSExpKind::Binary_1_1(LazyRawBinarySExp_1_1::from_value(v)),
            },
        }
    }
}

pub struct RawAnySExpIterator<'data> {
    encoding: RawAnySExpIteratorKind<'data>,
}

pub enum RawAnySExpIteratorKind<'data> {
    Text_1_0(RawTextSExpIterator_1_0<'data>),
    Binary_1_0(RawBinarySequenceIterator_1_0<'data>),
    Text_1_1(RawTextSequenceCacheIterator_1_1<'data>),
    Binary_1_1(RawBinarySequenceIterator_1_1<'data>),
}

impl<'data> Iterator for RawAnySExpIterator<'data> {
    type Item = IonResult<LazyRawValueExpr<'data, AnyEncoding>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.encoding {
            RawAnySExpIteratorKind::Text_1_0(i) => i
                .next()
                .map(|value_result| value_result.map(|value| value.into())),
            RawAnySExpIteratorKind::Binary_1_0(i) => i
                .next()
                .map(|value_result| value_result.map(|value| value.into())),
            RawAnySExpIteratorKind::Text_1_1(i) => i
                .next()
                .map(|value_result| value_result.map(|value| value.into())),
            RawAnySExpIteratorKind::Binary_1_1(i) => i
                .next()
                .map(|value_result| value_result.map(|value| value.into())),
        }
    }
}

impl<'top> LazyRawSequence<'top, AnyEncoding> for LazyRawAnySExp<'top> {
    type Iterator = RawAnySExpIterator<'top>;

    fn annotations(&self) -> <AnyEncoding as Decoder>::AnnotationsIterator<'top> {
        self.as_value().annotations()
    }

    fn ion_type(&self) -> IonType {
        match &self.encoding {
            LazyRawSExpKind::Text_1_0(s) => s.ion_type(),
            LazyRawSExpKind::Binary_1_0(s) => s.ion_type(),
            LazyRawSExpKind::Text_1_1(s) => s.ion_type(),
            LazyRawSExpKind::Binary_1_1(s) => s.ion_type(),
        }
    }

    fn iter(&self) -> Self::Iterator {
        match &self.encoding {
            LazyRawSExpKind::Text_1_0(s) => RawAnySExpIterator {
                encoding: RawAnySExpIteratorKind::Text_1_0(s.iter()),
            },
            LazyRawSExpKind::Binary_1_0(s) => RawAnySExpIterator {
                encoding: RawAnySExpIteratorKind::Binary_1_0(s.iter()),
            },
            LazyRawSExpKind::Text_1_1(s) => RawAnySExpIterator {
                encoding: RawAnySExpIteratorKind::Text_1_1(s.iter()),
            },
            LazyRawSExpKind::Binary_1_1(s) => RawAnySExpIterator {
                encoding: RawAnySExpIteratorKind::Binary_1_1(s.iter()),
            },
        }
    }
}

impl<'data> From<LazyRawTextSExp_1_0<'data>> for LazyRawAnySExp<'data> {
    fn from(value: LazyRawTextSExp_1_0<'data>) -> Self {
        LazyRawAnySExp {
            encoding: LazyRawSExpKind::Text_1_0(value),
        }
    }
}

impl<'data> From<LazyRawBinarySExp_1_0<'data>> for LazyRawAnySExp<'data> {
    fn from(value: LazyRawBinarySExp_1_0<'data>) -> Self {
        LazyRawAnySExp {
            encoding: LazyRawSExpKind::Binary_1_0(value),
        }
    }
}

impl<'data> From<LazyRawTextSExp_1_1<'data>> for LazyRawAnySExp<'data> {
    fn from(value: LazyRawTextSExp_1_1<'data>) -> Self {
        LazyRawAnySExp {
            encoding: LazyRawSExpKind::Text_1_1(value),
        }
    }
}

impl<'data> From<LazyRawBinarySExp_1_1<'data>> for LazyRawAnySExp<'data> {
    fn from(value: LazyRawBinarySExp_1_1<'data>) -> Self {
        LazyRawAnySExp {
            encoding: LazyRawSExpKind::Binary_1_1(value),
        }
    }
}

// ===== Structs =====

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyStruct<'data> {
    encoding: LazyRawStructKind<'data>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawStructKind<'data> {
    Text_1_0(LazyRawTextStruct_1_0<'data>),
    Binary_1_0(LazyRawBinaryStruct_1_0<'data>),
    Text_1_1(LazyRawTextStruct_1_1<'data>),
    Binary_1_1(LazyRawBinaryStruct_1_1<'data>),
}

impl<'top> LazyRawContainer<'top, AnyEncoding> for LazyRawAnyStruct<'top> {
    fn as_value(&self) -> <AnyEncoding as Decoder>::Value<'top> {
        match self.encoding {
            LazyRawStructKind::Text_1_0(s) => s.as_value().into(),
            LazyRawStructKind::Binary_1_0(s) => s.as_value().into(),
            LazyRawStructKind::Text_1_1(s) => s.as_value().into(),
            LazyRawStructKind::Binary_1_1(s) => s.as_value().into(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyFieldName<'data> {
    encoding: LazyRawFieldNameKind<'data>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawFieldNameKind<'data> {
    Text_1_0(LazyRawTextFieldName_1_0<'data>),
    Binary_1_0(LazyRawBinaryFieldName_1_0<'data>),
    Text_1_1(LazyRawTextFieldName_1_1<'data>),
    Binary_1_1(LazyRawBinaryFieldName_1_1<'data>),
}

impl<'top> HasSpan<'top> for LazyRawAnyFieldName<'top> {
    fn span(&self) -> Span<'top> {
        use LazyRawFieldNameKind::*;
        match self.encoding {
            Text_1_0(name) => name.span(),
            Binary_1_0(name) => name.span(),
            Text_1_1(name) => name.span(),
            Binary_1_1(name) => name.span(),
        }
    }
}

impl<'top> HasRange for LazyRawAnyFieldName<'top> {
    fn range(&self) -> Range<usize> {
        use LazyRawFieldNameKind::*;
        match self.encoding {
            Text_1_0(name) => name.range(),
            Binary_1_0(name) => name.range(),
            Text_1_1(name) => name.range(),
            Binary_1_1(name) => name.range(),
        }
    }
}

impl<'top> LazyRawFieldName<'top, AnyEncoding> for LazyRawAnyFieldName<'top> {
    fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        use LazyRawFieldNameKind::*;
        match self.encoding {
            Text_1_0(name) => name.read(),
            Binary_1_0(name) => name.read(),
            Text_1_1(name) => name.read(),
            Binary_1_1(name) => name.read(),
        }
    }
}

impl<'top> From<LazyRawFieldNameKind<'top>> for LazyRawAnyFieldName<'top> {
    fn from(value: LazyRawFieldNameKind<'top>) -> Self {
        LazyRawAnyFieldName { encoding: value }
    }
}

impl<'top> From<LazyRawTextFieldName_1_0<'top>> for LazyRawAnyFieldName<'top> {
    fn from(value: LazyRawTextFieldName_1_0<'top>) -> Self {
        LazyRawFieldNameKind::Text_1_0(value).into()
    }
}

impl<'top> From<LazyRawTextFieldName_1_1<'top>> for LazyRawAnyFieldName<'top> {
    fn from(value: LazyRawTextFieldName_1_1<'top>) -> Self {
        LazyRawFieldNameKind::Text_1_1(value).into()
    }
}

impl<'top> From<LazyRawBinaryFieldName_1_0<'top>> for LazyRawAnyFieldName<'top> {
    fn from(value: LazyRawBinaryFieldName_1_0<'top>) -> Self {
        LazyRawFieldNameKind::Binary_1_0(value).into()
    }
}

impl<'top> From<LazyRawBinaryFieldName_1_1<'top>> for LazyRawAnyFieldName<'top> {
    fn from(value: LazyRawBinaryFieldName_1_1<'top>) -> Self {
        LazyRawFieldNameKind::Binary_1_1(value).into()
    }
}

pub struct RawAnyStructIterator<'data> {
    encoding: RawAnyStructIteratorKind<'data>,
}

pub enum RawAnyStructIteratorKind<'data> {
    Text_1_0(RawTextStructIterator_1_0<'data>),
    Binary_1_0(RawBinaryStructIterator_1_0<'data>),
    Text_1_1(RawTextStructCacheIterator_1_1<'data>),
    Binary_1_1(RawBinaryStructIterator_1_1<'data>),
}

impl<'data> Iterator for RawAnyStructIterator<'data> {
    type Item = IonResult<LazyRawFieldExpr<'data, AnyEncoding>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.encoding {
            RawAnyStructIteratorKind::Text_1_0(i) => i
                .next()
                .map(|field_result| field_result.map(|field| field.into())),
            RawAnyStructIteratorKind::Binary_1_0(i) => i
                .next()
                .map(|field_result| field_result.map(|field| field.into())),
            RawAnyStructIteratorKind::Text_1_1(i) => i
                .next()
                .map(|field_result| field_result.map(|field| field.into())),
            RawAnyStructIteratorKind::Binary_1_1(i) => i
                .next()
                .map(|field_result| field_result.map(|field| field.into())),
        }
    }
}

impl<'data> From<LazyRawFieldExpr<'data, TextEncoding_1_0>>
    for LazyRawFieldExpr<'data, AnyEncoding>
{
    fn from(text_field: LazyRawFieldExpr<'data, TextEncoding_1_0>) -> Self {
        use LazyRawFieldExpr::*;
        match text_field {
            NameValue(name, value) => NameValue(name.into(), value.into()),
            NameEExp(_, _) => unreachable!("(name, e-exp) field in text Ion 1.0"),
            EExp(_) => unreachable!("e-exp field in text Ion 1.0"),
        }
    }
}

impl<'data> From<LazyRawFieldExpr<'data, BinaryEncoding_1_0>>
    for LazyRawFieldExpr<'data, AnyEncoding>
{
    fn from(binary_field: LazyRawFieldExpr<'data, BinaryEncoding_1_0>) -> Self {
        use LazyRawFieldExpr::*;
        match binary_field {
            NameValue(name, value) => NameValue(name.into(), value.into()),
            NameEExp(_, _) => unreachable!("(name, e-exp) field in binary Ion 1.0"),
            EExp(_) => unreachable!("e-exp field in binary Ion 1.0"),
        }
    }
}

impl<'data> From<LazyRawFieldExpr<'data, TextEncoding_1_1>>
    for LazyRawFieldExpr<'data, AnyEncoding>
{
    fn from(text_field: LazyRawFieldExpr<'data, TextEncoding_1_1>) -> Self {
        use LazyRawFieldExpr::*;
        match text_field {
            NameValue(name, value) => NameValue(name.into(), value.into()),
            NameEExp(name, eexp) => NameEExp(name.into(), eexp.into()),
            EExp(eexp) => EExp(eexp.into()),
        }
    }
}

impl<'data> From<LazyRawFieldExpr<'data, BinaryEncoding_1_1>>
    for LazyRawFieldExpr<'data, AnyEncoding>
{
    fn from(binary_field: LazyRawFieldExpr<'data, BinaryEncoding_1_1>) -> Self {
        use LazyRawFieldExpr::*;
        match binary_field {
            NameValue(name, value) => NameValue(name.into(), value.into()),
            NameEExp(_, _) => todo!("(name, e-exp) field in binary Ion 1.1"),
            EExp(_) => todo!("e-exp field in binary Ion 1.1"),
        }
    }
}

impl<'data> LazyContainerPrivate<'data, AnyEncoding> for LazyRawAnyStruct<'data> {
    fn from_value(value: LazyRawAnyValue<'data>) -> Self {
        match value.encoding {
            LazyRawValueKind::Text_1_0(v) => LazyRawAnyStruct {
                encoding: LazyRawStructKind::Text_1_0(LazyRawTextStruct_1_0::from_value(v)),
            },
            LazyRawValueKind::Binary_1_0(v) => LazyRawAnyStruct {
                encoding: LazyRawStructKind::Binary_1_0(LazyRawBinaryStruct_1_0::from_value(v)),
            },
            LazyRawValueKind::Text_1_1(v) => LazyRawAnyStruct {
                encoding: LazyRawStructKind::Text_1_1(LazyRawTextStruct_1_1::from_value(v)),
            },
            LazyRawValueKind::Binary_1_1(v) => LazyRawAnyStruct {
                encoding: LazyRawStructKind::Binary_1_1(LazyRawBinaryStruct_1_1::from_value(v)),
            },
        }
    }
}

impl<'top> LazyRawStruct<'top, AnyEncoding> for LazyRawAnyStruct<'top> {
    type Iterator = RawAnyStructIterator<'top>;

    fn annotations(&self) -> <AnyEncoding as Decoder>::AnnotationsIterator<'top> {
        match &self.encoding {
            LazyRawStructKind::Text_1_0(s) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Text_1_0(s.annotations()),
            },
            LazyRawStructKind::Binary_1_0(s) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Binary_1_0(s.annotations()),
            },
            LazyRawStructKind::Text_1_1(s) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Text_1_1(s.annotations()),
            },
            LazyRawStructKind::Binary_1_1(s) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Binary_1_1(s.annotations()),
            },
        }
    }

    fn iter(&self) -> Self::Iterator {
        match &self.encoding {
            LazyRawStructKind::Text_1_0(s) => RawAnyStructIterator {
                encoding: RawAnyStructIteratorKind::Text_1_0(s.iter()),
            },
            LazyRawStructKind::Binary_1_0(s) => RawAnyStructIterator {
                encoding: RawAnyStructIteratorKind::Binary_1_0(s.iter()),
            },
            LazyRawStructKind::Text_1_1(s) => RawAnyStructIterator {
                encoding: RawAnyStructIteratorKind::Text_1_1(s.iter()),
            },
            LazyRawStructKind::Binary_1_1(s) => RawAnyStructIterator {
                encoding: RawAnyStructIteratorKind::Binary_1_1(s.iter()),
            },
        }
    }
}

impl<'data> From<LazyRawTextStruct_1_0<'data>> for LazyRawAnyStruct<'data> {
    fn from(value: LazyRawTextStruct_1_0<'data>) -> Self {
        LazyRawAnyStruct {
            encoding: LazyRawStructKind::Text_1_0(value),
        }
    }
}

impl<'data> From<LazyRawBinaryStruct_1_0<'data>> for LazyRawAnyStruct<'data> {
    fn from(value: LazyRawBinaryStruct_1_0<'data>) -> Self {
        LazyRawAnyStruct {
            encoding: LazyRawStructKind::Binary_1_0(value),
        }
    }
}

impl<'data> From<LazyRawTextStruct_1_1<'data>> for LazyRawAnyStruct<'data> {
    fn from(value: LazyRawTextStruct_1_1<'data>) -> Self {
        LazyRawAnyStruct {
            encoding: LazyRawStructKind::Text_1_1(value),
        }
    }
}

impl<'data> From<LazyRawBinaryStruct_1_1<'data>> for LazyRawAnyStruct<'data> {
    fn from(value: LazyRawBinaryStruct_1_1<'data>) -> Self {
        LazyRawAnyStruct {
            encoding: LazyRawStructKind::Binary_1_1(value),
        }
    }
}

impl<'data> IntoIterator for LazyRawAnyStruct<'data> {
    type Item = IonResult<LazyRawFieldExpr<'data, AnyEncoding>>;
    type IntoIter = RawAnyStructIterator<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::any_encoding::LazyRawAnyReader;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::decoder::{LazyRawReader, LazyRawSequence, LazyRawValue};
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::raw_stream_item::LazyRawStreamItem;
    use crate::lazy::raw_value_ref::RawValueRef;
    use crate::{IonResult, RawSymbolRef, Timestamp};

    use super::*;

    #[test]
    fn any_encoding() -> IonResult<()> {
        fn test_input(data: &[u8]) -> IonResult<()> {
            let encoding_context = EncodingContext::empty();
            let context = encoding_context.get_ref();

            let mut reader = LazyRawAnyReader::new(data);
            assert_eq!(reader.next(context)?.expect_ivm()?.major_minor(), (1, 0));
            let _strukt = reader
                .next(context)?
                .expect_value()?
                .read()?
                .expect_struct()?;
            let name = reader.next(context)?.expect_value()?;
            assert_eq!(
                name.annotations().next().unwrap()?,
                RawSymbolRef::SymbolId(4)
            );
            assert_eq!(name.read()?.expect_string()?.text(), "Gary");
            assert_eq!(
                reader.next(context)?.expect_value()?.read()?,
                RawValueRef::String("foo".into())
            );
            assert_eq!(
                reader.next(context)?.expect_value()?.read()?,
                RawValueRef::Int(5.into())
            );
            assert_eq!(
                reader.next(context)?.expect_value()?.read()?,
                RawValueRef::Timestamp(Timestamp::with_year(2023).with_month(8).build()?)
            );
            assert_eq!(
                reader.next(context)?.expect_value()?.read()?,
                RawValueRef::Bool(false)
            );

            let mut sum = 0;
            for lazy_value_result in reader
                .next(context)?
                .expect_value()?
                .read()?
                .expect_list()?
                .iter()
            {
                sum += lazy_value_result?.expect_value()?.read()?.expect_i64()?;
            }
            assert_eq!(sum, 6);

            // We cannot test structs here because using them forces the binary encoding to have a
            // local symbol table and the raw reader interprets that as a different value.

            assert!(matches!(
                reader.next(context)?,
                LazyRawStreamItem::<AnyEncoding>::EndOfStream(_)
            ));
            Ok(())
        }

        let text_data = r#"
            $ion_1_0
            {$7: ["a", "b", "c"]}
            $4::"Gary"
            "foo"
            5
            2023-08T
            false
            [1, 2, 3]
            "#;
        let binary_data = to_binary_ion(text_data)?;

        test_input(text_data.as_bytes())?;
        test_input(&binary_data)?;

        Ok(())
    }

    fn expect_version_change(
        context_ref: EncodingContextRef,
        reader: &mut LazyRawAnyReader,
        encoding_before: IonEncoding,
        encoding_after: IonEncoding,
    ) -> IonResult<()> {
        // The reader is using the expected encoding before we hit the IVM
        assert_eq!(reader.encoding(), encoding_before);
        // The next item is an IVM
        let ivm = reader.next(context_ref)?.expect_ivm()?;
        // The IVM correctly reports the expected before/after encodings
        assert_eq!(ivm.stream_encoding_before_marker(), encoding_before);
        assert_eq!(ivm.stream_encoding_after_marker()?, encoding_after);
        // The reader is now using the new encoding
        assert_eq!(reader.encoding(), encoding_after);
        Ok(())
    }

    fn expect_int(
        context_ref: EncodingContextRef,
        reader: &mut LazyRawAnyReader,
        expected_encoding: IonEncoding,
        expected_int: i64,
    ) -> IonResult<()> {
        let value = reader.next(context_ref)?.expect_value()?;
        let actual_int = value.read()?.expect_i64()?;
        assert_eq!(actual_int, expected_int);
        assert_eq!(reader.encoding(), expected_encoding);
        Ok(())
    }

    #[test]
    fn switch_text_versions() -> IonResult<()> {
        const DATA: &str = r#"
            1
            $ion_1_0
            2
            $ion_1_1
            3
            $ion_1_1
            4
            $ion_1_0
            5
        "#;

        let mut reader = LazyRawAnyReader::new(DATA.as_bytes());
        let encoding_context = EncodingContext::empty();
        let context_ref = encoding_context.get_ref();

        expect_int(context_ref, &mut reader, IonEncoding::Text_1_0, 1)?;

        // This IVM doesn't change the encoding.
        expect_version_change(
            context_ref,
            &mut reader,
            IonEncoding::Text_1_0,
            IonEncoding::Text_1_0,
        )?;

        expect_int(context_ref, &mut reader, IonEncoding::Text_1_0, 2)?;

        // This IVM changes the encoding from 1.0 text to 1.1 text
        expect_version_change(
            context_ref,
            &mut reader,
            IonEncoding::Text_1_0,
            IonEncoding::Text_1_1,
        )?;

        expect_int(context_ref, &mut reader, IonEncoding::Text_1_1, 3)?;

        // This IVM doesn't change the encoding.
        expect_version_change(
            context_ref,
            &mut reader,
            IonEncoding::Text_1_1,
            IonEncoding::Text_1_1,
        )?;

        expect_int(context_ref, &mut reader, IonEncoding::Text_1_1, 4)?;

        // This IVM changes the encoding from 1.1 text to 1.0 text
        expect_version_change(
            context_ref,
            &mut reader,
            IonEncoding::Text_1_1,
            IonEncoding::Text_1_0,
        )?;

        expect_int(context_ref, &mut reader, IonEncoding::Text_1_0, 5)?;

        Ok(())
    }

    #[test]
    fn switch_binary_versions() -> IonResult<()> {
        const DATA: &[u8] = &[
            0xE0, 0x01, 0x00, 0xEA, // $ion_1_0
            0x21, 0x02, // 2
            0xE0, 0x01, 0x01, 0xEA, // $ion_1_1
            0x61, 0x03, // 3
            0xE0, 0x01, 0x01, 0xEA, // $ion_1_1
            0x61, 0x04, // 4
            0xE0, 0x01, 0x00, 0xEA, // $ion_1_0
            0x21, 0x05, // 5
        ];

        let mut reader = LazyRawAnyReader::new(DATA);
        let encoding_context = EncodingContext::empty();
        let context_ref = encoding_context.get_ref();

        // When the reader is constructed it peeks at the leading bytes to see if they're an IVM.
        // In this case, they were a binary Ion v1.0 IVM, so the reader is already expecting to see
        // binary 1.0 data. Reading the binary version marker tells the reader to switch encodings.
        expect_version_change(
            context_ref,
            &mut reader,
            IonEncoding::Binary_1_0,
            IonEncoding::Binary_1_0,
        )?;

        expect_int(context_ref, &mut reader, IonEncoding::Binary_1_0, 2)?;

        // This IVM changes the encoding from 1.0 binary to 1.1 binary
        expect_version_change(
            context_ref,
            &mut reader,
            IonEncoding::Binary_1_0,
            IonEncoding::Binary_1_1,
        )?;

        expect_int(context_ref, &mut reader, IonEncoding::Binary_1_1, 3)?;

        // This IVM doesn't change the encoding.
        expect_version_change(
            context_ref,
            &mut reader,
            IonEncoding::Binary_1_1,
            IonEncoding::Binary_1_1,
        )?;

        expect_int(context_ref, &mut reader, IonEncoding::Binary_1_1, 4)?;

        // This IVM changes the encoding from 1.1 binary to 1.0 binary
        expect_version_change(
            context_ref,
            &mut reader,
            IonEncoding::Binary_1_1,
            IonEncoding::Binary_1_0,
        )?;

        expect_int(context_ref, &mut reader, IonEncoding::Binary_1_0, 5)?;

        Ok(())
    }
}
