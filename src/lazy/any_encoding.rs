#![allow(non_camel_case_types)]

use std::fmt::Debug;

use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::{LazyRawBinaryStruct, RawBinaryStructIterator};
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::sequence::{
    LazyRawBinaryList, LazyRawBinarySExp, RawBinarySequenceIterator,
};
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::private::{LazyContainerPrivate, LazyRawValuePrivate};
use crate::lazy::decoder::{
    LazyDecoder, LazyRawFieldExpr, LazyRawReader, LazyRawSequence, LazyRawStruct, LazyRawValue,
    LazyRawValueExpr, RawFieldExpr, RawValueExpr,
};
use crate::lazy::encoding::{BinaryEncoding_1_0, TextEncoding_1_0, TextEncoding_1_1};
use crate::lazy::expanded::macro_evaluator::RawEExpression;
use crate::lazy::never::Never;
use crate::lazy::raw_stream_item::LazyRawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::text::raw::r#struct::{LazyRawTextStruct_1_0, RawTextStructIterator_1_0};
use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
use crate::lazy::text::raw::sequence::{
    LazyRawTextList_1_0, LazyRawTextSExp_1_0, RawTextListIterator_1_0, RawTextSExpIterator_1_0,
};
use crate::lazy::text::raw::v1_1::reader::{
    LazyRawTextList_1_1, LazyRawTextSExp_1_1, LazyRawTextStruct_1_1, MacroIdRef,
    RawTextEExpression_1_1, RawTextListIterator_1_1, RawTextSExpIterator_1_1,
    RawTextStructIterator_1_1,
};
use crate::lazy::text::value::{
    LazyRawTextValue_1_0, LazyRawTextValue_1_1, RawTextAnnotationsIterator,
};
use crate::{IonResult, IonType, RawSymbolTokenRef};

use bumpalo::Bump as BumpAllocator;

/// An implementation of the `LazyDecoder` trait that can read any encoding of Ion.
#[derive(Debug, Clone, Copy)]
pub struct AnyEncoding;

// This family of types avoids boxing and dynamic dispatch by using enums of the supported formats
// within each type. Trait methods are implemented by forwarding the call to the appropriate
// underlying type.
impl LazyDecoder for AnyEncoding {
    type Reader<'data> = LazyRawAnyReader<'data>;
    type Value<'top> = LazyRawAnyValue<'top>;
    type SExp<'top> = LazyRawAnySExp<'top>;
    type List<'top> = LazyRawAnyList<'top>;
    type Struct<'top> = LazyRawAnyStruct<'top>;
    type AnnotationsIterator<'top> = RawAnyAnnotationsIterator<'top>;
    type EExpression<'top> = LazyRawAnyEExpression<'top>;
}
#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyEExpression<'top> {
    encoding: LazyRawAnyEExpressionKind<'top>,
}

#[derive(Debug, Copy, Clone)]
enum LazyRawAnyEExpressionKind<'top> {
    // Ion 1.0 does not support macro invocations. Having these variants hold an instance of
    // `Never` (which cannot be instantiated) informs the compiler that it can eliminate these
    // branches in code paths exclusive to v1.0.
    Text_1_0(Never),
    Binary_1_0(Never),
    Text_1_1(RawTextEExpression_1_1<'top>),
}

impl<'top> From<RawTextEExpression_1_1<'top>> for LazyRawAnyEExpression<'top> {
    fn from(text_invocation: RawTextEExpression_1_1<'top>) -> Self {
        LazyRawAnyEExpression {
            encoding: LazyRawAnyEExpressionKind::Text_1_1(text_invocation),
        }
    }
}

impl<'top> RawEExpression<'top, AnyEncoding> for LazyRawAnyEExpression<'top> {
    type RawArgumentsIterator<'a> = LazyRawAnyMacroArgsIterator<'top,>  where Self: 'a;

    fn id(&self) -> MacroIdRef<'top> {
        match self.encoding {
            LazyRawAnyEExpressionKind::Text_1_0(_) => unreachable!("macro in text Ion 1.0"),
            LazyRawAnyEExpressionKind::Binary_1_0(_) => unreachable!("macro in binary Ion 1.0"),
            LazyRawAnyEExpressionKind::Text_1_1(ref m) => m.id(),
        }
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator<'_> {
        match self.encoding {
            LazyRawAnyEExpressionKind::Text_1_0(_) => unreachable!("macro in text Ion 1.0"),
            LazyRawAnyEExpressionKind::Binary_1_0(_) => unreachable!("macro in binary Ion 1.0"),
            LazyRawAnyEExpressionKind::Text_1_1(m) => LazyRawAnyMacroArgsIterator {
                encoding: LazyRawAnyMacroArgsIteratorKind::Text_1_1(m.raw_arguments()),
            },
        }
    }
}

pub enum LazyRawAnyMacroArgsIteratorKind<'top> {
    Text_1_1(
        <RawTextEExpression_1_1<'top> as RawEExpression<
                'top,
                TextEncoding_1_1,
            >>::RawArgumentsIterator<'top>,
    ),
}
pub struct LazyRawAnyMacroArgsIterator<'top> {
    encoding: LazyRawAnyMacroArgsIteratorKind<'top>,
}

impl<'top> Iterator for LazyRawAnyMacroArgsIterator<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, AnyEncoding>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.encoding {
            LazyRawAnyMacroArgsIteratorKind::Text_1_1(mut iter) => match iter.next() {
                Some(Ok(RawValueExpr::ValueLiteral(value))) => {
                    Some(Ok(RawValueExpr::ValueLiteral(LazyRawAnyValue::from(value))))
                }
                Some(Ok(RawValueExpr::MacroInvocation(invocation))) => {
                    Some(Ok(RawValueExpr::MacroInvocation(LazyRawAnyEExpression {
                        encoding: LazyRawAnyEExpressionKind::Text_1_1(invocation),
                    })))
                }
                Some(Err(e)) => Some(Err(e)),
                None => None,
            },
        }
    }
}

// ===== Readers ======

/// A lazy raw reader that can decode both text and binary Ion.
pub struct LazyRawAnyReader<'data> {
    encoding: RawReaderKind<'data>,
}

pub enum RawReaderKind<'data> {
    Text_1_0(LazyRawTextReader_1_0<'data>),
    Binary_1_0(LazyRawBinaryReader<'data>),
}

impl<'data> From<LazyRawTextReader_1_0<'data>> for LazyRawAnyReader<'data> {
    fn from(reader: LazyRawTextReader_1_0<'data>) -> Self {
        LazyRawAnyReader {
            encoding: RawReaderKind::Text_1_0(reader),
        }
    }
}

impl<'data> From<LazyRawBinaryReader<'data>> for LazyRawAnyReader<'data> {
    fn from(reader: LazyRawBinaryReader<'data>) -> Self {
        LazyRawAnyReader {
            encoding: RawReaderKind::Binary_1_0(reader),
        }
    }
}

impl<'data> LazyRawReader<'data, AnyEncoding> for LazyRawAnyReader<'data> {
    fn new(data: &'data [u8]) -> Self {
        if data.starts_with(&[0xE0u8, 0x01, 0x00, 0xEA]) {
            LazyRawBinaryReader::new(data).into()
        } else {
            LazyRawTextReader_1_0::new(data).into()
        }
    }

    fn next<'top>(
        &'top mut self,
        // TODO: This will be used once the 1.1 readers are added to the `self.encoding` enum
        _allocator: &'top BumpAllocator,
    ) -> IonResult<LazyRawStreamItem<'top, AnyEncoding>>
    where
        'data: 'top,
    {
        match &mut self.encoding {
            RawReaderKind::Text_1_0(r) => Ok(r.next()?.into()),
            RawReaderKind::Binary_1_0(r) => Ok(r.next()?.into()),
        }
    }
}

// ===== Values ======

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyValue<'top> {
    encoding: LazyRawValueKind<'top>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawValueKind<'top> {
    Text_1_0(LazyRawTextValue_1_0<'top>),
    Binary_1_0(LazyRawBinaryValue<'top>),
    Text_1_1(LazyRawTextValue_1_1<'top>),
}

impl<'top> From<LazyRawTextValue_1_0<'top>> for LazyRawAnyValue<'top> {
    fn from(value: LazyRawTextValue_1_0<'top>) -> Self {
        LazyRawAnyValue {
            encoding: LazyRawValueKind::Text_1_0(value),
        }
    }
}

impl<'top> From<LazyRawBinaryValue<'top>> for LazyRawAnyValue<'top> {
    fn from(value: LazyRawBinaryValue<'top>) -> Self {
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

impl<'top> From<LazyRawValueExpr<'top, TextEncoding_1_0>> for LazyRawValueExpr<'top, AnyEncoding> {
    fn from(value: LazyRawValueExpr<'top, TextEncoding_1_0>) -> Self {
        match value {
            RawValueExpr::ValueLiteral(v) => RawValueExpr::ValueLiteral(v.into()),
            RawValueExpr::MacroInvocation(m) => {
                let invocation = LazyRawAnyEExpression {
                    encoding: LazyRawAnyEExpressionKind::Text_1_0(m),
                };
                RawValueExpr::MacroInvocation(invocation)
            }
        }
    }
}

impl<'top> From<LazyRawValueExpr<'top, BinaryEncoding_1_0>>
    for LazyRawValueExpr<'top, AnyEncoding>
{
    fn from(value: LazyRawValueExpr<'top, BinaryEncoding_1_0>) -> Self {
        match value {
            RawValueExpr::ValueLiteral(v) => RawValueExpr::ValueLiteral(v.into()),
            RawValueExpr::MacroInvocation(m) => {
                let invocation = LazyRawAnyEExpression {
                    encoding: LazyRawAnyEExpressionKind::Binary_1_0(m),
                };
                RawValueExpr::MacroInvocation(invocation)
            }
        }
    }
}

impl<'top> From<LazyRawValueExpr<'top, TextEncoding_1_1>> for LazyRawValueExpr<'top, AnyEncoding> {
    fn from(value: LazyRawValueExpr<'top, TextEncoding_1_1>) -> Self {
        match value {
            RawValueExpr::ValueLiteral(v) => RawValueExpr::ValueLiteral(v.into()),
            RawValueExpr::MacroInvocation(m) => {
                let invocation = LazyRawAnyEExpression {
                    encoding: LazyRawAnyEExpressionKind::Text_1_1(m),
                };
                RawValueExpr::MacroInvocation(invocation)
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

impl<'top> From<LazyRawStreamItem<'top, TextEncoding_1_0>>
    for LazyRawStreamItem<'top, AnyEncoding>
{
    fn from(value: LazyRawStreamItem<'top, TextEncoding_1_0>) -> Self {
        match value {
            LazyRawStreamItem::<TextEncoding_1_0>::VersionMarker(major, minor) => {
                LazyRawStreamItem::<AnyEncoding>::VersionMarker(major, minor)
            }
            LazyRawStreamItem::<TextEncoding_1_0>::Value(value) => {
                LazyRawStreamItem::<AnyEncoding>::Value(value.into())
            }
            LazyRawStreamItem::<TextEncoding_1_0>::EExpression(_) => {
                unreachable!("Ion 1.0 does not support macro invocations")
            }
            LazyRawStreamItem::<TextEncoding_1_0>::EndOfStream => {
                LazyRawStreamItem::<AnyEncoding>::EndOfStream
            }
        }
    }
}

impl<'top> From<LazyRawStreamItem<'top, BinaryEncoding_1_0>>
    for LazyRawStreamItem<'top, AnyEncoding>
{
    fn from(value: LazyRawStreamItem<'top, BinaryEncoding_1_0>) -> Self {
        match value {
            LazyRawStreamItem::<BinaryEncoding_1_0>::VersionMarker(major, minor) => {
                LazyRawStreamItem::<AnyEncoding>::VersionMarker(major, minor)
            }
            LazyRawStreamItem::<BinaryEncoding_1_0>::Value(value) => {
                LazyRawStreamItem::<AnyEncoding>::Value(value.into())
            }
            LazyRawStreamItem::<BinaryEncoding_1_0>::EExpression(_) => {
                unreachable!("Ion 1.0 does not support macro invocations")
            }
            LazyRawStreamItem::<BinaryEncoding_1_0>::EndOfStream => {
                LazyRawStreamItem::<AnyEncoding>::EndOfStream
            }
        }
    }
}

impl<'top> From<LazyRawStreamItem<'top, TextEncoding_1_1>>
    for LazyRawStreamItem<'top, AnyEncoding>
{
    fn from(value: LazyRawStreamItem<'top, TextEncoding_1_1>) -> Self {
        match value {
            LazyRawStreamItem::<TextEncoding_1_1>::VersionMarker(major, minor) => {
                LazyRawStreamItem::<AnyEncoding>::VersionMarker(major, minor)
            }
            LazyRawStreamItem::<TextEncoding_1_1>::Value(value) => {
                LazyRawStreamItem::<AnyEncoding>::Value(value.into())
            }
            LazyRawStreamItem::<TextEncoding_1_1>::EExpression(invocation) => {
                LazyRawStreamItem::<AnyEncoding>::EExpression(LazyRawAnyEExpression {
                    encoding: LazyRawAnyEExpressionKind::Text_1_1(invocation),
                })
            }
            LazyRawStreamItem::<TextEncoding_1_1>::EndOfStream => {
                LazyRawStreamItem::<AnyEncoding>::EndOfStream
            }
        }
    }
}

impl<'top> LazyRawValuePrivate<'top> for LazyRawAnyValue<'top> {
    fn field_name(&self) -> IonResult<RawSymbolTokenRef<'top>> {
        match &self.encoding {
            LazyRawValueKind::Text_1_0(v) => v.field_name(),
            LazyRawValueKind::Binary_1_0(v) => v.field_name(),
            LazyRawValueKind::Text_1_1(v) => v.field_name(),
        }
    }
}

impl<'top> LazyRawValue<'top, AnyEncoding> for LazyRawAnyValue<'top> {
    fn ion_type(&self) -> IonType {
        match &self.encoding {
            LazyRawValueKind::Text_1_0(v) => v.ion_type(),
            LazyRawValueKind::Binary_1_0(v) => v.ion_type(),
            LazyRawValueKind::Text_1_1(v) => v.ion_type(),
        }
    }

    fn is_null(&self) -> bool {
        match &self.encoding {
            LazyRawValueKind::Text_1_0(v) => v.is_null(),
            LazyRawValueKind::Binary_1_0(v) => v.is_null(),
            LazyRawValueKind::Text_1_1(v) => v.is_null(),
        }
    }

    fn annotations(&self) -> RawAnyAnnotationsIterator<'top> {
        match &self.encoding {
            LazyRawValueKind::Text_1_0(v) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Text_1_0(v.annotations()),
            },
            LazyRawValueKind::Binary_1_0(v) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Binary_1_0(v.annotations()),
            },
            LazyRawValueKind::Text_1_1(v) => RawAnyAnnotationsIterator {
                encoding: RawAnnotationsIteratorKind::Text_1_1(v.annotations()),
            },
        }
    }

    fn read(&self) -> IonResult<RawValueRef<'top, AnyEncoding>> {
        match &self.encoding {
            LazyRawValueKind::Text_1_0(v) => Ok(v.read()?.into()),
            LazyRawValueKind::Binary_1_0(v) => Ok(v.read()?.into()),
            LazyRawValueKind::Text_1_1(v) => Ok(v.read()?.into()),
        }
    }
}

// ===== Annotations =====

pub struct RawAnyAnnotationsIterator<'top> {
    encoding: RawAnnotationsIteratorKind<'top>,
}

pub enum RawAnnotationsIteratorKind<'top> {
    Text_1_0(RawTextAnnotationsIterator<'top>),
    Binary_1_0(RawBinaryAnnotationsIterator<'top>),
    Text_1_1(RawTextAnnotationsIterator<'top>),
}

impl<'top> Iterator for RawAnyAnnotationsIterator<'top> {
    type Item = IonResult<RawSymbolTokenRef<'top>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.encoding {
            RawAnnotationsIteratorKind::Text_1_0(i) => i.next(),
            RawAnnotationsIteratorKind::Binary_1_0(i) => i.next(),
            RawAnnotationsIteratorKind::Text_1_1(i) => i.next(),
        }
    }
}

// ===== Lists ======

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyList<'top> {
    encoding: LazyRawListKind<'top>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawListKind<'top> {
    Text_1_0(LazyRawTextList_1_0<'top>),
    Binary_1_0(LazyRawBinaryList<'top>),
    Text_1_1(LazyRawTextList_1_1<'top>),
}

impl<'top> LazyContainerPrivate<'top, AnyEncoding> for LazyRawAnyList<'top> {
    fn from_value(value: LazyRawAnyValue<'top>) -> Self {
        match value.encoding {
            LazyRawValueKind::Text_1_0(v) => LazyRawAnyList {
                encoding: LazyRawListKind::Text_1_0(LazyRawTextList_1_0::from_value(v)),
            },
            LazyRawValueKind::Binary_1_0(v) => LazyRawAnyList {
                encoding: LazyRawListKind::Binary_1_0(LazyRawBinaryList::from_value(v)),
            },
            LazyRawValueKind::Text_1_1(v) => LazyRawAnyList {
                encoding: LazyRawListKind::Text_1_1(LazyRawTextList_1_1::from_value(v)),
            },
        }
    }
}

pub struct RawAnyListIterator<'data> {
    encoding: RawAnyListIteratorKind<'data>,
}

pub enum RawAnyListIteratorKind<'data> {
    Text_1_0(RawTextListIterator_1_0<'data>),
    Binary_1_0(RawBinarySequenceIterator<'data>),
    Text_1_1(RawTextListIterator_1_1<'data>),
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
        }
    }
}

impl<'top> LazyRawSequence<'top, AnyEncoding> for LazyRawAnyList<'top> {
    type Iterator = RawAnyListIterator<'top>;

    fn annotations(&self) -> <AnyEncoding as LazyDecoder>::AnnotationsIterator<'top> {
        self.as_value().annotations()
    }

    fn ion_type(&self) -> IonType {
        match &self.encoding {
            LazyRawListKind::Text_1_0(s) => s.ion_type(),
            LazyRawListKind::Binary_1_0(s) => s.ion_type(),
            LazyRawListKind::Text_1_1(s) => s.ion_type(),
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
        }
    }

    fn as_value(&self) -> LazyRawAnyValue<'top> {
        match &self.encoding {
            LazyRawListKind::Text_1_0(s) => s.as_value().into(),
            LazyRawListKind::Binary_1_0(s) => s.as_value().into(),
            LazyRawListKind::Text_1_1(s) => s.as_value().into(),
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

impl<'data> From<LazyRawBinaryList<'data>> for LazyRawAnyList<'data> {
    fn from(value: LazyRawBinaryList<'data>) -> Self {
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

// ===== SExps =====

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnySExp<'data> {
    encoding: LazyRawSExpKind<'data>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawSExpKind<'data> {
    Text_1_0(LazyRawTextSExp_1_0<'data>),
    Binary_1_0(LazyRawBinarySExp<'data>),
    Text_1_1(LazyRawTextSExp_1_1<'data>),
}

impl<'data> LazyContainerPrivate<'data, AnyEncoding> for LazyRawAnySExp<'data> {
    fn from_value(value: LazyRawAnyValue<'data>) -> Self {
        match value.encoding {
            LazyRawValueKind::Text_1_0(v) => LazyRawAnySExp {
                encoding: LazyRawSExpKind::Text_1_0(LazyRawTextSExp_1_0::from_value(v)),
            },
            LazyRawValueKind::Binary_1_0(v) => LazyRawAnySExp {
                encoding: LazyRawSExpKind::Binary_1_0(LazyRawBinarySExp::from_value(v)),
            },
            LazyRawValueKind::Text_1_1(v) => LazyRawAnySExp {
                encoding: LazyRawSExpKind::Text_1_1(LazyRawTextSExp_1_1::from_value(v)),
            },
        }
    }
}

pub struct RawAnySExpIterator<'data> {
    encoding: RawAnySExpIteratorKind<'data>,
}

pub enum RawAnySExpIteratorKind<'data> {
    Text_1_0(RawTextSExpIterator_1_0<'data>),
    Binary_1_0(RawBinarySequenceIterator<'data>),
    Text_1_1(RawTextSExpIterator_1_1<'data>),
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
        }
    }
}

impl<'top> LazyRawSequence<'top, AnyEncoding> for LazyRawAnySExp<'top> {
    type Iterator = RawAnySExpIterator<'top>;

    fn annotations(&self) -> <AnyEncoding as LazyDecoder>::AnnotationsIterator<'top> {
        self.as_value().annotations()
    }

    fn ion_type(&self) -> IonType {
        match &self.encoding {
            LazyRawSExpKind::Text_1_0(s) => s.ion_type(),
            LazyRawSExpKind::Binary_1_0(s) => s.ion_type(),
            LazyRawSExpKind::Text_1_1(s) => s.ion_type(),
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
        }
    }

    fn as_value(&self) -> LazyRawAnyValue<'top> {
        match &self.encoding {
            LazyRawSExpKind::Text_1_0(s) => (s.as_value()).into(),
            LazyRawSExpKind::Binary_1_0(s) => (s.as_value()).into(),
            LazyRawSExpKind::Text_1_1(s) => (s.as_value()).into(),
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

impl<'data> From<LazyRawBinarySExp<'data>> for LazyRawAnySExp<'data> {
    fn from(value: LazyRawBinarySExp<'data>) -> Self {
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

// ===== Structs =====

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyStruct<'data> {
    encoding: LazyRawStructKind<'data>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawStructKind<'data> {
    Text_1_0(LazyRawTextStruct_1_0<'data>),
    Binary_1_0(LazyRawBinaryStruct<'data>),
    Text_1_1(LazyRawTextStruct_1_1<'data>),
}

pub struct RawAnyStructIterator<'data> {
    encoding: RawAnyStructIteratorKind<'data>,
}

pub enum RawAnyStructIteratorKind<'data> {
    Text_1_0(RawTextStructIterator_1_0<'data>),
    Binary_1_0(RawBinaryStructIterator<'data>),
    Text_1_1(RawTextStructIterator_1_1<'data>),
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
        }
    }
}

impl<'data> From<LazyRawFieldExpr<'data, TextEncoding_1_0>>
    for LazyRawFieldExpr<'data, AnyEncoding>
{
    fn from(text_field: LazyRawFieldExpr<'data, TextEncoding_1_0>) -> Self {
        let (name, value) = match text_field {
            RawFieldExpr::NameValuePair(name, value) => (name, value),
            RawFieldExpr::MacroInvocation(_) => {
                unreachable!("macro invocation in Ion 1.0")
            }
        };
        // Convert the text-encoded value into an any-encoded value
        RawFieldExpr::NameValuePair(name, value.into())
    }
}

impl<'data> From<LazyRawFieldExpr<'data, BinaryEncoding_1_0>>
    for LazyRawFieldExpr<'data, AnyEncoding>
{
    fn from(binary_field: LazyRawFieldExpr<'data, BinaryEncoding_1_0>) -> Self {
        let (name, value) = match binary_field {
            RawFieldExpr::NameValuePair(name, value) => (name, value),
            RawFieldExpr::MacroInvocation(_) => {
                unreachable!("macro invocation in Ion 1.0")
            }
        };
        // Convert the binary-encoded value into an any-encoded value
        RawFieldExpr::NameValuePair(name, value.into())
    }
}

impl<'data> From<LazyRawFieldExpr<'data, TextEncoding_1_1>>
    for LazyRawFieldExpr<'data, AnyEncoding>
{
    fn from(text_field: LazyRawFieldExpr<'data, TextEncoding_1_1>) -> Self {
        use RawFieldExpr::{MacroInvocation as FieldMacroInvocation, NameValuePair};
        use RawValueExpr::{MacroInvocation as ValueMacroInvocation, ValueLiteral};
        match text_field {
            NameValuePair(name, ValueLiteral(value)) => {
                NameValuePair(name, ValueLiteral(value.into()))
            }
            NameValuePair(name, ValueMacroInvocation(invocation)) => {
                NameValuePair(name, ValueMacroInvocation(invocation.into()))
            }
            FieldMacroInvocation(invocation) => FieldMacroInvocation(invocation.into()),
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
                encoding: LazyRawStructKind::Binary_1_0(LazyRawBinaryStruct::from_value(v)),
            },
            LazyRawValueKind::Text_1_1(v) => LazyRawAnyStruct {
                encoding: LazyRawStructKind::Text_1_1(LazyRawTextStruct_1_1::from_value(v)),
            },
        }
    }
}

impl<'top> LazyRawStruct<'top, AnyEncoding> for LazyRawAnyStruct<'top> {
    type Iterator = RawAnyStructIterator<'top>;

    fn annotations(&self) -> <AnyEncoding as LazyDecoder>::AnnotationsIterator<'top> {
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

impl<'data> From<LazyRawBinaryStruct<'data>> for LazyRawAnyStruct<'data> {
    fn from(value: LazyRawBinaryStruct<'data>) -> Self {
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

impl<'data> IntoIterator for LazyRawAnyStruct<'data> {
    type Item = IonResult<LazyRawFieldExpr<'data, AnyEncoding>>;
    type IntoIter = RawAnyStructIterator<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::any_encoding::LazyRawAnyReader;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::decoder::{LazyRawReader, LazyRawSequence, LazyRawValue};
    use crate::lazy::raw_stream_item::LazyRawStreamItem;
    use crate::lazy::raw_value_ref::RawValueRef;
    use crate::{IonResult, RawSymbolTokenRef, Timestamp};

    #[test]
    fn any_encoding() -> IonResult<()> {
        fn test_input(data: &[u8]) -> IonResult<()> {
            let allocator = BumpAllocator::new();

            let mut reader = LazyRawAnyReader::new(data);
            assert_eq!(reader.next(&allocator)?.expect_ivm()?, (1, 0));
            let _strukt = reader
                .next(&allocator)?
                .expect_value()?
                .read()?
                .expect_struct()?;
            let name = reader.next(&allocator)?.expect_value()?;
            assert_eq!(
                name.annotations().next().unwrap()?,
                RawSymbolTokenRef::SymbolId(4)
            );
            assert_eq!(name.read()?.expect_string()?.text(), "Gary");
            assert_eq!(
                reader.next(&allocator)?.expect_value()?.read()?,
                RawValueRef::String("foo".into())
            );
            assert_eq!(
                reader.next(&allocator)?.expect_value()?.read()?,
                RawValueRef::Int(5.into())
            );
            assert_eq!(
                reader.next(&allocator)?.expect_value()?.read()?,
                RawValueRef::Timestamp(Timestamp::with_year(2023).with_month(8).build()?)
            );
            assert_eq!(
                reader.next(&allocator)?.expect_value()?.read()?,
                RawValueRef::Bool(false)
            );

            let mut sum = 0;
            for lazy_value_result in reader
                .next(&allocator)?
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
                reader.next(&allocator)?,
                LazyRawStreamItem::<AnyEncoding>::EndOfStream
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
}
