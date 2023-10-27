#![allow(non_camel_case_types)]

use crate::lazy::any_encoding::LazyRawAnyValue;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct;
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::sequence::{LazyRawBinaryList, LazyRawBinarySExp};
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::LazyDecoder;
use crate::lazy::never::Never;
use crate::lazy::text::raw::r#struct::LazyRawTextStruct_1_0;
use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
use crate::lazy::text::raw::sequence::{LazyRawTextList_1_0, LazyRawTextSExp_1_0};
use crate::lazy::text::raw::v1_1::reader::{
    LazyRawTextList_1_1, LazyRawTextReader_1_1, LazyRawTextSExp_1_1, LazyRawTextStruct_1_1,
    RawTextEExpression_1_1,
};
use crate::lazy::text::value::{
    LazyRawTextValue, LazyRawTextValue_1_0, LazyRawTextValue_1_1, MatchedRawTextValue,
    RawTextAnnotationsIterator,
};
use std::fmt::Debug;

/// Marker trait for types that represent an Ion encoding.
pub trait Encoding: Debug + Copy {
    fn name() -> &'static str;
}

// These types derive trait implementations in order to allow types that containing them
// to also derive trait implementations.

/// The Ion 1.0 binary encoding.
#[derive(Copy, Clone, Debug)]
pub struct BinaryEncoding_1_0;

impl BinaryEncoding for BinaryEncoding_1_0 {}

/// The Ion 1.0 text encoding.
#[derive(Copy, Clone, Debug)]
pub struct TextEncoding_1_0;

/// The Ion 1.1 text encoding.
#[derive(Copy, Clone, Debug)]
pub struct TextEncoding_1_1;

impl Encoding for BinaryEncoding_1_0 {
    fn name() -> &'static str {
        "binary Ion v1.0"
    }
}
impl Encoding for TextEncoding_1_0 {
    fn name() -> &'static str {
        "text Ion v1.0"
    }
}
impl Encoding for TextEncoding_1_1 {
    fn name() -> &'static str {
        "text Ion v1.1"
    }
}

/// Marker trait for binary encodings of any version.
pub trait BinaryEncoding: Encoding {}

/// Marker trait for text encodings.
pub trait TextEncoding<'top>:
    Encoding + LazyDecoder<AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>>
{
    fn value_from_matched(matched: MatchedRawTextValue) -> <Self as LazyDecoder>::Value<'_>;
}
impl<'top> TextEncoding<'top> for TextEncoding_1_0 {
    fn value_from_matched(matched: MatchedRawTextValue) -> <Self as LazyDecoder>::Value<'_> {
        LazyRawTextValue_1_0::from(matched)
    }
}
impl<'top> TextEncoding<'top> for TextEncoding_1_1 {
    fn value_from_matched(matched: MatchedRawTextValue) -> <Self as LazyDecoder>::Value<'_> {
        LazyRawTextValue_1_1::from(matched)
    }
}

/// Marker trait for encodings that support macros.
pub trait EncodingWithMacroSupport {}
impl EncodingWithMacroSupport for TextEncoding_1_1 {}

impl LazyDecoder for BinaryEncoding_1_0 {
    type Reader<'data> = LazyRawBinaryReader<'data>;
    type Value<'top> = LazyRawBinaryValue<'top>;
    type SExp<'top> = LazyRawBinarySExp<'top>;
    type List<'top> = LazyRawBinaryList<'top>;
    type Struct<'top> = LazyRawBinaryStruct<'top>;
    type AnnotationsIterator<'top> = RawBinaryAnnotationsIterator<'top>;
    // Macros are not supported in Ion 1.0
    type EExpression<'top> = Never;
}

impl LazyDecoder for TextEncoding_1_0 {
    type Reader<'data> = LazyRawTextReader_1_0<'data>;
    type Value<'top> = LazyRawTextValue_1_0<'top>;
    type SExp<'top> = LazyRawTextSExp_1_0<'top>;
    type List<'top> = LazyRawTextList_1_0<'top>;
    type Struct<'top> = LazyRawTextStruct_1_0<'top>;
    type AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>;
    // Macros are not supported in Ion 1.0
    type EExpression<'top> = Never;
}

impl LazyDecoder for TextEncoding_1_1 {
    type Reader<'data> = LazyRawTextReader_1_1<'data>;
    type Value<'top> = LazyRawTextValue_1_1<'top>;
    type SExp<'top> = LazyRawTextSExp_1_1<'top>;
    type List<'top> = LazyRawTextList_1_1<'top>;
    type Struct<'top> = LazyRawTextStruct_1_1<'top>;
    type AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>;
    type EExpression<'top> = RawTextEExpression_1_1<'top>;
}

/// Marker trait for types that represent value literals in an Ion stream of some encoding.
// This trait is used to provide generic conversion implementation of types used as a
// `LazyDecoder::Value` to `ExpandedValueSource`. That is:
//
//     impl<'top, 'data, V: RawValueLiteral, D: LazyDecoder<'data, Value = V>> From<V>
//         for ExpandedValueSource<'top, D>
//
// If we do not confine the implementation to types with a marker trait, rustc complains that
// someone may someday use `ExpandedValueSource` as a `LazyDecoder::Value`, and then the
// the implementation will conflict with the core `impl<T> From<T> for T` implementation.
pub trait RawValueLiteral {}

impl<'top> RawValueLiteral for MatchedRawTextValue<'top> {}
impl<'top, E: TextEncoding<'top>> RawValueLiteral for LazyRawTextValue<'top, E> {}
impl<'top> RawValueLiteral for LazyRawBinaryValue<'top> {}
impl<'top> RawValueLiteral for LazyRawAnyValue<'top> {}
