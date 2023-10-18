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
pub trait TextEncoding<'data>:
    Encoding + LazyDecoder<'data, AnnotationsIterator = RawTextAnnotationsIterator<'data>>
{
    fn value_from_matched(
        matched: MatchedRawTextValue<'data>,
    ) -> <Self as LazyDecoder<'data>>::Value;
}
impl<'data> TextEncoding<'data> for TextEncoding_1_0 {
    fn value_from_matched(
        matched: MatchedRawTextValue<'data>,
    ) -> <Self as LazyDecoder<'data>>::Value {
        LazyRawTextValue_1_0::from(matched)
    }
}
impl<'data> TextEncoding<'data> for TextEncoding_1_1 {
    fn value_from_matched(
        matched: MatchedRawTextValue<'data>,
    ) -> <Self as LazyDecoder<'data>>::Value {
        LazyRawTextValue_1_1::from(matched)
    }
}

/// Marker trait for encodings that support macros.
pub trait EncodingWithMacroSupport {}
impl EncodingWithMacroSupport for TextEncoding_1_1 {}

impl<'data> LazyDecoder<'data> for BinaryEncoding_1_0 {
    type Reader = LazyRawBinaryReader<'data>;
    type Value = LazyRawBinaryValue<'data>;
    type SExp = LazyRawBinarySExp<'data>;
    type List = LazyRawBinaryList<'data>;
    type Struct = LazyRawBinaryStruct<'data>;
    type AnnotationsIterator = RawBinaryAnnotationsIterator<'data>;
    // Macros are not supported in Ion 1.0
    type EExpression = Never;
}

impl<'data> LazyDecoder<'data> for TextEncoding_1_0 {
    type Reader = LazyRawTextReader_1_0<'data>;
    type Value = LazyRawTextValue_1_0<'data>;
    type SExp = LazyRawTextSExp_1_0<'data>;
    type List = LazyRawTextList_1_0<'data>;
    type Struct = LazyRawTextStruct_1_0<'data>;
    type AnnotationsIterator = RawTextAnnotationsIterator<'data>;
    // Macros are not supported in Ion 1.0
    type EExpression = Never;
}

impl<'data> LazyDecoder<'data> for TextEncoding_1_1 {
    type Reader = LazyRawTextReader_1_1<'data>;
    type Value = LazyRawTextValue_1_1<'data>;
    type SExp = LazyRawTextSExp_1_1<'data>;
    type List = LazyRawTextList_1_1<'data>;
    type Struct = LazyRawTextStruct_1_1<'data>;
    type AnnotationsIterator = RawTextAnnotationsIterator<'data>;
    type EExpression = RawTextEExpression_1_1<'data>;
}

/// Marker trait for types that represent value literals in an Ion stream of some encoding.
// This trait is used to provide generic conversion implementation of types used as a
// `LazyDecoder::Value` to `ExpandedValueSource`. That is:
//
//     impl<'top, 'data, V: RawValueLiteral, D: LazyDecoder<'data, Value = V>> From<V>
//         for ExpandedValueSource<'top, 'data, D>
//
// If we do not confine the implementation to types with a marker trait, rustc complains that
// someone may someday use `ExpandedValueSource` as a `LazyDecoder::Value`, and then the
// the implementation will conflict with the core `impl<T> From<T> for T` implementation.
pub trait RawValueLiteral {}

impl<'data> RawValueLiteral for MatchedRawTextValue<'data> {}
impl<'data, E: TextEncoding<'data>> RawValueLiteral for LazyRawTextValue<'data, E> {}
impl<'data> RawValueLiteral for LazyRawBinaryValue<'data> {}
impl<'data> RawValueLiteral for LazyRawAnyValue<'data> {}
