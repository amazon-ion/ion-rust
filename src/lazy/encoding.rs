#![allow(non_camel_case_types)]

use std::fmt::Debug;

use crate::lazy::any_encoding::LazyRawAnyValue;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct_1_0;
use crate::lazy::binary::raw::reader::LazyRawBinaryReader_1_0;
use crate::lazy::binary::raw::sequence::{LazyRawBinaryList_1_0, LazyRawBinarySExp_1_0};
use crate::lazy::binary::raw::v1_1::reader::LazyRawBinaryReader_1_1;
use crate::lazy::binary::raw::v1_1::{
    r#struct::LazyRawBinaryStruct_1_1,
    sequence::{LazyRawBinaryList_1_1, LazyRawBinarySExp_1_1},
    value::LazyRawBinaryValue_1_1,
    RawBinaryAnnotationsIterator_1_1,
};
use crate::lazy::binary::raw::value::LazyRawBinaryValue_1_0;
use crate::lazy::decoder::LazyDecoder;
use crate::lazy::encoder::LazyEncoder;
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
use crate::{TextKind, WriteConfig};

/// Marker trait for types that represent an Ion encoding.
pub trait Encoding: LazyEncoder + LazyDecoder {
    fn name() -> &'static str;
    fn default_write_config() -> WriteConfig<Self>;
}

// These types derive trait implementations in order to allow types that containing them
// to also derive trait implementations.

/// The Ion 1.0 binary encoding.
#[derive(Copy, Clone, Debug)]
pub struct BinaryEncoding_1_0;

/// The Ion 1.1 binary encoding.
#[derive(Copy, Clone, Debug)]
pub struct BinaryEncoding_1_1;

impl<'top> BinaryEncoding<'top> for BinaryEncoding_1_0 {}
impl<'top> BinaryEncoding<'top> for BinaryEncoding_1_1 {}

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
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new()
    }
}
impl Encoding for BinaryEncoding_1_1 {
    fn name() -> &'static str {
        "binary Ion v1.1"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new()
    }
}
impl Encoding for TextEncoding_1_0 {
    fn name() -> &'static str {
        "text Ion v1.0"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new(<TextKind as Default>::default())
    }
}

impl Encoding for TextEncoding_1_1 {
    fn name() -> &'static str {
        "text Ion v1.1"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new(<TextKind as Default>::default())
    }
}

/// Marker trait for binary encodings of any version.
pub trait BinaryEncoding<'top>: Encoding + LazyDecoder {}

/// Marker trait for text encodings.
pub trait TextEncoding<'top>:
    Encoding + LazyDecoder<AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>>
{
    fn value_from_matched(
        matched: MatchedRawTextValue<'top, Self>,
    ) -> <Self as LazyDecoder>::Value<'top>;
}
impl<'top> TextEncoding<'top> for TextEncoding_1_0 {
    fn value_from_matched(
        matched: MatchedRawTextValue<'_, Self>,
    ) -> <Self as LazyDecoder>::Value<'_> {
        LazyRawTextValue_1_0::from(matched)
    }
}
impl<'top> TextEncoding<'top> for TextEncoding_1_1 {
    fn value_from_matched(
        matched: MatchedRawTextValue<'_, Self>,
    ) -> <Self as LazyDecoder>::Value<'_> {
        LazyRawTextValue_1_1::from(matched)
    }
}

/// Marker trait for encodings that support macros.
pub trait EncodingWithMacroSupport {}
impl EncodingWithMacroSupport for TextEncoding_1_1 {}

impl LazyDecoder for BinaryEncoding_1_0 {
    type Reader<'data> = LazyRawBinaryReader_1_0<'data>;
    type ReaderSavedState = ();
    type Value<'top> = LazyRawBinaryValue_1_0<'top>;
    type SExp<'top> = LazyRawBinarySExp_1_0<'top>;
    type List<'top> = LazyRawBinaryList_1_0<'top>;
    type Struct<'top> = LazyRawBinaryStruct_1_0<'top>;
    type AnnotationsIterator<'top> = RawBinaryAnnotationsIterator<'top>;
    // Macros are not supported in Ion 1.0
    type EExpression<'top> = Never;
}

impl LazyDecoder for TextEncoding_1_0 {
    type Reader<'data> = LazyRawTextReader_1_0<'data>;
    type ReaderSavedState = ();
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
    type ReaderSavedState = ();
    type Value<'top> = LazyRawTextValue_1_1<'top>;
    type SExp<'top> = LazyRawTextSExp_1_1<'top>;
    type List<'top> = LazyRawTextList_1_1<'top>;
    type Struct<'top> = LazyRawTextStruct_1_1<'top>;
    type AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>;
    type EExpression<'top> = RawTextEExpression_1_1<'top>;
}

impl LazyDecoder for BinaryEncoding_1_1 {
    type Reader<'data> = LazyRawBinaryReader_1_1<'data>;
    type ReaderSavedState = ();
    type Value<'top> = LazyRawBinaryValue_1_1<'top>;
    type SExp<'top> = LazyRawBinarySExp_1_1<'top>;
    type List<'top> = LazyRawBinaryList_1_1<'top>;
    type Struct<'top> = LazyRawBinaryStruct_1_1<'top>;
    type AnnotationsIterator<'top> = RawBinaryAnnotationsIterator_1_1<'top>;
    // TODO: implement macros in 1.1
    type EExpression<'top> = Never;
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

impl<'top, E: TextEncoding<'top>> RawValueLiteral for MatchedRawTextValue<'top, E> {}
impl<'top, E: TextEncoding<'top>> RawValueLiteral for LazyRawTextValue<'top, E> {}
impl<'top> RawValueLiteral for LazyRawBinaryValue_1_0<'top> {}
impl<'top> RawValueLiteral for LazyRawBinaryValue_1_1<'top> {}
impl<'top> RawValueLiteral for LazyRawAnyValue<'top> {}
