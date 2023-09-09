#![allow(non_camel_case_types)]

use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct;
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::sequence::{LazyRawBinaryList, LazyRawBinarySExp};
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::LazyDecoder;
use crate::lazy::expanded::macro_evaluator::{ArgumentKind, MacroInvocation, ToArgumentKind};
use crate::lazy::expanded::EncodingContext;
use crate::lazy::text::raw::r#struct::LazyRawTextStruct_1_0;
use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
use crate::lazy::text::raw::sequence::{LazyRawTextList_1_0, LazyRawTextSExp_1_0};
use crate::lazy::text::raw::v1_1::reader::{
    LazyRawTextList_1_1, LazyRawTextReader_1_1, LazyRawTextSExp_1_1, LazyRawTextStruct_1_1,
    MacroIdRef, RawTextMacroInvocation,
};
use crate::lazy::text::value::{
    LazyRawTextValue_1_0, LazyRawTextValue_1_1, MatchedRawTextValue, RawTextAnnotationsIterator,
};
use crate::IonResult;

// These types derive trait implementations in order to allow types that containing them
// to also derive trait implementations.

/// Marker trait for binary encodings of any version.
pub trait BinaryEncoding {}

/// Marker trait for encodings that support macros.
pub trait EncodingWithMacroSupport {}
impl EncodingWithMacroSupport for TextEncoding_1_1 {}

/// Marker trait for text encodings.
pub trait TextEncoding<'data>:
    LazyDecoder<'data, AnnotationsIterator = RawTextAnnotationsIterator<'data>>
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

/// The Ion 1.0 binary encoding.
#[derive(Clone, Debug)]
pub struct BinaryEncoding_1_0;
impl BinaryEncoding for BinaryEncoding_1_0 {}

/// The Ion 1.0 text encoding.
#[derive(Clone, Debug)]
pub struct TextEncoding_1_0;

/// An uninhabited type that signals to the compiler that related code paths are not reachable.
#[derive(Debug, Copy, Clone)]
pub enum Never {
    // Has no variants, cannot be instantiated.
}

impl<'data> LazyDecoder<'data> for BinaryEncoding_1_0 {
    type Reader = LazyRawBinaryReader<'data>;
    type Value = LazyRawBinaryValue<'data>;
    type SExp = LazyRawBinarySExp<'data>;
    type List = LazyRawBinaryList<'data>;
    type Struct = LazyRawBinaryStruct<'data>;
    type AnnotationsIterator = RawBinaryAnnotationsIterator<'data>;
    // Macros are not supported in Ion 1.0
    type MacroInvocation = Never;
}

impl<'data> LazyDecoder<'data> for TextEncoding_1_0 {
    type Reader = LazyRawTextReader_1_0<'data>;
    type Value = LazyRawTextValue_1_0<'data>;
    type SExp = LazyRawTextSExp_1_0<'data>;
    type List = LazyRawTextList_1_0<'data>;
    type Struct = LazyRawTextStruct_1_0<'data>;
    type AnnotationsIterator = RawTextAnnotationsIterator<'data>;
    // Macros are not supported in Ion 1.0
    type MacroInvocation = Never;
}

// Ion 1.0 uses `Never` as a placeholder type for MacroInvocation.
// The compiler should optimize these methods away.
impl<'data, D: LazyDecoder<'data>> MacroInvocation<'data, D> for Never {
    type ArgumentExpr = Never;
    // This uses a Box<dyn> to avoid defining yet another placeholder type.
    type ArgumentsIterator = Box<dyn Iterator<Item = IonResult<Never>>>;

    fn id(&self) -> MacroIdRef<'_> {
        unreachable!("macro in Ion 1.0 (method: id)")
    }

    fn arguments(&self) -> Self::ArgumentsIterator {
        unreachable!("macro in Ion 1.0 (method: arguments)")
    }
}

impl<'data, D: LazyDecoder<'data>> ToArgumentKind<'data, D, Self> for Never {
    fn to_arg_expr<'top>(
        self,
        _context: EncodingContext<'top>,
    ) -> ArgumentKind<'top, 'data, D, Self>
    where
        Self: 'top,
    {
        unreachable!("macro in Ion 1.0 (method: to_value_expr)")
    }
}

// The Ion 1.1 text encoding.
#[derive(Clone, Debug)]
pub struct TextEncoding_1_1;

impl<'data> LazyDecoder<'data> for TextEncoding_1_1 {
    type Reader = LazyRawTextReader_1_1<'data>;
    type Value = LazyRawTextValue_1_1<'data>;
    type SExp = LazyRawTextSExp_1_1<'data>;
    type List = LazyRawTextList_1_1<'data>;
    type Struct = LazyRawTextStruct_1_1<'data>;
    type AnnotationsIterator = RawTextAnnotationsIterator<'data>;
    type MacroInvocation = RawTextMacroInvocation<'data>;
}
