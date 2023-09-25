#![allow(non_camel_case_types)]
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct;
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::sequence::{LazyRawBinaryList, LazyRawBinarySExp};
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::{LazyDecoder, LazyMacroInvocation};
use crate::lazy::text::raw::r#struct::LazyRawTextStruct_1_0;
use crate::lazy::text::raw::reader::LazyRawTextReader;
use crate::lazy::text::raw::sequence::{LazyRawTextList_1_0, LazyRawTextSExp_1_0};
use crate::lazy::text::value::{LazyRawTextValue_1_0, RawTextAnnotationsIterator};

// These types derive trait implementations in order to allow types that containing them
// to also derive trait implementations.

/// Marker trait for binary encodings of any version.
pub trait LazyBinaryDecoder {}

/// The Ion 1.0 binary encoding.
#[derive(Clone, Debug)]
pub struct BinaryEncoding_1_0;
impl LazyBinaryDecoder for BinaryEncoding_1_0 {}

/// The Ion 1.0 text encoding.
#[derive(Clone, Debug)]
pub struct TextEncoding_1_0;

impl<'data> LazyDecoder<'data> for BinaryEncoding_1_0 {
    type Reader = LazyRawBinaryReader<'data>;
    type Value = LazyRawBinaryValue<'data>;
    type SExp = LazyRawBinarySExp<'data>;
    type List = LazyRawBinaryList<'data>;
    type Struct = LazyRawBinaryStruct<'data>;
    type AnnotationsIterator = RawBinaryAnnotationsIterator<'data>;
    // Macros are not supported in Ion 1.0
    type MacroInvocation = ();
}

impl<'data> LazyDecoder<'data> for TextEncoding_1_0 {
    type Reader = LazyRawTextReader<'data>;
    type Value = LazyRawTextValue_1_0<'data>;
    type SExp = LazyRawTextSExp_1_0<'data>;
    type List = LazyRawTextList_1_0<'data>;
    type Struct = LazyRawTextStruct_1_0<'data>;
    type AnnotationsIterator = RawTextAnnotationsIterator<'data>;
    // Macros are not supported in Ion 1.0
    type MacroInvocation = ();
}

// Ion 1.0 uses `()` as a placeholder for MacroInvocation.
impl<'data, D: LazyDecoder<'data>> LazyMacroInvocation<'data, D> for () {
    // Nothing for now.
}
