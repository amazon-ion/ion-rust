#![allow(non_camel_case_types)]

use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator as RawBinaryAnnotationsIterator_1_0;
use crate::lazy::binary::raw::r#struct::{
    LazyRawBinaryFieldName_1_0, LazyRawBinaryStruct_1_0, RawBinaryStructIterator_1_0,
};
use crate::lazy::binary::raw::reader::LazyRawBinaryReader_1_0;
use crate::lazy::binary::raw::sequence::{
    LazyRawBinaryList_1_0, LazyRawBinarySExp_1_0, RawBinarySequenceIterator_1_0,
};
use crate::lazy::binary::raw::value::{LazyRawBinaryValue_1_0, LazyRawBinaryVersionMarker_1_0};
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, HasRange, HasSpan, LazyRawContainer, LazyRawFieldExpr, LazyRawFieldName,
    LazyRawReader, LazyRawSequence, LazyRawStruct, LazyRawValue, LazyRawValueExpr, RawValueExpr,
    RawVersionMarker,
};
use crate::lazy::encoding::{BinaryEncoding_1_0, TextEncoding_1_0};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::never::Never;
use crate::lazy::raw_stream_item::LazyRawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::span::Span;
use crate::lazy::streaming_raw_reader::RawReaderState;
use crate::lazy::text::raw::r#struct::{
    LazyRawTextFieldName, LazyRawTextStruct, RawTextStructCacheIterator,
};
use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
use crate::lazy::text::raw::sequence::{RawTextList, RawTextSExp, RawTextSequenceCacheIterator};
use crate::lazy::text::value::{
    LazyRawTextValue_1_0, LazyRawTextVersionMarker_1_0, RawTextAnnotationsIterator,
};
use crate::result::IonFailure;
use crate::symbol_table::{SystemSymbolTable, SYSTEM_SYMBOLS_1_0, SYSTEM_SYMBOLS_1_1};
use crate::{Encoding, IonResult, IonType, RawStreamItem, RawSymbolRef};
use std::fmt::Debug;
use std::ops::Range;

/// An implementation of the `LazyDecoder` trait that can read any encoding of Ion.
#[derive(Debug, Clone, Copy)]
pub struct AnyEncoding;

// This family of types avoids boxing and dynamic dispatch by using enums of the supported formats
// within each type. Trait methods are implemented by forwarding the call to the appropriate
// underlying type.
impl Decoder for AnyEncoding {
    // Before a reader using `AnyEncoding` begins reading, it expects text Ion v1.0.
    // At the outset of the stream, it inspects the first bytes to see if the stream is binary or text.
    // If it encounters a version marker, the expected version will change.
    const INITIAL_ENCODING_EXPECTED: IonEncoding = IonEncoding::Text_1_0;
    type Reader<'data> = LazyRawAnyReader<'data>;
    type Value<'top> = LazyRawAnyValue<'top>;
    type SExp<'top> = LazyRawAnySExp<'top>;
    type List<'top> = LazyRawAnyList<'top>;
    type Struct<'top> = LazyRawAnyStruct<'top>;
    type FieldName<'top> = LazyRawAnyFieldName<'top>;
    type AnnotationsIterator<'top> = RawAnyAnnotationsIterator<'top>;
    // `AnyEncoding` only supports Ion 1.0, which has no e-expressions.
    type EExp<'top> = Never;
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
}

impl LazyRawAnyVersionMarker<'_> {
    pub fn encoding(&self) -> IonEncoding {
        use crate::lazy::any_encoding::LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(_) => TextEncoding_1_0.encoding(),
            Binary_1_0(_) => BinaryEncoding_1_0.encoding(),
        }
    }
}

impl<'top> HasSpan<'top> for LazyRawAnyVersionMarker<'top> {
    fn span(&self) -> Span<'top> {
        use LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(marker) => marker.span(),
            Binary_1_0(marker) => marker.span(),
        }
    }
}

impl HasRange for LazyRawAnyVersionMarker<'_> {
    fn range(&self) -> Range<usize> {
        use LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(marker) => marker.range(),
            Binary_1_0(marker) => marker.range(),
        }
    }
}

impl<'top> RawVersionMarker<'top> for LazyRawAnyVersionMarker<'top> {
    fn major_minor(&self) -> (u8, u8) {
        use LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(marker) => marker.major_minor(),
            Binary_1_0(marker) => marker.major_minor(),
        }
    }

    fn stream_encoding_before_marker(&self) -> IonEncoding {
        use LazyRawAnyVersionMarkerKind::*;
        match self.encoding {
            Text_1_0(_) => IonEncoding::Text_1_0,
            Binary_1_0(_) => IonEncoding::Binary_1_0,
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
impl<'top> From<LazyRawTextVersionMarker_1_0<'top>> for LazyRawAnyVersionMarker<'top> {
    fn from(value: LazyRawTextVersionMarker_1_0<'top>) -> Self {
        LazyRawAnyVersionMarker {
            encoding: LazyRawAnyVersionMarkerKind::Text_1_0(value),
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

impl LazyRawAnyReader<'_> {
    fn detect_encoding(data: &[u8]) -> IonEncoding {
        match *data {
            // A binary Ion 1.1 IVM (`E0 01 01 EA`) is also handed to the binary 1.0 reader; it
            // reports the marker as an unsupported version rather than attempting to decode the
            // Ion 1.1 stream that follows.
            [0xE0, 0x01, 0x00 | 0x01, 0xEA, ..] => IonEncoding::Binary_1_0,
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
}

impl<'data> RawReaderKind<'data> {
    fn resume_at_offset(
        context: EncodingContextRef<'data>,
        saved_state: RawReaderState<'data>,
    ) -> RawReaderKind<'data> {
        use IonEncoding::*;
        // `AnyEncoding` has no Ion 1.1 readers, so the 1.1 encodings are folded into their 1.0
        // counterparts. They cannot reach this point in practice: `detect_encoding` never reports
        // them and `LazyRawAnyReader::next` rejects a 1.1 IVM before recording a new encoding. If
        // one does arrive in a caller-supplied `RawReaderState`, the 1.0 reader will report the
        // stream's IVM as an unsupported version.
        match saved_state.encoding() {
            Text_1_0 | Text_1_1 => {
                RawReaderKind::Text_1_0(LazyRawTextReader_1_0::resume(context, saved_state))
            }
            Binary_1_0 | Binary_1_1 => {
                RawReaderKind::Binary_1_0(LazyRawBinaryReader_1_0::resume(context, saved_state))
            }
        }
    }

    fn context(&self) -> EncodingContextRef<'data> {
        match self {
            RawReaderKind::Text_1_0(r) => r.context(),
            RawReaderKind::Binary_1_0(r) => r.context(),
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
            // TODO(pt005b): remove with Ion 1.1. These no longer implement `Encoding`, whose
            //               `name()` the other arms delegate to.
            Text_1_1 => "text Ion v1.1",
            Binary_1_1 => "binary Ion v1.1",
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

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
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

    /// Returns the system symbol table associated with this Ion version.
    pub fn system_symbol_table(&self) -> &'static SystemSymbolTable {
        match self {
            IonVersion::v1_0 => SYSTEM_SYMBOLS_1_0,
            IonVersion::v1_1 => SYSTEM_SYMBOLS_1_1,
        }
    }
}

impl<'data> From<LazyRawTextReader_1_0<'data>> for LazyRawAnyReader<'data> {
    fn from(reader: LazyRawTextReader_1_0<'data>) -> Self {
        RawReaderKind::Text_1_0(reader).into()
    }
}

impl<'data> From<LazyRawBinaryReader_1_0<'data>> for LazyRawAnyReader<'data> {
    fn from(reader: LazyRawBinaryReader_1_0<'data>) -> Self {
        RawReaderKind::Binary_1_0(reader).into()
    }
}

impl<'data> LazyRawReader<'data, AnyEncoding> for LazyRawAnyReader<'data> {
    fn new(context: EncodingContextRef<'data>, data: &'data [u8], is_final_data: bool) -> Self {
        let encoding = Self::detect_encoding(data);
        let state = RawReaderState::new(data, 0, is_final_data, encoding);
        LazyRawAnyReader {
            new_encoding: None,
            encoding_reader: RawReaderKind::resume_at_offset(context, state),
        }
    }

    fn resume(context: EncodingContextRef<'data>, mut saved_state: RawReaderState<'data>) -> Self {
        let offset = saved_state.offset();
        let data = saved_state.data();
        if offset == 0 {
            // If we're at the beginning of the stream, the saved state's encoding may be a
            // default. We need to inspect the bytes to see if we should override it.
            saved_state.set_encoding(Self::detect_encoding(data));
        }
        RawReaderKind::resume_at_offset(context, saved_state).into()
    }

    fn save_state(&self) -> RawReaderState<'data> {
        use RawReaderKind::*;
        let reader_state = match &self.encoding_reader {
            Text_1_0(r) => r.save_state(),
            Binary_1_0(r) => r.save_state(),
        };
        // If we hit an IVM that changed the encoding but we haven't changed our reader yet,
        // we still want to report the new encoding.
        if let Some(new_encoding) = self.new_encoding {
            return RawReaderState::new(
                reader_state.data(),
                reader_state.offset(),
                reader_state.is_final_data(),
                new_encoding,
            );
        }
        reader_state
    }

    fn next(&mut self) -> IonResult<LazyRawStreamItem<'data, AnyEncoding>> {
        // If we previously ran into an IVM that changed the stream encoding, replace our reader
        // with one that can read the new encoding.
        if let Some(new_encoding) = self.new_encoding.take() {
            let mut reader_state = self.save_state();
            reader_state.set_encoding(new_encoding);
            let new_encoding_reader =
                RawReaderKind::resume_at_offset(self.encoding_reader.context(), reader_state);
            self.encoding_reader = new_encoding_reader;
        }

        use RawReaderKind::*;
        let item: LazyRawStreamItem<'_, AnyEncoding> = match &mut self.encoding_reader {
            Text_1_0(r) => r.next()?.into(),
            Binary_1_0(r) => r.next()?.into(),
        };

        // If this item is an IVM:
        //   * the encoding context will be reset, but this is handled by higher-level readers.
        //   * the encoding itself may change, and we need to handle that at this level.
        if let RawStreamItem::VersionMarker(ivm) = item {
            let ivm_old_encoding = ivm.stream_encoding_before_marker();
            let ivm_new_encoding = ivm.stream_encoding_after_marker()?;
            // TODO(pt005b): `IonVersion::v1_1` still exists, so `stream_encoding_after_marker()`
            //               reports an Ion 1.1 IVM as supported. `AnyEncoding` has no Ion 1.1
            //               readers, so reject it here. When `IonVersion::v1_1` is removed,
            //               `stream_encoding_after_marker()` will supply this error itself and
            //               this check can go away.
            if ivm_new_encoding.version() == IonVersion::v1_1 {
                let (major, minor) = ivm.major_minor();
                return IonResult::decoding_error(format!(
                    "Ion version {major}.{minor} is not supported"
                ));
            }
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
    pub fn kind(&self) -> LazyRawValueKind<'top> {
        self.encoding
    }

    pub fn encoding(&self) -> IonEncoding {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(_) => TextEncoding_1_0.encoding(),
            Binary_1_0(_) => BinaryEncoding_1_0.encoding(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawValueKind<'top> {
    Text_1_0(LazyRawTextValue_1_0<'top>),
    Binary_1_0(&'top LazyRawBinaryValue_1_0<'top>),
}

impl<'top> From<LazyRawTextValue_1_0<'top>> for LazyRawAnyValue<'top> {
    fn from(value: LazyRawTextValue_1_0<'top>) -> Self {
        LazyRawAnyValue {
            encoding: LazyRawValueKind::Text_1_0(value),
        }
    }
}

impl<'top> From<&'top LazyRawBinaryValue_1_0<'top>> for LazyRawAnyValue<'top> {
    fn from(value: &'top LazyRawBinaryValue_1_0<'top>) -> Self {
        LazyRawAnyValue {
            encoding: LazyRawValueKind::Binary_1_0(value),
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

impl<'top> HasSpan<'top> for LazyRawAnyValue<'top> {
    fn span(&self) -> Span<'top> {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.span(),
            Binary_1_0(v) => v.span(),
        }
    }
}

impl HasRange for LazyRawAnyValue<'_> {
    fn range(&self) -> Range<usize> {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.range(),
            Binary_1_0(v) => v.range(),
        }
    }
}

impl<'top> LazyRawValue<'top, AnyEncoding> for LazyRawAnyValue<'top> {
    fn ion_type(&self) -> IonType {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.ion_type(),
            Binary_1_0(v) => v.ion_type(),
        }
    }

    fn is_null(&self) -> bool {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.is_null(),
            Binary_1_0(v) => v.is_null(),
        }
    }

    fn is_delimited(&self) -> bool {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.is_delimited(),
            Binary_1_0(v) => v.is_delimited(),
        }
    }

    fn has_annotations(&self) -> bool {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => v.has_annotations(),
            Binary_1_0(v) => v.has_annotations(),
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
        }
    }

    fn read(&self) -> IonResult<RawValueRef<'top, AnyEncoding>> {
        use LazyRawValueKind::*;
        match &self.encoding {
            Text_1_0(v) => Ok(v.read()?.into()),
            Binary_1_0(v) => Ok(v.read()?.into()),
        }
    }

    fn annotations_span(&self) -> Span<'top> {
        match &self.encoding {
            LazyRawValueKind::Text_1_0(v) => v.annotations_span(),
            LazyRawValueKind::Binary_1_0(v) => v.annotations_span(),
        }
    }

    fn value_span(&self) -> Span<'top> {
        match &self.encoding {
            LazyRawValueKind::Text_1_0(v) => v.value_span(),
            LazyRawValueKind::Binary_1_0(v) => v.value_span(),
        }
    }

    fn with_backing_data(&self, span: Span<'top>) -> Self {
        Self {
            encoding: match &self.encoding {
                LazyRawValueKind::Text_1_0(v) => {
                    LazyRawValueKind::Text_1_0(v.with_backing_data(span))
                }
                LazyRawValueKind::Binary_1_0(v) => {
                    LazyRawValueKind::Binary_1_0(v.with_backing_data(span))
                }
            },
        }
    }

    fn encoding(&self) -> IonEncoding {
        match self.encoding {
            LazyRawValueKind::Text_1_0(_) => IonEncoding::Text_1_0,
            LazyRawValueKind::Binary_1_0(_) => IonEncoding::Binary_1_0,
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
}

impl<'top> Iterator for RawAnyAnnotationsIterator<'top> {
    type Item = IonResult<RawSymbolRef<'top>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.encoding {
            RawAnnotationsIteratorKind::Text_1_0(i) => i.next(),
            RawAnnotationsIteratorKind::Binary_1_0(i) => i.next(),
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
    Text_1_0(RawTextList<'top, TextEncoding_1_0>),
    Binary_1_0(LazyRawBinaryList_1_0<'top>),
}

impl<'top> LazyContainerPrivate<'top, AnyEncoding> for LazyRawAnyList<'top> {
    fn from_value(value: LazyRawAnyValue<'top>) -> Self {
        use LazyRawValueKind::*;
        match value.encoding {
            Text_1_0(v) => LazyRawAnyList {
                encoding: LazyRawListKind::Text_1_0(RawTextList::from_value(v)),
            },
            Binary_1_0(v) => LazyRawAnyList {
                encoding: LazyRawListKind::Binary_1_0(LazyRawBinaryList_1_0::from_value(v)),
            },
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawAnyListIterator<'data> {
    encoding: RawAnyListIteratorKind<'data>,
}

#[derive(Debug, Copy, Clone)]
pub enum RawAnyListIteratorKind<'data> {
    Text_1_0(RawTextSequenceCacheIterator<'data, TextEncoding_1_0>),
    Binary_1_0(RawBinarySequenceIterator_1_0<'data>),
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
        }
    }
}

impl<'top> LazyRawContainer<'top, AnyEncoding> for LazyRawAnyList<'top> {
    fn as_value(&self) -> <AnyEncoding as Decoder>::Value<'top> {
        match &self.encoding {
            LazyRawListKind::Text_1_0(s) => s.as_value().into(),
            LazyRawListKind::Binary_1_0(s) => s.as_value().into(),
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
        }
    }
}

impl<'data> From<RawTextList<'data, TextEncoding_1_0>> for LazyRawAnyList<'data> {
    fn from(value: RawTextList<'data, TextEncoding_1_0>) -> Self {
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
    Text_1_0(RawTextSExp<'data, TextEncoding_1_0>),
    Binary_1_0(LazyRawBinarySExp_1_0<'data>),
}

impl<'top> LazyRawContainer<'top, AnyEncoding> for LazyRawAnySExp<'top> {
    fn as_value(&self) -> <AnyEncoding as Decoder>::Value<'top> {
        use LazyRawSExpKind::*;
        match self.encoding {
            Text_1_0(s) => s.as_value().into(),
            Binary_1_0(s) => s.as_value().into(),
        }
    }
}

impl<'data> LazyContainerPrivate<'data, AnyEncoding> for LazyRawAnySExp<'data> {
    fn from_value(value: LazyRawAnyValue<'data>) -> Self {
        match value.encoding {
            LazyRawValueKind::Text_1_0(v) => LazyRawAnySExp {
                encoding: LazyRawSExpKind::Text_1_0(RawTextSExp::from_value(v)),
            },
            LazyRawValueKind::Binary_1_0(v) => LazyRawAnySExp {
                encoding: LazyRawSExpKind::Binary_1_0(LazyRawBinarySExp_1_0::from_value(v)),
            },
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawAnySExpIterator<'data> {
    encoding: RawAnySExpIteratorKind<'data>,
}

#[derive(Debug, Copy, Clone)]
pub enum RawAnySExpIteratorKind<'data> {
    Text_1_0(RawTextSequenceCacheIterator<'data, TextEncoding_1_0>),
    Binary_1_0(RawBinarySequenceIterator_1_0<'data>),
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
        }
    }
}

impl<'data> From<RawTextSExp<'data, TextEncoding_1_0>> for LazyRawAnySExp<'data> {
    fn from(value: RawTextSExp<'data, TextEncoding_1_0>) -> Self {
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

// ===== Structs =====

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyStruct<'data> {
    encoding: LazyRawStructKind<'data>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawStructKind<'data> {
    Text_1_0(LazyRawTextStruct<'data, TextEncoding_1_0>),
    Binary_1_0(LazyRawBinaryStruct_1_0<'data>),
}

impl<'top> LazyRawContainer<'top, AnyEncoding> for LazyRawAnyStruct<'top> {
    fn as_value(&self) -> <AnyEncoding as Decoder>::Value<'top> {
        match self.encoding {
            LazyRawStructKind::Text_1_0(s) => s.as_value().into(),
            LazyRawStructKind::Binary_1_0(s) => s.as_value().into(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawAnyFieldName<'data> {
    encoding: LazyRawFieldNameKind<'data>,
}

#[derive(Debug, Copy, Clone)]
pub enum LazyRawFieldNameKind<'data> {
    Text_1_0(LazyRawTextFieldName<'data, TextEncoding_1_0>),
    Binary_1_0(LazyRawBinaryFieldName_1_0<'data>),
}

impl<'top> HasSpan<'top> for LazyRawAnyFieldName<'top> {
    fn span(&self) -> Span<'top> {
        use LazyRawFieldNameKind::*;
        match self.encoding {
            Text_1_0(name) => name.span(),
            Binary_1_0(name) => name.span(),
        }
    }
}

impl HasRange for LazyRawAnyFieldName<'_> {
    fn range(&self) -> Range<usize> {
        use LazyRawFieldNameKind::*;
        match self.encoding {
            Text_1_0(name) => name.range(),
            Binary_1_0(name) => name.range(),
        }
    }
}

impl<'top> LazyRawFieldName<'top, AnyEncoding> for LazyRawAnyFieldName<'top> {
    fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        use LazyRawFieldNameKind::*;
        match self.encoding {
            Text_1_0(name) => name.read(),
            Binary_1_0(name) => name.read(),
        }
    }
}

impl<'top> From<LazyRawFieldNameKind<'top>> for LazyRawAnyFieldName<'top> {
    fn from(value: LazyRawFieldNameKind<'top>) -> Self {
        LazyRawAnyFieldName { encoding: value }
    }
}

impl<'top> From<LazyRawTextFieldName<'top, TextEncoding_1_0>> for LazyRawAnyFieldName<'top> {
    fn from(value: LazyRawTextFieldName<'top, TextEncoding_1_0>) -> Self {
        LazyRawFieldNameKind::Text_1_0(value).into()
    }
}

impl<'top> From<LazyRawBinaryFieldName_1_0<'top>> for LazyRawAnyFieldName<'top> {
    fn from(value: LazyRawBinaryFieldName_1_0<'top>) -> Self {
        LazyRawFieldNameKind::Binary_1_0(value).into()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawAnyStructIterator<'data> {
    encoding: RawAnyStructIteratorKind<'data>,
}

#[derive(Debug, Copy, Clone)]
pub enum RawAnyStructIteratorKind<'data> {
    Text_1_0(RawTextStructCacheIterator<'data, TextEncoding_1_0>),
    Binary_1_0(RawBinaryStructIterator_1_0<'data>),
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

impl<'data> LazyContainerPrivate<'data, AnyEncoding> for LazyRawAnyStruct<'data> {
    fn from_value(value: LazyRawAnyValue<'data>) -> Self {
        match value.encoding {
            LazyRawValueKind::Text_1_0(v) => LazyRawAnyStruct {
                encoding: LazyRawStructKind::Text_1_0(
                    LazyRawTextStruct::<TextEncoding_1_0>::from_value(v),
                ),
            },
            LazyRawValueKind::Binary_1_0(v) => LazyRawAnyStruct {
                encoding: LazyRawStructKind::Binary_1_0(LazyRawBinaryStruct_1_0::from_value(v)),
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
        }
    }
}

impl<'data> From<LazyRawTextStruct<'data, TextEncoding_1_0>> for LazyRawAnyStruct<'data> {
    fn from(value: LazyRawTextStruct<'data, TextEncoding_1_0>) -> Self {
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

            let mut reader = LazyRawAnyReader::new(context, data, true);
            assert_eq!(reader.next()?.expect_ivm()?.major_minor(), (1, 0));
            let _strukt = reader.next()?.expect_value()?.read()?.expect_struct()?;
            let name = reader.next()?.expect_value()?;
            assert_eq!(
                name.annotations().next().unwrap()?,
                RawSymbolRef::SymbolId(4)
            );
            assert_eq!(name.read()?.expect_string()?.text(), "Gary");
            assert_eq!(
                reader.next()?.expect_value()?.read()?,
                RawValueRef::String("foo".into())
            );
            assert_eq!(
                reader.next()?.expect_value()?.read()?,
                RawValueRef::Int(5.into())
            );
            assert_eq!(
                reader.next()?.expect_value()?.read()?,
                RawValueRef::Timestamp(Timestamp::with_year(2023).with_month(8).build()?)
            );
            assert_eq!(
                reader.next()?.expect_value()?.read()?,
                RawValueRef::Bool(false)
            );

            let mut sum = 0;
            for lazy_value_result in reader.next()?.expect_value()?.read()?.expect_list()?.iter() {
                sum += lazy_value_result?.expect_value()?.read()?.expect_i64()?;
            }
            assert_eq!(sum, 6);

            // We cannot test structs here because using them forces the binary encoding to have a
            // local symbol table and the raw reader interprets that as a different value.

            assert!(matches!(
                reader.next()?,
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
        reader: &mut LazyRawAnyReader<'_>,
        encoding_before: IonEncoding,
        encoding_after: IonEncoding,
    ) -> IonResult<()> {
        // The reader is using the expected encoding before we hit the IVM
        assert_eq!(reader.encoding(), encoding_before);
        // The next item is an IVM
        let ivm = reader.next()?.expect_ivm()?;
        // The IVM correctly reports the expected before/after encodings
        assert_eq!(ivm.stream_encoding_before_marker(), encoding_before);
        assert_eq!(ivm.stream_encoding_after_marker()?, encoding_after);
        // The reader is now using the new encoding
        assert_eq!(reader.encoding(), encoding_after);
        Ok(())
    }

    fn expect_int(
        reader: &mut LazyRawAnyReader<'_>,
        expected_encoding: IonEncoding,
        expected_int: i64,
    ) -> IonResult<()> {
        let value = reader.next()?.expect_value()?;
        let actual_int = value.read()?.expect_i64()?;
        assert_eq!(actual_int, expected_int);
        assert_eq!(reader.encoding(), expected_encoding);
        Ok(())
    }

    /// Asserts that the reader's next item is an IVM for an unsupported Ion version and that
    /// reading it produces an error. `AnyEncoding` only supports Ion 1.0, so an Ion 1.1 IVM must
    /// be rejected rather than silently mis-parsed as Ion 1.0.
    fn expect_unsupported_version(reader: &mut LazyRawAnyReader<'_>) {
        match reader.next() {
            Ok(_) => panic!("expected an unsupported-version error, but the item was accepted"),
            Err(error) => {
                let message = error.to_string();
                assert!(
                    message.contains("Ion version 1.1 is not supported"),
                    "expected an unsupported-version error, got: {message}"
                );
            }
        }
    }

    #[test]
    fn switch_text_versions() -> IonResult<()> {
        const DATA: &str = r#"
            1
            $ion_1_0
            2
            $ion_1_1
            3
        "#;

        let encoding_context = EncodingContext::empty();
        let mut reader = LazyRawAnyReader::new(encoding_context.get_ref(), DATA.as_bytes(), true);

        expect_int(&mut reader, IonEncoding::Text_1_0, 1)?;

        // This IVM doesn't change the encoding.
        expect_version_change(&mut reader, IonEncoding::Text_1_0, IonEncoding::Text_1_0)?;

        expect_int(&mut reader, IonEncoding::Text_1_0, 2)?;

        // `AnyEncoding` has no Ion 1.1 reader, so the `$ion_1_1` IVM is rejected. The `3` that
        // follows it is never read.
        expect_unsupported_version(&mut reader);

        Ok(())
    }

    #[test]
    fn switch_binary_versions() -> IonResult<()> {
        const DATA: &[u8] = &[
            0xE0, 0x01, 0x00, 0xEA, // $ion_1_0
            0x21, 0x02, // 2
            0xE0, 0x01, 0x01, 0xEA, // $ion_1_1
            0x61, 0x03, // 3, encoded as binary Ion 1.1
        ];

        let encoding_context = EncodingContext::empty();
        let mut reader = LazyRawAnyReader::new(encoding_context.get_ref(), DATA, true);

        // When the reader is constructed it peeks at the leading bytes to see if they're an IVM.
        // In this case, they were a binary Ion v1.0 IVM, so the reader is already expecting to see
        // binary 1.0 data. Reading the binary version marker tells the reader to switch encodings.
        expect_version_change(
            &mut reader,
            IonEncoding::Binary_1_0,
            IonEncoding::Binary_1_0,
        )?;

        expect_int(&mut reader, IonEncoding::Binary_1_0, 2)?;

        // `AnyEncoding` has no Ion 1.1 reader, so the binary 1.1 IVM is rejected. The `3` that
        // follows it is never read.
        expect_unsupported_version(&mut reader);

        Ok(())
    }

    #[test]
    fn reject_leading_binary_1_1_ivm() {
        // `detect_encoding` hands a leading binary Ion 1.1 IVM to the binary 1.0 reader, which
        // surfaces it as a version marker for an unsupported version.
        const DATA: &[u8] = &[
            0xE0, 0x01, 0x01, 0xEA, // $ion_1_1
            0x61, 0x03, // 3, encoded as binary Ion 1.1
        ];

        let encoding_context = EncodingContext::empty();
        let mut reader = LazyRawAnyReader::new(encoding_context.get_ref(), DATA, true);
        expect_unsupported_version(&mut reader);
    }
}
