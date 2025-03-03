#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Range;

use crate::lazy::any_encoding::IonEncoding;
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, HasRange, HasSpan, LazyRawContainer, LazyRawFieldExpr, LazyRawReader, LazyRawStruct,
    LazyRawValue, LazyRawValueExpr,
};
use crate::lazy::encoding::{TextEncoding, TextEncoding_1_1};
use crate::lazy::expanded::macro_evaluator::RawEExpression;
use crate::lazy::expanded::macro_table::ION_1_1_SYSTEM_MACROS;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem, RawStreamItem};
use crate::lazy::span::Span;
use crate::lazy::streaming_raw_reader::RawReaderState;
use crate::lazy::text::buffer::{incomplete_is_ok, TextBuffer};
use crate::lazy::text::matched::MatchedValue;
use crate::lazy::text::parse_result::WithContext;
use crate::lazy::text::raw::v1_1::arg_group::{EExpArg, TextEExpArgGroup};
use crate::lazy::text::value::{LazyRawTextValue, RawTextAnnotationsIterator};
use crate::{v1_1, Encoding, IonResult};

use winnow::Parser;
pub struct LazyRawTextReader_1_1<'data> {
    input: TextBuffer<'data>,
}

impl<'data> LazyRawTextReader_1_1<'data> {
    pub fn context(&self) -> EncodingContextRef<'data> {
        self.input.context
    }
}

impl<'data> LazyRawReader<'data, TextEncoding_1_1> for LazyRawTextReader_1_1<'data> {
    fn new(context: EncodingContextRef<'data>, data: &'data [u8], is_final_data: bool) -> Self {
        Self::resume(
            context,
            RawReaderState::new(data, 0, is_final_data, IonEncoding::Text_1_1),
        )
    }

    fn resume(context: EncodingContextRef<'data>, saved_state: RawReaderState<'data>) -> Self {
        LazyRawTextReader_1_1 {
            input: TextBuffer::with_offset(
                context,
                saved_state.offset(),
                saved_state.data(),
                saved_state.is_final_data(),
            ),
        }
    }

    fn save_state(&self) -> RawReaderState<'data> {
        RawReaderState::new(
            self.input.bytes(),
            self.position(),
            self.input.is_final_data(),
            self.encoding(),
        )
    }

    fn next(&mut self) -> IonResult<LazyRawStreamItem<'data, TextEncoding_1_1>> {
        let _whitespace = self
            .input
            .match_optional_comments_and_whitespace()
            .with_context(
                "reading v1.1 whitespace/comments at the top level",
                self.input,
            )?;
        if self.input.is_empty() {
            return Ok(RawStreamItem::EndOfStream(EndPosition::new(
                TextEncoding_1_1.encoding(),
                self.input.offset(),
            )));
        }

        // Consume any trailing whitespace that followed this item. Doing this allows us to check
        // whether this was the last item in the buffer by testing `buffer.is_empty()` afterward.
        let matched_item = self
            .input
            .match_top_level_item_1_1()
            .with_context("reading a v1.1 top-level value", self.input)?;

        let _trailing_ws = incomplete_is_ok(TextBuffer::match_optional_comments_and_whitespace)
            .parse_next(&mut self.input)
            .with_context(
                "reading trailing top-level whitespace/comments in v1.1",
                self.input,
            )?;
        Ok(matched_item)
    }

    fn position(&self) -> usize {
        self.input.offset()
    }

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Text_1_1
    }
}

/// The index at which this macro can be found in the macro table.
pub type MacroAddress = usize;

/// An address in the Ion 1.1 system macro table.
/// Guaranteed to fit in a byte.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct SystemMacroAddress(u8);

impl SystemMacroAddress {
    pub fn new(address: MacroAddress) -> Option<Self> {
        if address < ION_1_1_SYSTEM_MACROS.len() {
            Some(Self(address as u8))
        } else {
            None
        }
    }

    pub const fn new_unchecked(address: MacroAddress) -> Self {
        Self(address as u8)
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    pub fn as_u8(&self) -> u8 {
        self.0
    }
}

pub(crate) mod system_macros {
    use crate::lazy::text::raw::v1_1::reader::SystemMacroAddress;

    pub const NONE: SystemMacroAddress = SystemMacroAddress(0x00);
    pub const VALUES: SystemMacroAddress = SystemMacroAddress(0x01);
    pub const DEFAULT: SystemMacroAddress = SystemMacroAddress(0x02);
    pub const META: SystemMacroAddress = SystemMacroAddress(0x03);
    pub const REPEAT: SystemMacroAddress = SystemMacroAddress(0x04);
    pub const FLATTEN: SystemMacroAddress = SystemMacroAddress(0x05);
    pub const DELTA: SystemMacroAddress = SystemMacroAddress(0x06);
    pub const SUM: SystemMacroAddress = SystemMacroAddress(0x07);
    pub const ANNOTATE: SystemMacroAddress = SystemMacroAddress(0x08);
    pub const MAKE_STRING: SystemMacroAddress = SystemMacroAddress(0x09);
    pub const MAKE_SYMBOL: SystemMacroAddress = SystemMacroAddress(0x0A);
    pub const MAKE_DECIMAL: SystemMacroAddress = SystemMacroAddress(0x0B);
    pub const MAKE_TIMESTAMP: SystemMacroAddress = SystemMacroAddress(0x0C);
    pub const MAKE_BLOB: SystemMacroAddress = SystemMacroAddress(0x0D);
    pub const MAKE_LIST: SystemMacroAddress = SystemMacroAddress(0x0E);
    pub const MAKE_SEXP: SystemMacroAddress = SystemMacroAddress(0x0F);
    pub const MAKE_FIELD: SystemMacroAddress = SystemMacroAddress(0x10);
    pub const MAKE_STRUCT: SystemMacroAddress = SystemMacroAddress(0x11);
    pub const PARSE_ION: SystemMacroAddress = SystemMacroAddress(0x12);
    pub const SET_SYMBOLS: SystemMacroAddress = SystemMacroAddress(0x13);
    pub const ADD_SYMBOLS: SystemMacroAddress = SystemMacroAddress(0x14);
    pub const SET_MACROS: SystemMacroAddress = SystemMacroAddress(0x15);
    pub const ADD_MACROS: SystemMacroAddress = SystemMacroAddress(0x16);
    pub const USE: SystemMacroAddress = SystemMacroAddress(0x17);
}

/// The index at which a value expression can be found within a template's body.
pub type TemplateBodyExprAddress = usize;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum MacroIdRef<'data> {
    LocalName(&'data str),
    LocalAddress(usize),
    SystemAddress(SystemMacroAddress),
    // TODO: Addresses and qualified names
}

impl Display for MacroIdRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            MacroIdRef::LocalName(name) => write!(f, "{}", name),
            MacroIdRef::LocalAddress(address) => write!(f, "{}", address),
            MacroIdRef::SystemAddress(address) => {
                write!(f, "$ion::{}", address.as_usize())
            }
        }
    }
}

impl From<usize> for MacroIdRef<'_> {
    fn from(address: usize) -> Self {
        MacroIdRef::LocalAddress(address)
    }
}

impl<'data> From<&'data str> for MacroIdRef<'data> {
    fn from(name: &'data str) -> Self {
        MacroIdRef::LocalName(name)
    }
}

impl From<SystemMacroAddress> for MacroIdRef<'_> {
    fn from(system_macro_address: SystemMacroAddress) -> Self {
        MacroIdRef::SystemAddress(system_macro_address)
    }
}

#[derive(Copy, Clone)]
pub struct TextEExpression_1_1<'top> {
    pub(crate) input: TextBuffer<'top>,
    pub(crate) id: MacroIdRef<'top>,
    pub(crate) arg_cache: &'top [EExpArg<'top, TextEncoding_1_1>],
}

impl<'top> HasSpan<'top> for TextEExpression_1_1<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl HasRange for TextEExpression_1_1<'_> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> RawEExpression<'top, TextEncoding_1_1> for TextEExpression_1_1<'top> {
    type RawArgumentsIterator = TextEExpArgsIterator_1_1<'top>;
    type ArgGroup = TextEExpArgGroup<'top>;

    fn id(self) -> MacroIdRef<'top> {
        self.id
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator {
        TextEExpArgsIterator_1_1::new(self.arg_cache)
    }
}

impl Debug for TextEExpression_1_1<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // This is a text macro and the parser accepted it, so it's valid UTF-8. We can `unwrap()`.
        write!(f, "<macro invocation '{}'>", self.input.as_text().unwrap())
    }
}

impl<'top> TextEExpression_1_1<'top> {
    pub(crate) fn new(
        id: MacroIdRef<'top>,
        input: TextBuffer<'top>,
        arg_cache: &'top [EExpArg<'top, TextEncoding_1_1>],
    ) -> Self {
        Self {
            input,
            id,
            arg_cache,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct EncodedTextMacroInvocation {
    // The ID always begins at index 2 (after the opening `(:`). The parameters follow the ID.
    id_length: u16,
}

impl EncodedTextMacroInvocation {
    pub fn new(id_length: u16) -> Self {
        Self { id_length }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawTextSequenceCacheIterator<'top, E: TextEncoding> {
    child_exprs: &'top [LazyRawValueExpr<'top, E>],
    index: usize,
}

impl<'top, E: TextEncoding> RawTextSequenceCacheIterator<'top, E> {
    pub fn new(child_exprs: &'top [LazyRawValueExpr<'top, E>]) -> Self {
        Self {
            child_exprs,
            index: 0,
        }
    }
}

impl<'top, E: TextEncoding> Iterator for RawTextSequenceCacheIterator<'top, E> {
    type Item = IonResult<LazyRawValueExpr<'top, E>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_expr = self.child_exprs.get(self.index)?;
        self.index += 1;
        Some(Ok(*next_expr))
    }
}

#[derive(Debug, Copy, Clone)]
pub struct TextEExpArgsIterator_1_1<'top> {
    arg_exprs: &'top [EExpArg<'top, v1_1::Text>],
    index: usize,
}

impl<'top> TextEExpArgsIterator_1_1<'top> {
    pub fn new(arg_exprs: &'top [EExpArg<'top, v1_1::Text>]) -> Self {
        Self {
            arg_exprs,
            index: 0,
        }
    }
}

impl<'top> Iterator for TextEExpArgsIterator_1_1<'top> {
    type Item = IonResult<EExpArg<'top, v1_1::Text>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_expr = self.arg_exprs.get(self.index)?;
        self.index += 1;
        Some(Ok(*next_expr))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let num_args = self.arg_exprs.len();
        // Tells the macro evaluator how much space to allocate to hold these arguments
        (num_args, Some(num_args))
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawTextStruct<'top, E: TextEncoding> {
    pub(crate) value: LazyRawTextValue<'top, E>,
}

impl<E: TextEncoding> Debug for LazyRawTextStruct<'_, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for field_result in self.iter() {
            let field = field_result?;
            use LazyRawFieldExpr::*;
            match field {
                NameValue(name, value) => {
                    write!(f, "{name:?}: {value:?}")
                }
                NameEExp(name, eexp) => {
                    write!(f, "{name:?}: {eexp:?}")
                }
                EExp(eexp) => {
                    write!(f, "{eexp:?}")
                }
            }?;
        }
        write!(f, "}}").unwrap();

        Ok(())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawTextStructCacheIterator<'top, E: TextEncoding> {
    field_exprs: &'top [LazyRawFieldExpr<'top, E>],
    index: usize,
}

impl<'top, E: TextEncoding> RawTextStructCacheIterator<'top, E> {
    pub fn new(field_exprs: &'top [LazyRawFieldExpr<'top, E>]) -> Self {
        Self {
            field_exprs,
            index: 0,
        }
    }
}

impl<'top, E: TextEncoding> Iterator for RawTextStructCacheIterator<'top, E> {
    type Item = IonResult<LazyRawFieldExpr<'top, E>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_expr = self.field_exprs.get(self.index)?;
        self.index += 1;
        // TODO: Remove the result wrapper because these values are already in the cache
        Some(Ok(*next_expr))
    }
}

impl<'top, E: TextEncoding> LazyContainerPrivate<'top, E> for LazyRawTextStruct<'top, E> {
    fn from_value(value: LazyRawTextValue<'top, E>) -> Self {
        LazyRawTextStruct { value }
    }
}

impl<'top, E: TextEncoding> LazyRawContainer<'top, E> for LazyRawTextStruct<'top, E> {
    fn as_value(&self) -> <E as Decoder>::Value<'top> {
        self.value
    }
}

impl<'top, E: TextEncoding> LazyRawStruct<'top, E> for LazyRawTextStruct<'top, E> {
    type Iterator = RawTextStructCacheIterator<'top, E>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'top> {
        self.value.annotations()
    }

    fn iter(&self) -> Self::Iterator {
        let MatchedValue::Struct(field_exprs) = self.value.encoded_value.matched() else {
            unreachable!("struct contained a matched value of the wrong type")
        };
        RawTextStructCacheIterator::new(field_exprs)
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::any_encoding::IonVersion;
    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::raw_value_ref::RawValueRef;
    use crate::{IonType, RawVersionMarker};

    use super::*;

    fn expect_next<'data>(
        reader: &mut LazyRawTextReader_1_1<'data>,
        expected: RawValueRef<'data, TextEncoding_1_1>,
    ) {
        let lazy_value = reader
            .next()
            .expect("advancing the reader failed")
            .expect_value()
            .expect("expected a value");
        assert_eq!(
            matches!(expected, RawValueRef::Null(_)),
            lazy_value.is_null()
        );
        let value_ref = lazy_value.read().expect("reading failed");
        assert_eq!(value_ref, expected, "{:?} != {:?}", value_ref, expected);
    }

    #[test]
    fn top_level() -> IonResult<()> {
        let data = r#"
            $ion_1_1
            "foo"
            bar
            (baz null.string)
            (:quux quuz)
            77
            false
       "#;

        let mut context = EncodingContext::for_ion_version(IonVersion::v1_1);
        let macro_quux =
            TemplateCompiler::compile_from_source(context.get_ref(), "(macro quux (x) null)")?;
        context.macro_table_mut().add_template_macro(macro_quux)?;
        let reader = &mut LazyRawTextReader_1_1::new(context.get_ref(), data.as_bytes(), true);

        // $ion_1_1
        assert_eq!(reader.next()?.expect_ivm()?.major_minor(), (1, 1));
        // "foo"
        expect_next(reader, RawValueRef::String("foo".into()));
        // bar
        expect_next(reader, RawValueRef::Symbol("bar".into()));
        // (baz null.string)
        let sexp = reader.next()?.expect_value()?.read()?.expect_sexp()?;
        let mut children = sexp.iter();
        assert_eq!(
            children.next().unwrap()?.expect_value()?.read()?,
            RawValueRef::Symbol("baz".into())
        );
        assert_eq!(
            children.next().unwrap()?.expect_value()?.read()?,
            RawValueRef::Null(IonType::String)
        );
        assert!(children.next().is_none());
        // (:quux quuz)
        let macro_invocation = reader.next()?.expect_eexp()?;
        assert_eq!(macro_invocation.id, MacroIdRef::LocalName("quux"));
        expect_next(reader, RawValueRef::Int(77.into()));
        expect_next(reader, RawValueRef::Bool(false));
        Ok(())
    }
}
