use std::fmt::Debug;
use std::io::Write;
use std::ops::Range;

use crate::lazy::any_encoding::{IonEncoding, IonVersion};
use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
use crate::lazy::encoder::text::v1_1::writer::LazyRawTextWriter_1_1;
use crate::lazy::encoder::write_as_ion::{WriteableEExp, WriteableRawValue};
use crate::lazy::encoding::{
    BinaryEncoding, BinaryEncoding_1_0, RawValueLiteral, TextEncoding_1_0,
};
use crate::lazy::expanded::macro_evaluator::RawEExpression;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::raw_stream_item::LazyRawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::span::Span;
use crate::lazy::streaming_raw_reader::RawReaderState;
use crate::read_config::ReadConfig;
use crate::result::IonFailure;
use crate::{
    v1_0, v1_1, Catalog, Encoding, FieldExpr, IonResult, IonType, LazyExpandedFieldName,
    LazyExpandedValue, LazyRawAnyFieldName, LazyRawWriter, MacroExpr, RawSymbolRef, ValueExpr,
    ValueRef,
};

pub trait HasSpan<'top>: HasRange {
    fn span(&self) -> Span<'top>;
}

pub trait HasRange {
    fn range(&self) -> Range<usize>;

    /// Returns the number of bytes this encoded item occupies.
    ///
    /// This method is equivalent to calling `.range().len()`, but types have the option to
    /// override its implementation if the length can be found more quickly without computing the
    /// range first.
    fn byte_length(&self) -> usize {
        self.range().len()
    }
}

impl HasRange for Range<usize> {
    fn range(&self) -> Range<usize> {
        self.start..self.end
    }
}

/// A family of types that collectively comprise the lazy reader API for an Ion serialization
/// format. These types operate at the 'raw' level; they do not attempt to resolve symbols
/// using the active symbol table.
// Implementations of this trait are typically unit structs that are never instantiated.
// However, many types are generic over some `D: LazyDecoder`, and having this trait
// extend 'static, Sized, Debug, Clone and Copy means that those types can #[derive(...)]
// those traits themselves without boilerplate `where` clauses.
pub trait Decoder: 'static + Sized + Debug + Clone + Copy {
    /// The Ion encoding that this decoder expects to read at the outset of the stream.
    /// This determines how the encoding context is initialized.
    /// The version may change if an Ion version marker is encountered.
    /// Decoders may or may not support multiple Ion versions.
    const INITIAL_ENCODING_EXPECTED: IonEncoding;

    /// A lazy reader that yields [`Self::Value`]s representing the top level values in its input.
    type Reader<'data>: LazyRawReader<'data, Self>;
    /// A value (at any depth) in the input. This can be further inspected to access either its
    /// scalar data or, if it is a container, to view it as [`Self::List`], [`Self::SExp`] or
    /// [`Self::Struct`].
    type Value<'top>: LazyRawValue<'top, Self>;

    /// A list whose child values may be accessed iteratively.
    type SExp<'top>: LazyRawSequence<'top, Self>;
    /// An s-expression whose child values may be accessed iteratively.
    type List<'top>: LazyRawSequence<'top, Self>;
    /// A struct whose fields may be accessed iteratively or by field name.
    type Struct<'top>: LazyRawStruct<'top, Self>;
    /// A symbol token representing the name of a field within a struct.
    type FieldName<'top>: LazyRawFieldName<'top, Self>;
    /// An iterator over the annotations on the input stream's values.
    type AnnotationsIterator<'top>: Iterator<Item = IonResult<RawSymbolRef<'top>>>;
    /// An e-expression invoking a macro. (Ion 1.1+)
    type EExp<'top>: RawEExpression<'top, Self>;

    type VersionMarker<'top>: RawVersionMarker<'top>;

    fn with_catalog(self, catalog: impl Catalog + 'static) -> ReadConfig<Self> {
        ReadConfig::new_with_catalog(self, catalog)
    }
}

pub trait RawVersionMarker<'top>: Debug + Copy + Clone + HasSpan<'top> {
    /// Returns the major version of the Ion encoding to which the stream is switching.
    fn major(&self) -> u8 {
        self.major_minor().0
    }

    /// Returns the minor version of the Ion encoding to which the stream is switching.
    fn minor(&self) -> u8 {
        self.major_minor().1
    }

    /// Returns a tuple representing the `(major, minor)` version pair for the Ion encoding
    /// to which the stream is switching.
    fn major_minor(&self) -> (u8, u8);

    /// If this marker is encoded in binary Ion, returns `true`. Otherwise, returns `false`.
    ///
    /// Ion streams can switch versions (for example: from v1.0 to v1.1 or vice-versa), but they
    /// cannot change formats (for example: from binary to text or vice-versa). Therefore the value
    /// returned by this method will be true for the stream prior to the IVM _and_ for the stream
    /// that follows the IVM.
    fn is_binary(&self) -> bool {
        self.stream_encoding_before_marker().is_binary()
    }

    /// If this marker is encoded in text Ion, returns `true`. Otherwise, returns `false`.
    ///
    /// Ion streams can switch versions (for example: from v1.0 to v1.1 or vice-versa), but they
    /// cannot change formats (for example: from binary to text or vice-versa). Therefore, the value
    /// returned by this method will be true for the stream prior to the IVM _and_ for the stream
    /// that follows the IVM.
    // This is currently unused, but provided for symmetry with `is_binary`.
    #[allow(dead_code)]
    fn is_text(&self) -> bool {
        self.stream_encoding_before_marker().is_text()
    }

    /// The `IonVersion` that was used to encode this IVM.
    #[allow(dead_code)]
    fn stream_version_before_marker(&self) -> IonVersion {
        self.stream_encoding_before_marker().version()
    }

    /// If this marker's `(major, minor)` version pair represents a supported Ion version,
    /// returns `Ok(ion_version)`. Otherwise, returns a decoding error. To access the marker's
    /// version without confirming it is supported, see [`major_minor`](Self::major_minor).
    fn stream_version_after_marker(&self) -> IonResult<IonVersion> {
        match self.major_minor() {
            (1, 0) => Ok(IonVersion::v1_0),
            #[cfg(feature = "experimental-ion-1-1")]
            (1, 1) => Ok(IonVersion::v1_1),
            (major, minor) => {
                IonResult::decoding_error(format!("Ion version {major}.{minor} is not supported"))
            }
        }
    }

    fn stream_encoding_before_marker(&self) -> IonEncoding;

    /// If this marker's `(major, minor)` version pair represents a supported Ion version,
    /// returns `Ok(ion_encoding)`. Otherwise, returns a decoding error. To access the marker's
    /// encoding information without confirming it is supported, see [`major_minor`](Self::major_minor) and
    /// [`is_binary`](Self::is_binary)/[`is_text`](Self::is_text).
    fn stream_encoding_after_marker(&self) -> IonResult<IonEncoding> {
        let encoding = match (self.is_binary(), self.stream_version_after_marker()?) {
            (true, IonVersion::v1_0) => IonEncoding::Binary_1_0,
            (false, IonVersion::v1_0) => IonEncoding::Text_1_0,
            (true, IonVersion::v1_1) => IonEncoding::Binary_1_1,
            (false, IonVersion::v1_1) => IonEncoding::Text_1_1,
        };
        Ok(encoding)
    }
}

/// An expression found in value position in either serialized Ion or a template.
/// If it is a value literal, it is considered a stream with exactly one Ion value.
/// If it is a macro invocation, it is a stream with zero or more Ion values.
///
/// When working with `RawValueExpr`s that always use a given decoder's `Value` and
/// `MacroInvocation` associated types, consider using [`LazyRawValueExpr`] instead.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum RawValueExpr<V, E> {
    /// A value literal. For example: `5`, `foo`, or `"hello"` in text.
    ValueLiteral(V),
    /// An Ion 1.1+ macro invocation. For example: `(:employee 12345 "Sarah" "Gonzalez")` in text.
    EExp(E),
}

// `RawValueExpr` above has no ties to a particular encoding. The `LazyRawValueExpr` type alias
// below uses the `Value` and `MacroInvocation` associated types from the decoder `D`. In most
// places, this is a helpful constraint; we can talk about the value expression in terms of the
// LazyDecoder it's associated with. However, in some places (primarily when expanding template
// values that don't have a LazyDecoder) we need to be able to use it without constraints.

/// An item found in value position within an Ion data stream written in the encoding represented
/// by the LazyDecoder `D`. This item may be either a value literal or a macro invocation.
///
/// For a version of this type that is not constrained to a particular encoding, see
/// [`RawValueExpr`].
pub type LazyRawValueExpr<'top, D> =
    RawValueExpr<<D as Decoder>::Value<'top>, <D as Decoder>::EExp<'top>>;

impl<V: Debug, M: Debug> RawValueExpr<V, M> {
    pub fn expect_value(self) -> IonResult<V> {
        match self {
            RawValueExpr::ValueLiteral(v) => Ok(v),
            RawValueExpr::EExp(_m) => IonResult::decoding_error(
                "expected a value literal, but found a macro invocation ({:?})",
            ),
        }
    }

    pub fn expect_macro(self) -> IonResult<M> {
        match self {
            RawValueExpr::ValueLiteral(v) => IonResult::decoding_error(format!(
                "expected a macro invocation but found a value literal ({v:?})",
            )),
            RawValueExpr::EExp(m) => Ok(m),
        }
    }
}

impl<V, M> RawValueExpr<V, M> {
    pub fn resolve<'top, D>(
        self,
        context: EncodingContextRef<'top>,
    ) -> IonResult<ValueExpr<'top, D>>
    where
        V: LazyRawValue<'top, D>,
        M: RawEExpression<'top, D>,
        D: Decoder<Value<'top> = V, EExp<'top> = M>,
    {
        let expr = match self {
            RawValueExpr::ValueLiteral(value) => {
                ValueExpr::ValueLiteral(LazyExpandedValue::from_literal(context, value))
            }
            RawValueExpr::EExp(invocation) => {
                ValueExpr::MacroInvocation(MacroExpr::from_eexp(invocation.resolve(context)?))
            }
        };
        Ok(expr)
    }
}

impl<V: HasRange, M: HasRange> HasRange for RawValueExpr<V, M> {
    fn range(&self) -> Range<usize> {
        match self {
            RawValueExpr::ValueLiteral(value) => value.range(),
            RawValueExpr::EExp(eexp) => eexp.range(),
        }
    }
}

impl<'top, V: HasSpan<'top>, M: HasSpan<'top>> HasSpan<'top> for RawValueExpr<V, M> {
    fn span(&self) -> Span<'top> {
        match self {
            RawValueExpr::ValueLiteral(value) => value.span(),
            RawValueExpr::EExp(eexp) => eexp.span(),
        }
    }
}

/// A (name, value expression) pair representing a field in a struct.
/// The value expression may be either:
///   * a value literal
///   * an e-expression
#[derive(Copy, Clone, Debug)]
pub enum LazyRawFieldExpr<'top, D: Decoder> {
    NameValue(D::FieldName<'top>, D::Value<'top>),
    NameEExp(D::FieldName<'top>, D::EExp<'top>),
    EExp(D::EExp<'top>),
}

impl<'top, D: Decoder> LazyRawFieldExpr<'top, D> {
    pub fn resolve(self, context: EncodingContextRef<'top>) -> IonResult<FieldExpr<'top, D>> {
        use LazyRawFieldExpr::*;
        let field = match self {
            NameValue(name, value) => FieldExpr::NameValue(
                name.resolve(context),
                LazyExpandedValue::from_literal(context, value),
            ),
            NameEExp(name, eexp) => {
                FieldExpr::NameMacro(name.resolve(context), eexp.resolve(context)?.into())
            }
            EExp(eexp) => FieldExpr::EExp(eexp.resolve(context)?),
        };
        Ok(field)
    }

    pub fn expect_name_value(self) -> IonResult<(D::FieldName<'top>, D::Value<'top>)> {
        let LazyRawFieldExpr::NameValue(name, value) = self else {
            return IonResult::decoding_error(format!(
                "expected a name/value pair but found {self:?}",
            ));
        };
        Ok((name, value))
    }

    pub fn expect_name_eexp(self) -> IonResult<(D::FieldName<'top>, D::EExp<'top>)> {
        let LazyRawFieldExpr::NameEExp(name, eexp) = self else {
            return IonResult::decoding_error(format!(
                "expected a name/e-expression pair but found {self:?}",
            ));
        };
        Ok((name, eexp))
    }

    pub fn expect_eexp(self) -> IonResult<D::EExp<'top>> {
        let LazyRawFieldExpr::EExp(eexp) = self else {
            return IonResult::decoding_error(format!(
                "expected an e-expression but found {self:?}",
            ));
        };
        Ok(eexp)
    }
}

// ======= 1.0 text fields are guaranteed to have a name and value ======

impl<'top> LazyRawFieldExpr<'top, TextEncoding_1_0> {
    pub fn name(&self) -> <TextEncoding_1_0 as Decoder>::FieldName<'top> {
        use LazyRawFieldExpr::*;
        match self {
            NameValue(name, _value) => *name,
            NameEExp(_, _) => unreachable!("name/eexp field in text Ion 1.0"),
            EExp(_) => unreachable!("eexp field in text Ion 1.0"),
        }
    }
    pub fn value(&self) -> <TextEncoding_1_0 as Decoder>::Value<'top> {
        use LazyRawFieldExpr::*;
        match self {
            NameValue(_name, value) => *value,
            NameEExp(_, _) => unreachable!("name/eexp field in text Ion 1.0"),
            EExp(_) => unreachable!("eexp field in text Ion 1.0"),
        }
    }

    pub fn name_and_value(
        &self,
    ) -> (
        <TextEncoding_1_0 as Decoder>::FieldName<'top>,
        <TextEncoding_1_0 as Decoder>::Value<'top>,
    ) {
        use LazyRawFieldExpr::*;
        match self {
            NameValue(name, value) => (*name, *value),
            NameEExp(_, _) => unreachable!("name/eexp field in text Ion 1.0"),
            EExp(_) => unreachable!("eexp field in text Ion 1.0"),
        }
    }
}

// ======= 1.0 binary fields are guaranteed to have a name and value ======

impl<'top> LazyRawFieldExpr<'top, BinaryEncoding_1_0> {
    pub fn name(&self) -> <BinaryEncoding_1_0 as Decoder>::FieldName<'top> {
        use LazyRawFieldExpr::*;
        match self {
            NameValue(name, _value) => *name,
            NameEExp(_, _) => unreachable!("name/eexp field in binary Ion 1.0"),
            EExp(_) => unreachable!("eexp field in text Ion 1.0"),
        }
    }
    pub fn value(&self) -> <BinaryEncoding_1_0 as Decoder>::Value<'top> {
        use LazyRawFieldExpr::*;
        match self {
            NameValue(_name, value) => *value,
            NameEExp(_, _) => unreachable!("name/eexp field in text Ion 1.0"),
            EExp(_) => unreachable!("eexp field in text Ion 1.0"),
        }
    }

    pub fn name_and_value(
        &self,
    ) -> (
        <BinaryEncoding_1_0 as Decoder>::FieldName<'top>,
        <BinaryEncoding_1_0 as Decoder>::Value<'top>,
    ) {
        use LazyRawFieldExpr::*;
        match self {
            NameValue(name, value) => (*name, *value),
            NameEExp(_, _) => unreachable!("name/eexp field in text Ion 1.0"),
            EExp(_) => unreachable!("eexp field in text Ion 1.0"),
        }
    }
}

impl<D: Decoder> HasRange for LazyRawFieldExpr<'_, D> {
    // This type does not offer a `span()` method to get the bytes of the entire field.
    // In the case of a name/value or name/eexp pair, text parsers would need to provide a span that
    // included the interstitial whitespace and delimiting `:` between the name and value,
    // which is not especially useful.
    fn range(&self) -> Range<usize> {
        match self {
            LazyRawFieldExpr::NameValue(name, value) => name.range().start..value.range().end,
            LazyRawFieldExpr::NameEExp(name, eexp) => name.range().start..eexp.range().end,
            LazyRawFieldExpr::EExp(eexp) => eexp.range(),
        }
    }
}

// This private module houses public traits. This allows the public traits below to depend on them,
// but keeps users from being able to use them.
//
// For example: `LazyRawField` is a public trait that extends `LazyRawFieldPrivate`, a trait that
// contains functions which are implementation details we reserve the right to change at any time.
// `LazyRawFieldPrivate` is a public trait that lives in a crate-visible module. This allows
// internal code that is defined in terms of `LazyRawField` to call the private `into_value()`
// function while also preventing users from seeing or depending on it.
pub(crate) mod private {
    use crate::lazy::expanded::macro_evaluator::RawEExpression;
    use crate::lazy::expanded::r#struct::FieldExpr;
    use crate::lazy::expanded::EncodingContextRef;
    use crate::{try_next, try_or_some_err, IonResult, LazyExpandedValue, LazyRawFieldName};

    use super::{Decoder, LazyRawFieldExpr, LazyRawStruct};

    pub trait LazyContainerPrivate<'top, D: Decoder> {
        /// Constructs a new lazy raw container from a lazy raw value that has been confirmed to be
        /// of the correct type.
        fn from_value(value: D::Value<'top>) -> Self;
    }

    pub struct RawStructFieldExprIterator<'top, D: Decoder> {
        context: EncodingContextRef<'top>,
        raw_fields: <D::Struct<'top> as LazyRawStruct<'top, D>>::Iterator,
    }

    impl<'top, D: Decoder> RawStructFieldExprIterator<'top, D> {
        pub fn new(
            context: EncodingContextRef<'top>,
            raw_fields: <D::Struct<'top> as LazyRawStruct<'top, D>>::Iterator,
        ) -> Self {
            Self {
                context,
                raw_fields,
            }
        }
    }

    impl<'top, D: Decoder> Iterator for RawStructFieldExprIterator<'top, D> {
        type Item = IonResult<FieldExpr<'top, D>>;

        fn next(&mut self) -> Option<Self::Item> {
            let field: LazyRawFieldExpr<'top, D> = try_next!(self.raw_fields.next());
            use LazyRawFieldExpr::*;
            let unexpanded_field = match field {
                NameValue(name, value) => FieldExpr::NameValue(
                    name.resolve(self.context),
                    LazyExpandedValue::from_literal(self.context, value),
                ),
                NameEExp(name, raw_eexp) => {
                    let eexp = try_or_some_err!(raw_eexp.resolve(self.context));
                    FieldExpr::NameMacro(name.resolve(self.context), eexp.into())
                }
                EExp(raw_eexp) => {
                    let eexp = try_or_some_err!(raw_eexp.resolve(self.context));
                    FieldExpr::EExp(eexp)
                }
            };
            Some(Ok(unexpanded_field))
        }
    }
}

pub trait LazyRawReader<'data, D: Decoder>: Sized {
    /// Constructs a new raw reader using decoder `D` that will read from `data`.
    /// `data` must be the beginning of the stream. To continue reading from the middle of a
    /// stream, see [`resume_at_offset`](Self::resume).
    // This is widely used in unit tests, which is the primary codebase where one might wish to
    // initialize a LazyRawReader implementation.
    #[cfg_attr(not(test), allow(dead_code))]
    fn new(context: EncodingContextRef<'data>, data: &'data [u8], is_final_data: bool) -> Self;

    /// Constructs a new raw reader using decoder `D` that will read from `data`.
    ///
    /// Automatically detecting the stream's encoding is only possible when `offset` is zero.
    /// If offset is not zero, the caller must supply an `encoding_hint` indicating the expected
    /// encoding. Encoding-specific raw readers will ignore this hint--the stream's encoding must be
    /// the one that they support--but the `LazyRawAnyReader` will use it.
    fn resume(context: EncodingContextRef<'data>, saved_state: RawReaderState<'data>) -> Self;

    /// Deconstructs this reader, returning a tuple of `(remaining_data, stream_offset, encoding)`.
    fn save_state(&self) -> RawReaderState<'data>;

    fn next(&mut self) -> IonResult<LazyRawStreamItem<'data, D>>;

    /// The stream byte offset at which the reader will begin parsing the next item to return.
    /// This position is not necessarily the first byte of the next value; it may be (e.g.) a NOP,
    /// a comment, or whitespace that the reader will traverse as part of matching the next item.
    fn position(&self) -> usize;

    /// The Ion encoding of the stream that the reader has been processing.
    ///
    /// Note that:
    /// * Before any items have been read from the stream, the encoding defaults
    ///   to [`IonEncoding::Text_1_0`].
    /// * When an IVM is encountered, the Ion version reported afterward can be different but the
    ///   format (text vs binary) will remain the same.
    fn encoding(&self) -> IonEncoding;
}

/// Allows writers to specify which Ion encodings they can losslessly transcribe from.
///
/// TODO: At the moment, this implementation does not process encoding directives in the
///       input stream, which means it only works for very simple use cases. A better solution
///       would be to take a `&mut SystemReader<_>` that can maintain the encoding context while
///       also only paying attention to stream literals.
pub trait TranscribeRaw<E: Encoding> {
    #[allow(dead_code)]
    fn transcribe<'a, R: LazyRawReader<'a, E>>(&mut self, reader: &mut R) -> IonResult<()>
    where
        Self: 'a;
}

impl<W: Write> TranscribeRaw<v1_1::Binary> for LazyRawTextWriter_1_1<W> {
    fn transcribe<'a, R: LazyRawReader<'a, v1_1::Binary>>(
        &mut self,
        reader: &mut R,
    ) -> IonResult<()>
    where
        Self: 'a,
    {
        transcribe_raw_binary_to_text(reader, self)
    }
}

impl<W: Write> TranscribeRaw<v1_0::Binary> for LazyRawTextWriter_1_1<W> {
    fn transcribe<'a, R: LazyRawReader<'a, v1_0::Binary>>(
        &mut self,
        reader: &mut R,
    ) -> IonResult<()>
    where
        Self: 'a,
    {
        transcribe_raw_binary_to_text(reader, self)
    }
}

impl<W: Write> TranscribeRaw<v1_0::Binary> for LazyRawTextWriter_1_0<W> {
    fn transcribe<'a, R: LazyRawReader<'a, v1_0::Binary>>(
        &mut self,
        reader: &mut R,
    ) -> IonResult<()>
    where
        Self: 'a,
    {
        transcribe_raw_binary_to_text(reader, self)
    }
}

fn transcribe_raw_binary_to_text<
    'a,
    W: Write + 'a,
    InputEncoding: BinaryEncoding,
    Reader: LazyRawReader<'a, InputEncoding>,
    Writer: LazyRawWriter<W>,
>(
    reader: &mut Reader,
    writer: &mut Writer,
) -> IonResult<()> {
    const FLUSH_EVERY_N: usize = 100;
    let mut item_number: usize = 0;
    loop {
        let item = reader.next()?;
        use crate::RawStreamItem::*;
        match item {
            VersionMarker(_m) if item_number == 0 => {
                // The writer automatically emits an IVM at the head of the output.
            }
            VersionMarker(_m) => {
                // If the reader surfaces another IVM, write a matching one in the output.
                writer.write_version_marker()?
            }
            Value(v) => {
                writer.write(WriteableRawValue::new(v))?;
            }
            EExp(e) => {
                writer.write(WriteableEExp::new(e))?;
            }
            EndOfStream(_) => {
                writer.flush()?;
                return Ok(());
            }
        }
        item_number += 1;
        if item_number % FLUSH_EVERY_N == 0 {
            writer.flush()?;
        }
    }
}

pub trait LazyRawContainer<'top, D: Decoder> {
    fn as_value(&self) -> D::Value<'top>;
}

pub trait LazyRawValue<'top, D: Decoder>:
    HasSpan<'top> + RawValueLiteral + Copy + Clone + Debug + Sized
{
    fn ion_type(&self) -> IonType;
    fn is_null(&self) -> bool;

    fn is_delimited(&self) -> bool;
    fn has_annotations(&self) -> bool;
    fn annotations(&self) -> D::AnnotationsIterator<'top>;
    fn read(&self) -> IonResult<RawValueRef<'top, D>>;
    fn read_resolved(&self, context: EncodingContextRef<'top>) -> IonResult<ValueRef<'top, D>> {
        self.read()?.resolve(context)
    }

    fn annotations_span(&self) -> Span<'top>;

    fn value_span(&self) -> Span<'top>;

    /// Returns a copy of the `LazyRawValue` whose backing data—the slice of bytes representing the
    /// serialized value—has been replaced by `span`.
    ///
    /// This method is used when converting a `LazyValue` (which may be backed by a slice of the
    /// input buffer) to a `LazyElement` (which needs to be backed by heap data).
    fn with_backing_data(&self, span: Span<'top>) -> Self;

    fn encoding(&self) -> IonEncoding;
}

pub trait RawSequenceIterator<'top, D: Decoder>:
    Debug + Copy + Clone + Iterator<Item = IonResult<LazyRawValueExpr<'top, D>>>
{
    /// Returns the next raw value expression (or `None` if exhausted) without advancing the iterator.
    #[allow(dead_code)]
    fn peek_next(&self) -> Option<IonResult<LazyRawValueExpr<'top, D>>> {
        // Because RawSequenceIterator impls are `Copy`, we can make a cheap copy of `self` and advance
        // *it* without affecting `self`.
        let mut iter_clone = *self;
        iter_clone.next()
    }
}

impl<'top, D: Decoder, T> RawSequenceIterator<'top, D> for T
where
    T: Debug + Copy + Clone + Iterator<Item = IonResult<LazyRawValueExpr<'top, D>>>,
{
    // Nothing to do
}

pub trait LazyRawSequence<'top, D: Decoder>:
    LazyRawContainer<'top, D> + private::LazyContainerPrivate<'top, D> + Debug + Copy + Clone
{
    type Iterator: RawSequenceIterator<'top, D>;
    fn annotations(&self) -> D::AnnotationsIterator<'top>;
    fn ion_type(&self) -> IonType;
    fn iter(&self) -> Self::Iterator;
}

pub trait RawStructIterator<'top, D: Decoder>:
    Debug + Copy + Clone + Iterator<Item = IonResult<LazyRawFieldExpr<'top, D>>>
{
    /// Returns the next raw value expression (or `None` if exhausted) without advancing the iterator.
    #[allow(dead_code)]
    fn peek_next(&self) -> Option<IonResult<LazyRawFieldExpr<'top, D>>> {
        // Because RawStructIterator impls are `Copy`, we can make a cheap copy of `self` and advance
        // *it* without affecting `self`.
        let mut iter_clone = *self;
        iter_clone.next()
    }
}

impl<'top, D: Decoder, T> RawStructIterator<'top, D> for T
where
    T: Debug + Copy + Clone + Iterator<Item = IonResult<LazyRawFieldExpr<'top, D>>>,
{
    // Nothing to do
}

pub trait LazyRawStruct<'top, D: Decoder>:
    LazyRawContainer<'top, D> + private::LazyContainerPrivate<'top, D> + Debug + Copy + Clone
{
    type Iterator: RawStructIterator<'top, D>;

    fn annotations(&self) -> D::AnnotationsIterator<'top>;

    fn iter(&self) -> Self::Iterator;
}

pub trait LazyRawFieldName<'top, D: Decoder<FieldName<'top> = Self>>:
    Into<LazyRawAnyFieldName<'top>> + HasSpan<'top> + Copy + Debug + Clone
{
    fn read(&self) -> IonResult<RawSymbolRef<'top>>;

    fn resolve(&self, context: EncodingContextRef<'top>) -> LazyExpandedFieldName<'top, D> {
        LazyExpandedFieldName::RawName(context, *self)
    }
}
