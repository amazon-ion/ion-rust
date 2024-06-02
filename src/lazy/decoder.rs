use std::fmt::Debug;
use std::ops::Range;

use bumpalo::Bump as BumpAllocator;

use crate::lazy::encoding::{BinaryEncoding_1_0, RawValueLiteral, TextEncoding_1_0};
use crate::lazy::expanded::macro_evaluator::RawEExpression;
use crate::lazy::raw_stream_item::LazyRawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::span::Span;
use crate::read_config::ReadConfig;
use crate::result::IonFailure;
use crate::{Catalog, IonResult, IonType, RawSymbolRef};

pub trait HasSpan<'top>: HasRange {
    fn span(&self) -> Span<'top>;
}

pub trait HasRange {
    fn range(&self) -> Range<usize>;
}

/// A family of types that collectively comprise the lazy reader API for an Ion serialization
/// format. These types operate at the 'raw' level; they do not attempt to resolve symbols
/// using the active symbol table.
// Implementations of this trait are typically unit structs that are never instantiated.
// However, many types are generic over some `D: LazyDecoder`, and having this trait
// extend 'static, Sized, Debug, Clone and Copy means that those types can #[derive(...)]
// those traits themselves without boilerplate `where` clauses.
pub trait Decoder: 'static + Sized + Debug + Clone + Copy {
    /// A lazy reader that yields [`Self::Value`]s representing the top level values in its input.
    type Reader<'data>: LazyRawReader<'data, Self>;
    /// Additional data (beyond the offset) that the reader will need in order to resume reading
    /// from a different point in the stream.
    // At the moment this feature is only used by `LazyAnyRawReader`, which needs to remember what
    // encoding the stream was using during earlier read operations.
    type ReaderSavedState: Copy + Default;
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
    type FieldName<'top>: LazyRawFieldName<'top>;
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
    fn major(&self) -> u8 {
        self.version().0
    }
    fn minor(&self) -> u8 {
        self.version().1
    }
    fn version(&self) -> (u8, u8);
}

/// An expression found in value position in either serialized Ion or a template.
/// If it is a value literal, it is considered a stream with exactly one Ion value.
/// If it is a macro invocation, it is a stream with zero or more Ion values.
///
/// When working with `RawValueExpr`s that always use a given decoder's `Value` and
/// `MacroInvocation` associated types, consider using [`LazyRawValueExpr`] instead.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum RawValueExpr<V, M> {
    /// A value literal. For example: `5`, `foo`, or `"hello"` in text.
    ValueLiteral(V),
    /// An Ion 1.1+ macro invocation. For example: `(:employee 12345 "Sarah" "Gonzalez")` in text.
    MacroInvocation(M),
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
            RawValueExpr::MacroInvocation(_m) => IonResult::decoding_error(
                "expected a value literal, but found a macro invocation ({:?})",
            ),
        }
    }

    pub fn expect_macro(self) -> IonResult<M> {
        match self {
            RawValueExpr::ValueLiteral(v) => IonResult::decoding_error(format!(
                "expected a macro invocation but found a value literal ({:?})",
                v
            )),
            RawValueExpr::MacroInvocation(m) => Ok(m),
        }
    }
}

impl<V: HasRange, M: HasRange> HasRange for RawValueExpr<V, M> {
    fn range(&self) -> Range<usize> {
        match self {
            RawValueExpr::ValueLiteral(value) => value.range(),
            RawValueExpr::MacroInvocation(eexp) => eexp.range(),
        }
    }
}

impl<'top, V: HasSpan<'top>, M: HasSpan<'top>> HasSpan<'top> for RawValueExpr<V, M> {
    fn span(&self) -> Span<'top> {
        match self {
            RawValueExpr::ValueLiteral(value) => value.span(),
            RawValueExpr::MacroInvocation(eexp) => eexp.span(),
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
    pub fn expect_name_value(self) -> IonResult<(D::FieldName<'top>, D::Value<'top>)> {
        let LazyRawFieldExpr::NameValue(name, value) = self else {
            return IonResult::decoding_error(format!(
                "expected a name/value pair but found {:?}",
                self
            ));
        };
        Ok((name, value))
    }

    pub fn expect_name_eexp(self) -> IonResult<(D::FieldName<'top>, D::EExp<'top>)> {
        let LazyRawFieldExpr::NameEExp(name, eexp) = self else {
            return IonResult::decoding_error(format!(
                "expected a name/e-expression pair but found {:?}",
                self
            ));
        };
        Ok((name, eexp))
    }

    pub fn expect_eexp(self) -> IonResult<D::EExp<'top>> {
        let LazyRawFieldExpr::EExp(eexp) = self else {
            return IonResult::decoding_error(format!(
                "expected an e-expression but found {:?}",
                self
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

impl<'top, D: Decoder> HasRange for LazyRawFieldExpr<'top, D> {
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
    use crate::lazy::expanded::r#struct::UnexpandedField;
    use crate::lazy::expanded::EncodingContextRef;
    use crate::IonResult;

    use super::{Decoder, LazyRawFieldExpr, LazyRawStruct};

    pub trait LazyContainerPrivate<'top, D: Decoder> {
        /// Constructs a new lazy raw container from a lazy raw value that has been confirmed to be
        /// of the correct type.
        fn from_value(value: D::Value<'top>) -> Self;
    }

    pub trait LazyRawStructPrivate<'top, D: Decoder> {
        /// Creates an iterator that converts each raw struct field into an `UnexpandedField`, a
        /// common representation for both raw fields and template fields that is used in the
        /// expansion process.
        fn unexpanded_fields(
            &self,
            context: EncodingContextRef<'top>,
        ) -> RawStructUnexpandedFieldsIterator<'top, D>;
    }

    pub struct RawStructUnexpandedFieldsIterator<'top, D: Decoder> {
        context: EncodingContextRef<'top>,
        raw_fields: <D::Struct<'top> as LazyRawStruct<'top, D>>::Iterator,
    }

    impl<'top, D: Decoder> RawStructUnexpandedFieldsIterator<'top, D> {
        pub fn context(&self) -> EncodingContextRef<'top> {
            self.context
        }
    }

    impl<'top, D: Decoder> Iterator for RawStructUnexpandedFieldsIterator<'top, D> {
        type Item = IonResult<UnexpandedField<'top, D>>;

        fn next(&mut self) -> Option<Self::Item> {
            let field: LazyRawFieldExpr<'top, D> = match self.raw_fields.next() {
                Some(Ok(field)) => field,
                Some(Err(e)) => return Some(Err(e)),
                None => return None,
            };
            use LazyRawFieldExpr::*;
            let unexpanded_field = match field {
                NameValue(name, value) => UnexpandedField::RawNameValue(self.context, name, value),
                NameEExp(name, eexp) => UnexpandedField::RawNameEExp(self.context, name, eexp),
                EExp(eexp) => UnexpandedField::RawEExp(self.context, eexp),
            };
            Some(Ok(unexpanded_field))
        }
    }

    impl<'top, D: Decoder<Struct<'top> = S>, S> LazyRawStructPrivate<'top, D> for S
    where
        S: LazyRawStruct<'top, D>,
    {
        fn unexpanded_fields(
            &self,
            context: EncodingContextRef<'top>,
        ) -> RawStructUnexpandedFieldsIterator<'top, D> {
            let raw_fields = <Self as LazyRawStruct<'top, D>>::iter(self);
            RawStructUnexpandedFieldsIterator {
                context,
                raw_fields,
            }
        }
    }
}

pub trait LazyRawReader<'data, D: Decoder>: Sized {
    fn new(data: &'data [u8]) -> Self {
        Self::resume_at_offset(data, 0, D::ReaderSavedState::default())
    }

    fn resume_at_offset(data: &'data [u8], offset: usize, saved_state: D::ReaderSavedState)
        -> Self;
    fn next<'top>(
        &'top mut self,
        allocator: &'top BumpAllocator,
    ) -> IonResult<LazyRawStreamItem<'top, D>>
    where
        'data: 'top;

    fn save_state(&self) -> D::ReaderSavedState {
        D::ReaderSavedState::default()
    }

    /// The stream byte offset at which the reader will begin parsing the next item to return.
    /// This position is not necessarily the first byte of the next value; it may be (e.g.) a NOP,
    /// a comment, or whitespace that the reader will traverse as part of matching the next item.
    fn position(&self) -> usize;
}

pub trait LazyRawContainer<'top, D: Decoder> {
    fn as_value(&self) -> D::Value<'top>;
}

pub trait LazyRawValue<'top, D: Decoder>:
    HasSpan<'top> + RawValueLiteral + Copy + Clone + Debug + Sized
{
    fn ion_type(&self) -> IonType;
    fn is_null(&self) -> bool;
    fn has_annotations(&self) -> bool;
    fn annotations(&self) -> D::AnnotationsIterator<'top>;
    fn read(&self) -> IonResult<RawValueRef<'top, D>>;

    fn annotations_span(&self) -> Span<'top>;

    fn value_span(&self) -> Span<'top>;
}

pub trait LazyRawSequence<'top, D: Decoder>:
    LazyRawContainer<'top, D> + private::LazyContainerPrivate<'top, D> + Debug + Copy + Clone
{
    type Iterator: Iterator<Item = IonResult<LazyRawValueExpr<'top, D>>>;
    fn annotations(&self) -> D::AnnotationsIterator<'top>;
    fn ion_type(&self) -> IonType;
    fn iter(&self) -> Self::Iterator;
}

pub trait LazyRawStruct<'top, D: Decoder>:
    LazyRawContainer<'top, D>
    + private::LazyContainerPrivate<'top, D>
    + private::LazyRawStructPrivate<'top, D>
    + Debug
    + Copy
    + Clone
{
    type Iterator: Iterator<Item = IonResult<LazyRawFieldExpr<'top, D>>>;

    fn annotations(&self) -> D::AnnotationsIterator<'top>;

    fn iter(&self) -> Self::Iterator;
}

pub trait LazyRawFieldName<'top>: HasSpan<'top> + Copy + Debug + Clone {
    fn read(&self) -> IonResult<RawSymbolRef<'top>>;
}
