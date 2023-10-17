use std::fmt::Debug;

use crate::lazy::encoding::TextEncoding_1_1;
use crate::lazy::expanded::e_expression::{EExpression, TextEExpression_1_1};
use crate::lazy::expanded::macro_evaluator::RawEExpression;
use crate::lazy::expanded::EncodingContext;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::text::raw::v1_1::reader::{
    MacroIdRef, RawTextEExpression_1_1, RawTextSExpIterator_1_1,
};
use crate::result::IonFailure;
use crate::{IonError, IonResult, IonType, RawSymbolTokenRef};

/// A family of types that collectively comprise the lazy reader API for an Ion serialization
/// format. These types operate at the 'raw' level; they do not attempt to resolve symbols
/// using the active symbol table.
pub trait LazyDecoder<'data>: 'static + Sized + Debug + Clone + Copy {
    /// A lazy reader that yields [`Self::Value`]s representing the top level values in its input.
    type Reader: LazyRawReader<'data, Self>;
    /// A value (at any depth) in the input. This can be further inspected to access either its
    /// scalar data or, if it is a container, to view it as [`Self::List`], [`Self::SExp`] or
    /// [`Self::Struct`].  
    type Value: LazyRawValue<'data, Self>;
    /// A list whose child values may be accessed iteratively.
    type SExp: LazyRawSequence<'data, Self>;
    /// An s-expression whose child values may be accessed iteratively.
    type List: LazyRawSequence<'data, Self>;
    /// A struct whose fields may be accessed iteratively or by field name.
    type Struct: LazyRawStruct<'data, Self>;
    /// An iterator over the annotations on the input stream's values.
    type AnnotationsIterator: Iterator<Item = IonResult<RawSymbolTokenRef<'data>>>;
    /// An e-expression invoking a macro. (Ion 1.1+)
    type RawMacroInvocation: RawEExpression<'data, Self>;
}

/// An expression found in value position in either serialized Ion or a template.
/// If it is a value literal, it is considered a stream with exactly one Ion value.
/// If it is a macro invocation, it is a stream with zero or more Ion values.
///
/// When working with `RawValueExpr`s that always use a given decoder's `Value` and
/// `MacroInvocation` associated types, consider using [`LazyRawValueExpr`] instead.
#[derive(Copy, Clone, Debug)]
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
pub type LazyRawValueExpr<'data, D> =
    RawValueExpr<<D as LazyDecoder<'data>>::Value, <D as LazyDecoder<'data>>::RawMacroInvocation>;

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

/// An item found in field position within a struct.
/// This item may be:
///   * a name/value pair (as it is in Ion 1.0)
///   * a name/e-expression pair
///   * an e-expression
#[derive(Debug)]
pub enum RawFieldExpr<'name, V, M> {
    NameValuePair(RawSymbolTokenRef<'name>, RawValueExpr<V, M>),
    MacroInvocation(M),
}

// As with the `RawValueExpr`/`LazyRawValueExpr` type pair, a `RawFieldExpr` has no constraints
// on the types used for values or macros, while the `LazyRawFieldExpr` type alias below uses the
// value and macro types associated with the decoder `D`.

/// An item found in struct field position an Ion data stream written in the encoding represented
/// by the LazyDecoder `D`.
pub type LazyRawFieldExpr<'data, D> = RawFieldExpr<
    'data,
    <D as LazyDecoder<'data>>::Value,
    <D as LazyDecoder<'data>>::RawMacroInvocation,
>;

impl<'name, V: Debug, M: Debug> RawFieldExpr<'name, V, M> {
    pub fn expect_name_value(self) -> IonResult<(RawSymbolTokenRef<'name>, V)> {
        match self {
            RawFieldExpr::NameValuePair(name, RawValueExpr::ValueLiteral(value)) => {
                Ok((name, value))
            }
            _ => IonResult::decoding_error(format!(
                "expected a name/value pair but found {:?}",
                self
            )),
        }
    }

    pub fn expect_name_macro(self) -> IonResult<(RawSymbolTokenRef<'name>, M)> {
        match self {
            RawFieldExpr::NameValuePair(name, RawValueExpr::MacroInvocation(invocation)) => {
                Ok((name, invocation))
            }
            _ => IonResult::decoding_error(format!(
                "expected a name/macro pair but found {:?}",
                self
            )),
        }
    }

    pub fn expect_macro(self) -> IonResult<M> {
        match self {
            RawFieldExpr::MacroInvocation(invocation) => Ok(invocation),
            _ => IonResult::decoding_error(format!(
                "expected a macro invocation but found {:?}",
                self
            )),
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
    use crate::lazy::encoding::RawValueLiteral;
    use crate::{IonResult, RawSymbolTokenRef};

    use super::LazyDecoder;

    pub trait LazyRawFieldPrivate<'data, D: LazyDecoder<'data>> {
        /// Converts the `LazyRawField` impl to a `LazyRawValue` impl.
        // At the moment, `LazyRawField`s are just thin wrappers around a `LazyRawValue` that can
        // safely assume that the value has a field name associated with it. This method allows
        // us to convert from one to the other when needed.
        fn into_value(self) -> D::Value;
    }

    pub trait LazyContainerPrivate<'data, D: LazyDecoder<'data>> {
        /// Constructs a new lazy raw container from a lazy raw value that has been confirmed to be
        /// of the correct type.
        fn from_value(value: D::Value) -> Self;
    }

    pub trait LazyRawValuePrivate<'data>: RawValueLiteral {
        /// Returns the field name associated with this value. If the value is not inside a struct,
        /// returns `IllegalOperation`.
        fn field_name(&self) -> IonResult<RawSymbolTokenRef<'data>>;
    }
}

// TODO: Everything should use LazyRawValueExpr in the RMI impl?

impl<'data> RawEExpression<'data, TextEncoding_1_1> for RawTextEExpression_1_1<'data> {
    type RawArgumentsIterator<'a> = RawTextSExpIterator_1_1<'data> where Self: 'a;

    fn id(&self) -> MacroIdRef<'data> {
        self.id
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator<'_> {
        RawTextSExpIterator_1_1::new(self.arguments_bytes())
    }

    fn resolve<'top>(
        self,
        context: EncodingContext<'top>,
    ) -> IonResult<EExpression<'top, 'data, TextEncoding_1_1>>
    where
        'data: 'top,
    {
        let invoked_macro = context
            .macro_table
            .macro_with_id(self.id())
            .ok_or_else(|| {
                IonError::decoding_error(format!("unrecognized macro ID {:?}", self.id()))
            })?;
        Ok(TextEExpression_1_1::new(context, self, invoked_macro))
    }
}

pub trait LazyRawReader<'data, D: LazyDecoder<'data>> {
    fn new(data: &'data [u8]) -> Self;
    fn next<'a>(&'a mut self) -> IonResult<RawStreamItem<'data, D>>;
}

pub trait LazyRawValue<'data, D: LazyDecoder<'data>>:
    private::LazyRawValuePrivate<'data> + Copy + Clone + Debug
{
    fn ion_type(&self) -> IonType;
    fn is_null(&self) -> bool;
    fn annotations(&self) -> D::AnnotationsIterator;
    fn read(&self) -> IonResult<RawValueRef<'data, D>>;
}

pub trait LazyRawSequence<'data, D: LazyDecoder<'data>>:
    private::LazyContainerPrivate<'data, D> + Debug + Copy + Clone
{
    type Iterator: Iterator<Item = IonResult<LazyRawValueExpr<'data, D>>>;
    fn annotations(&self) -> D::AnnotationsIterator;
    fn ion_type(&self) -> IonType;
    fn iter(&self) -> Self::Iterator;
    fn as_value(&self) -> D::Value;
}

pub trait LazyRawStruct<'data, D: LazyDecoder<'data>>:
    private::LazyContainerPrivate<'data, D> + Debug + Copy + Clone
{
    type Iterator: Iterator<Item = IonResult<LazyRawFieldExpr<'data, D>>>;

    fn annotations(&self) -> D::AnnotationsIterator;

    fn iter(&self) -> Self::Iterator;
}

pub trait LazyRawField<'data, D: LazyDecoder<'data>>:
    private::LazyRawFieldPrivate<'data, D> + Debug
{
    fn name(&self) -> RawSymbolTokenRef<'data>;
    fn value(&self) -> D::Value;
}
