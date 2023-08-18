use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::result::IonFailure;
use crate::{IonResult, IonType, RawSymbolTokenRef};
use std::fmt::Debug;

/// A family of types that collectively comprise the lazy reader API for an Ion serialization
/// format. These types operate at the 'raw' level; they do not attempt to resolve symbols
/// using the active symbol table.
pub trait LazyDecoder<'data>: Sized + Debug + Clone {
    /// A lazy reader that yields [`Self::Value`]s representing the top level values in its input.
    type Reader: LazyRawReader<'data, Self>;
    /// A value (at any depth) in the input. This can be further inspected to access either its
    /// scalar data or, if it is a container, to view it as [`Self::Sequence`] or [`Self::Struct`].  
    type Value: LazyRawValue<'data, Self>;
    /// A list whose child values may be accessed iteratively.
    type SExp: LazyRawSequence<'data, Self>;
    /// An s-expression whose child values may be accessed iteratively.
    type List: LazyRawSequence<'data, Self>;
    /// A struct whose fields may be accessed iteratively or by field name.
    type Struct: LazyRawStruct<'data, Self>;
    /// An iterator over the annotations on the input stream's values.
    type AnnotationsIterator: Iterator<Item = IonResult<RawSymbolTokenRef<'data>>>;
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
    use super::LazyDecoder;
    use crate::{IonResult, RawSymbolTokenRef};

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

    pub trait LazyRawValuePrivate<'data> {
        /// Returns the field name associated with this value. If the value is not inside a struct,
        /// returns `IllegalOperation`.
        fn field_name(&self) -> IonResult<RawSymbolTokenRef<'data>>;
    }
}

pub trait LazyRawReader<'data, D: LazyDecoder<'data>> {
    fn new(data: &'data [u8]) -> Self;
    fn next<'a>(&'a mut self) -> IonResult<RawStreamItem<'data, D>>;
}

pub trait LazyRawValue<'data, D: LazyDecoder<'data>>:
    private::LazyRawValuePrivate<'data> + Clone + Debug
{
    fn ion_type(&self) -> IonType;
    fn is_null(&self) -> bool;
    fn annotations(&self) -> D::AnnotationsIterator;
    fn read(&self) -> IonResult<RawValueRef<'data, D>>;
}

pub trait LazyRawSequence<'data, D: LazyDecoder<'data>>:
    private::LazyContainerPrivate<'data, D> + Debug
{
    type Iterator: Iterator<Item = IonResult<D::Value>>;
    fn annotations(&self) -> D::AnnotationsIterator;
    fn ion_type(&self) -> IonType;
    fn iter(&self) -> Self::Iterator;
    fn as_value(&self) -> D::Value;
}

pub trait LazyRawStruct<'data, D: LazyDecoder<'data>>:
    private::LazyContainerPrivate<'data, D> + Debug
{
    type Field: LazyRawField<'data, D>;
    type Iterator: Iterator<Item = IonResult<Self::Field>>;

    fn annotations(&self) -> D::AnnotationsIterator;
    fn find(&self, name: &str) -> IonResult<Option<D::Value>>;
    fn get(&self, name: &str) -> IonResult<Option<RawValueRef<'data, D>>>;
    fn get_expected(&self, name: &str) -> IonResult<RawValueRef<'data, D>> {
        if let Some(value) = self.get(name)? {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("did not find expected struct field '{}'", name))
        }
    }
    fn iter(&self) -> Self::Iterator;
}

pub trait LazyRawField<'data, D: LazyDecoder<'data>>:
    private::LazyRawFieldPrivate<'data, D> + Debug
{
    fn name(&self) -> RawSymbolTokenRef<'data>;
    fn value(&self) -> D::Value;
}
