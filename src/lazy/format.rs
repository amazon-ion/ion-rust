use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::{IonResult, IonType, RawSymbolTokenRef};
use std::fmt::Debug;

/// A family of types that collectively comprise the lazy reader API for an Ion serialization
/// format. These types operate at the 'raw' level; they do not attempt to resolve symbols
/// using the active symbol table.
pub trait LazyFormat<'data>: Sized + Debug + Clone {
    /// A lazy reader that yields [`Self::Value`]s representing the top level values in its input.
    type Reader: LazyRawReader<'data, Self>;
    /// A value (at any depth) in the input. This can be further inspected to access either its
    /// scalar data or, if it is a container, to view it as [`Self::Sequence`] or [`Self::Struct`].  
    type Value: LazyRawValue<'data, Self>;
    /// A list or expression whose child values may be accessed iteratively or by index.
    type Sequence: LazyRawSequence<'data, Self>;
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
    use super::LazyFormat;
    use crate::RawSymbolTokenRef;

    pub trait LazyRawFieldPrivate<'data, F: LazyFormat<'data>> {
        /// Converts the `LazyRawField` impl to a `LazyRawValue` impl.
        // At the moment, `LazyRawField`s are just thin wrappers around a `LazyRawValue` that can
        // safely assume that the value has a field name associated with it. This method allows
        // us to convert from one to the other when needed.
        fn into_value(self) -> F::Value;
    }

    pub trait LazyContainerPrivate<'data, F: LazyFormat<'data>> {
        /// Constructs a new lazy raw container from a lazy raw value that has been confirmed to be
        /// of the correct type.
        fn from_value(value: F::Value) -> Self;
    }

    pub trait LazyRawValuePrivate<'data> {
        /// Returns the field name associated with this value. If the value is not inside a struct,
        /// returns `None`.
        fn field_name(&self) -> Option<RawSymbolTokenRef<'data>>;
    }
}

pub trait LazyRawReader<'data, F: LazyFormat<'data>> {
    fn new(data: &'data [u8]) -> Self;
    fn next<'a>(&'a mut self) -> IonResult<RawStreamItem<'data, F>>;
}

pub trait LazyRawValue<'data, F: LazyFormat<'data>>:
    private::LazyRawValuePrivate<'data> + Clone + Debug
{
    fn ion_type(&self) -> IonType;
    fn annotations(&self) -> F::AnnotationsIterator;
    fn read(&self) -> IonResult<RawValueRef<'data, F>>;
}

pub trait LazyRawSequence<'data, F: LazyFormat<'data>>:
    private::LazyContainerPrivate<'data, F> + Debug
{
    type Iterator: Iterator<Item = IonResult<F::Value>>;
    fn annotations(&self) -> F::AnnotationsIterator;
    fn ion_type(&self) -> IonType;
    fn iter(&self) -> Self::Iterator;
    fn as_value(&self) -> &F::Value;
}

pub trait LazyRawStruct<'data, F: LazyFormat<'data>>:
    private::LazyContainerPrivate<'data, F> + Debug
{
    type Field: LazyRawField<'data, F>;
    type Iterator: Iterator<Item = IonResult<Self::Field>>;

    fn annotations(&self) -> F::AnnotationsIterator;
    fn find(&self, name: &str) -> IonResult<Option<F::Value>>;
    fn get(&self, name: &str) -> IonResult<Option<RawValueRef<'data, F>>>;
    fn iter(&self) -> Self::Iterator;
}

pub trait LazyRawField<'data, F: LazyFormat<'data>>:
    private::LazyRawFieldPrivate<'data, F> + Debug
{
    fn name(&self) -> RawSymbolTokenRef<'data>;
    fn value(&self) -> &F::Value;
}
