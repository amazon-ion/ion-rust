//! Defines traits that allow Rust values to be serialized as Ion.
//!
//! In order for a [`LazyRawWriter`](crate::lazy::encoder::LazyRawWriter) to serialize a Rust value
//! as Ion, that Rust type must implement [`WriteAsIonValue`] and may optionally also
//! implement [`WriteAsIon`].
//!
//! [`WriteAsIonValue`] allows the implementor to map the Rust value to an unannotated Ion value.
//!
//! [`WriteAsIon`] builds on [`WriteAsIonValue`], offering a staged writer that requires the
//! implementor to specify what annotations to write before delegating to [`WriteAsIonValue`]
//! to serialize the value itself.
//!
//! Types that do not explicitly implement [`WriteAsIon`] will fall back to a blanket implementation
//! that uses an empty annotations sequence. A custom annotations sequence can be set on a per-value
//! basis by using the [`annotate`](crate::lazy::encoder::annotate::Annotate::annotated_with) method
//! provided by the [`Annotate`](crate::lazy::encoder::annotate::Annotate) trait.
use std::marker::PhantomData;

use crate::lazy::encoder::value_writer::{
    AnnotatableValueWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::{
    Blob, Clob, Decimal, Element, Int, IonResult, Null, RawSymbolToken, RawSymbolTokenRef, Symbol,
    SymbolRef, Timestamp, Value,
};

/// Defines how a Rust type should be serialized as Ion in terms of the methods available
/// on [`ValueWriter`]. To annotate instances of your type with a sequence of text values,
/// implement the [`WriteAsIon`] trait instaed.
pub trait WriteAsIonValue {
    fn write_as_ion_value<V: ValueWriter>(&self, writer: V) -> IonResult<()>;
}

/// Defines how a Rust type should be serialized as Ion in terms of the methods available
/// on [`AnnotatableValueWriter`] and [`ValueWriter`].
pub trait WriteAsIon {
    fn write_as_ion<V: AnnotatableValueWriter>(&self, writer: V) -> IonResult<()>;
}

impl WriteAsIon for &Element {
    fn write_as_ion<V: AnnotatableValueWriter>(&self, writer: V) -> IonResult<()> {
        if self.annotations().is_empty() {
            self.value()
                .write_as_ion_value(writer.without_annotations())
        } else {
            self.value().write_as_ion_value(
                writer.with_annotations(&Vec::from_iter(self.annotations().iter())),
            )
        }
    }
}

// Any type that does not define `WriteAsIon` itself will use this blanket implementation that does
// not write any annotations.
impl<T> WriteAsIon for T
where
    T: WriteAsIonValue,
{
    fn write_as_ion<V: AnnotatableValueWriter>(&self, writer: V) -> IonResult<()> {
        self.write_as_ion_value(writer.without_annotations())
    }
}

// ===== WriteAsIonValue implementations for common types =====

macro_rules! impl_write_as_ion_value {
    // End of iteration
    () => {};
    // The caller defined an expression to write other than `self` (e.g. `*self`, `*self.0`, etc)
    ($target_type:ty => $method:ident with $self:ident as $value:expr, $($rest:tt)*) => {
        impl WriteAsIonValue for $target_type {
            #[inline]
            fn write_as_ion_value<V: ValueWriter>(&$self, writer: V) -> IonResult<()> {
                writer.$method($value)
            }
        }
        impl_write_as_ion_value!($($rest)*);
    };
    // We're writing the expression `self`
    ($target_type:ty => $method:ident, $($rest:tt)*) => {
        impl WriteAsIonValue for $target_type {
            #[inline]
            fn write_as_ion_value<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
                writer.$method(self)
            }
        }
        impl_write_as_ion_value!($($rest)*);
    };
}

// TODO: For the moment, `i8` and `u8` do not directly implement `WriteAsIon` because this causes
//       the desired serialization for `&[u8]` and `&[i8]` to be ambiguous. They could be serialized
//       either as blobs or as lists of integers. We should use the same trick that `SExpTypeHint`
//       employs to make it possible for users to override the default blob serialization by writing:
//           writer.write(&[1u8, 2, 3].as_list())
impl_write_as_ion_value!(
    Null => write_null with self as self.0,
    bool => write_bool with self as *self,
    i16 => write_i64 with self as *self as i64,
    i32 => write_i64 with self as *self as i64,
    i64 => write_i64 with self as *self,
    isize => write_i64 with self as *self as i64,
    u16 => write_i64 with self as i64::from(*self),
    u32 => write_i64 with self as i64::from(*self),
    u64 => write_int with self as &Int::from(*self),
    usize => write_int with self as &Int::from(*self),
    f32 => write_f32 with self as *self,
    f64 => write_f64 with self as *self,
    Decimal => write_decimal,
    Timestamp => write_timestamp,
    Symbol => write_symbol,
    RawSymbolToken => write_symbol,
    &str => write_string,
    String => write_string,
    &[u8] => write_blob,
    Blob => write_blob,
    Clob => write_clob,
);

impl<'b> WriteAsIonValue for RawSymbolTokenRef<'b> {
    #[inline]
    fn write_as_ion_value<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        writer.write_symbol(self)
    }
}

impl<'b> WriteAsIonValue for SymbolRef<'b> {
    #[inline]
    fn write_as_ion_value<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        writer.write_symbol(self)
    }
}

impl<const N: usize> WriteAsIonValue for [u8; N] {
    fn write_as_ion_value<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        writer.write_blob(self)
    }
}

impl<T: WriteAsIonValue> WriteAsIonValue for &T {
    #[inline]
    fn write_as_ion_value<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        (*self).write_as_ion_value(writer)
    }
}

macro_rules! impl_write_as_ion_value_for_iterable {
    ($iterable:ty, $item:ident $(, const $n:ident: $n_type:ty)?) => {
        impl<$item $(, const $n: $n_type)?> WriteAsIonValue for $iterable
        where
            for<'a> &'a $item: WriteAsIon,
        {
            fn write_as_ion_value<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
                writer.write_list(|list: &mut V::ListWriter| {
                    for value in self.iter() {
                        list.write(value)?;
                    }
                    Ok(())
                })
            }
        }
    };
}

impl_write_as_ion_value_for_iterable!(Vec<T>, T);
impl_write_as_ion_value_for_iterable!(&[T], T);
impl_write_as_ion_value_for_iterable!([T; N], T, const N: usize);

pub trait WriteAsSExp<T>: Sized
where
    T: WriteAsIon,
{
    // The name `as_sexp` makes common cases read as a short sentence:
    //     writer.write([1, 2, 3].as_sexp())?;
    // Clippy complains because in most contexts, `as_*` methods borrow by reference.
    #[allow(clippy::wrong_self_convention)]
    /// Wraps `self` (which may be a reference) in a [`SExpTypeHint`], causing the value to be
    /// serialized as an Ion S-expression instead of a list.
    fn as_sexp(self) -> SExpTypeHint<Self, T>;
}
macro_rules! impl_write_as_sexp_for_iterable {
    ($iterable:ty, $item:ident $(, const $n:ident: $n_type:ty)?) => {
        impl<$item $(, const $n: $n_type)?> WriteAsSExp<$item> for $iterable
        where
            $item: WriteAsIon,
        {
            fn as_sexp(self) -> SExpTypeHint<Self, T> {
                SExpTypeHint::new(self)
            }
        }
    };
}

impl_write_as_sexp_for_iterable!(Vec<T>, T);
impl_write_as_sexp_for_iterable!(&[T], T);
impl_write_as_sexp_for_iterable!([T; N], T, const N: usize);

/// A wrapper type that hints to the Ion writer that the sequence within should be serialized
/// as an s-expression, not a list.
///
/// Slices, `Vec`s, and arrays all implement the [`WriteAsSExp`] trait, which grants them the
/// [`as_sexp()`](WriteAsSExp::as_sexp) method.
pub struct SExpTypeHint<S, T> {
    values: S,
    spooky: PhantomData<T>,
}

impl<S, T> SExpTypeHint<S, T> {
    pub fn new(values: S) -> Self {
        Self {
            values,
            spooky: PhantomData,
        }
    }
}

macro_rules! impl_write_as_ion_value_for_sexp_type_hint {
    ($iterable:ty, $item:ident $(, const $n:ident: $n_type:ty)?) => {
        impl<$item $(, const $n: $n_type)?> WriteAsIonValue for SExpTypeHint<$iterable, $item>
        where
            for<'a> &'a $item: WriteAsIon,
        {
            fn write_as_ion_value<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
                writer.write_sexp(|sexp| {
                    for value in self.values.iter() {
                        sexp.write(value)?;
                    }
                    Ok(())
                })
            }
        }
    };
}

impl_write_as_ion_value_for_sexp_type_hint!(Vec<T>, T);
impl_write_as_ion_value_for_sexp_type_hint!(&[T], T);
impl_write_as_ion_value_for_sexp_type_hint!([T; N], T, const N: usize);

impl WriteAsIonValue for Value {
    fn write_as_ion_value<V: ValueWriter>(&self, value_writer: V) -> IonResult<()> {
        match self {
            Value::Null(i) => value_writer.write_null(*i),
            Value::Bool(b) => value_writer.write_bool(*b),
            Value::Int(i) => value_writer.write_int(i),
            Value::Float(f) => value_writer.write_f64(*f),
            Value::Decimal(d) => value_writer.write_decimal(d),
            Value::Timestamp(t) => value_writer.write_timestamp(t),
            Value::Symbol(s) => value_writer.write_symbol(s),
            Value::String(s) => value_writer.write_string(s),
            Value::Clob(c) => value_writer.write_clob(c),
            Value::Blob(b) => value_writer.write_blob(b),
            Value::List(l) => value_writer.write_list(|list| {
                for value in l {
                    list.write(value)?;
                }
                Ok(())
            }),
            Value::SExp(s) => value_writer.write_sexp(|sexp| {
                for value in s {
                    sexp.write(value)?;
                }
                Ok(())
            }),
            Value::Struct(s) => value_writer.write_struct(|struct_value| {
                for (k, v) in s {
                    struct_value.write(k, v)?;
                }
                Ok(())
            }),
        }
    }
}
