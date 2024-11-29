//! Defines traits that allow Rust values to be serialized as Ion.
//!
//! In order for a [`LazyRawWriter`](crate::lazy::encoder::LazyRawWriter) to serialize a Rust value
//! as Ion, that Rust type must implement [`WriteAsIon`] and may optionally also
//! implement [`WriteAsIon`].
//!
//! [`WriteAsIon`] allows the implementor to map the Rust value to an unannotated Ion value.
//!
//! [`WriteAsIon`] builds on [`WriteAsIon`], offering a staged writer that requires the
//! implementor to specify what annotations to write before delegating to [`WriteAsIon`]
//! to serialize the value itself.
//!
//! Types that do not explicitly implement [`WriteAsIon`] will fall back to a blanket implementation
//! that uses an empty annotations sequence. A custom annotations sequence can be set on a per-value
//! basis by using the [`annotate`](crate::lazy::encoder::annotate::Annotatable::annotated_with) method
//! provided by the [`Annotate`](crate::lazy::encoder::annotate::Annotatable) trait.
use std::io;
use std::marker::PhantomData;

use crate::lazy::decoder::{Decoder, LazyRawValueExpr, RawValueExpr};
use crate::lazy::encoder::annotation_seq::AnnotationsVec;
use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter, ValueWriter};
use crate::lazy::encoding::Encoding;
use crate::lazy::expanded::macro_evaluator::RawEExpression;
use crate::lazy::text::raw::v1_1::arg_group::{EExpArg, EExpArgExpr};
use crate::lazy::value::LazyValue;
use crate::lazy::value_ref::ValueRef;
use crate::v1_0::RawValueRef;
use crate::{
    Blob, Clob, Decimal, Element, Int, IonResult, IonType, LazyList, LazyRawFieldExpr,
    LazyRawFieldName, LazyRawSequence, LazyRawStruct, LazyRawValue, LazySExp, LazyStruct, Null,
    RawSymbolRef, Symbol, SymbolRef, Timestamp, Value, WriteConfig,
};

/// Defines how a Rust type should be serialized as Ion in terms of the methods available
/// on [`ValueWriter`].
pub trait WriteAsIon {
    /// Maps this value to the Ion data model using the provided [`ValueWriter`] implementation.
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()>;

    /// Encodes this value as an Ion stream with `self` as the single top-level value.
    /// If the requested encoding is binary of any version, returns a `Vec<u8>` containing the
    /// encoded bytes. If the requested encoding is text of any version, returns a `String` instead.
    /// ```
    ///# use ion_rs::IonResult;
    ///# #[cfg(feature = "experimental-reader-writer")]
    ///# fn main() -> IonResult<()> {
    ///# use ion_rs::*;
    ///
    /// use ion_rs::WriteAsIon;
    /// let ion_text: String = "foo bar baz".encode_as(v1_0::Text)?;
    /// let element = Element::read_one(ion_text)?;
    /// assert_eq!(element.as_string().unwrap(), "foo bar baz");
    ///# Ok(())
    ///# }
    ///# #[cfg(not(feature = "experimental-reader-writer"))]
    ///# fn main() -> IonResult<()> { Ok(()) }
    /// ```
    fn encode_as<E: Encoding, C: Into<WriteConfig<E>>>(&self, config: C) -> IonResult<E::Output>
    where
        for<'a> &'a Self: WriteAsIon,
    {
        config.into().encode(self)
    }

    /// Encodes this value as an Ion stream with `self` as the single top-level value, writing
    /// the resulting stream to the specified `output`.
    fn encode_to<E: Encoding, C: Into<WriteConfig<E>>, W: io::Write>(
        &self,
        config: C,
        output: W,
    ) -> IonResult<W>
    where
        for<'a> &'a Self: WriteAsIon,
    {
        config.into().encode_to(self, output)
    }
}

impl WriteAsIon for &Element {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        if self.annotations().is_empty() {
            self.value().write_as_ion(writer)
        } else {
            self.value()
                .write_as_ion(writer.with_annotations(self.annotations().as_ref())?)
        }
    }
}

// ===== WriteAsIonValue implementations for common types =====

macro_rules! impl_write_as_ion_value {
    // End of iteration
    () => {};
    // The caller defined an expression to write other than `self` (e.g. `*self`, `*self.0`, etc)
    ($target_type:ty => $method:ident with $self:ident as $value:expr, $($rest:tt)*) => {
        impl WriteAsIon for $target_type {
            #[inline]
            fn write_as_ion<V: ValueWriter>(&$self, writer: V) -> IonResult<()> {
                writer.$method($value)
            }
        }
        impl_write_as_ion_value!($($rest)*);
    };
    // We're writing the expression `self`
    ($target_type:ty => $method:ident, $($rest:tt)*) => {
        impl WriteAsIon for $target_type {
            #[inline]
            fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
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
    Int => write_int,
    Decimal => write_decimal,
    Timestamp => write_timestamp,
    Symbol => write_symbol,
    &str => write_string,
    String => write_string,
    &[u8] => write_blob,
    Blob => write_blob,
    Clob => write_clob,
);

impl WriteAsIon for RawSymbolRef<'_> {
    #[inline]
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        writer.write_symbol(self)
    }
}

impl WriteAsIon for SymbolRef<'_> {
    #[inline]
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        writer.write_symbol(self)
    }
}

impl<const N: usize> WriteAsIon for [u8; N] {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        writer.write_blob(self)
    }
}

impl<T: WriteAsIon> WriteAsIon for &T {
    #[inline]
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        (*self).write_as_ion(writer)
    }
}

macro_rules! impl_write_as_ion_value_for_iterable {
    ($iterable:ty, $item:ident $(, const $n:ident: $n_type:ty)?) => {
        impl<'a, $item $(, const $n: $n_type)?> WriteAsIon for $iterable
        where
            $item: WriteAsIon + 'a,
        {
            fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
                writer.write_list(self.into_iter())
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
        impl<$item $(, const $n: $n_type)?> WriteAsIon for SExpTypeHint<$iterable, $item>
        where
            $item: WriteAsIon,
            for<'a> &'a $item: WriteAsIon,
        {
            fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
                writer.write_sexp((&self.values).into_iter())
            }
        }
    };
}

impl_write_as_ion_value_for_sexp_type_hint!(Vec<T>, T);
impl_write_as_ion_value_for_sexp_type_hint!(&[T], T);
impl_write_as_ion_value_for_sexp_type_hint!([T; N], T, const N: usize);

impl WriteAsIon for Value {
    fn write_as_ion<V: ValueWriter>(&self, value_writer: V) -> IonResult<()> {
        use Value::*;
        match self {
            Null(i) => value_writer.write_null(*i),
            Bool(b) => value_writer.write_bool(*b),
            Int(i) => value_writer.write_int(i),
            Float(f) => value_writer.write_f64(*f),
            Decimal(d) => value_writer.write_decimal(d),
            Timestamp(t) => value_writer.write_timestamp(t),
            Symbol(s) => value_writer.write_symbol(s),
            String(s) => value_writer.write_string(s),
            Clob(c) => value_writer.write_clob(c),
            Blob(b) => value_writer.write_blob(b),
            List(l) => value_writer.write_list(l),
            SExp(s) => value_writer.write_sexp(s),
            Struct(s) => value_writer.write_struct(s.iter()),
        }
    }
}

impl<D: Decoder> WriteAsIon for LazyValue<'_, D> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        if self.has_annotations() {
            let mut annotations = AnnotationsVec::new();
            for annotation in self.annotations() {
                annotations.push(annotation?.into());
            }
            self.read()?
                .write_as_ion(writer.with_annotations(annotations)?)
        } else {
            self.read()?.write_as_ion(writer)
        }
    }
}

impl<D: Decoder> WriteAsIon for RawValueRef<'_, D> {
    fn write_as_ion<V: ValueWriter>(&self, value_writer: V) -> IonResult<()> {
        use RawValueRef::*;
        match self {
            Null(i) => value_writer.write_null(*i),
            Bool(b) => value_writer.write_bool(*b),
            Int(i) => value_writer.write_int(i),
            Float(f) => value_writer.write_f64(*f),
            Decimal(d) => value_writer.write_decimal(d),
            Timestamp(t) => value_writer.write_timestamp(t),
            Symbol(s) => value_writer.write_symbol(s),
            String(s) => value_writer.write_string(s.text()),
            Clob(c) => value_writer.write_clob(c.as_ref()),
            Blob(b) => value_writer.write_blob(b.as_ref()),
            List(l) => {
                let mut list_writer = value_writer.list_writer()?;
                for value_result in l.iter() {
                    list_writer.write(WriteableRawValueExpr::<'_, D>::new(value_result?))?;
                }
                list_writer.close()
            }
            SExp(s) => {
                let mut sexp_writer = value_writer.sexp_writer()?;
                for value_result in s.iter() {
                    sexp_writer.write(WriteableRawValueExpr::<'_, D>::new(value_result?))?;
                }
                sexp_writer.close()
            }
            Struct(s) => {
                let mut struct_writer = value_writer.struct_writer()?;
                for field_result in s.iter() {
                    let field: LazyRawFieldExpr<'_, D> = field_result?;
                    match field {
                        LazyRawFieldExpr::NameValue(name, value) => {
                            struct_writer.write(name.read()?, WriteableRawValue::new(value))?;
                        }
                        LazyRawFieldExpr::NameEExp(name, eexp) => {
                            struct_writer.write(name.read()?, WriteableEExp::new(eexp))?;
                        }
                        LazyRawFieldExpr::EExp(_eexp) => {
                            todo!("Writing e-expressions in field name position during transcription.");
                        }
                    }
                }
                struct_writer.close()
            }
        }
    }
}

/// Wrapper type for `LazyRawValue`s that implements `WriteAsIon`.
pub struct WriteableRawValue<'a, D: Decoder, RawValue: LazyRawValue<'a, D>> {
    raw_value: RawValue,
    spooky: PhantomData<&'a D>,
}

impl<'a, D: Decoder, RawValue: LazyRawValue<'a, D>> WriteableRawValue<'a, D, RawValue> {
    pub fn new(raw_value: RawValue) -> Self {
        Self {
            raw_value,
            spooky: PhantomData,
        }
    }
}

impl<'a, D: Decoder, RawValue: LazyRawValue<'a, D>> WriteAsIon
    for WriteableRawValue<'a, D, RawValue>
{
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        if self.raw_value.has_annotations() {
            let mut annotations = AnnotationsVec::new();
            for annotation in self.raw_value.annotations() {
                annotations.push(annotation?);
            }
            self.raw_value
                .read()?
                .write_as_ion(writer.with_annotations(annotations)?)
        } else {
            self.raw_value.read()?.write_as_ion(writer)
        }
    }
}

/// Wrapper type for `RawEExpression`s that implements `WriteAsIon`.
pub struct WriteableEExp<'a, D: Decoder<EExp<'a> = RawEExp>, RawEExp: RawEExpression<'a, D> + 'a> {
    raw_eexp: RawEExp,
    spooky: PhantomData<&'a D>,
}

impl<'a, D: Decoder<EExp<'a> = RawEExp>, RawEExp: RawEExpression<'a, D> + 'a>
    WriteableEExp<'a, D, RawEExp>
{
    pub fn new(raw_eexp: RawEExp) -> Self {
        Self {
            raw_eexp,
            spooky: PhantomData,
        }
    }
}

impl<'a, D: Decoder<EExp<'a> = RawEExp>, RawEExp: RawEExpression<'a, D> + 'a> WriteAsIon
    for WriteableEExp<'a, D, RawEExp>
{
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        let id = self.raw_eexp.id();
        let mut eexp_writer = writer.eexp_writer(id)?;
        for arg_result in self.raw_eexp.raw_arguments() {
            let arg = arg_result?;
            eexp_writer.write(WriteableEExpArg::<'_, D>::new(arg))?;
        }
        eexp_writer.close()
    }
}

/// Wrapper type for `EExpArg`s that implements `WriteAsIon`.
pub struct WriteableEExpArg<'a, D: Decoder> {
    arg_expr: EExpArg<'a, D>,
    spooky: PhantomData<&'a D>,
}

impl<'a, D: Decoder> WriteableEExpArg<'a, D> {
    pub fn new(arg_expr: EExpArg<'a, D>) -> Self {
        Self {
            arg_expr,
            spooky: PhantomData,
        }
    }
}

impl<D: Decoder> WriteAsIon for WriteableEExpArg<'_, D> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        use EExpArgExpr::*;
        match self.arg_expr.expr() {
            // TODO: Untagged encodings
            ValueLiteral(v) => WriteableRawValue::new(*v).write_as_ion(writer),
            EExp(e) => WriteableEExp::new(*e).write_as_ion(writer),
            ArgGroup(group) => WriteableEExpArgGroup::<'_, D>::new(*group).write_as_ion(writer),
        }
    }
}

/// Wrapper type for `WriteableEExpArgGroup`s that implements `WriteAsIon`.
pub struct WriteableEExpArgGroup<'a, D: Decoder> {
    arg_group: <<D as Decoder>::EExp<'a> as RawEExpression<'a, D>>::ArgGroup,
    spooky: PhantomData<&'a D>,
}

impl<'a, D: Decoder> WriteableEExpArgGroup<'a, D> {
    pub fn new(arg_group: <<D as Decoder>::EExp<'a> as RawEExpression<'a, D>>::ArgGroup) -> Self {
        Self {
            arg_group,
            spooky: PhantomData,
        }
    }
}

impl<D: Decoder> WriteAsIon for WriteableEExpArgGroup<'_, D> {
    fn write_as_ion<V: ValueWriter>(&self, _writer: V) -> IonResult<()> {
        todo!()
    }
}

/// Wrapper type for `LazyRawValueExpr`s that implements `WriteAsIon`.
pub struct WriteableRawValueExpr<'a, D: Decoder> {
    raw_value_expr: LazyRawValueExpr<'a, D>,
    spooky: PhantomData<&'a D>,
}

impl<'a, D: Decoder> WriteableRawValueExpr<'a, D> {
    pub fn new(raw_value_expr: LazyRawValueExpr<'a, D>) -> Self {
        Self {
            raw_value_expr,
            spooky: PhantomData,
        }
    }
}

impl<D: Decoder> WriteAsIon for WriteableRawValueExpr<'_, D> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        use RawValueExpr::*;
        match self.raw_value_expr {
            ValueLiteral(v) => WriteableRawValue::new(v).write_as_ion(writer),
            EExp(e) => WriteableEExp::new(e).write_as_ion(writer),
        }
    }
}

impl<D: Decoder> WriteAsIon for ValueRef<'_, D> {
    fn write_as_ion<V: ValueWriter>(&self, value_writer: V) -> IonResult<()> {
        use ValueRef::*;
        match self {
            Null(i) => value_writer.write_null(*i),
            Bool(b) => value_writer.write_bool(*b),
            Int(i) => value_writer.write_int(i),
            Float(f) => value_writer.write_f64(*f),
            Decimal(d) => value_writer.write_decimal(d),
            Timestamp(t) => value_writer.write_timestamp(t),
            Symbol(s) => value_writer.write_symbol(s),
            String(s) => value_writer.write_string(s.text()),
            Clob(c) => value_writer.write_clob(c.as_ref()),
            Blob(b) => value_writer.write_blob(b.as_ref()),
            List(l) => value_writer.write(l),
            SExp(s) => value_writer.write(s),
            Struct(s) => value_writer.write(s),
        }
    }
}

impl<D: Decoder> WriteAsIon for LazyList<'_, D> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        let mut list = writer.list_writer()?;
        for value in self {
            list.write(value?)?;
        }
        list.close()
    }
}

impl<D: Decoder> WriteAsIon for LazySExp<'_, D> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        let mut sexp = writer.sexp_writer()?;
        for value in self {
            sexp.write(value?)?;
        }
        sexp.close()
    }
}

impl<D: Decoder> WriteAsIon for LazyStruct<'_, D> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        let mut struct_writer = writer.struct_writer()?;
        for field_result in self {
            let field = field_result?;
            struct_writer.write(field.name()?, field.value())?;
        }
        struct_writer.close()
    }
}

impl<T: WriteAsIon> WriteAsIon for Option<T> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        if let Some(value) = self {
            value.write_as_ion(writer)
        } else {
            writer.write_null(IonType::Null)
        }
    }
}
