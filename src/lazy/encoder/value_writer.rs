use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::write_as_ion::{WriteAsIon, WriteAsIonValue};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{Decimal, Int, IonResult, IonType, Timestamp};
use delegate::delegate;

pub(crate) mod internal {
    use crate::lazy::encoder::value_writer::AnnotatableValueWriter;

    pub trait MakeValueWriter {
        type ValueWriter<'a>: AnnotatableValueWriter
        where
            Self: 'a;

        fn value_writer(&mut self) -> Self::ValueWriter<'_>;
    }
}

/// One-shot methods that take a (possibly empty) sequence of annotations to encode and return a ValueWriter.
pub trait AnnotatableValueWriter: Sized {
    type ValueWriter: ValueWriter;
    type AnnotatedValueWriter<'a, SymbolType: AsRawSymbolTokenRef + 'a>: ValueWriter
    where
        Self: 'a;
    /// Writes the provided annotations to the output stream and returns a [`ValueWriter`] that can
    /// be used to serialize the value itself.
    ///
    /// If there are no annotations, use [`Self::without_annotations`] instead. This method will loop
    /// over the empty sequence, incurring minor performance overhead while `without_annotations`
    /// is a true no-op.
    fn with_annotations<'a, SymbolType: AsRawSymbolTokenRef>(
        self,
        annotations: &'a [SymbolType],
    ) -> Self::AnnotatedValueWriter<'a, SymbolType>
    where
        Self: 'a;

    /// Performs no operations and returns a [`ValueWriter`].
    fn without_annotations(self) -> Self::ValueWriter;

    // Users can call `ValueWriter` methods on the `AnnotatedValueWriter` directly. Doing so
    // will implicitly call `without_annotations`.
    delegate! {
        to self.without_annotations() {
            fn write_null(self, ion_type: IonType) -> IonResult<()>;
            fn write_bool(self, value: bool) -> IonResult<()>;
            fn write_i64(self, value: i64) -> IonResult<()>;
            fn write_int(self, value: &Int) -> IonResult<()>;
            fn write_f32(self, value: f32) -> IonResult<()>;
            fn write_f64(self, value: f64) -> IonResult<()>;
            fn write_decimal(self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(self, value: &Timestamp) -> IonResult<()>;
            fn write_string<A: AsRef<str>>(self, value: A) -> IonResult<()>;
            fn write_symbol<A: AsRawSymbolTokenRef>(self, value: A) -> IonResult<()>;
            fn write_clob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()>;
            fn write_blob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()>;
            fn write_list<F: for<'a> FnOnce(&mut <Self::ValueWriter as ValueWriter>::ListWriter<'a>) -> IonResult<()>>(
                self,
                list_fn: F,
            ) -> IonResult<()>;
            fn write_sexp<F: for<'a> FnOnce(&mut <Self::ValueWriter as ValueWriter>::SExpWriter<'a>) -> IonResult<()>>(
                self,
                sexp_fn: F,
            ) -> IonResult<()>;
            fn write_struct<
                F: for<'a> FnOnce(&mut <Self::ValueWriter as ValueWriter>::StructWriter<'a>) -> IonResult<()>,
            >(
                self,
                struct_fn: F,
            ) -> IonResult<()>;
                fn write(self, value: impl WriteAsIonValue) -> IonResult<()>;
        }
    }
}

pub trait ValueWriter: Sized {
    type ListWriter<'a>: SequenceWriter;
    type SExpWriter<'a>: SequenceWriter;
    type StructWriter<'a>: StructWriter;

    fn write_null(self, ion_type: IonType) -> IonResult<()>;
    fn write_bool(self, value: bool) -> IonResult<()>;
    fn write_i64(self, value: i64) -> IonResult<()>;
    fn write_int(self, value: &Int) -> IonResult<()>;
    fn write_f32(self, value: f32) -> IonResult<()>;
    fn write_f64(self, value: f64) -> IonResult<()>;
    fn write_decimal(self, value: &Decimal) -> IonResult<()>;
    fn write_timestamp(self, value: &Timestamp) -> IonResult<()>;
    fn write_string(self, value: impl AsRef<str>) -> IonResult<()>;
    fn write_symbol(self, value: impl AsRawSymbolTokenRef) -> IonResult<()>;
    fn write_clob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
    fn write_blob(self, value: impl AsRef<[u8]>) -> IonResult<()>;

    fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
        self,
        list_fn: F,
    ) -> IonResult<()>;

    fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
        self,
        sexp_fn: F,
    ) -> IonResult<()>;

    fn write_struct<F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>>(
        self,
        struct_fn: F,
    ) -> IonResult<()>;

    fn write(self, value: impl WriteAsIonValue) -> IonResult<()> {
        value.write_as_ion_value(self)
    }
}

pub trait StructWriter {
    /// Writes a struct field using the provided name/value pair.
    fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        name: A,
        value: V,
    ) -> IonResult<&mut Self>;
}

/// Takes a series of `TYPE => METHOD` pairs, generating a function for each that calls the
/// corresponding value writer method and then returns `Ok(self)` upon success.
macro_rules! delegate_and_return_self {
    // End of iteration
    () => {};
    // Recurses one argument pair at a time
    ($value_type:ty => $method:ident, $($rest:tt)*) => {
        fn $method(&mut self, value: $value_type) -> IonResult<&mut Self> {
            self.value_writer().without_annotations().$method(value)?;
            Ok(self)
        }
        delegate_and_return_self!($($rest)*);
    };
}

pub trait SequenceWriter: MakeValueWriter {
    fn annotate<'a, A: AsRawSymbolTokenRef>(
        &'a mut self,
        annotations: &'a [A],
    ) -> <<Self as MakeValueWriter>::ValueWriter<'_> as AnnotatableValueWriter>::AnnotatedValueWriter<'a, A>
    {
        self.value_writer().with_annotations(annotations)
    }

    /// Writes a value in the current context (list, s-expression, or stream) and upon success
    /// returns another reference to `self` to enable method chaining.
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        value.write_as_ion(self.value_writer())?;
        Ok(self)
    }

    // Creates functions that delegate to the ValueWriter method of the same name but which then
    // return `self` so it can be re-used/chained.
    delegate_and_return_self!(
        IonType => write_null,
        bool => write_bool,
        i64 => write_i64,
        &Int => write_int,
        f32 => write_f32,
        f64 => write_f64,
        &Decimal => write_decimal,
        &Timestamp => write_timestamp,
        impl AsRef<str> => write_string,
        impl AsRawSymbolTokenRef => write_symbol,
        impl AsRef<[u8]> => write_clob,
        impl AsRef<[u8]> => write_blob,
    );

    // XXX: For now, it's not possible to offer versions of `write_list`, `write_sexp`, or
    //      `write_struct`. This is due to a point-in-time limitation in the borrow checker[1].
    //      It is still possible to call (e.g.)
    //          self.value_writer().list_writer(...)
    //      as a workaround.
    // [1]: https://blog.rust-lang.org/2022/10/28/gats-stabilization.html#implied-static-requirement-from-higher-ranked-trait-bounds
}
