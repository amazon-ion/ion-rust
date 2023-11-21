use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::{
    TextAnnotatedValueWriter_1_0, TextListWriter_1_0, TextSExpWriter_1_0, TextStructWriter_1_0,
    TextValueWriter_1_0,
};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::text::text_formatter::IonValueFormatter;
use crate::{Decimal, Int, IonResult, IonType, RawTextWriter, Timestamp};
use delegate::delegate;
use std::fmt::Formatter;
use std::io::Write;

// TODO: Make this private
pub trait MakeValueWriter {
    type ValueWriter<'a>: AnnotatableValueWriter
    where
        Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_>;
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
        }
    }
}

pub trait ValueWriter {
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
    fn write_string<A: AsRef<str>>(self, value: A) -> IonResult<()>;
    fn write_symbol<A: AsRawSymbolTokenRef>(self, value: A) -> IonResult<()>;
    fn write_clob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()>;
    fn write_blob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()>;

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
        fn $method<V: WriteAsIon>(&mut self, value: $value_type) -> IonResult<&mut Self> {
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

impl<'value, W: Write + 'value, SymbolType: AsRawSymbolTokenRef> ValueWriter
    for TextAnnotatedValueWriter_1_0<'value, W, SymbolType>
{
    type ListWriter<'a> = TextListWriter_1_0<'value, W>;
    type SExpWriter<'a> = TextSExpWriter_1_0<'value, W>;
    type StructWriter<'a> = TextStructWriter_1_0<'value, W>;

    delegate! {
        to self.encode_annotations()? {
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
            fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
                self,
                list_fn: F,
            ) -> IonResult<()>;
            fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
                self,
                sexp_fn: F,
            ) -> IonResult<()>;
            fn write_struct<
                F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>,
            >(
                self,
                struct_fn: F,
            ) -> IonResult<()>;
        }
    }
}

impl<'value, W: Write> ValueWriter for TextValueWriter_1_0<'value, W> {
    type ListWriter<'a> = TextListWriter_1_0<'value, W>;
    type SExpWriter<'a> = TextSExpWriter_1_0<'value, W>;
    type StructWriter<'a> = TextStructWriter_1_0<'value, W>;
    fn write_null(mut self, ion_type: IonType) -> IonResult<()> {
        use crate::IonType::*;
        let null_text = match ion_type {
            Null => "null",
            Bool => "null.bool",
            Int => "null.int",
            Float => "null.float",
            Decimal => "null.decimal",
            Timestamp => "null.timestamp",
            Symbol => "null.symbol",
            String => "null.string",
            Blob => "null.blob",
            Clob => "null.clob",
            List => "null.list",
            SExp => "null.sexp",
            Struct => "null.struct",
        };
        write!(self.output(), "{null_text}")?;
        Ok(())
    }

    fn write_bool(mut self, value: bool) -> IonResult<()> {
        let bool_text = match value {
            true => "true",
            false => "false",
        };
        write!(self.output(), "{bool_text}")?;
        Ok(())
    }

    fn write_i64(mut self, value: i64) -> IonResult<()> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_int(mut self, value: &Int) -> IonResult<()> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_f32(self, value: f32) -> IonResult<()> {
        self.write_f64(value as f64)
    }

    fn write_f64(mut self, value: f64) -> IonResult<()> {
        if value.is_nan() {
            write!(self.output(), "nan")?;
            return Ok(());
        }

        if value.is_infinite() {
            if value.is_sign_positive() {
                write!(self.output(), "+inf")?;
            } else {
                write!(self.output(), "-inf")?;
            }
            return Ok(());
        }

        // The {:e} formatter provided by the Display trait writes floats using scientific
        // notation. It works for all floating point values except -0.0 (it drops the sign).
        // See: https://github.com/rust-lang/rust/issues/20596
        if value == 0.0f64 && value.is_sign_negative() {
            write!(self.output(), "-0e0")?;
            return Ok(());
        }

        write!(self.output(), "{value:e}")?;
        Ok(())
    }

    fn write_decimal(mut self, value: &Decimal) -> IonResult<()> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_timestamp(mut self, value: &Timestamp) -> IonResult<()> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_string<A: AsRef<str>>(mut self, value: A) -> IonResult<()> {
        write!(self.output(), "\"")?;
        RawTextWriter::<W>::write_escaped_text_body(self.output(), value)?;
        write!(self.output(), "\"")?;
        Ok(())
    }

    fn write_symbol<A: AsRawSymbolTokenRef>(mut self, value: A) -> IonResult<()> {
        RawTextWriter::<W>::write_symbol_token(self.output(), value)?;
        Ok(())
    }

    fn write_clob<A: AsRef<[u8]>>(mut self, value: A) -> IonResult<()> {
        // This type exists solely to enable using the IonValueFormatter (which operates on
        // `std::fmt::Write`) to write to a `std::io::Write`.
        struct ClobShim<'a>(&'a [u8]);
        impl<'a> std::fmt::Display for ClobShim<'a> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                let mut formatter = IonValueFormatter { output: f };
                formatter.format_clob(self.0)?;
                Ok(())
            }
        }

        write!(self.output(), "{}", ClobShim(value.as_ref()))?;
        Ok(())
    }

    fn write_blob<A: AsRef<[u8]>>(mut self, value: A) -> IonResult<()> {
        // Rust format strings escape curly braces by doubling them. The following string is:
        // * The opening {{ from a text Ion blob, with each brace doubled to escape it.
        // * A {} pair used by the format string to indicate where the base64-encoded bytes
        //   should be inserted.
        // * The closing }} from a text Ion blob, with each brace doubled to escape it.
        write!(self.output(), "{{{{{}}}}}", base64::encode(value))?;
        Ok(())
    }

    fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
        self,
        list_fn: F,
    ) -> IonResult<()> {
        let mut list_writer = TextListWriter_1_0::new(self.writer, self.depth + 1)?;
        list_fn(&mut list_writer)?;
        list_writer.end()
    }
    fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
        self,
        sexp_fn: F,
    ) -> IonResult<()> {
        let mut sexp_writer = TextSExpWriter_1_0::new(self.writer, self.depth + 1)?;
        sexp_fn(&mut sexp_writer)?;
        sexp_writer.end()
    }
    fn write_struct<F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>>(
        self,
        struct_fn: F,
    ) -> IonResult<()> {
        let mut struct_writer = TextStructWriter_1_0::new(self.writer, self.depth + 1)?;
        struct_fn(&mut struct_writer)?;
        struct_writer.end()
    }
}
