use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::write_as_ion::{WriteAsIon, WriteAsIonValue};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{Decimal, Int, IonResult, IonType, Timestamp};
use delegate::delegate;

pub mod internal {
    use crate::lazy::encoder::value_writer::AnnotatableValueWriter;

    pub trait MakeValueWriter {
        type ValueWriter<'a>: AnnotatableValueWriter
        where
            Self: 'a;

        fn make_value_writer(&mut self) -> Self::ValueWriter<'_>;
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
}

pub trait MacroArgsWriter: SequenceWriter {
    // TODO: methods for writing tagless encodings
}

pub trait ValueWriter: Sized {
    type ListWriter: SequenceWriter;
    type SExpWriter: SequenceWriter;
    type StructWriter: StructWriter;
    type MacroArgsWriter: MacroArgsWriter;
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

    fn write_list(self, list_fn: impl ListFn<Self>) -> IonResult<()>;

    fn write_sexp(self, sexp_fn: impl SExpFn<Self>) -> IonResult<()>;

    fn write_struct(self, struct_fn: impl StructFn<Self>) -> IonResult<()>;

    fn write_eexp<'macro_id>(
        self,
        _macro_id: impl Into<MacroIdRef<'macro_id>>,
        _macro_fn: impl MacroArgsFn<Self>,
    ) -> IonResult<()>;

    fn write(self, value: impl WriteAsIonValue) -> IonResult<()> {
        value.write_as_ion_value(self)
    }
}

/// There are several implementations of `ValueWriter` that simply delegate calls to an expression.
/// This macro takes an expression and calls the `delegate!` proc macro on it for all of the methods
/// in the ValueWriter trait. For example:
/// ```text
///     delegate_value_writer_to!()     => delegate! { to self { ...signatures ... } }
///     delegate_value_writer_to!(foo)  => delegate! { to self.foo { ...signatures ... } }
///     delegate_value_writer_to!(0)    => delegate! { to self.0 { ...signatures ... } }
///     delegate_value_writer_to!(
///         closure
///         |self_: Self| {
///             self_.value_writer()
///         }
///     )                               => delegate! { to self.value_writer() { ...signatures ... } }
///     delegate_value_writer_to!(
///         fallible closure
///         |self_: Self| {
///             self_.returns_result()
///         }
///     )                               => delegate! { to self.returns_result()? { ...signatures ... } }
/// ```
///
/// Notice that if no parameter expression is passed, it results in delegation to `self`, which is helpful if
/// the trait is implemented by calling methods on the type's inherent impls.
///
/// Using this macro for such use cases centralizes the method signatures of ValueWriter, simplifying refactoring.
macro_rules! delegate_value_writer_to {
    // Declarative Rust macros (those defined with `macro_rules!`) cannot work with a `self` instance
    // from the enclosing context. Callers can pass `self` as an argument, but the macro's parameter
    // cannot be named `self`. The `delegate!` macro circumvents this by being a proc macro, which
    // does not have to adhere to the same macro hygiene rules as declarative macros.
    //
    // All of the patterns that this macro accepts are transformed into invocations of the final
    // `fallible closure` pattern, allowing us to only write out all of the trait method signatures
    // once.
    //
    // If no arguments are passed, trait method calls are delegated to inherent impl methods on `self`.
    () => {
        $crate::lazy::encoder::value_writer::delegate_value_writer_to!(closure |self_: Self| self_);
    };
    // If an identifier is passed, it is treated as the name of a subfield of `self`.
    ($name:ident) => {
       $crate::lazy::encoder::value_writer::delegate_value_writer_to!(closure |self_: Self| self_.$name);
    };
    // If a closure is provided, trait method calls are delegated to the closure's return value.
    (closure $f:expr) => {
        // In order to forward this call to the `fallible closure` pattern, the provided closure is
        // wrapped in another closure that wraps the closure's output in IonResult::Ok(_). The
        // compiler can eliminate the redundant closure call.
        $crate::lazy::encoder::value_writer::delegate_value_writer_to!(fallible closure |self_: Self| {
            let infallible_closure = $f;
            $crate::IonResult::Ok(infallible_closure(self_))
        });
    };
    // If a fallible closure is provided, it will be called. If it returns an `Err`, the method
    // will return. Otherwise, trait method calls are delegated to the `Ok(_)` value.
    (fallible closure $f:expr) => {
        // The `self` keyword can only be used within the `delegate!` proc macro.
        delegate! {
            to {let f = $f; f(self)?} {
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
                fn write_list(self, list_fn: impl $crate::lazy::encoder::container_fn::ListFn<Self>) -> IonResult<()>;
                fn write_sexp(
                    self,
                    sexp_fn: impl $crate::lazy::encoder::container_fn::SExpFn<Self>,
                ) -> IonResult<()>;
                fn write_struct(
                    self,
                    struct_fn: impl $crate::lazy::encoder::container_fn::StructFn<Self>,
                ) -> IonResult<()>;
                fn write_eexp<
                    'macro_id,
                >(
                    self,
                    macro_id: impl Into<MacroIdRef<'macro_id>>,
                    macro_fn: impl $crate::lazy::encoder::container_fn::MacroArgsFn<Self>,
                ) -> IonResult<()>;
            }
        }
    };
}

/// [`delegate_value_writer_to`] allows you to omit arguments altogether, but that makes its effect
/// a bit unclear. This macro calls [`delegate_value_writer_to`] with no parameters but has a more
/// informative name.
macro_rules! delegate_value_writer_to_self {
    () => {
        $crate::lazy::encoder::value_writer::delegate_value_writer_to!();
    };
}

use crate::lazy::encoder::container_fn::{ListFn, MacroArgsFn, SExpFn, StructFn};
pub(crate) use delegate_value_writer_to;
pub(crate) use delegate_value_writer_to_self;

impl<V> ValueWriter for V
where
    V: AnnotatableValueWriter,
{
    type ListWriter = <V::ValueWriter as ValueWriter>::ListWriter;
    type SExpWriter = <V::ValueWriter as ValueWriter>::SExpWriter;
    type StructWriter = <V::ValueWriter as ValueWriter>::StructWriter;
    type MacroArgsWriter = <V::ValueWriter as ValueWriter>::MacroArgsWriter;

    delegate_value_writer_to!(closure |self_: Self| {
       self_.without_annotations()
    });
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
    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        <Self as MakeValueWriter>::make_value_writer(self)
    }

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
        value.write_as_ion(self.make_value_writer())?;
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

    // XXX: For now, it's not possible to offer versions of `write_list`, `write_sexp`,
    //      `write_struct` or `write_eexp`. This is due to a point-in-time limitation in the borrow checker[1].
    //      It is still possible to call (e.g.)
    //          self.value_writer().list_writer(...)
    //      as a workaround.
    // [1]: https://blog.rust-lang.org/2022/10/28/gats-stabilization.html#implied-static-requirement-from-higher-ranked-trait-bounds
    //
    // The ValueWriter implementation of these methods moves `self`. In contrast, all of the methods
    // in the SequenceWriter interface take `&mut self`, which adds another lifetime to the mix. The
    // borrow checker is not currently able to tell that `&mut self`'s lifetime will outlive the
    // closure argument's.
}
