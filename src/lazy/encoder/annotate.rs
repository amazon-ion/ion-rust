use crate::lazy::encoder::value_writer::AnnotatableValueWriter;
use crate::lazy::encoder::write_as_ion::{WriteAsIon, WriteAsIonValue};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::IonResult;

/// Associates a value to serialize with a sequence of annotations.
pub struct Annotated<'a, T: ?Sized, A> {
    value: &'a T,
    annotations: &'a [A],
}

/// Provides implementors with an extension method ([`annotate`](Annotate::annotated_with)) that allows
/// them to be serialized with an associated sequence of annotations.    
pub trait Annotate {
    /// Pairs a reference to the provided value with a slice containing annotations.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::{Element, IonData};
    /// use ion_rs::lazy::encoder::LazyRawTextWriter_1_0;
    /// use ion_rs::lazy::encoder::annotate::Annotate;
    ///
    /// let mut buffer = vec![];
    /// let mut writer = LazyRawTextWriter_1_0::new(&mut buffer);
    ///
    /// writer.write(42_usize.annotated_with(&["foo", "bar", "baz"]))?.flush()?;
    ///
    /// let expected = Element::read_one("foo::bar::baz::42")?;
    /// let actual = Element::read_one(&buffer)?;
    ///
    /// assert!(IonData::eq(&expected, &actual));
    ///# Ok(())
    ///# }
    /// ```
    fn annotated_with<'a, A: AsRawSymbolTokenRef>(
        &'a self,
        annotations: &'a [A],
    ) -> Annotated<'a, Self, A>;
}

// Any Rust value that can be serialized as an Ion value can call `annotate`.
impl<T> Annotate for T
where
    T: ?Sized + WriteAsIonValue,
{
    fn annotated_with<'a, A: AsRawSymbolTokenRef>(
        &'a self,
        annotations: &'a [A],
    ) -> Annotated<'a, Self, A> {
        Annotated {
            value: self,
            annotations,
        }
    }
}

// The `Annotated` struct implements `WriteAsIon` by serializing its sequence of annotations
// and then invoking the inner value's implementation of `WriteAsIonValue`.
impl<'annotations, T, A> WriteAsIon for Annotated<'annotations, T, A>
where
    T: WriteAsIonValue,
    A: AsRawSymbolTokenRef,
{
    fn write_as_ion<V: AnnotatableValueWriter>(&self, writer: V) -> IonResult<()> {
        let value_writer = writer.with_annotations(self.annotations);
        self.value.write_as_ion_value(value_writer)
    }
}

impl<'annotations, T, A> WriteAsIon for &Annotated<'annotations, T, A>
where
    T: WriteAsIonValue,
    A: AsRawSymbolTokenRef,
{
    fn write_as_ion<V: AnnotatableValueWriter>(&self, writer: V) -> IonResult<()> {
        (*self).write_as_ion(writer)
    }
}
