use crate::lazy::encoder::write_as_ion::{WriteAsIon, WriteAsIonValue};
use crate::lazy::encoder::{AnnotatedValueWriter, LazyEncoder};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::IonResult;
use std::io::Write;

/// Associates a value to serialize with a sequence of annotations.
pub struct Annotated<'a, T: ?Sized, A> {
    value: &'a T,
    annotations: &'a [A],
}

/// Provides implementors with an extension method ([`annotate`](Annotate::annotate)) that allows
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
    /// writer.write(42_usize.annotate(&["foo", "bar", "baz"]))?.flush()?;
    ///
    /// let expected = Element::read_one("foo::bar::baz::42")?;
    /// let actual = Element::read_one(&buffer)?;
    ///
    /// assert!(IonData::eq(&expected, &actual));
    ///# Ok(())
    ///# }
    /// ```
    fn annotate<'a, A: AsRawSymbolTokenRef>(
        &'a self,
        annotations: &'a [A],
    ) -> Annotated<'a, Self, A>;
}

// Any Rust value that can be serialized as an Ion value can call `annotate`.
impl<T> Annotate for T
where
    T: WriteAsIonValue,
{
    fn annotate<'a, A: AsRawSymbolTokenRef>(
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
impl<'b, T, A> WriteAsIon for Annotated<'b, T, A>
where
    T: WriteAsIonValue,
    A: AsRawSymbolTokenRef,
{
    fn write_as_ion<'a, W: Write + 'a, E: LazyEncoder<W>, V: AnnotatedValueWriter<'a, W, E>>(
        &self,
        annotations_writer: V,
    ) -> IonResult<()> {
        let value_writer = annotations_writer.write_annotations(self.annotations.iter())?;
        self.value.write_as_ion_value(value_writer)
    }
}
