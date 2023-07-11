use crate::lazy::binary::format::BinaryFormat;
use crate::lazy::format::{LazyFormat, LazyRawSequence, LazyRawValue};
use crate::lazy::value::{AnnotationsIterator, LazyValue};
use crate::{Annotations, Element, IntoAnnotatedElement, Sequence, Value};
use crate::{IonError, IonResult, IonType, SymbolTable};
use std::fmt;
use std::fmt::{Debug, Formatter};

/// A list or S-expression in a binary Ion stream whose header has been parsed but whose body
/// (i.e. its child values) have not. A `LazySequence` is immutable; its data can be read any
/// number of times.
///
/// ```
///# use ion_rs::IonResult;
///# fn main() -> IonResult<()> {
///
/// // Construct an Element and serialize it as binary Ion.
/// use ion_rs::{Element, ion_list};
/// use ion_rs::lazy::reader::LazyBinaryReader;;
///
/// let element: Element = ion_list! [10, 20, 30].into();
/// let binary_ion = element.to_binary()?;
///
/// let mut lazy_reader = LazyBinaryReader::new(&binary_ion)?;
///
/// // Get the first value from the stream and confirm that it's a list.
/// let lazy_list = lazy_reader.expect_next()?.read()?.expect_list()?;
///
/// // Visit the values in the list
/// let mut sum = 0;
/// for lazy_value in &lazy_list {
///     // Read each lazy value in the lazy list as an int (i64) and
///     // add it to the running total
///     sum += lazy_value?.read()?.expect_i64()?;
/// }
///
/// assert_eq!(sum, 60);
///
/// // Note that we can re-read any of the lazy values. Here we'll step into the list again and
/// // read the first child value.
/// let first_int = lazy_list.iter().next().unwrap()?.read()?.expect_i64()?;
/// assert_eq!(first_int, 10);
///
///# Ok(())
///# }
/// ```
pub struct LazySequence<'top, 'data, F: LazyFormat<'data>> {
    pub(crate) raw_sequence: F::Sequence,
    pub(crate) symbol_table: &'top SymbolTable,
}

pub type LazyBinarySequence<'top, 'data> = LazySequence<'top, 'data, BinaryFormat>;

impl<'top, 'data, F: LazyFormat<'data>> LazySequence<'top, 'data, F> {
    /// Returns the [`IonType`] of this sequence.
    ///
    /// This will always be either [`IonType::List`] or [`IonType::SExp`].
    // TODO: We should have a `SequenceType` enum with only those options.
    pub fn ion_type(&self) -> IonType {
        self.raw_sequence.ion_type()
    }

    /// Returns an iterator over the values in this sequence. See: [`LazyValue`].
    pub fn iter(&self) -> SequenceIterator<'top, 'data, F> {
        SequenceIterator {
            raw_sequence_iter: self.raw_sequence.iter(),
            symbol_table: self.symbol_table,
        }
    }

    /// Returns an iterator over the annotations on this value. If this value has no annotations,
    /// the resulting iterator will be empty.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{ion_sexp, Element, IntoAnnotatedElement};
    /// use ion_rs::lazy::reader::LazyBinaryReader;
    ///
    /// let element: Element = ion_sexp!(true false).with_annotations(["foo", "bar", "baz"]);
    /// let binary_ion = element.to_binary()?;
    ///
    /// let mut lazy_reader = LazyBinaryReader::new(&binary_ion)?;
    ///
    /// // Get the first lazy value from the stream.
    /// let lazy_sexp = lazy_reader.expect_next()?.read()?.expect_sexp()?;
    ///
    /// // Inspect its annotations.
    /// let mut annotations = lazy_sexp.annotations();
    /// assert_eq!(annotations.next().unwrap()?, "foo");
    /// assert_eq!(annotations.next().unwrap()?, "bar");
    /// assert_eq!(annotations.next().unwrap()?, "baz");
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn annotations(&self) -> AnnotationsIterator<'top, 'data, F> {
        AnnotationsIterator {
            raw_annotations: self.raw_sequence.as_value().annotations(),
            symbol_table: self.symbol_table,
        }
    }
}

impl<'top, 'data, F: LazyFormat<'data>> TryFrom<LazySequence<'top, 'data, F>> for Sequence {
    type Error = IonError;

    fn try_from(lazy_sequence: LazySequence<'top, 'data, F>) -> Result<Self, Self::Error> {
        let sequence: Sequence = lazy_sequence
            .iter()
            .map(|v| Element::try_from(v?))
            .collect::<IonResult<Vec<_>>>()?
            .into();
        Ok(sequence)
    }
}

impl<'top, 'data, F: LazyFormat<'data>> TryFrom<LazySequence<'top, 'data, F>> for Element {
    type Error = IonError;

    fn try_from(lazy_sequence: LazySequence<'top, 'data, F>) -> Result<Self, Self::Error> {
        let ion_type = lazy_sequence.ion_type();
        let annotations: Annotations = lazy_sequence.annotations().try_into()?;
        let sequence: Sequence = lazy_sequence.try_into()?;
        let value = match ion_type {
            IonType::SExp => Value::SExp(sequence),
            IonType::List => Value::List(sequence),
            _ => unreachable!("no other IonTypes are sequences"),
        };
        Ok(value.with_annotations(annotations))
    }
}

impl<'a, 'top, 'data, F: LazyFormat<'data>> IntoIterator for &'a LazySequence<'top, 'data, F> {
    type Item = IonResult<LazyValue<'top, 'data, F>>;
    type IntoIter = SequenceIterator<'top, 'data, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct SequenceIterator<'top, 'data, F: LazyFormat<'data>> {
    raw_sequence_iter: <F::Sequence as LazyRawSequence<'data, F>>::Iterator,
    symbol_table: &'top SymbolTable,
}

impl<'top, 'data, F: LazyFormat<'data>> Iterator for SequenceIterator<'top, 'data, F> {
    type Item = IonResult<LazyValue<'top, 'data, F>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_value = match self.raw_sequence_iter.next() {
            Some(Ok(raw_value)) => raw_value,
            Some(Err(e)) => return Some(Err(e)),
            None => return None,
        };

        let lazy_value = LazyValue {
            raw_value,
            symbol_table: self.symbol_table,
        };
        Some(Ok(lazy_value))
    }
}

impl<'top, 'data, F: LazyFormat<'data>> Debug for LazySequence<'top, 'data, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.ion_type() {
            IonType::SExp => {
                write!(f, "(")?;
                for value in self {
                    write!(
                        f,
                        "{:?} ",
                        value
                            .map_err(|_| fmt::Error)?
                            .read()
                            .map_err(|_| fmt::Error)?
                    )?;
                }
                write!(f, ")")?;
            }
            IonType::List => {
                write!(f, "[")?;
                for value in self {
                    write!(
                        f,
                        "{:?},",
                        value
                            .map_err(|_| fmt::Error)?
                            .read()
                            .map_err(|_| fmt::Error)?
                    )?;
                }
                write!(f, "]")?;
            }
            _ => unreachable!("LazySequence is only created for list and sexp"),
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::element::Element;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::reader::LazyBinaryReader;
    use crate::IonResult;

    #[test]
    fn annotations() -> IonResult<()> {
        let binary_ion = to_binary_ion("foo::bar::baz::[1, 2, 3]")?;
        let mut reader = LazyBinaryReader::new(&binary_ion)?;
        let list = reader.expect_next()?.read()?.expect_list()?;
        assert!(list.annotations().are(["foo", "bar", "baz"])?);
        list.annotations().expect(["foo", "bar", "baz"])?;
        Ok(())
    }

    #[test]
    fn try_into_element() -> IonResult<()> {
        let ion_text = "foo::baz::baz::[1, 2, 3]";
        let binary_ion = to_binary_ion(ion_text)?;
        let mut reader = LazyBinaryReader::new(&binary_ion)?;
        let list = reader.expect_next()?.read()?.expect_list()?;
        let result: IonResult<Element> = list.try_into();
        assert!(result.is_ok());
        assert_eq!(result?, Element::read_one(ion_text)?);
        Ok(())
    }

    #[test]
    fn try_into_element_error() -> IonResult<()> {
        let mut binary_ion = to_binary_ion("foo::baz::baz::[1, 2, 3]")?;
        let _oops_i_lost_a_byte = binary_ion.pop().unwrap();
        let mut reader = LazyBinaryReader::new(&binary_ion)?;
        let list = reader.expect_next()?.read()?.expect_list()?;
        // Conversion will fail because the reader will encounter an unexpected end of input
        let result: IonResult<Element> = list.try_into();
        assert!(result.is_err());
        Ok(())
    }
}
