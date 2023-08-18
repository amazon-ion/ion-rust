use crate::lazy::decoder::{LazyDecoder, LazyRawSequence, LazyRawValue};
use crate::lazy::encoding::BinaryEncoding;
use crate::lazy::value::{AnnotationsIterator, LazyValue};
use crate::{Annotations, Element, IntoAnnotatedElement, Sequence, Value};
use crate::{IonError, IonResult, IonType, SymbolTable};
use std::fmt;
use std::fmt::{Debug, Formatter};

/// A list in a binary Ion stream whose header has been parsed but whose body
/// (i.e. its child values) have not. A `LazyList` is immutable; its data can be read any
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
pub struct LazyList<'top, 'data, D: LazyDecoder<'data>> {
    pub(crate) raw_list: D::List,
    pub(crate) symbol_table: &'top SymbolTable,
}

pub type LazyBinarySequence<'top, 'data> = LazyList<'top, 'data, BinaryEncoding>;

impl<'top, 'data, D: LazyDecoder<'data>> LazyList<'top, 'data, D> {
    /// Returns the [`IonType`] of this sequence.
    ///
    /// This will always be either [`IonType::List`] or [`IonType::SExp`].
    // TODO: We should have a `SequenceType` enum with only those options.
    pub fn ion_type(&self) -> IonType {
        self.raw_list.ion_type()
    }

    /// Returns an iterator over the values in this sequence. See: [`LazyValue`].
    pub fn iter(&self) -> ListIterator<'top, 'data, D> {
        ListIterator {
            raw_list_iter: self.raw_list.iter(),
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
    pub fn annotations(&self) -> AnnotationsIterator<'top, 'data, D> {
        AnnotationsIterator {
            raw_annotations: self.raw_list.as_value().annotations(),
            symbol_table: self.symbol_table,
        }
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> TryFrom<LazyList<'top, 'data, D>> for Sequence {
    type Error = IonError;

    fn try_from(lazy_sequence: LazyList<'top, 'data, D>) -> Result<Self, Self::Error> {
        let sequence: Sequence = lazy_sequence
            .iter()
            .map(|v| Element::try_from(v?))
            .collect::<IonResult<Vec<_>>>()?
            .into();
        Ok(sequence)
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> TryFrom<LazyList<'top, 'data, D>> for Element {
    type Error = IonError;

    fn try_from(lazy_list: LazyList<'top, 'data, D>) -> Result<Self, Self::Error> {
        let annotations: Annotations = lazy_list.annotations().try_into()?;
        let sequence: Sequence = lazy_list.try_into()?;
        let value = Value::List(sequence);
        Ok(value.with_annotations(annotations))
    }
}

impl<'a, 'top, 'data, D: LazyDecoder<'data>> IntoIterator for &'a LazyList<'top, 'data, D> {
    type Item = IonResult<LazyValue<'top, 'data, D>>;
    type IntoIter = ListIterator<'top, 'data, D>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct ListIterator<'top, 'data, D: LazyDecoder<'data>> {
    raw_list_iter: <D::List as LazyRawSequence<'data, D>>::Iterator,
    symbol_table: &'top SymbolTable,
}

impl<'top, 'data, D: LazyDecoder<'data>> Iterator for ListIterator<'top, 'data, D> {
    type Item = IonResult<LazyValue<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_value = match self.raw_list_iter.next() {
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

impl<'top, 'data, D: LazyDecoder<'data>> Debug for LazyList<'top, 'data, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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

        Ok(())
    }
}

// ===== SExps =====

pub struct LazySExp<'top, 'data, D: LazyDecoder<'data>> {
    pub(crate) raw_sexp: D::SExp,
    pub(crate) symbol_table: &'top SymbolTable,
}

impl<'top, 'data, D: LazyDecoder<'data>> Debug for LazySExp<'top, 'data, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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

        Ok(())
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> LazySExp<'top, 'data, D> {
    /// Returns an iterator over the values in this sequence. See: [`LazyValue`].
    pub fn iter(&self) -> SExpIterator<'top, 'data, D> {
        SExpIterator {
            raw_sexp_iter: self.raw_sexp.iter(),
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
    pub fn annotations(&self) -> AnnotationsIterator<'top, 'data, D> {
        AnnotationsIterator {
            raw_annotations: self.raw_sexp.as_value().annotations(),
            symbol_table: self.symbol_table,
        }
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> TryFrom<LazySExp<'top, 'data, D>> for Sequence {
    type Error = IonError;

    fn try_from(lazy_sequence: LazySExp<'top, 'data, D>) -> Result<Self, Self::Error> {
        let sequence: Sequence = lazy_sequence
            .iter()
            .map(|v| Element::try_from(v?))
            .collect::<IonResult<Vec<_>>>()?
            .into();
        Ok(sequence)
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> TryFrom<LazySExp<'top, 'data, D>> for Element {
    type Error = IonError;

    fn try_from(lazy_sequence: LazySExp<'top, 'data, D>) -> Result<Self, Self::Error> {
        let annotations: Annotations = lazy_sequence.annotations().try_into()?;
        let sequence: Sequence = lazy_sequence.try_into()?;
        let value = Value::SExp(sequence);
        Ok(value.with_annotations(annotations))
    }
}

impl<'a, 'top, 'data, D: LazyDecoder<'data>> IntoIterator for &'a LazySExp<'top, 'data, D> {
    type Item = IonResult<LazyValue<'top, 'data, D>>;
    type IntoIter = SExpIterator<'top, 'data, D>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct SExpIterator<'top, 'data, D: LazyDecoder<'data>> {
    raw_sexp_iter: <D::SExp as LazyRawSequence<'data, D>>::Iterator,
    symbol_table: &'top SymbolTable,
}

impl<'top, 'data, D: LazyDecoder<'data>> Iterator for SExpIterator<'top, 'data, D> {
    type Item = IonResult<LazyValue<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_value = match self.raw_sexp_iter.next() {
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
