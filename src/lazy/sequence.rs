use std::fmt;
use std::fmt::{Debug, Formatter};

use crate::lazy::decoder::LazyDecoder;
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::lazy::expanded::sequence::{
    ExpandedListIterator, ExpandedSExpIterator, LazyExpandedList, LazyExpandedSExp,
};
use crate::lazy::value::{AnnotationsIterator, LazyValue};
use crate::{Annotations, Element, IntoAnnotatedElement, Sequence, Value};
use crate::{IonError, IonResult};

/// A list in a binary Ion stream whose header has been parsed but whose body
/// (i.e. its child values) have not. A `LazyList` is immutable; its data can be read any
/// number of times.
///
/// ```
///# use ion_rs::IonResult;
///# #[cfg(feature = "experimental-reader-writer")]
///# fn main() -> IonResult<()> {
///
/// // Construct an Element and serialize it as binary Ion.
/// use ion_rs::{Element, ion_list};
/// use ion_rs::v1_0::{Binary, BinaryReader};
///
/// let element: Element = ion_list! [10, 20, 30].into();
/// let binary_ion = element.encode_as(Binary)?;
///
/// let mut lazy_reader = BinaryReader::new(binary_ion)?;
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
///# #[cfg(not(feature = "experimental-reader-writer"))]
///# fn main() -> IonResult<()> { Ok(()) }
/// ```
#[derive(Copy, Clone)]
pub struct LazyList<'top, D: LazyDecoder> {
    pub(crate) expanded_list: LazyExpandedList<'top, D>,
}

pub type LazyBinarySequence<'top, 'data> = LazyList<'top, BinaryEncoding_1_0>;

impl<'top, D: LazyDecoder> LazyList<'top, D> {
    /// Returns an iterator over the values in this sequence. See: [`LazyValue`].
    pub fn iter(&self) -> ListIterator<'top, D> {
        ListIterator {
            expanded_list_iter: self.expanded_list.iter(),
        }
    }

    #[cfg(feature = "experimental-tooling-apis")]
    pub fn lower(&self) -> LazyExpandedList<'top, D> {
        self.expanded_list
    }

    #[cfg(not(feature = "experimental-tooling-apis"))]
    pub(crate) fn lower(&self) -> LazyExpandedList<'top, D> {
        self.expanded_list
    }

    /// Returns an iterator over the annotations on this value. If this value has no annotations,
    /// the resulting iterator will be empty.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# #[cfg(feature = "experimental-reader-writer")]
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{ion_sexp, Element, IntoAnnotatedElement};
    /// use ion_rs::v1_0::{Binary, BinaryReader};
    ///
    /// let element: Element = ion_sexp!(true false).with_annotations(["foo", "bar", "baz"]);
    /// let binary_ion = element.encode_as(Binary)?;
    ///
    /// let mut lazy_reader = BinaryReader::new(binary_ion)?;
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
    ///# #[cfg(not(feature = "experimental-reader-writer"))]
    ///# fn main() -> IonResult<()> { Ok(()) }
    /// ```
    pub fn annotations(&self) -> AnnotationsIterator<'top, D> {
        AnnotationsIterator {
            expanded_annotations: self.expanded_list.annotations(),
            symbol_table: self.expanded_list.context.symbol_table,
        }
    }
}

impl<'top, D: LazyDecoder> TryFrom<LazyList<'top, D>> for Sequence {
    type Error = IonError;

    fn try_from(lazy_sequence: LazyList<'top, D>) -> Result<Self, Self::Error> {
        let sequence: Sequence = lazy_sequence
            .iter()
            .map(|v| Element::try_from(v?))
            .collect::<IonResult<Vec<_>>>()?
            .into();
        Ok(sequence)
    }
}

impl<'top, D: LazyDecoder> TryFrom<LazyList<'top, D>> for Element {
    type Error = IonError;

    fn try_from(lazy_list: LazyList<'top, D>) -> Result<Self, Self::Error> {
        let annotations: Annotations = lazy_list.annotations().try_into()?;
        let sequence: Sequence = lazy_list.try_into()?;
        let value = Value::List(sequence);
        Ok(value.with_annotations(annotations))
    }
}

impl<'a, 'top, 'data: 'top, D: LazyDecoder> IntoIterator for &'a LazyList<'top, D> {
    type Item = IonResult<LazyValue<'top, D>>;
    type IntoIter = ListIterator<'top, D>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct ListIterator<'top, D: LazyDecoder> {
    expanded_list_iter: ExpandedListIterator<'top, D>,
}

impl<'top, D: LazyDecoder> Iterator for ListIterator<'top, D> {
    type Item = IonResult<LazyValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let expanded_value = match self.expanded_list_iter.next() {
            Some(Ok(expanded_value)) => expanded_value,
            Some(Err(e)) => return Some(Err(e)),
            None => return None,
        };

        let lazy_value = LazyValue { expanded_value };
        Some(Ok(lazy_value))
    }
}

impl<'top, D: LazyDecoder> Debug for LazyList<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for value in self {
            write!(f, "{:?},", value?.read()?)?;
        }
        write!(f, "]")?;

        Ok(())
    }
}

// ===== SExps =====

#[derive(Copy, Clone)]
pub struct LazySExp<'top, D: LazyDecoder> {
    pub(crate) expanded_sexp: LazyExpandedSExp<'top, D>,
}

impl<'top, D: LazyDecoder> Debug for LazySExp<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for value in self {
            write!(f, "{:?} ", value?.read()?)?;
        }
        write!(f, ")")?;

        Ok(())
    }
}

impl<'top, D: LazyDecoder> LazySExp<'top, D> {
    pub fn lower(&self) -> LazyExpandedSExp<'top, D> {
        self.expanded_sexp
    }

    /// Returns an iterator over the values in this sequence. See: [`LazyValue`].
    pub fn iter(&self) -> SExpIterator<'top, D> {
        SExpIterator {
            expanded_sexp_iter: self.expanded_sexp.iter(),
        }
    }

    /// Returns an iterator over the annotations on this value. If this value has no annotations,
    /// the resulting iterator will be empty.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# #[cfg(feature = "experimental-reader-writer")]
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{ion_sexp, Element, IntoAnnotatedElement};
    /// use ion_rs::v1_0::{Binary, BinaryReader};
    ///
    /// let element: Element = ion_sexp!(true false).with_annotations(["foo", "bar", "baz"]);
    /// let binary_ion = element.encode_as(Binary)?;
    ///
    /// let mut lazy_reader = BinaryReader::new(binary_ion)?;
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
    ///# #[cfg(not(feature = "experimental-reader-writer"))]
    ///# fn main() -> IonResult<()> { Ok(()) }
    /// ```
    pub fn annotations(&self) -> AnnotationsIterator<'top, D> {
        AnnotationsIterator {
            expanded_annotations: self.expanded_sexp.annotations(),
            symbol_table: self.expanded_sexp.context.symbol_table,
        }
    }
}

impl<'top, D: LazyDecoder> TryFrom<LazySExp<'top, D>> for Sequence {
    type Error = IonError;

    fn try_from(lazy_sequence: LazySExp<'top, D>) -> Result<Self, Self::Error> {
        let sequence: Sequence = lazy_sequence
            .iter()
            .map(|v| Element::try_from(v?))
            .collect::<IonResult<Vec<_>>>()?
            .into();
        Ok(sequence)
    }
}

impl<'top, D: LazyDecoder> TryFrom<LazySExp<'top, D>> for Element {
    type Error = IonError;

    fn try_from(lazy_sequence: LazySExp<'top, D>) -> Result<Self, Self::Error> {
        let annotations: Annotations = lazy_sequence.annotations().try_into()?;
        let sequence: Sequence = lazy_sequence.try_into()?;
        let value = Value::SExp(sequence);
        Ok(value.with_annotations(annotations))
    }
}

impl<'a, 'top, 'data: 'top, D: LazyDecoder> IntoIterator for &'a LazySExp<'top, D> {
    type Item = IonResult<LazyValue<'top, D>>;
    type IntoIter = SExpIterator<'top, D>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct SExpIterator<'top, D: LazyDecoder> {
    expanded_sexp_iter: ExpandedSExpIterator<'top, D>,
}

impl<'top, D: LazyDecoder> Iterator for SExpIterator<'top, D> {
    type Item = IonResult<LazyValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let expanded_value = match self.expanded_sexp_iter.next() {
            Some(Ok(expanded_value)) => expanded_value,
            Some(Err(e)) => return Some(Err(e)),
            None => return None,
        };

        let lazy_value = LazyValue { expanded_value };
        Some(Ok(lazy_value))
    }
}

#[cfg(test)]
mod tests {
    use crate::element::Element;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::reader::BinaryReader_1_0;
    use crate::IonResult;

    #[test]
    fn annotations() -> IonResult<()> {
        let binary_ion = to_binary_ion("foo::bar::baz::[1, 2, 3]")?;
        let mut reader = BinaryReader_1_0::new(binary_ion)?;
        let list = reader.expect_next()?.read()?.expect_list()?;
        assert!(list.annotations().are(["foo", "bar", "baz"])?);
        list.annotations().expect(["foo", "bar", "baz"])?;
        Ok(())
    }

    #[test]
    fn try_into_element() -> IonResult<()> {
        let ion_text = "foo::baz::baz::[1, 2, 3]";
        let binary_ion = to_binary_ion(ion_text)?;
        let mut reader = BinaryReader_1_0::new(binary_ion)?;
        let list = reader.expect_next()?.read()?.expect_list()?;
        let result: IonResult<Element> = list.try_into();
        assert!(result.is_ok());
        assert_eq!(result?, Element::read_one(ion_text)?);
        Ok(())
    }
}
