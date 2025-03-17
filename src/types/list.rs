use crate::element::builders::SequenceBuilder;
use crate::element::iterators::SequenceIterator;
use crate::ion_data::{IonDataHash, IonEq};
use crate::text::text_formatter::FmtValueFormatter;
use crate::{Element, Sequence};
use delegate::delegate;
use std::fmt::{Display, Formatter};
use std::hash::Hasher;

/// An in-memory representation of an Ion list.
/// ```
/// use ion_rs::{ion_list, Element};
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// let list = ion_list![1, 2, 3];
/// assert_eq!(list.len(), 3);
/// assert_eq!(list.get(1), Some(&Element::int(2)));
/// # Ok(())
/// # }
/// ```
/// To build a `List` incrementally, see [SequenceBuilder].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct List(pub Sequence);

impl List {
    pub fn new(elements: impl Into<Sequence>) -> Self {
        List(elements.into())
    }
}

impl List {
    delegate! {
        to self.0 {
            pub fn clone_builder(&self) -> SequenceBuilder;
            pub fn elements(&self) -> SequenceIterator<'_>;
            pub fn get(&self, index: usize) -> Option<&Element>;
            pub fn len(&self) -> usize;
            pub fn is_empty(&self) -> bool;
        }
    }
}

impl IonEq for List {
    fn ion_eq(&self, other: &Self) -> bool {
        // The inner `Sequence` of both Lists are IonEq
        self.0.ion_eq(&other.0)
    }
}

impl IonDataHash for List {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.0.ion_data_hash(state)
    }
}

impl AsRef<Sequence> for List {
    fn as_ref(&self) -> &Sequence {
        &self.0
    }
}

impl AsRef<[Element]> for List {
    fn as_ref(&self) -> &[Element] {
        self.0.as_ref()
    }
}

// Allows `for element in &list {...}` syntax
impl<'a> IntoIterator for &'a List {
    type Item = &'a Element;
    type IntoIter = SequenceIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements()
    }
}

impl Display for List {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = FmtValueFormatter { output: f };
        ivf.format_list(self).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl From<Sequence> for List {
    fn from(sequence: Sequence) -> Self {
        Self(sequence)
    }
}

impl From<Vec<Element>> for List {
    fn from(elements: Vec<Element>) -> Self {
        Self(elements.into())
    }
}

impl FromIterator<Element> for List {
    fn from_iter<T: IntoIterator<Item = Element>>(iter: T) -> Self {
        Vec::from_iter(iter).into()
    }
}

impl From<List> for Sequence {
    fn from(value: List) -> Self {
        value.0
    }
}

#[cfg(test)]
mod tests {
    use crate::{ion_list, Element, IonResult, List};

    #[test]
    fn for_element_in_list() -> IonResult<()> {
        // Simple example to exercise List's implementation of IntoIterator
        let list = ion_list![1, 2, 3];
        let mut sum = 0;
        for element in &list {
            sum += element.expect_int()?.expect_i64()?;
        }
        assert_eq!(sum, 6i64);
        Ok(())
    }

    #[test]
    fn list_from_vec() -> IonResult<()> {
        let elements = vec![Element::int(1), Element::int(2), Element::int(3)];
        let actual: List = elements.into();
        let expected = ion_list![1, 2, 3];
        assert_eq!(actual, expected);
        Ok(())
    }

    #[test]
    fn list_from_iter() -> IonResult<()> {
        let elements = vec![Element::int(1), Element::int(2), Element::int(3)];
        let actual: List = elements.into_iter().collect();
        let expected = ion_list![1, 2, 3];
        assert_eq!(actual, expected);
        Ok(())
    }
}
