use crate::element::builders::SequenceBuilder;
use crate::element::iterators::ElementsIterator;
use crate::element::{Element, Sequence};
use crate::ion_data::IonEq;
use crate::text::text_formatter::IonValueFormatter;
use delegate::delegate;
use std::fmt::{Display, Formatter};

/// An in-memory representation of an Ion list.
/// ```
/// use ion_rs::element::{Element, List};
/// use ion_rs::ion_list;
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// let list = ion_list![1, 2, 3];
/// assert_eq!(list.len(), 3);
/// assert_eq!(list.get(1), Some(&Element::integer(2)));
/// # Ok(())
/// # }
/// ```
/// To build a `List` incrementally, see [SequenceBuilder].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct List(pub Sequence);

impl List {
    pub(crate) fn new(elements: impl Into<Sequence>) -> Self {
        List(elements.into())
    }
}

impl List {
    delegate! {
        to self.0 {
            pub fn clone_builder(&self) -> SequenceBuilder;
            pub fn elements(&self) -> ElementsIterator<'_>;
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

impl AsRef<Sequence> for List {
    fn as_ref(&self) -> &Sequence {
        &self.0
    }
}

// Allows `for element in &list {...}` syntax
impl<'a> IntoIterator for &'a List {
    type Item = &'a Element;
    type IntoIter = ElementsIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements()
    }
}

impl Display for List {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = IonValueFormatter { output: f };
        ivf.format_list(self).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl From<Sequence> for List {
    fn from(sequence: Sequence) -> Self {
        List(sequence)
    }
}

impl From<List> for Sequence {
    fn from(value: List) -> Self {
        value.0
    }
}

#[cfg(test)]
mod tests {
    use crate::ion_list;
    use crate::types::IntAccess;

    #[test]
    fn for_element_in_list() {
        // Simple example to exercise List's implementation of IntoIterator
        let list = ion_list![1, 2, 3];
        let mut sum = 0;
        for element in &list {
            sum += element.as_i64().unwrap();
        }
        assert_eq!(sum, 6i64);
    }
}
