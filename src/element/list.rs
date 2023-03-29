use crate::element::builders::ListBuilder;
use crate::element::iterators::ElementsIterator;
use crate::element::{Element, IonSequence};
use crate::text::text_formatter::IonValueFormatter;
use std::fmt::{Display, Formatter};

/// An in-memory representation of an Ion list.
///
/// [`List`] implements [`IonSequence`], which defines most of its functionality.
/// ```
/// use ion_rs::element::{Element, IonSequence, List};
/// use ion_rs::ion_list;
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// let list = ion_list![1, 2, 3];
/// assert_eq!(list.len(), 3);
/// assert_eq!(list.get(1), Some(&Element::integer(2)));
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct List {
    pub(super) children: Vec<Element>,
}

impl List {
    pub(crate) fn new(children: Vec<Element>) -> Self {
        Self { children }
    }

    pub fn builder() -> ListBuilder {
        ListBuilder::new()
    }

    pub fn clone_builder(&self) -> ListBuilder {
        ListBuilder::with_initial_elements(&self.children)
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

#[cfg(test)]
mod tests {
    use crate::ion_list;
    use crate::types::integer::IntAccess;

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
