use crate::element::builders::SequenceBuilder;
use crate::element::iterators::ElementsIterator;
use crate::element::{Element, Sequence};
use crate::ion_data::IonEq;
use crate::text::text_formatter::IonValueFormatter;
use delegate::delegate;
use std::fmt::{Display, Formatter};

/// An in-memory representation of an Ion s-expression
/// ```
/// use ion_rs::element::{Element, List};
/// use ion_rs::ion_sexp;
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// let sexp = ion_sexp!(1 2 3);
/// assert_eq!(sexp.len(), 3);
/// assert_eq!(sexp.get(1), Some(&Element::integer(2)));
/// # Ok(())
/// # }
/// ```
/// To build a `SExp` incrementally, see [SequenceBuilder].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SExp(pub Sequence);

impl SExp {
    pub(crate) fn new(elements: impl Into<Sequence>) -> Self {
        SExp(elements.into())
    }
}

impl SExp {
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

impl IonEq for SExp {
    fn ion_eq(&self, other: &Self) -> bool {
        // The inner `Sequence` of both Lists are IonEq
        self.0.ion_eq(&other.0)
    }
}

impl AsRef<Sequence> for SExp {
    fn as_ref(&self) -> &Sequence {
        &self.0
    }
}

// Allows `for element in &sexp {...}` syntax
impl<'a> IntoIterator for &'a SExp {
    type Item = &'a Element;
    type IntoIter = ElementsIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements()
    }
}

impl Display for SExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = IonValueFormatter { output: f };
        ivf.format_sexp(self).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl From<Sequence> for SExp {
    fn from(sequence: Sequence) -> Self {
        SExp(sequence)
    }
}

impl From<SExp> for Sequence {
    fn from(value: SExp) -> Self {
        value.0
    }
}

#[cfg(test)]
mod tests {
    use crate::ion_sexp;
    use crate::types::IntAccess;

    #[test]
    fn for_element_in_sexp() {
        // Simple example to exercise SExp's implementation of IntoIterator
        let sexp = ion_sexp!(1 2 3);
        let mut sum = 0;
        for element in &sexp {
            sum += element.as_i64().unwrap();
        }
        assert_eq!(sum, 6i64);
    }
}
