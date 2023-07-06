use crate::element::builders::SequenceBuilder;
use crate::element::iterators::SequenceIterator;
use crate::element::Element;
use crate::ion_data::{IonEq, IonOrd};
use std::cmp::Ordering;

/// An iterable, addressable series of Ion [`Element`]s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sequence {
    elements: Vec<Element>,
}

impl Sequence {
    pub fn new<E: Into<Element>, I: IntoIterator<Item = E>>(elements: I) -> Sequence {
        let elements = elements.into_iter().map(|e| e.into()).collect();
        Sequence { elements }
    }

    pub fn builder() -> SequenceBuilder {
        SequenceBuilder::new()
    }

    pub fn clone_builder(&self) -> SequenceBuilder {
        SequenceBuilder::with_initial_elements(&self.elements)
    }

    pub fn elements(&self) -> SequenceIterator<'_> {
        SequenceIterator::new(&self.elements)
    }

    pub fn get(&self, index: usize) -> Option<&Element> {
        self.elements.get(index)
    }

    pub fn len(&self) -> usize {
        self.elements.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> SequenceIterator<'_> {
        self.elements()
    }
}

impl AsRef<Sequence> for Sequence {
    fn as_ref(&self) -> &Sequence {
        self
    }
}

// This is more efficient than Sequence::new(), which will iterate over and convert each value to
// an Element for better ergonomics.
impl From<Vec<Element>> for Sequence {
    fn from(elements: Vec<Element>) -> Self {
        Sequence { elements }
    }
}

impl<'a> IntoIterator for &'a Sequence {
    type Item = &'a Element;
    // TODO: Change once `impl Trait` type aliases are stable
    // type IntoIter = impl Iterator<Item = &'a Element>;
    type IntoIter = SequenceIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements()
    }
}

// TODO: This currently clones elements. We should change `Sequence` to wrap a VecDeque so we can
//       pop from the front.
impl IntoIterator for Sequence {
    type Item = Element;
    // TODO: Change once `impl Trait` type aliases are stable
    // type IntoIter = impl Iterator<Item = &'a Element>;
    type IntoIter = OwnedSequenceIterator;

    fn into_iter(self) -> Self::IntoIter {
        OwnedSequenceIterator {
            current: 0,
            sequence: self,
        }
    }
}

impl FromIterator<Element> for Sequence {
    fn from_iter<T: IntoIterator<Item = Element>>(iter: T) -> Self {
        Vec::from_iter(iter.into_iter()).into()
    }
}

impl IonEq for Sequence {
    fn ion_eq(&self, other: &Self) -> bool {
        self.elements.ion_eq(&other.elements)
    }
}

impl IonOrd for Sequence {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.elements.ion_cmp(&other.elements)
    }
}

pub struct OwnedSequenceIterator {
    current: usize,
    sequence: Sequence,
}

impl Iterator for OwnedSequenceIterator {
    type Item = Element;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(element) = self.sequence.get(self.current) {
            self.current += 1;
            Some(element.clone())
        } else {
            None
        }
    }
}
