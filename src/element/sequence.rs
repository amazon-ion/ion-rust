use crate::element::iterators::ElementsIterator;
use crate::element::{Element, List, SExp};
use crate::ion_eq::IonEq;

/// Behavior that is common to both [SExp] and [Struct].
pub trait IonSequence {
    fn elements(&self) -> ElementsIterator<'_>;
    fn get(&self, index: usize) -> Option<&Element>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl IonSequence for List {
    fn elements(&self) -> ElementsIterator<'_> {
        ElementsIterator::new(&self.children)
    }

    fn get(&self, index: usize) -> Option<&Element> {
        self.children.get(index)
    }

    fn len(&self) -> usize {
        self.children.len()
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<S: IonSequence> IonEq for S {
    fn ion_eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for (item1, item2) in self.elements().zip(other.elements()) {
            if !item1.ion_eq(item2) {
                return false;
            }
        }
        true
    }
}

impl IonSequence for SExp {
    fn elements(&self) -> ElementsIterator<'_> {
        ElementsIterator::new(&self.children)
    }

    fn get(&self, index: usize) -> Option<&Element> {
        self.children.get(index)
    }

    fn len(&self) -> usize {
        self.children.len()
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl IonEq for Vec<Element> {
    fn ion_eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for (v1, v2) in self.iter().zip(other.iter()) {
            if !v1.ion_eq(v2) {
                return false;
            }
        }
        true
    }
}
