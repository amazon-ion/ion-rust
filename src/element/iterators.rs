use crate::element::Element;
use crate::Symbol;
use smallvec::SmallVec;
// This macro defines a new iterator type for a given `Iterator => Item` type name pair.
//
// The implementation produced can be used to iterate over any `Vec<Item>` or `&[Item]`.
macro_rules! create_new_slice_iterator_type {
    ($($iterator_name:ident => $item_name:ty),+) => ($(
        // Define a new type called '$iterator_name' that's a thin wrapper around a slice iterator.
        // We wrap the slice iterator in an `Option` so we can provide the functionality of an empty
        // iterator without requiring that an empty Vec or slice be provided. This sidesteps some
        // hairy lifetime issues.
        pub struct $iterator_name<'a> {
            values: Option<std::slice::Iter<'a, $item_name>>
        }

        impl<'a> $iterator_name<'a> {
            // Define a constructor that takes a slice of `Item`
            pub(crate) fn new(data: &'a [$item_name]) -> Self {
                $iterator_name {
                    values: Some(data.iter()),
                }
            }

            // Define a constructor that takes no parameters and returns an empty iterator
            pub(crate) fn empty() -> $iterator_name<'static> {
                $iterator_name { values: None }
            }
        }

        // Implement the Iterator trait for our new type
        impl<'a> Iterator for $iterator_name<'a> {
            type Item = &'a $item_name;

            fn next(&mut self) -> Option<Self::Item> {
                self.values.as_mut().and_then(|iter| iter.next())
            }
        }
    )*)
}
create_new_slice_iterator_type!(
    // Used for iterating over an Element's annotations
    SymbolsIterator => Symbol,
    // Used for iterating over a Sequence's Elements
    ElementsIterator => Element
);

/// Consuming iterator for [`Annotations`](crate::element::Annotations).
#[derive(Debug, Clone)]
pub struct AnnotationsIntoIter {
    into_iter: std::vec::IntoIter<Symbol>,
}

impl AnnotationsIntoIter {
    pub(crate) fn new(into_iter: std::vec::IntoIter<Symbol>) -> Self {
        Self { into_iter }
    }
}

impl Iterator for AnnotationsIntoIter {
    type Item = Symbol;

    fn next(&mut self) -> Option<Self::Item> {
        self.into_iter.next()
    }
}

// A convenient type alias for a vector capable of storing a single `usize` inline
// without heap allocation. This type should not be used in public interfaces directly.
pub(crate) type IndexVec = SmallVec<[usize; 1]>;

/// Iterates over the (field name, field value) pairs in a Struct.
pub struct FieldIterator<'a> {
    values: Option<std::slice::Iter<'a, (Symbol, Element)>>,
}

impl<'a> FieldIterator<'a> {
    pub(crate) fn new(data: &'a [(Symbol, Element)]) -> Self {
        FieldIterator {
            values: Some(data.iter()),
        }
    }

    pub(crate) fn empty() -> FieldIterator<'static> {
        FieldIterator { values: None }
    }
}

impl<'a> Iterator for FieldIterator<'a> {
    type Item = (&'a Symbol, &'a Element);

    fn next(&mut self) -> Option<Self::Item> {
        self.values
            .as_mut()
            // Get the next &(name, value) and convert it to (&name, &value)
            .and_then(|iter| iter.next().map(|field| (&field.0, &field.1)))
    }
}

/// Iterates over the values associated with a given field name in a Struct.
pub struct FieldValuesIterator<'a> {
    pub(super) current: usize,
    pub(super) indexes: Option<&'a IndexVec>,
    pub(super) by_index: &'a Vec<(Symbol, Element)>,
}

impl<'a> Iterator for FieldValuesIterator<'a> {
    type Item = &'a Element;

    fn next(&mut self) -> Option<Self::Item> {
        self.indexes
            .and_then(|i| i.get(self.current))
            .and_then(|i| {
                self.current += 1;
                self.by_index.get(*i)
            })
            .map(|(_name, value)| value)
    }
}
