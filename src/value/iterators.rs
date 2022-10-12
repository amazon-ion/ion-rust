use crate::value::borrowed::ElementRef;
use crate::value::owned::Element;
use crate::{Symbol, SymbolRef};
// This macro defines a new iterator type for a given `Iterator => Item` type name pair.
//
// The implementation produced can be used to iterate over any `Vec<Item>` or `&[Item]`.
macro_rules! create_new_slice_iterator_type {
    ($($iterator_name:ident => $item_name:ty),*) => ($(
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

// Like the `create_new_slice_iterator_type` macro defined above, but works for Ref types that have
// an additional lifetime.
macro_rules! create_new_ref_slice_iterator_type {
    ($($iterator_name:ident => $item_name:ident),*) => ($(
        // Define a new type called '$iterator_name' that's a thin wrapper around a slice iterator.
        // We wrap the slice iterator in an `Option` so we can provide the functionality of an empty
        // iterator without requiring that an empty Vec or slice be provided. This sidesteps some
        // hairy lifetime issues.
        pub struct $iterator_name<'iter, 'data: 'iter> {
            values: Option<std::slice::Iter<'iter, $item_name<'data> >>
        }

        impl<'iter, 'data: 'iter> $iterator_name<'iter, 'data> {
            // Define a constructor that takes a slice of `Item`
            pub(crate) fn new(data: &'iter [$item_name<'data>]) -> $iterator_name<'iter, 'data> {
                $iterator_name {
                    values: Some(data.iter()),
                }
            }

            // Define a constructor that takes no parameters and returns an empty iterator
            pub(crate) fn empty() -> $iterator_name<'static, 'static> {
                $iterator_name { values: None }
            }
        }

        // Implement the Iterator trait for our new type
        impl<'iter, 'data: 'iter> Iterator for $iterator_name<'iter, 'data> {
            type Item = &'iter $item_name<'data>;

            fn next(&mut self) -> Option<Self::Item> {
                self.values.as_mut().and_then(|iter| iter.next())
            }
        }
    )*)
}

create_new_ref_slice_iterator_type!(
    // Used for iterating over an ElementRef's annotations
    SymbolRefIterator => SymbolRef,
    // Used for iterating over a SequenceRef's ElementRefs
    ElementRefIterator => ElementRef
);

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

/// Iterates over the (field name, field value) ref pairs in a StructRef.
pub struct FieldRefIterator<'iter, 'data> {
    values: Option<std::slice::Iter<'iter, (SymbolRef<'data>, ElementRef<'data>)>>,
}

impl<'iter, 'data> FieldRefIterator<'iter, 'data> {
    pub(crate) fn new(data: &'iter [(SymbolRef<'data>, ElementRef<'data>)]) -> Self {
        FieldRefIterator {
            values: Some(data.iter()),
        }
    }

    pub(crate) fn empty() -> FieldRefIterator<'static, 'static> {
        FieldRefIterator { values: None }
    }
}

impl<'iter, 'data> Iterator for FieldRefIterator<'iter, 'data> {
    type Item = (&'iter SymbolRef<'data>, &'iter ElementRef<'data>);

    fn next(&mut self) -> Option<Self::Item> {
        self.values
            .as_mut()
            // Get the next &(name, value) and convert it to (&name, &value)
            .and_then(|iter| iter.next().map(|field| (&field.0, &field.1)))
    }
}

/// Iterates over the value refs associated with a given field name in a StructRef.
pub struct FieldValueRefsIterator<'iter, 'data> {
    pub(super) current: usize,
    pub(super) indexes: Option<&'iter IndexVec>,
    pub(super) fields: &'iter Vec<(SymbolRef<'data>, ElementRef<'data>)>,
}

impl<'iter, 'data> Iterator for FieldValueRefsIterator<'iter, 'data> {
    type Item = &'iter ElementRef<'data>;

    fn next(&mut self) -> Option<Self::Item> {
        self.indexes
            .and_then(|i| i.get(self.current))
            .and_then(|i| {
                self.current += 1;
                self.fields.get(*i)
            })
            .map(|(_name, value)| value)
    }
}
