use crate::value::borrowed::ElementRef;
use crate::value::owned::Element;
use crate::{Symbol, SymbolRef};
// This macro defines a new iterator type (Rc static no good)
// TODO: explain
macro_rules! create_new_slice_iterator_type {
    ($($iterator_name:ident => $item_name:ty),*) => ($(
        // Define a new type called '$iterator_name' that's a thin wrapper around a slice iterator.
        pub struct $iterator_name<'a> {
            values: Option<std::slice::Iter<'a, $item_name>>
        }

        // Provide 'new' and 'empty' constructors for our new iterator type
        impl<'a> $iterator_name<'a> {
            pub(crate) fn new(data: &'a [$item_name]) -> Self {
                $iterator_name {
                    values: Some(data.iter()),
                }
            }

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
    // Owned
    SymbolsIterator => Symbol,
    ElementsIterator => Element,
    // TODO: this should be Item = (&Symbol, &Element), not Item = &(Symbol, Element)
    FieldsIterator => (Symbol, Element)
);

pub type FieldRef<'a> = (SymbolRef<'a>, ElementRef<'a>);

macro_rules! create_new_ref_slice_iterator_type {
    ($($iterator_name:ident => $item_name:ident),*) => ($(
        // Define a new type called '$iterator_name' that's a thin wrapper around a slice iterator.
        pub struct $iterator_name<'iter, 'data: 'iter> {
            values: Option<std::slice::Iter<'iter, $item_name<'data> >>
        }

        // Provide 'new' and 'empty' constructors for our new iterator type
        impl<'iter, 'data: 'iter> $iterator_name<'iter, 'data> {
            pub(crate) fn new(data: &'iter [$item_name<'data>]) -> $iterator_name<'iter, 'data> {
                $iterator_name {
                    values: Some(data.iter()),
                }
            }

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
    SymbolRefIterator => SymbolRef,
    ElementRefIterator => ElementRef,
    FieldRefIterator => FieldRef
);

pub struct StructFieldIterator<'a> {
    values: Option<std::slice::Iter<'a, (Symbol, Element)>>,
}

// Provide 'new' and 'empty' constructors for our new iterator type
impl<'a> StructFieldIterator<'a> {
    pub(crate) fn new(data: &'a [(Symbol, Element)]) -> Self {
        StructFieldIterator {
            values: Some(data.iter()),
        }
    }

    pub(crate) fn empty() -> StructFieldIterator<'static> {
        StructFieldIterator { values: None }
    }
}

// Implement the Iterator trait for our new type
impl<'a> Iterator for StructFieldIterator<'a> {
    type Item = (&'a Symbol, &'a Element);

    fn next(&mut self) -> Option<Self::Item> {
        self.values
            .as_mut()
            // Get the next &(name, value) and convert it to (&name, &value)
            .and_then(|iter| iter.next().map(|field| (&field.0, &field.1)))
    }
}
