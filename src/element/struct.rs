use crate::element::builders::StructBuilder;
use crate::element::iterators::{FieldIterator, FieldValuesIterator, IndexVec};
use crate::element::Element;
use crate::ion_eq::IonEq;
use crate::symbol_ref::AsSymbolRef;
use crate::text::text_formatter::IonValueFormatter;
use crate::Symbol;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

// This collection is broken out into its own type to allow instances of it to be shared with Arc/Rc.
#[derive(Debug, Clone)]
struct Fields {
    // Key/value pairs in the order they were inserted
    by_index: Vec<(Symbol, Element)>,
    // Maps symbols to a list of indexes where values may be found in `by_index` above
    by_name: HashMap<Symbol, IndexVec>,
}

impl Fields {
    /// Gets all of the indexes that contain a value associated with the given field name.
    fn get_indexes<A: AsSymbolRef>(&self, field_name: A) -> Option<&IndexVec> {
        field_name
            .as_symbol_ref()
            .text()
            .map(|text| {
                // If the symbol has defined text, look it up by &str
                self.by_name.get(text)
            })
            .unwrap_or_else(|| {
                // Otherwise, construct a (cheap, stack-allocated) Symbol with unknown text...
                let symbol = Symbol::unknown_text();
                // ...and use the unknown text symbol to look up matching field values
                self.by_name.get(&symbol)
            })
    }

    /// Iterates over the values found at the specified indexes.
    fn get_values_at_indexes<'a>(&'a self, indexes: &'a IndexVec) -> FieldValuesIterator<'a> {
        FieldValuesIterator {
            current: 0,
            indexes: Some(indexes),
            by_index: &self.by_index,
        }
    }

    /// Gets the last value in the Struct that is associated with the specified field name.
    ///
    /// Note that the Ion data model views a struct as a bag of (name, value) pairs and does not
    /// have a notion of field ordering. In most use cases, field names are distinct and the last
    /// appearance of a field in the struct's serialized form will have been the _only_ appearance.
    /// If a field name appears more than once, this method makes the arbitrary decision to return
    /// the value associated with the last appearance. If your application uses structs that repeat
    /// field names, you are encouraged to use [`get_all`](Self::get_all) instead.
    fn get_last<A: AsSymbolRef>(&self, field_name: A) -> Option<&Element> {
        self.get_indexes(field_name)
            .and_then(|indexes| indexes.last())
            .and_then(|index| self.by_index.get(*index))
            .map(|(_name, value)| value)
    }

    /// Iterates over all of the values associated with the given field name.
    fn get_all<A: AsSymbolRef>(&self, field_name: A) -> FieldValuesIterator {
        let indexes = self.get_indexes(field_name);
        FieldValuesIterator {
            current: 0,
            indexes,
            by_index: &self.by_index,
        }
    }

    /// Iterates over all of the (field name, field value) pairs in the struct.
    fn iter(&self) -> impl Iterator<Item = &(Symbol, Element)> {
        self.by_index.iter()
    }
}

/// An in-memory representation of an Ion Struct
/// ```
/// use ion_rs::element::Element;
/// use ion_rs::ion_struct;
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// let struct_ = ion_struct! {
///   "foo": 1,
///   "bar": true,
///   "baz": "hello"
/// };
/// assert_eq!(struct_.len(), 3);
/// assert_eq!(struct_.get("baz"), Some(&Element::string("hello")));
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct Struct {
    fields: Fields,
}

impl Display for Struct {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = IonValueFormatter { output: f };
        ivf.format_struct(self).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl Struct {
    pub fn builder() -> StructBuilder {
        StructBuilder::new()
    }

    pub fn clone_builder(&self) -> StructBuilder {
        StructBuilder::with_initial_fields(&self.fields.by_index)
    }

    /// Returns an iterator over the field name/value pairs in this Struct.
    pub fn fields(&self) -> impl Iterator<Item = (&Symbol, &Element)> {
        self.fields
            .iter()
            // Here we convert from &(name, value) to (&name, &value).
            // The former makes a stronger assertion about how the data is being stored. We don't
            // want that to be a mandatory part of the public API.
            .map(|(name, element)| (name, element))
    }

    fn fields_eq(&self, other: &Self) -> bool {
        // For each field name in `self`, get the list of indexes that contain a value with that name.
        for (field_name, field_value_indexes) in &self.fields.by_name {
            let other_value_indexes = match other.fields.get_indexes(field_name) {
                Some(indexes) => indexes,
                // The other struct doesn't have a field with this name so they're not equal.
                None => return false,
            };

            if field_value_indexes.len() != other_value_indexes.len() {
                // The other struct has fields with the same name, but a different number of them.
                return false;
            }

            for field_value in self.fields.get_values_at_indexes(field_value_indexes) {
                if other
                    .fields
                    .get_values_at_indexes(other_value_indexes)
                    .all(|other_value| !field_value.ion_eq(other_value))
                {
                    // Couldn't find an equivalent field in the other struct
                    return false;
                }
            }
        }

        // If all of the above conditions hold, the two structs are equal.
        true
    }

    /// Returns the number of fields in this Struct.
    pub fn len(&self) -> usize {
        self.fields.by_index.len()
    }

    /// Returns `true` if this struct has zero fields.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> FieldIterator<'_> {
        FieldIterator::new(&self.fields.by_index)
    }

    pub fn get<A: AsSymbolRef>(&self, field_name: A) -> Option<&Element> {
        self.fields.get_last(field_name)
    }

    pub fn get_all<A: AsSymbolRef>(&self, field_name: A) -> FieldValuesIterator<'_> {
        self.fields.get_all(field_name)
    }
}

// Allows `for (name, value) in &my_struct {...}` syntax
impl<'a> IntoIterator for &'a Struct {
    type Item = (&'a Symbol, &'a Element);
    type IntoIter = FieldIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K, V> FromIterator<(K, V)> for Struct
where
    K: Into<Symbol>,
    V: Into<Element>,
{
    /// Returns an owned struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut by_index: Vec<(Symbol, Element)> = Vec::new();
        let mut by_name: HashMap<Symbol, IndexVec> = HashMap::new();
        for (field_name, field_value) in iter {
            let field_name = field_name.into();
            let field_value = field_value.into();

            by_name
                .entry(field_name.clone())
                .or_insert_with(IndexVec::new)
                .push(by_index.len());
            by_index.push((field_name, field_value));
        }

        let fields = Fields { by_index, by_name };
        Self { fields }
    }
}

impl PartialEq for Struct {
    fn eq(&self, other: &Self) -> bool {
        // check if both fields have same length
        self.len() == other.len()
            // we need to test equality in both directions for both fields
            // A good example for this is annotated vs not annotated values in struct
            //  { a:4, a:4 } vs. { a:4, a:a::4 } // returns true
            //  { a:4, a:a::4 } vs. { a:4, a:4 } // returns false
            && self.fields_eq(other) && other.fields_eq(self)
    }
}

impl Eq for Struct {}

#[cfg(test)]
mod tests {
    use crate::element::Element;
    use crate::ion_struct;

    #[test]
    fn for_field_in_struct() {
        // Simple example to exercise List's implementation of IntoIterator
        let s = ion_struct! { "foo": 1, "bar": 2, "baz": 3};
        let mut baz_value = None;
        for (name, value) in &s {
            if *name == "baz" {
                baz_value = Some(value);
            }
        }
        assert_eq!(baz_value, Some(&Element::integer(3)));
    }
}
