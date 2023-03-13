use crate::value::owned::{Element, List, SExp, Struct};
use crate::Symbol;

/// Constructs [List] values incrementally.
///
/// ```
/// use ion_rs::ion;
/// use ion_rs::value::owned::Element;
/// let actual: Element = Element::list_builder()
///     .push(1)
///     .push(true)
///     .push("foo")
///     .build();
/// let expected = ion!(r#"[1, true, "foo"]"#);
/// assert_eq!(actual, expected);
/// ```
pub struct ListBuilder {
    values: Vec<Element>,
}

impl ListBuilder {
    /// Crate visible; users should call [`List::builder()`] or [`Element::list_builder()`] instead.
    pub(crate) fn new() -> Self {
        Self { values: Vec::new() }
    }

    /// Helper method for [`List::clone_builder()`].
    pub(crate) fn with_initial_elements(elements: &[Element]) -> Self {
        let mut new_elements = Vec::with_capacity(elements.len());
        new_elements.extend_from_slice(elements);
        Self {
            values: new_elements,
        }
    }

    /// Adds the provided element to the end of the [`List`] being constructed.
    pub fn push<E: Into<Element>>(mut self, element: E) -> Self {
        self.values.push(element.into());
        self
    }

    /// Removes the element at the specified position from the [`List`] being constructed.
    /// If the index is out of bounds, this method will panic.
    pub fn remove(mut self, index: usize) -> Self {
        // This has O(n) behavior; the removals could be
        // buffered until the build() if needed.
        self.values.remove(index);
        self
    }

    /// Builds a [`List`] with the previously specified elements.
    pub fn build_list(self) -> List {
        List::new(self.values)
    }

    /// Builds a list [`Element`] with the previously specified child elements.
    pub fn build(self) -> Element {
        self.build_list().into()
    }
}

/// Constructs [SExp] values incrementally.
///
/// ```
/// use ion_rs::ion;
/// use ion_rs::value::owned::Element;
/// let actual: Element = Element::sexp_builder()
///     .push(1)
///     .push(true)
///     .push("foo")
///     .build();
/// let expected = ion!(r#"(1 true "foo")"#);
/// assert_eq!(actual, expected);
/// ```
pub struct SExpBuilder {
    values: Vec<Element>,
}

impl SExpBuilder {
    /// Crate visible; users should call [`SExp::builder()`] or [`Element::sexp_builder()`] instead.
    pub(crate) fn new() -> Self {
        Self { values: Vec::new() }
    }

    /// Helper method for [`SExp::clone_builder()`].
    pub(crate) fn with_initial_elements(elements: &[Element]) -> Self {
        let mut new_elements = Vec::with_capacity(elements.len());
        new_elements.extend_from_slice(elements);
        Self {
            values: new_elements,
        }
    }

    /// Adds the provided element to the end of the [`SExp`] being constructed.
    pub fn push<E: Into<Element>>(mut self, element: E) -> Self {
        self.values.push(element.into());
        self
    }

    /// Removes the element at the specified position from the [`SExp`] being constructed.
    /// If the index is out of bounds, this method will panic.
    pub fn remove(mut self, index: usize) -> Self {
        // This has O(n) behavior; the removals could be
        // buffered until the build() if needed.
        self.values.remove(index);
        self
    }

    /// Builds a [`SExp`] with the previously specified elements.
    pub fn build_sexp(self) -> SExp {
        SExp::new(self.values)
    }

    /// Builds an s-expression [`Element`] with the previously specified child elements.
    pub fn build(self) -> Element {
        self.build_sexp().into()
    }
}

/// Constructs [Struct] values incrementally.
///
/// ```
/// use ion_rs::ion;
/// use ion_rs::value::owned::Element;
/// let actual: Element = Element::struct_builder()
///     .with_field("a", 1)
///     .with_field("b", true)
///     .with_field("c", "foo")
///     .build();
/// let expected = ion!(r#"{a: 1, b: true, c: "foo"}"#);
/// assert_eq!(actual, expected);
/// ```
pub struct StructBuilder {
    fields: Vec<(Symbol, Element)>,
}

impl StructBuilder {
    /// Crate visible; users should call [`Struct::builder()`] or [`Element::struct_builder`] instead.
    pub(crate) fn new() -> Self {
        StructBuilder { fields: Vec::new() }
    }

    /// Helper method for [`Struct::clone_builder()`].
    pub(crate) fn with_initial_fields(elements: &[(Symbol, Element)]) -> Self {
        let mut new_elements = Vec::with_capacity(elements.len());
        new_elements.extend_from_slice(elements);
        Self {
            fields: new_elements,
        }
    }

    /// Adds the provided `(name, value)` pair to the [`Struct`] being constructed.
    pub fn with_field<S: Into<Symbol>, E: Into<Element>>(
        mut self,
        field_name: S,
        field_value: E,
    ) -> Self {
        self.fields.push((field_name.into(), field_value.into()));
        self
    }

    /// Removes the first field with the specified name from the [`Struct`] being constructed.
    pub fn remove_field<A: AsRef<str>>(mut self, field_to_remove: A) -> Self {
        // TODO: This removes the first field with a matching name.
        //       Do we need other versions for remove_all or remove_last?
        // TODO: This has O(n) behavior; it could be optimized.
        let field_to_remove: &str = field_to_remove.as_ref();
        let _ = self
            .fields
            .iter()
            .position(|(name, _)| name == &field_to_remove)
            .map(|index| self.fields.remove(index));
        self
    }

    /// Builds a [`Struct`] with the previously specified fields.
    pub fn build_struct(self) -> Struct {
        Struct::from_iter(self.fields.into_iter())
    }

    /// Builds a struct [`Element`] with the previously specified fields.
    pub fn build(self) -> Element {
        self.build_struct().into()
    }
}

// These `From` implementations allow a builder to be passed into any method that takes an
// `Into<Element>`, allowing you to avoid having to explicitly call `build()` on them when
// the intent is clear.

impl From<ListBuilder> for Element {
    fn from(list_builder: ListBuilder) -> Self {
        list_builder.build()
    }
}

impl From<SExpBuilder> for Element {
    fn from(s_expr_builder: SExpBuilder) -> Self {
        s_expr_builder.build()
    }
}

impl From<StructBuilder> for Element {
    fn from(struct_builder: StructBuilder) -> Self {
        struct_builder.build()
    }
}

/// Constructs a list [`Element`] with the specified child values.
///
/// ```
/// use ion_rs::{ion, ion_list};
/// // Construct a list Element from Rust values
/// let actual = ion_list!["foo", 7, false, ion_list![1.5f64, -8.25f64]];
/// // Construct an Element from serialized Ion data
/// let expected = ion!(r#"["foo", 7, false, [1.5e0, -8.25e0]]"#);
/// // Compare the two Elements
/// assert_eq!(expected, actual);
/// ```
#[macro_export]
macro_rules! ion_list {
    ($($element:expr),*) => {{
        use $crate::value::owned::List;
        List::builder()$(.push($element))*.build()
    }};
}

/// Constructs an s-expression [`Element`] with the specified child values.
///
/// Each child value can be any Rust value that implements `Into<Element>`.
///
/// ```
/// use ion_rs::{ion, ion_sexp};
/// // Construct an s-expression Element from Rust values
/// let actual = ion_sexp!("foo" 7 false ion_sexp!(1.5f64 8.25f64));
/// // Construct an Element from serialized Ion data
/// let expected = ion!(r#"("foo" 7 false (1.5e0 8.25e0))"#);
/// // Compare the two Elements
/// println!("{} == {}", expected, actual);
/// assert_eq!(expected, actual);
/// ```
#[macro_export]
macro_rules! ion_sexp {
    ($($element:expr)*) => {{
        use $crate::value::owned::SExp;
        SExp::builder()$(.push($element))*.build()
    }};
}

/// Constructs an struct [`Element`] with the specified fields.
///
/// For each field, the name must implement `Into<Symbol>` and the value must implement
/// `Into<Element>`.
///
/// ```
/// use ion_rs::{ion, ion_struct};
/// let field_name_2 = "x";
/// // Construct an s-expression Element from Rust values
/// let actual = ion_struct!{
///     "w": "foo",
/// //   ^--- Quoted strings are field name literals
/// //   v--- Unquoted field names are interpreted as variables
///     field_name_2: 7,
///     "y": false,
///     "z": ion_struct!{ "a": 1.5f64, "b": -8.25f64}
/// };
/// // Construct an Element from serialized Ion data
/// let expected = ion!(r#"{w: "foo", x: 7, y: false, z: {a: 1.5e0, b: -8.25e0}}"#);
/// // Compare the two Elements
/// println!("{} == {}", expected, actual);
/// assert_eq!(expected, actual);
/// ```
#[macro_export]
macro_rules! ion_struct {
    ($($field_name:tt : $element:expr),*) => {{
        use $crate::value::owned::Struct;
        Struct::builder()$(.with_field($field_name, $element))*.build()
    }};
}

/// Reads a single Ion [`Element`] from the provided data source. If the data source has invalid
/// data or does not contain at least one Ion value, this macro will panic.
///
/// The data source can be any value which implements `AsRef<[u8]>`.
/// ```
/// use ion_rs::ion;
/// use ion_rs::value::owned::Element;
/// let element_from_source = ion!(r#"7"#);
/// let element_from_value = Element::from(7i64);
/// assert_eq!(element_from_source, element_from_value);
/// ```
#[macro_export]
macro_rules! ion {
    ($source:expr) => {{
        use $crate::value::native_reader::NativeElementReader;
        use $crate::value::reader::ElementReader;
        let bytes: &[u8] = $source.as_ref();
        NativeElementReader
            .iterate_over(bytes)
            .unwrap()
            .next()
            .expect("Data passed to the ion! macro did not contain any values.")
            .expect("Invalid Ion data passed to the `ion!` macro.")
    }};
}

pub use ion_list;
pub use ion_sexp;
pub use ion_struct;

#[cfg(test)]
mod tests {
    use crate::value::builders::{ListBuilder, SExpBuilder, StructBuilder};
    use crate::value::owned::Element;
    use crate::Symbol;
    use crate::{ion, ion_list, ion_sexp, ion_struct};

    #[test]
    fn build_list() {
        let actual: Element = ListBuilder::new()
            .push(1)
            .push(true)
            .push("foo")
            .push(Symbol::owned("bar"))
            .build();
        let expected = ion!(r#"[1, true, "foo", bar]"#);
        assert_eq!(actual, expected);
    }

    #[test]
    fn build_list_with_macro() {
        let actual: Element = ion_list![1, true, "foo", Symbol::owned("bar")];
        let expected = ion!(r#"[1, true, "foo", bar]"#);
        assert_eq!(actual, expected);
    }

    #[test]
    fn build_list_remove() {
        let actual: Element = ListBuilder::new()
            .push(1)
            .push(true)
            .push("foo")
            .remove(1)
            .remove(1)
            .push(Symbol::owned("bar"))
            .build();
        let expected = ion!("[1, bar]");
        assert_eq!(actual, expected);
    }

    #[test]
    fn list_clone_builder() {
        let original_list = ion_list![1, true, "foo", Symbol::owned("bar")];
        let new_list = original_list
            .as_list()
            .unwrap()
            .clone_builder()
            .remove(1)
            .push(88)
            .build();
        let expected_list = ion!(r#"[1, "foo", bar, 88]"#);
        assert_eq!(new_list, expected_list);
    }

    #[test]
    fn build_sexp() {
        let actual: Element = SExpBuilder::new()
            .push(1)
            .push(true)
            .push("foo")
            .push(Symbol::owned("bar"))
            .build();
        let expected = ion!(r#"(1 true "foo" bar)"#);
        assert_eq!(actual, expected);
    }

    #[test]
    fn sexp_clone_builder() {
        let original_sexp = ion_sexp!(1 true "foo" Symbol::owned("bar"));
        let new_sexp = original_sexp
            .as_sexp()
            .unwrap()
            .clone_builder()
            .remove(1)
            .push(88)
            .build();
        let expected_sexp = ion!(r#"(1 "foo" bar 88)"#);
        assert_eq!(new_sexp, expected_sexp);
    }

    #[test]
    fn build_sexp_remove() {
        let actual: Element = SExpBuilder::new()
            .push(1)
            .push(true)
            .push("foo")
            .remove(1)
            .remove(1)
            .push(Symbol::owned("bar"))
            .build();
        let expected = ion!("(1 bar)");
        assert_eq!(actual, expected);
    }

    #[test]
    fn build_sexp_with_macro() {
        let actual: Element = ion_sexp!(1 true "foo" Symbol::owned("bar"));
        let expected = ion!(r#"(1 true "foo" bar)"#);
        assert_eq!(actual, expected);
    }

    #[test]
    fn build_struct() {
        let actual: Element = StructBuilder::new()
            .with_field("a", 1)
            .with_field("b", true)
            .with_field("c", "foo")
            .with_field("d", Symbol::owned("bar"))
            .build();
        let expected = ion!(r#"{a: 1, b: true, c: "foo", d: bar}"#);
        assert_eq!(actual, expected);
    }

    #[test]
    fn build_struct_with_macro() {
        let actual: Element = ion_struct! {
            "a": 1,
            "b": true,
            "c": "foo",
            "d": Symbol::owned("bar")
        };
        let expected = ion!(r#"{a: 1, b: true, c: "foo", d: bar}"#);
        assert_eq!(actual, expected);
    }

    #[test]
    fn build_struct_without() {
        let actual: Element = StructBuilder::new()
            .with_field("a", 1)
            .with_field("b", true)
            .with_field("c", "foo")
            .with_field("d", Symbol::owned("bar"))
            .with_field("d", Symbol::owned("baz"))
            // Removes the only 'b' field
            .remove_field("b")
            // Removes the first 'd' field, leaves the second
            .remove_field("d")
            .build();
        let expected = ion!(r#"{a: 1, c: "foo", d: baz}"#);
        assert_eq!(actual, expected);
        assert_eq!(actual, expected);
    }
}
