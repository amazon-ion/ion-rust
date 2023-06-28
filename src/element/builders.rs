use crate::element::{Element, Sequence, Struct};
use crate::Symbol;

/// Constructs [Sequence], [List], and [SExp] values incrementally.
///
/// Building a [Sequence]:
/// ```
/// use ion_rs::element::{Element, Sequence};
/// let actual: Sequence = Sequence::builder().push(1).push(true).push("foo").build();
/// let expected: Sequence = Sequence::new([
///     Element::integer(1),
///     Element::boolean(true),
///     Element::string("foo"),
/// ]);
/// assert_eq!(actual, expected);
/// ```
/// Building a [List]:
/// ```
/// use ion_rs::element::{Element, List, Sequence};
/// let actual: List = Sequence::builder()
///     .push(1)
///     .push(true)
///     .push("foo")
///     .build_list();
/// let expected: List = List(Sequence::new([
///     Element::integer(1),
///     Element::boolean(true),
///     Element::string("foo"),
/// ]));
/// assert_eq!(actual, expected);
/// ```
/// Building a [SExp]:
/// ```
/// use ion_rs::element::{Element, SExp, Sequence};
/// let actual: SExp = Sequence::builder()
///     .push(1)
///     .push(true)
///     .push("foo")
///     .build_sexp();
/// let expected: SExp = SExp(Sequence::new([
///     Element::integer(1),
///     Element::boolean(true),
///     Element::string("foo"),
/// ]));
/// assert_eq!(actual, expected);
/// ```
pub struct SequenceBuilder {
    values: Vec<Element>,
}

impl SequenceBuilder {
    /// Crate visible; users should call [`Sequence::builder()`] instead.
    pub(crate) fn new() -> Self {
        Self { values: Vec::new() }
    }

    /// Helper method for [`Sequence::clone_builder()`].
    pub(crate) fn with_initial_elements(elements: &[Element]) -> Self {
        let mut new_elements = Vec::with_capacity(elements.len());
        new_elements.extend_from_slice(elements);
        Self {
            values: new_elements,
        }
    }

    /// Adds the provided element to the end of the [`Sequence`] being constructed.
    pub fn push<E: Into<Element>>(mut self, element: E) -> Self {
        self.values.push(element.into());
        self
    }

    /// Removes the element at the specified position from the [`Sequence`] being constructed.
    /// If the index is out of bounds, this method will panic.
    pub fn remove(mut self, index: usize) -> Self {
        // This has O(n) behavior; the removals could be
        // buffered until the build() if needed.
        self.values.remove(index);
        self
    }

    /// Builds a [`Sequence`] with the previously specified elements.
    pub fn build(self) -> Sequence {
        self.values.into()
    }

    /// Builds a [`List`] with the previously specified elements.
    pub fn build_list(self) -> List {
        List(self.build())
    }

    /// Builds a [`SExp`] with the previously specified elements.
    pub fn build_sexp(self) -> SExp {
        SExp(self.build())
    }
}

/// Constructs [Struct] values incrementally.
///
/// ```
/// use ion_rs::element::Element;
/// use ion_rs::ion_struct;
/// let actual: Element = ion_struct! {
///     "a": 1,
///     "b": true,
///     "c": "foo"
/// }
/// .into();
/// let expected = Element::read_one(r#"{a: 1, b: true, c: "foo"}"#).unwrap();
/// assert_eq!(actual, expected);
/// ```
///
/// ```
/// use ion_rs::element::{Element, Struct};
/// use ion_rs::ion_struct;
/// let base_struct: Struct = ion_struct! {
///     "foo": 1,
///     "bar": 2,
///     "baz": 3
/// };
///
/// let modified_struct: Element = base_struct
///     .clone_builder()
///     .remove_field("bar")
///     .with_field("quux", 4)
///     .build()
///     .into(); // Convert from `Struct` to `Element`
///
/// let expected = Element::read_one(r#"{foo: 1, baz: 3, quux: 4}"#).unwrap();
/// assert_eq!(expected, modified_struct);
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

    /// Adds all of the provided `(name, value)` pairs to the [`Struct`] being constructed.
    ///
    /// ```
    /// use ion_rs::element::Element;
    /// use ion_rs::ion_struct;
    ///
    /// let struct1 = ion_struct! {
    ///     "foo": 1,
    ///     "bar": 2,
    ///     "baz": 3
    /// };
    ///
    /// let struct2 = ion_struct! {
    ///     "a": 4,
    ///     "b": 5,
    ///     "c": 6
    /// };
    ///
    /// let merged = struct1
    ///     .clone_builder()
    ///     .with_fields(struct2.fields())
    ///     .build();
    ///
    /// let expected = Element::read_one("{foo: 1, bar: 2, baz: 3, a: 4, b: 5, c: 6}").unwrap();
    /// ```
    pub fn with_fields<S, E, I>(mut self, fields: I) -> Self
    where
        S: Into<Symbol>,
        E: Into<Element>,
        I: IntoIterator<Item = (S, E)>,
    {
        for (name, value) in fields.into_iter() {
            let name: Symbol = name.into();
            let value: Element = value.into();
            self.fields.push((name, value));
        }
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
    pub fn build(self) -> Struct {
        Struct::from_iter(self.fields.into_iter())
    }
}

/// Constructs a list [`Element`] with the specified child values.
///
/// ```
/// use ion_rs::element::Element;
/// use ion_rs::ion_list;
/// // Construct a list Element from Rust values
/// let actual: Element = ion_list!["foo", 7, false, ion_list![1.5f64, -8.25f64]].into();
/// // Construct an Element from serialized Ion data
/// let expected = Element::read_one(r#"["foo", 7, false, [1.5e0, -8.25e0]]"#).unwrap();
/// // Compare the two Elements
/// assert_eq!(expected, actual);
/// ```
///
/// Child values can be anything that implements `Into<Element>`, which
/// includes existing [Element] values.
///
/// ```
/// // Construct a list Element from existing Elements
/// use ion_rs::element::{Element, IntoAnnotatedElement};
/// use ion_rs::ion_list;
///
/// let string_element: Element = "foo".into();
/// let bool_element: Element = true.into();
///
/// let actual: Element = ion_list![
///     string_element,
///     bool_element,
///     10i64.with_annotations(["bar"]), // .with_annotations() constructs an Element
///     Element::clob("hello"),
///     Element::symbol("world")
/// ]
/// .into();
/// // Construct an Element from serialized Ion data
/// let expected = Element::read_one(r#"["foo", true, bar::10, {{"hello"}}, world]"#).unwrap();
/// // Compare the two Elements
/// assert_eq!(expected, actual);
/// ```
#[macro_export]
macro_rules! ion_list {
    ($($element:expr),* $(,)?) => {{
        use $crate::element::Sequence;
        Sequence::builder()$(.push($element))*.build_list()
    }};
}

/// Constructs an s-expression [`Element`] with the specified child values.
///
/// ```
/// use ion_rs::ion_sexp;
/// use ion_rs::element::Element;
/// // Construct an s-expression Element from Rust values
/// let actual: Element = ion_sexp!("foo" 7 false ion_sexp!(1.5f64 8.25f64)).into();
/// // Construct an Element from serialized Ion data
/// let expected = Element::read_one(r#"("foo" 7 false (1.5e0 8.25e0))"#).unwrap();
/// // Compare the two Elements
/// assert_eq!(expected, actual);
/// ```
///
/// Child values can be anything that implements `Into<Element>`, which
/// includes existing [Element] values.
///
/// ```
/// // Construct a s-expression Element from existing Elements
/// use ion_rs::ion_sexp;
/// use ion_rs::element::{Element, IntoAnnotatedElement};
///
/// let string_element: Element = "foo".into();
/// let bool_element: Element = true.into();
///
/// let actual: Element = ion_sexp!(
///     string_element
///     bool_element
///     10i64.with_annotations(["bar"]) // .with_annotations() constructs an Element
///     Element::clob("hello")
///     Element::symbol("world")
/// ).into();
/// // Construct an Element from serialized Ion data
/// let expected = Element::read_one(r#"("foo" true bar::10 {{"hello"}} world)"#).unwrap();
/// // Compare the two Elements
/// assert_eq!(expected, actual);
/// ```
#[macro_export]
macro_rules! ion_sexp {
    ($($element:expr)*) => {{
        use $crate::element::Sequence;
        Sequence::builder()$(.push($element))*.build_sexp()
    }};
}

/// Constructs an struct [`Element`] with the specified fields.
///
/// For each field, the name must implement `Into<Symbol>` and the value must implement
/// `Into<Element>`.
///
/// ```
/// use ion_rs::element::Element;
/// use ion_rs::{ion_struct, IonType};
/// let field_name_2 = "x";
/// let prefix = "abc";
/// let suffix = "def";
/// // Construct an s-expression Element from Rust values
/// let actual = ion_struct! {
///     "w": "foo",
/// //   ^--- Quoted strings are field name literals
/// //   v--- Unquoted field names are interpreted as variables
///     field_name_2: 7,
///     "y": false,
///     "z": ion_struct!{ "a": 1.5f64, "b": -8.25f64},
/// //        Arbitrary expressions are acceptable, though some may require
/// //   v--- an extra scope (braces: `{}`) to be understood properly.
///      {format!("{}_{}", prefix, suffix)}: IonType::Null
/// }
/// .into();
/// // Construct an Element from serialized Ion data
/// let expected = Element::read_one(
///     r#"{w: "foo", x: 7, y: false, z: {a: 1.5e0, b: -8.25e0}, abc_def: null}"#,
/// )
/// .unwrap();
/// // Compare the two Elements
/// assert_eq!(expected, actual);
/// ```
#[macro_export]
macro_rules! ion_struct {
    ($($field_name:tt : $element:expr),* $(,)?) => {{
        use $crate::element::Struct;
        Struct::builder()$(.with_field($field_name, $element))*.build()
    }};
}

/// Constructs a [`Sequence`] with the specified child values.
///
/// Note that a `Sequence` is NOT a type of `Element`. However, one can convert a `Sequence` into a
/// `List` or `SExp`.
///
/// ```
/// use ion_rs::element::{Element, Sequence};
/// use ion_rs::{ion_seq, ion_list};
/// // Construct a Sequence from serialized Ion data
/// let expected: Sequence = Element::read_all(r#" "foo" 7 false [1.5e0, -8.25e0] "#).unwrap();
/// // Construct a Sequence from Rust values
/// let actual: Sequence = ion_seq!("foo" 7 false ion_list![1.5f64, -8.25f64]);
/// // Compare the two Sequences
/// assert_eq!(expected, actual);
///
/// // The ion_seq! macro can also accept a comma-delimited list of Rust values to convert
/// let actual: Sequence = ion_seq!["foo", 7, false, ion_list![1.5f64, -8.25f64]];
/// assert_eq!(expected, actual);
/// ```
#[macro_export]
macro_rules! ion_seq {
    ($($element:expr),* $(,)?) => {{
        use $crate::element::Sequence;
        Sequence::builder()$(.push($element))*.build()
    }};
    ($($element:expr)*) => {{
        use $crate::element::Sequence;
        Sequence::builder()$(.push($element))*.build()
    }};
}

use crate::types::{List, SExp};
pub use {ion_list, ion_sexp, ion_struct};

#[cfg(test)]
mod tests {
    use crate::element::builders::{SequenceBuilder, StructBuilder};
    use crate::element::Element;
    use crate::{ion_list, ion_sexp, ion_struct, Symbol};

    #[test]
    fn make_seq_with_macro() {
        let expected = Element::read_all(r#"1 true "foo" "bar""#).unwrap();
        // Sequences without commas (as found in SExps and at the top level) are ok
        assert_eq!(ion_seq!(1 true "foo" "bar"), expected);
        // Sequences with commas (as found in lists) are ok
        assert_eq!(ion_seq![1, true, "foo", "bar"], expected);
        // Trailing commas are allowed
        assert_eq!(ion_seq![1, true, "foo", "bar",], expected);
    }

    #[test]
    fn make_list_with_builder() {
        let actual: Element = SequenceBuilder::new()
            .push(1)
            .push(true)
            .push("foo")
            .push(Symbol::owned("bar"))
            .build_list()
            .into();
        let expected = Element::read_one(r#"[1, true, "foo", bar]"#).unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn make_list_with_macro() {
        let actual: Element = ion_list![1, true, "foo", Symbol::owned("bar")].into();
        let expected = Element::read_one(r#"[1, true, "foo", bar]"#).unwrap();
        assert_eq!(actual, expected);
        // Trailing commas are allowed
        let actual: Element = ion_list![1, true, "foo", Symbol::owned("bar"),].into();
        assert_eq!(actual, expected);
    }

    #[test]
    fn make_list_with_builder_using_remove() {
        let actual: Element = SequenceBuilder::new()
            .push(1)
            .push(true)
            .push("foo")
            .remove(1)
            .remove(1)
            .push(Symbol::owned("bar"))
            .build_list()
            .into();
        let expected = Element::read_one("[1, bar]").unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn list_clone_builder() {
        let original_list = ion_list![1, true, "foo", Symbol::owned("bar")];
        let new_list: Element = original_list
            .clone_builder()
            .remove(1)
            .push(88)
            .build_list()
            .into();
        let expected_list = Element::read_one(r#"[1, "foo", bar, 88]"#).unwrap();
        assert_eq!(new_list, expected_list);
    }

    #[test]
    fn make_sexp_with_builder() {
        let actual: Element = SequenceBuilder::new()
            .push(1)
            .push(true)
            .push("foo")
            .push(Symbol::owned("bar"))
            .build_sexp()
            .into();
        let expected = Element::read_one(r#"(1 true "foo" bar)"#).unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn sexp_clone_builder() {
        let original_sexp = ion_sexp!(1 true "foo" Symbol::owned("bar"));
        let new_sexp: Element = original_sexp
            .clone_builder()
            .remove(1)
            .push(88)
            .build_sexp()
            .into();
        let expected_sexp = Element::read_one(r#"(1 "foo" bar 88)"#).unwrap();
        assert_eq!(new_sexp, expected_sexp);
    }

    #[test]
    fn make_sexp_with_builder_using_remove() {
        let actual: Element = SequenceBuilder::new()
            .push(1)
            .push(true)
            .push("foo")
            .remove(1)
            .remove(1)
            .push(Symbol::owned("bar"))
            .build_sexp()
            .into();
        let expected = Element::read_one("(1 bar)").unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn make_sexp_with_macro() {
        let actual: Element = ion_sexp!(1 true "foo" Symbol::owned("bar")).into();
        let expected = Element::read_one(r#"(1 true "foo" bar)"#).unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn make_struct_with_builder() {
        let actual: Element = StructBuilder::new()
            .with_field("a", 1)
            .with_field("b", true)
            .with_field("c", "foo")
            .with_field("d", Symbol::owned("bar"))
            .build()
            .into();
        let expected = Element::read_one(r#"{a: 1, b: true, c: "foo", d: bar}"#).unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn make_struct_with_macro() {
        let actual: Element = ion_struct! {
            "a": 1,
            "b": true,
            "c": "foo",
            "d": Symbol::owned("bar")
        }
        .into();
        let expected = Element::read_one(r#"{a: 1, b: true, c: "foo", d: bar}"#).unwrap();
        assert_eq!(actual, expected);

        // Trailing commas are allowed
        let actual: Element = ion_struct! {
            "a": 1,
            "b": true,
            "c": "foo",
            "d": Symbol::owned("bar"), // <-- trailing comma
        }
        .into();
        assert_eq!(actual, expected);
    }

    #[test]
    fn make_struct_with_builder_using_remove_field() {
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
            .build()
            .into();
        let expected = Element::read_one(r#"{a: 1, c: "foo", d: baz}"#).unwrap();
        assert_eq!(actual, expected);
    }
}
