// Copyright Amazon.com, Inc. or its affiliates.

//! Provides a in-memory tree representation of Ion values that can be operated on in
//! a dynamically typed way.
//!
//! This module consists of two submodules that implement the value traits:
//!
//! * The [`owned`] module provides an implementation of values that have no associated
//!   lifetime.  These types are convenient, but may imply extra copying/cloning.
//! * The [`borrowed`] module provides an implementation of values that are tied to some
//!   associated lifetime and borrow a reference to their underlying data in some way
//!   (e.g. storing a `&str` in the value versus a fully owned `String`).
//! * The [`reader`] module provides API and implementation to read Ion data into [`Element`]
//!   instances.
//! * The [`writer`] module provides API and implementation to write Ion data from [`Element`]
//!   instances.
//!
//! ## Examples
//! In general, users will use the [`ElementReader`](reader::ElementReader) trait to read in data:
//!
//! ```
//! use ion_rs::IonType;
//! use ion_rs::result::IonResult;
//! use ion_rs::value::{IonElement, IonStruct};
//! use ion_rs::value::reader::element_reader;
//! use ion_rs::value::reader::ElementReader;
//!
//! fn main() -> IonResult<()> {
//!     let mut iter = element_reader().iterate_over(br#""hello!""#)?;
//!     if let Some(Ok(elem)) = iter.next() {
//!         assert_eq!(IonType::String, elem.ion_type());
//!         assert_eq!("hello!", elem.as_str().unwrap());
//!     } else {
//!         panic!("Expected an element!");
//!     }
//!     assert!(iter.next().is_none());
//!     Ok(())
//! }
//! ```
//!
//! [`ElementReader::read_all`](reader::ElementReader::read_all) is a convenient way to put all of the
//! parsed [`Element`] into a [`Vec`], with a single [`IonError`](crate::result::IonError) wrapper:
//!
//! ```
//! # use ion_rs::IonType;
//! # use ion_rs::result::IonResult;
//! # use ion_rs::value::{IonElement, IonStruct};
//! # use ion_rs::value::reader::element_reader;
//! # use ion_rs::value::reader::ElementReader;
//! # fn main() -> IonResult<()> {
//! #
//! let elems = element_reader().read_all(br#""hello" world"#)?;
//! assert_eq!(2, elems.len());
//! assert_eq!(IonType::String, elems[0].ion_type());
//! assert_eq!("hello", elems[0].as_str().unwrap());
//! assert_eq!(IonType::Symbol, elems[1].ion_type());
//! assert_eq!("world", elems[1].as_str().unwrap());
//! #
//! #    Ok(())
//! # }
//! ```
//!
//! [`ElementReader::read_one`](reader::ElementReader::read_one) is another convenient way to parse a single
//! top-level element into a [`Element`].  This method will return an error if the data has
//! a parsing error or if there is more than one [`Element`] in the stream:
//!
//! ```
//! # use ion_rs::IonType;
//! # use ion_rs::result::IonResult;
//! use ion_rs::types::integer::IntAccess;
//! # use ion_rs::value::{IonElement,  IonStruct};
//! # use ion_rs::value::reader::element_reader;
//! # use ion_rs::value::reader::ElementReader;
//! # fn main() -> IonResult<()> {
//! #
//! // read a single value from binary: 42
//! let elem = element_reader().read_one(&[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x2A])?;
//! assert_eq!(IonType::Integer, elem.ion_type());
//! assert_eq!(42, elem.as_i64().unwrap());
//!
//! // cannot read two values in a stream this way: 42 0
//! assert!(element_reader().read_one(&[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x2A, 0x20]).is_err());
//!
//! // cannot read an empty stream (binary IVM only)
//! assert!(element_reader().read_one(&[0xE0, 0x01, 0x00, 0xEA]).is_err());
//!
//! // normal malformed binary is a failure!
//! assert!(element_reader().read_one(&[0xE0, 0x01, 0x00, 0xEA, 0xF0]).is_err());
//!
//! // also an error if malformed data happens after valid single value
//! assert!(element_reader().read_one(&[0xE0, 0x01, 0x00, 0xEA, 0x20, 0x30]).is_err());
//! #
//! #    Ok(())
//! # }
//! ```
//!
//! To serialize data, users can use the [`ElementWriter`](writer::ElementWriter) trait to serialize data
//! from [`Element`] to binary or text Ion:
//!
//! ```ignore
//! use ion_rs::result::IonResult;
//! use ion_rs::value::Element;
//! use ion_rs::value::reader::{element_reader, ElementReader};
//! use ion_rs::value::writer::{ElementWriter, Format};
//!
//! // a fixed buffer length to write to
//! const BUF_SIZE: usize = 8 * 1024 * 1024;
//!
//! fn main() -> IonResult<()> {
//!     let elems = element_reader().read_all(b"null true 1")?;
//!
//!     let mut buf = vec![0u8; BUF_SIZE];
//!     // This method requires the `ion-c-sys` feature to be enabled
//!     let mut writer = Format::Binary.element_writer_for_slice(&mut buf)?;
//!     writer.write_all(elems.iter())?;
//!
//!     let output = writer.finish()?;
//!     assert_eq!(&[0xE0, 0x01, 0x00, 0xEA, 0x0F, 0x11, 0x21, 0x01], output);    
//!     
//!     Ok(())
//! }
//! ```
//!
//! Users should use the traits in this module to make their code work
//! in contexts that have either [`borrowed`] or [`owned`] values.  This can be done
//! most easily by writing generic functions that can work with a reference of any type.
//!
//! For example, consider a fairly contrived, but generic `extract_text` function that unwraps
//! and converts [`SymbolToken::text()`] into an owned `String`:
//!
//! ```
//! use ion_rs::Symbol;
//! use ion_rs::value::IonSymbolToken;
//! use ion_rs::SymbolRef;
//!
//! fn extract_text<T: IonSymbolToken>(tok: &T) -> String {
//!     tok.text().unwrap().into()
//! }
//!
//! let owned_token: Symbol = "hello".into();
//!
//! // owned value to emphasize lifetime
//! let text = String::from("hello");
//! let borrowed_token: SymbolRef = text.as_str().into();
//!
//! let owned_text = extract_text(&owned_token);
//! let borrowed_text = extract_text(&borrowed_token);
//! assert_eq!(owned_text, borrowed_text);
//! ```
//!
//! This extends to the [`Element`] trait as well which is the "top-level" API type for
//! any Ion datum.  Consider a contrived function that extracts and returns the annotations
//! of an underlying element as a `Vec<String>`.  Note that it filters out any annotation
//! that may not have text (so data could be dropped):
//!
//! ```
//! use ion_rs::value::{IonElement, IonSymbolToken};
//! use ion_rs::value::borrowed::{
//!     ValueRef,
//!     ElementRef,
//!     text_token as borrowed_text_token
//! };
//! use ion_rs::value::owned::{
//!     Value,
//!     Element,
//!     text_token as owned_text_token
//! };
//!
//! fn extract_annotations<T: IonElement>(elem: &T) -> Vec<Option<String>> {
//!     elem.annotations().map(
//!         |tok| tok.text().map(|text_ref| text_ref.to_string())
//!     ).collect()
//! }
//!
//! let owned_elem = Element::new(
//!     vec![
//!         owned_text_token("foo"),
//!         owned_text_token("bar")
//!     ],
//!     Value::String("baz".into())
//! );
//!
//! // owned values to emphasize lifetime
//! let strings: Vec<String> =
//!     vec!["foo", "bar", "baz"].iter().map(|x| x.to_string()).collect();
//! let borrowed_elem = ElementRef::new(
//!     vec![
//!         borrowed_text_token(&strings[0]),
//!         borrowed_text_token(&strings[1])
//!     ],
//!     ValueRef::String(&strings[2])
//! );
//!
//! let owned_annotations = extract_annotations(&owned_elem);
//! let borrowed_annotations = extract_annotations(&borrowed_elem);
//! assert_eq!(owned_annotations, borrowed_annotations);
//! ```
//!
//! For reference here are a couple other _value_ style APIs for JSON:
//! * [`simd_json`'s `Value` API][simd-json-value]
//! * [`serde_json`'s `Value` API][serde-json-value]
//!
//! [simd-json-value]: https://docs.rs/simd-json/latest/simd_json/value/index.html
//! [serde-json-value]: https://docs.serde.rs/serde_json/value/enum.Value.html

use crate::symbol_ref::AsSymbolRef;
use crate::types::decimal::Decimal;
use crate::types::integer::Integer;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::IonType;
use num_bigint::BigInt;
use std::fmt::Debug;

pub mod borrowed;
mod element_stream_reader;
pub mod native_reader;
pub mod native_writer;
pub mod owned;
pub mod reader;
pub mod writer;

/// A view of a symbolic token.
///
/// This can be either a content associated with a symbol value, an annotation,
/// or a struct field name.
///
/// A given token may have `text`, a symbol ID ("SID"), or both depending on that implementation's
/// level of abstraction. For example:
///
/// * A symbol token implementation used by a raw binary reader might _only_ have a symbol ID, as
///   raw readers do not process symbol tables and so are not able to map symbol IDs to text.
/// * A symbol token implementation used by a raw text reader might have _either_ a symbol ID or
///   text, as text streams can encode symbols as either inline text (`foo`) or as
///   symbol IDs (`$10`).
/// * A symbol token implementation used by a user-level reader might always have text (because a
///   user-level reader can map symbol IDs to text) and choose to discard the symbol ID that was
///   used to encode that text because it is no longer necessary.
///
///  It is illegal for an implementation to return `None` for BOTH the text and local SID. If the
///  symbol token does not have known text, the implementation must return a local SID of `0`
///  (or another local SID whose value in the symbol table is `null`).
///
///  If an implementation represents a _resolved_ token...
///  * ...and the token has known text, the `text()` method MUST return `Some`.
///  * ...and the token has explicitly undefined text (for example, `$0` or any symbol ID whose
///    value in the symbol table is `null`), the `symbol_id()` method MUST return `Some(0)`.
///    (For example, if the symbol token in the stream is `$38` and its corresponding symbol table
///    entry is `null`, the `symbol_id` method must return `0` instead of `38`.)
///
///  This enables consistent equality testing; two raw tokens with different symbol IDs can be said
///  to be unequal because neither is resolved. In contrast, two resolved tokens with different
///  symbol IDs must be considered equal if those symbol IDs point to the same text or both have
///  undefined text.
pub trait IonSymbolToken: Debug + PartialEq {
    /// The text of the token.
    ///
    /// If the token was encoded as a symbol ID but has not been resolved (that is: mapped to text
    /// via the symbol table), this method will return `None`.
    ///
    /// If this token was encoded as a symbol ID whose text is explicitly known to be *undefined*
    /// (for example: `$0`), this method will return `None`.
    fn text(&self) -> Option<&str>;

    /// The symbol ID of the token, which may be `None` if no ID is associated with the
    /// token (e.g. Ion text symbols).
    fn symbol_id(&self) -> Option<SymbolId>;

    /// Decorates the [`IonSymbolToken`] with text.
    fn with_text(self, text: &'static str) -> Self;

    /// Decorates the [`IonSymbolToken`] with a symbol ID.
    fn with_symbol_id(self, symbol_id: SymbolId) -> Self;

    /// Constructs an [`IonSymbolToken`] with text and no symbol ID.
    /// A common case for text and synthesizing tokens.
    fn text_token(text: &'static str) -> Self;

    /// Constructs an [`IonSymbolToken`] with unknown text and a local symbol ID.
    /// A common case for binary parsing (though technically relevant in text).
    fn symbol_id_token(symbol_id: SymbolId) -> Self;

    /// Returns `true` if this token has been resolved.
    ///
    /// Tokens with text are inherently resolved. Tokens without text are considered resolved if
    /// they explicitly have unknown text (i.e. `$0` or a symbol ID whose corresponding value in the
    /// symbol table is `null`.)
    ///
    /// If a token has unknown text but `is_resolved` returns `false`, it may or may not have
    /// associated text.
    fn is_resolved(&self) -> bool {
        self.text().is_some() || self.symbol_id() == Some(0)
    }
}

/// Represents a either a borrowed or owned Ion value and its associated annotations (if any). There
/// are/will be specific APIs for _borrowed_ and _owned_ implementations, but this trait unifies
/// operations on either.
pub trait IonElement
where
    Self: From<i64>
        + From<bool>
        + From<Decimal>
        + From<Timestamp>
        + From<f64>
        + From<BigInt>
        + Debug
        + PartialEq,
{
    type SymbolToken: IonSymbolToken + Debug + PartialEq;
    type Sequence: IonSequence<Element = Self> + ?Sized + Debug + PartialEq;
    type Struct: IonStruct<FieldName = Self::SymbolToken, Element = Self>
        + ?Sized
        + Debug
        + PartialEq;
    type Builder: Builder<SymbolToken = Self::SymbolToken, Element = Self> + ?Sized;

    /// The type of data this element represents.
    fn ion_type(&self) -> IonType;

    /// The annotations for this element.
    ///
    /// ## Usage
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::owned::*;
    /// # use ion_rs::value::borrowed::*;
    /// // simple function to extract the annotations to owned strings.
    /// // will panic if the text is not there!
    /// fn annotation_strings<T: IonElement>(elem: &T) -> Vec<String> {
    ///     elem.annotations().map(|tok| tok.text().unwrap().into()).collect()
    /// }
    ///
    /// let strs = vec!["a", "b", "c"];
    /// let owned_elem = Element::new(
    ///     strs.iter().map(|s| (*s).into()).collect(),
    ///     Value::String("moo".into())
    /// );
    /// let borrowed_elem = ElementRef::new(
    ///     strs.iter().map(|s| (*s).into()).collect(),
    ///     ValueRef::String("moo")
    /// );
    ///
    /// let expected: Vec<String> = strs.iter().map(|s| (*s).into()).collect();
    /// assert_eq!(expected, annotation_strings(&owned_elem));
    /// assert_eq!(expected, annotation_strings(&borrowed_elem));
    ///
    /// // check if the element contains a particular annotation
    /// assert!(&owned_elem.has_annotation("a"));
    /// assert!(!&owned_elem.has_annotation("d"));
    /// assert!(&borrowed_elem.has_annotation("a"));
    /// assert!(!&borrowed_elem.has_annotation("d"));
    /// ```
    ///
    /// Note that this uses a `Box<dyn Iterator<...>>` to capture the borrow cleanly without
    /// without [generic associated types (GAT)][gat].  In theory, when GAT lands, this could
    /// be replaced with static polymorphism.
    ///
    /// [gat]: https://rust-lang.github.io/rfcs/1598-generic_associated_types.html
    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::SymbolToken> + 'a>;

    /// Return an `Element` with given annotations
    fn with_annotations<I: IntoIterator<Item = Self::SymbolToken>>(self, annotations: I) -> Self;

    /// Return true if an `Element` contains given annotation otherwise return false
    fn has_annotation(&self, annotation: &str) -> bool;

    /// Returns whether this element is a `null` value
    fn is_null(&self) -> bool;

    /// Returns a reference to the underlying [`Integer`] for this element.
    ///
    /// This will return `None` if the type is not `int` or the value is any `null`.
    fn as_integer(&self) -> Option<&Integer>;

    /// Returns a reference to the underlying float value for this element.
    ///
    /// This will return `None` if the type is not `float` or the value is any `null`.
    fn as_f64(&self) -> Option<f64>;

    /// Returns a reference to the underlying [`Decimal`] for this element.
    ///
    /// This will return `None` if the type is not `decimal` or the value is any `null`.
    fn as_decimal(&self) -> Option<&Decimal>;

    /// Returns a reference to the underlying [`Timestamp`] for this element.
    ///
    /// This will return `None` if the type is not `timestamp` or the value is any `null`.
    fn as_timestamp(&self) -> Option<&Timestamp>;

    /// Returns a slice to the textual value of this element.
    ///
    /// This will return `None` in the case that the type is not `string`/`symbol`,
    /// if the value is any `null`, or the text of the `symbol` is not defined.
    fn as_str(&self) -> Option<&str>;

    /// Returns a reference to the [`SymbolToken`] of this element.
    ///
    /// This will return `None` in the case that the type is not `symbol` or the value is
    /// any `null`.
    fn as_sym(&self) -> Option<&Self::SymbolToken>;

    /// Returns a reference to the boolean value of this element.
    ///
    ///  This will return `None` in the case that the type is not `bool` or the value is
    ///   any `null`.
    fn as_bool(&self) -> Option<bool>;

    /// Returns a reference to the underlying bytes of this element.
    ///
    /// This will return `None` in the case that the type is not `blob`/`clob` or the value is
    /// any `null`.
    fn as_bytes(&self) -> Option<&[u8]>;

    /// Returns a reference to the [`Sequence`] of this element.
    ///
    /// This will return `None` in the case that the type is not `sexp`/`list` or
    /// if the value is any `null`.
    fn as_sequence(&self) -> Option<&Self::Sequence>;

    /// Returns a reference to the [`Struct`] of this element.
    ///
    /// This will return `None` in the case that the type is not `struct` or the value is
    /// any `null`.
    fn as_struct(&self) -> Option<&Self::Struct>;

    // TODO add all the accessors to the trait

    // TODO add mutation methods to the trait
}

/// Represents the _value_ of sequences of Ion elements (i.e. `list` and `sexp`).
pub trait IonSequence: Debug + PartialEq {
    type Element: IonElement + ?Sized;

    /// The children of the sequence.
    ///
    /// Note that this uses a `Box<dyn Iterator<...>>` to capture the borrow cleanly without
    /// without [generic associated types (GAT)][gat].  In theory, when GAT lands, this could
    /// be replaced with static polymorphism.
    ///
    /// [gat]: https://rust-lang.github.io/rfcs/1598-generic_associated_types.html
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a>;

    /// Returns a reference to the element in the sequence at the given index or
    /// returns `None` if the index is out of the bounds.
    fn get(&self, i: usize) -> Option<&Self::Element>;

    /// Returns the length of the sequence
    fn len(&self) -> usize;

    /// Returns true if the sequence is empty otherwise returns false
    fn is_empty(&self) -> bool;
}

/// Represents the _value_ of `struct` of Ion elements.
pub trait IonStruct: Debug + PartialEq {
    type FieldName: IonSymbolToken + ?Sized;
    type Element: IonElement + ?Sized;

    /// The fields of the structure.
    ///
    /// Note that this uses a `Box<dyn Iterator<...>>` to capture the borrow cleanly without
    /// without [generic associated types (GAT)][gat].  In theory, when GAT lands, this could
    /// be replaced with static polymorphism.
    ///
    /// [gat]: https://rust-lang.github.io/rfcs/1598-generic_associated_types.html
    fn iter<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = (&'a Self::FieldName, &'a Self::Element)> + 'a>;

    /// Returns the last value corresponding to the field_name in the struct or
    /// returns `None` if the field_name does not exist in the struct
    ///
    /// ## Usage
    /// Using the [borrowed] API:
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::borrowed::*;
    /// let fields: Vec<(&str, ValueRef)>= vec![("e", "f"), ("g", "h")]
    ///     .into_iter().map(|(k, v)| (k, ValueRef::String(v))).collect();
    /// let borrowed: StructRef = fields.into_iter().collect();
    /// assert_eq!("h", borrowed.get("g".to_string()).map(|e| e.as_str()).flatten().unwrap());
    /// ```
    ///
    /// Using the [owned] API:
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::owned::*;
    /// let fields: Vec<(&str, Value)>= vec![("a", "b"), ("c", "d")]
    ///     .into_iter().map(|(k, v)| (k, Value::String(v.into()))).collect();
    /// let owned: Struct = fields.into_iter().collect();
    /// assert_eq!("d", owned.get("c".to_string()).map(|e| e.as_str()).flatten().unwrap());
    /// ```
    fn get<T: AsSymbolRef>(&self, field_name: T) -> Option<&Self::Element>;

    /// Returns an iterator with all the values corresponding to the field_name in the struct or
    /// returns an empty iterator if the field_name does not exist in the struct
    ///
    /// ## Usage
    /// Using the [borrowed] API:
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::borrowed::*;
    /// let fields: Vec<(&str, ValueRef)>= vec![("a", "b"), ("c", "d"), ("c", "e")]
    ///     .into_iter().map(|(k, v)| (k, ValueRef::String(v))).collect();
    /// let borrowed: StructRef = fields.into_iter().collect();
    /// assert_eq!(
    ///     vec!["d", "e"],
    ///     borrowed.get_all("c").flat_map(|e| e.as_str()).collect::<Vec<&str>>()
    /// );
    /// ```
    ///
    /// Using the [owned] API:
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::owned::*;
    /// let fields: Vec<(&str, Value)>= vec![("d", "e"), ("d", "f"), ("g", "h")]
    ///     .into_iter().map(|(k, v)| (k, Value::String(v.into()))).collect();
    /// let owned: Struct = fields.into_iter().collect();
    /// assert_eq!(
    ///     vec!["e", "f"],
    ///     owned.get_all("d").flat_map(|e| e.as_str()).collect::<Vec<&str>>()
    /// );
    /// ```
    fn get_all<'a, T: AsSymbolRef>(
        &'a self,
        field_name: T,
    ) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a>;
}

pub trait Builder {
    type Element: IonElement + ?Sized;
    type SymbolToken: IonSymbolToken + PartialEq;
    type Sequence: IonSequence<Element = Self::Element> + ?Sized;
    type Struct: IonStruct<FieldName = Self::SymbolToken, Element = Self::Element> + ?Sized;

    /// Builds a `null` from IonType using Builder.
    fn new_null(e_type: IonType) -> Self::Element;

    /// Builds a `bool` using Builder.
    fn new_bool(bool: bool) -> Self::Element;

    /// Builds a `string` using Builder.
    fn new_string(str: &'static str) -> Self::Element;

    /// Builds a `symbol` from SymbolToken using Builder.
    fn new_symbol(sym: Self::SymbolToken) -> Self::Element;

    /// Builds a `i64` using Builder.
    fn new_i64(int: i64) -> Self::Element;

    /// Builds a `big int` using Builder.
    fn new_big_int(big_int: BigInt) -> Self::Element;

    /// Builds a `decimal` using Builder.
    fn new_decimal(decimal: Decimal) -> Self::Element;

    /// Builds a `timestamp` using Builder.
    fn new_timestamp(timestamp: Timestamp) -> Self::Element;

    /// Builds a `f64` using Builder.
    fn new_f64(float: f64) -> Self::Element;

    /// Builds a `clob` using Builder.
    fn new_clob(bytes: &'static [u8]) -> Self::Element;

    /// Builds a `blob` using Builder.
    fn new_blob(bytes: &'static [u8]) -> Self::Element;

    /// Builds a `list` from Sequence using Builder.
    fn new_list<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element;

    /// Builds a `sexp` from Sequence using Builder.
    fn new_sexp<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element;

    /// Builds a `struct` from Struct using Builder.
    fn new_struct<K, V, I>(structure: I) -> Self::Element
    where
        K: Into<Self::SymbolToken>,
        V: Into<Self::Element>,
        I: IntoIterator<Item = (K, V)>;
}

#[cfg(test)]
mod generic_value_tests {
    use super::*;
    use crate::types::timestamp::Timestamp;
    use crate::value::borrowed::*;
    use crate::value::owned::*;
    use crate::value::IonElement;
    use crate::IonType;
    use chrono::*;
    use rstest::*;
    use std::iter::{once, Once};

    /// Makes a timestamp from an RFC-3339 string and panics if it can't
    fn make_timestamp<T: AsRef<str>>(text: T) -> Timestamp {
        DateTime::parse_from_rfc3339(text.as_ref()).unwrap().into()
    }

    struct CaseAnnotations<E: IonElement> {
        elem: E,
        annotations: Vec<E::SymbolToken>,
    }

    fn annotations_text_case<E: IonElement>() -> CaseAnnotations<E> {
        CaseAnnotations {
            elem: E::Builder::new_i64(10).with_annotations(vec![
                E::SymbolToken::text_token("foo"),
                E::SymbolToken::text_token("bar"),
                E::SymbolToken::text_token("baz"),
            ]),
            annotations: vec![
                E::SymbolToken::text_token("foo"),
                E::SymbolToken::text_token("bar"),
                E::SymbolToken::text_token("baz"),
            ],
        }
    }

    fn annotations_local_sid_case<E: IonElement>() -> CaseAnnotations<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        CaseAnnotations {
            elem: E::Builder::new_i64(10).with_annotations(vec![
                E::SymbolToken::symbol_id_token(21),
                E::SymbolToken::symbol_id_token(22),
            ]),
            annotations: vec![
                E::SymbolToken::symbol_id_token(21),
                E::SymbolToken::symbol_id_token(22),
            ],
        }
    }

    fn no_annotations_case<E: IonElement>() -> CaseAnnotations<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        CaseAnnotations {
            elem: E::Builder::new_i64(10),
            annotations: vec![],
        }
    }

    #[rstest]
    #[case::owned_annotations_text(annotations_text_case::<Element>())]
    #[case::borrowed_annotations_text(annotations_text_case::<ElementRef>())]
    #[case::owned_annotations_local_sid(annotations_local_sid_case::<Element>())]
    #[case::borrowed_annotations_local_sid(annotations_local_sid_case::<ElementRef>())]
    #[case::owned_no_annotations(no_annotations_case::<Element>())]
    #[case::borrowed_no_annotations(no_annotations_case::<ElementRef>())]
    fn annotations_with_element<E: IonElement>(#[case] input: CaseAnnotations<E>) {
        let actual: Vec<&E::SymbolToken> = input.elem.annotations().collect();
        let expected: Vec<&E::SymbolToken> = input.annotations.iter().collect();
        assert_eq!(actual, expected);
    }

    struct CaseSym<E: IonElement> {
        eq_annotations: Vec<E::SymbolToken>,
        ne_annotations: Vec<E::SymbolToken>,
    }

    fn sym_text_case<E: IonElement>() -> CaseSym<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        // SymbolTokens with same text are equivalent
        CaseSym {
            eq_annotations: vec![
                E::SymbolToken::text_token("foo"),
                E::SymbolToken::text_token("foo").with_symbol_id(10),
            ],
            ne_annotations: vec![
                E::SymbolToken::text_token("bar"),
                E::SymbolToken::symbol_id_token(10),
            ],
        }
    }

    fn sym_local_sid_case<E: IonElement>() -> CaseSym<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        // local sids with no text are equivalent to each other and to SID $0
        CaseSym {
            eq_annotations: vec![
                E::SymbolToken::symbol_id_token(200),
                E::SymbolToken::symbol_id_token(100),
                E::SymbolToken::symbol_id_token(0),
            ],
            ne_annotations: vec![E::SymbolToken::text_token("foo")],
        }
    }

    /// Each case is a set of tokens that are the same, and a set of tokens that are not ever equal to the first.
    /// This should test symmetry/transitivity/commutativity
    #[rstest]
    #[case::owned_sym_text(sym_text_case::<Element>())]
    #[case::borrowed_sym_text(sym_text_case::<ElementRef>())]
    #[case::owned_sym_local_sid(sym_local_sid_case::<Element>())]
    #[case::borrowed_sym_local_sid(sym_local_sid_case::<ElementRef>())]
    fn symbol_token_eq<E: IonElement>(#[case] input: CaseSym<E>) {
        // check if equivalent vector contains set of tokens that are all equal
        for eq_this_token in &input.eq_annotations {
            for eq_other_token in &input.eq_annotations {
                assert_eq!(eq_this_token, eq_other_token);
            }
        }

        // check if non_equivalent vector contains a set of tokens that are not ever equal
        // to the equivalent set tokens.
        for eq_token in &input.eq_annotations {
            for non_eq_token in &input.ne_annotations {
                assert_ne!(eq_token, non_eq_token);
            }
        }
    }

    /// A struct that defines input case for `struct_accessors` method
    struct CaseStruct<E: IonElement> {
        /// set of struct elements that are the same
        eq_annotations: Vec<E>,
        /// set of struct elements that are never equal to `eq_annotations`
        ne_annotations: Vec<E>,
    }

    fn struct_with_local_sid_case<E: IonElement>() -> CaseStruct<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        CaseStruct {
            eq_annotations: vec![
                E::Builder::new_struct(
                    vec![(
                        E::SymbolToken::symbol_id_token(21),
                        E::Builder::new_string("hello"),
                    )]
                    .into_iter(),
                ),
                // SymbolToken with local SID and no text are equivalent to each other and to SID $0
                E::Builder::new_struct(
                    vec![(
                        E::SymbolToken::symbol_id_token(22),
                        E::Builder::new_string("hello"),
                    )]
                    .into_iter(),
                ),
            ],
            ne_annotations: vec![
                // structs with different symbol token values
                E::Builder::new_struct(
                    vec![(
                        E::SymbolToken::symbol_id_token(21).with_text("foo"),
                        E::Builder::new_string("hello"),
                    )]
                    .into_iter(),
                ),
                // struct with annotated value
                E::Builder::new_struct(
                    vec![(
                        E::SymbolToken::symbol_id_token(21),
                        E::Builder::new_string("hello")
                            .with_annotations(vec![E::SymbolToken::text_token("foo")]),
                    )]
                    .into_iter(),
                ),
                // struct with different value for (field,value) pair
                E::Builder::new_struct(
                    vec![(E::SymbolToken::symbol_id_token(21), E::Builder::new_i64(10))]
                        .into_iter(),
                ),
                // structs with different fields length
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::symbol_id_token(21),
                            E::Builder::new_string("hello"),
                        ),
                        (
                            E::SymbolToken::symbol_id_token(21),
                            E::Builder::new_string("hi"),
                        ),
                    ]
                    .into_iter(),
                ),
            ],
        }
    }

    fn struct_with_multiple_fields_case<E: IonElement>() -> CaseStruct<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        CaseStruct {
            eq_annotations: vec![
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                        (
                            E::SymbolToken::text_token("name"),
                            E::Builder::new_string("Ion"),
                        ),
                    ]
                    .into_iter(),
                ),
                // structs with different order of fields
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("name"),
                            E::Builder::new_string("Ion"),
                        ),
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                    ]
                    .into_iter(),
                ),
            ],
            ne_annotations: vec![
                // structs with different length and duplicates
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                        (
                            E::SymbolToken::text_token("name"),
                            E::Builder::new_string("Ion"),
                        ),
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                    ]
                    .into_iter(),
                ),
                // structs with different fields length and duplicates
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                        (
                            E::SymbolToken::text_token("name"),
                            E::Builder::new_string("Ion"),
                        ),
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("bye"),
                        ),
                    ]
                    .into_iter(),
                ),
                // structs with different fields length
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                        (
                            E::SymbolToken::text_token("name"),
                            E::Builder::new_string("Ion"),
                        ),
                        (
                            E::SymbolToken::text_token("message"),
                            E::Builder::new_string("bye"),
                        ),
                    ]
                    .into_iter(),
                ),
            ],
        }
    }

    fn struct_with_duplicates_in_multiple_fields_case<E: IonElement>() -> CaseStruct<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        CaseStruct {
            eq_annotations: vec![
                E::Builder::new_struct(
                    vec![
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                    ]
                    .into_iter(),
                ),
                // structs with different symbol token sids
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("a").with_symbol_id(21),
                            E::Builder::new_i64(1),
                        ),
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                    ]
                    .into_iter(),
                ),
            ],
            ne_annotations: vec![
                // structs with different length
                E::Builder::new_struct(
                    vec![
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                    ]
                    .into_iter(),
                ),
                // structs with annotated values
                E::Builder::new_struct(
                    vec![
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                        (
                            E::SymbolToken::text_token("a"),
                            E::Builder::new_i64(1)
                                .with_annotations(vec![E::SymbolToken::text_token("a")]),
                        ),
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                    ]
                    .into_iter(),
                ),
                // structs with different value for duplicates
                E::Builder::new_struct(
                    vec![
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(2)),
                        (E::SymbolToken::text_token("a"), E::Builder::new_i64(1)),
                    ]
                    .into_iter(),
                ),
            ],
        }
    }

    fn struct_with_duplicate_fieldnames_case<E: IonElement>() -> CaseStruct<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        CaseStruct {
            eq_annotations: vec![
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("world"),
                        ),
                    ]
                    .into_iter(),
                ),
                // structs with unordered fields
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("world"),
                        ),
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                    ]
                    .into_iter(),
                ),
            ],
            ne_annotations: vec![
                // structs with different length and duplicates
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("world"),
                        ),
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hey"),
                        ),
                    ]
                    .into_iter(),
                ),
                // structs with annotated values
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("world")
                                .with_annotations(vec![E::SymbolToken::text_token("foo")]),
                        ),
                    ]
                    .into_iter(),
                ),
                // structs with different length
                E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hello"),
                        ),
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("world"),
                        ),
                        (
                            E::SymbolToken::text_token("name"),
                            E::Builder::new_string("hello"),
                        ),
                    ]
                    .into_iter(),
                ),
            ],
        }
    }

    #[rstest]
    #[case::owned_struct_with_local_sid(struct_with_local_sid_case::<Element>())]
    #[case::borrowed_struct_with_local_sid(struct_with_local_sid_case::<ElementRef>())]
    #[case::owned_struct_with_multiple_fields(struct_with_multiple_fields_case::<Element>())]
    #[case::borrowed_struct_with_multiple_fields(struct_with_multiple_fields_case::<ElementRef>())]
    #[case::owned_struct_with_duplicates_in_multiple_fields(struct_with_duplicates_in_multiple_fields_case::<Element>())]
    #[case::borrowed_struct_with_duplicates_in_multiple_fields(struct_with_duplicates_in_multiple_fields_case::<ElementRef>())]
    #[case::owned_struct_with_duplicate_fieldnames(struct_with_duplicate_fieldnames_case::<Element>())]
    #[case::borrowed_struct_with_duplicate_fieldnames(struct_with_duplicate_fieldnames_case::<ElementRef>())]
    fn struct_accessors<E: IonElement>(#[case] input: CaseStruct<E>) {
        // check if equivalent vector contains set of structs that are all equal
        for eq_this_struct in &input.eq_annotations {
            for eq_other_struct in &input.eq_annotations {
                assert_eq!(eq_this_struct, eq_other_struct);
            }
        }

        // check if non_equivalent vector contains a set of structs that are not ever equal
        // to the equivalent set structs.
        for eq_struct in &input.eq_annotations {
            for non_eq_struct in &input.ne_annotations {
                assert_ne!(eq_struct, non_eq_struct);
            }
        }
    }

    /// Models the operations on `Element` that we want to test.
    #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
    enum ElemOp {
        IsNull,
        AsBool,
        AsAnyInt,
        AsF64,
        AsDecimal,
        AsTimestamp,
        AsStr,
        AsSym,
        AsBytes,
        AsSequence,
        AsStruct,
    }

    impl IntoIterator for ElemOp {
        type Item = ElemOp;
        type IntoIter = <Once<ElemOp> as IntoIterator>::IntoIter;

        fn into_iter(self) -> Self::IntoIter {
            once(self)
        }
    }

    use crate::types::integer::IntAccess;
    use std::collections::HashSet;
    use std::str::FromStr;
    use ElemOp::*;

    type ElemAssertFunc<E> = dyn Fn(&E);

    struct Case<E: IonElement> {
        elem: E,
        ion_type: IonType,
        ops: Vec<ElemOp>,
        op_assert: Box<dyn Fn(&E)>,
    }

    fn null_case<E: IonElement>() -> Case<E> {
        Case {
            elem: E::Builder::new_null(IonType::Null),
            ion_type: IonType::Null,
            ops: vec![IsNull],
            op_assert: Box::new(|e: &E| assert_eq!(true, e.is_null())),
        }
    }

    fn bool_case<E: IonElement>() -> Case<E> {
        Case {
            elem: true.into(),
            ion_type: IonType::Boolean,
            ops: vec![AsBool],
            op_assert: Box::new(|e: &E| {
                let expected = &E::Builder::new_bool(true);
                assert_eq!(Some(true), e.as_bool());
                assert_eq!(expected, e);
            }),
        }
    }

    fn i64_case<E: IonElement>() -> Case<E> {
        Case {
            elem: 100.into(),
            ion_type: IonType::Integer,
            ops: vec![AsAnyInt],
            op_assert: Box::new(|e: &E| {
                let expected = &E::Builder::new_i64(100);
                assert_eq!(Some(&Integer::I64(100)), e.as_integer());
                assert_eq!(Some(100), e.as_i64());
                assert_eq!(None, e.as_big_int());
                assert_eq!(expected, e);
            }),
        }
    }

    fn big_int_case<E: IonElement>() -> Case<E> {
        Case {
            elem: BigInt::from(100).into(),
            ion_type: IonType::Integer,
            ops: vec![AsAnyInt],
            op_assert: Box::new(|e: &E| {
                let expected = &E::Builder::new_big_int(BigInt::from(100));
                assert_eq!(Some(&Integer::BigInt(BigInt::from(100))), e.as_integer());
                assert_eq!(BigInt::from_str("100").unwrap(), *e.as_big_int().unwrap());
                assert_eq!(expected, e);
            }),
        }
    }

    fn f64_case<E: IonElement>() -> Case<E> {
        Case {
            elem: 16.0.into(),
            ion_type: IonType::Float,
            ops: vec![AsF64],
            op_assert: Box::new(|e: &E| {
                let expected = &E::Builder::new_f64(16.0);
                assert_eq!(Some(16.0), e.as_f64());
                assert_eq!(expected, e);
            }),
        }
    }

    fn timestamp_case<E: IonElement>() -> Case<E> {
        Case {
            elem: make_timestamp("2014-10-16T12:01:00-00:00").into(),
            ion_type: IonType::Timestamp,
            ops: vec![AsTimestamp],
            op_assert: Box::new(|e: &E| {
                let expected =
                    &E::Builder::new_timestamp(make_timestamp("2014-10-16T12:01:00+00:00"));
                assert_eq!(
                    Some(&make_timestamp("2014-10-16T12:01:00+00:00")),
                    e.as_timestamp()
                );
                assert_eq!(expected, e);
            }),
        }
    }

    fn decimal_case<E: IonElement>() -> Case<E> {
        Case {
            elem: Decimal::new(8, 3).into(),
            ion_type: IonType::Decimal,
            ops: vec![AsDecimal],
            op_assert: Box::new(|e: &E| {
                let expected = &E::Builder::new_decimal(Decimal::new(8, 3));
                assert_eq!(Some(&Decimal::new(80, 2)), e.as_decimal());
                assert_eq!(expected, e);
            }),
        }
    }

    fn string_case<E: IonElement>() -> Case<E> {
        Case {
            elem: E::Builder::new_string("hello"),
            ion_type: IonType::String,
            ops: vec![AsStr],
            op_assert: Box::new(|e: &E| assert_eq!(Some("hello"), e.as_str())),
        }
    }

    fn symbol_case<E: IonElement>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_symbol(E::SymbolToken::text_token("foo").with_symbol_id(10)),
            ion_type: IonType::Symbol,
            ops: vec![AsSym, AsStr],
            op_assert: Box::new(|e: &E| {
                assert_eq!(Some("foo"), e.as_sym().unwrap().text());
                assert_eq!(Some("foo"), e.as_str());
            }),
        }
    }

    fn symbol_with_local_sid_case<E: IonElement>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_symbol(E::SymbolToken::symbol_id_token(10)),
            ion_type: IonType::Symbol,
            ops: vec![AsSym, AsStr],
            op_assert: Box::new(|e: &E| {
                let symbol = e.as_sym().unwrap();
                if symbol.is_resolved() {
                    // SymbolToken implementations that represent a resolved token will return
                    // SID 0 if they do not have known text.
                    assert_eq!(Some(0), e.as_sym().unwrap().symbol_id());
                } else {
                    // The symbol ID *must* be 10.
                    assert_eq!(Some(10), e.as_sym().unwrap().symbol_id());
                }
            }),
        }
    }

    fn blob_case<E: IonElement>() -> Case<E> {
        Case {
            elem: E::Builder::new_blob(b"hello"),
            ion_type: IonType::Blob,
            ops: vec![AsBytes],
            op_assert: Box::new(|e: &E| assert_eq!(Some("hello".as_bytes()), e.as_bytes())),
        }
    }

    fn clob_case<E: IonElement>() -> Case<E> {
        Case {
            elem: E::Builder::new_clob(b"goodbye"),
            ion_type: IonType::Clob,
            ops: vec![AsBytes],
            op_assert: Box::new(|e: &E| assert_eq!(Some("goodbye".as_bytes()), e.as_bytes())),
        }
    }

    fn list_case<E: IonElement>() -> Case<E> {
        Case {
            elem: E::Builder::new_list(vec![true.into(), false.into()].into_iter()),
            ion_type: IonType::List,
            ops: vec![AsSequence],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_sequence().unwrap();
                let expected: Vec<E> = vec![true.into(), false.into()];
                // assert the length of list
                assert_eq!(2, actual.len());
                for i in 0..actual.len() {
                    // assert the list elements one-by-one
                    assert_eq!(Some(&expected[i]), actual.get(i));
                }
                assert_eq!(false, actual.is_empty());
            }),
        }
    }

    fn sexp_case<E: IonElement>() -> Case<E> {
        Case {
            elem: E::Builder::new_sexp(vec![true.into(), false.into()].into_iter()),
            ion_type: IonType::SExpression,
            ops: vec![AsSequence],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_sequence().unwrap();
                let expected: Vec<E> = vec![true.into(), false.into()];
                // assert the length of s-expression
                assert_eq!(2, actual.len());
                for i in 0..actual.len() {
                    // assert the s-expression elements one-by-one
                    assert_eq!(Some(&expected[i]), actual.get(i));
                }
            }),
        }
    }

    fn struct_case<E: IonElement>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_struct(
                vec![
                    (
                        E::SymbolToken::text_token("greetings"),
                        E::Builder::new_string("hello"),
                    ),
                    (
                        E::SymbolToken::text_token("name"),
                        E::Builder::new_string("ion"),
                    ),
                ]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct().unwrap();

                // verify that the field order is maintained when creating Struct
                assert_eq!(
                    actual.iter().next(),
                    Some((
                        &E::SymbolToken::text_token("greetings"),
                        &E::Builder::new_string("hello"),
                    ))
                );

                assert_eq!(
                    actual.get("greetings"),
                    Some(&E::Builder::new_string("hello"))
                );
            }),
        }
    }
    // TODO add more tests to remove the separate Owned/Borrowed tests and only keep generic tests

    #[rstest]
    #[case::owned_null(null_case::<Element>())]
    #[case::borrowed_null(null_case::<ElementRef>())]
    #[case::owned_bool(bool_case::<Element>())]
    #[case::borrowed_bool(bool_case::<ElementRef>())]
    #[case::owned_i64(i64_case::<Element>())]
    #[case::borrowed_i64(i64_case::<ElementRef>())]
    #[case::owned_big_int(big_int_case::<Element>())]
    #[case::borrowed_big_int(big_int_case::<ElementRef>())]
    #[case::owned_f64(f64_case::<Element>())]
    #[case::borrowed_f64(f64_case::<ElementRef>())]
    #[case::owned_decimal(decimal_case::<Element>())]
    #[case::borrowed_decimal(decimal_case::<ElementRef>())]
    #[case::owned_timestamp(timestamp_case::<Element>())]
    #[case::borrowed_timestamp(timestamp_case::<ElementRef>())]
    #[case::owned_string(string_case::<Element>())]
    #[case::borrowed_string(string_case::<ElementRef>())]
    #[case::owned_blob(blob_case::<Element>())]
    #[case::borrowed_blob(blob_case::<ElementRef>())]
    #[case::owned_clob(clob_case::<Element>())]
    #[case::borrowed_clob(clob_case::<ElementRef>())]
    #[case::owned_list(list_case::<Element>())]
    #[case::borrowed_list(list_case::<ElementRef>())]
    #[case::owned_sexp(sexp_case::<Element>())]
    #[case::borrowed_sexp(sexp_case::<ElementRef>())]
    #[case::owned_struct(struct_case::<Element>())]
    #[case::borrowed_struct(struct_case::<ElementRef>())]
    #[case::owned_symbol(symbol_case::<Element>())]
    #[case::borrowed_symbol(symbol_case::<ElementRef>())]
    #[case::owned_symbol_with_local_sid(symbol_with_local_sid_case::<Element>())]
    #[case::borrowed_symbol_with_local_sid(symbol_with_local_sid_case::<ElementRef>())]
    fn element_accessors<E: IonElement>(#[case] input_case: Case<E>) {
        // table of negative assertions for each operation
        let neg_table: Vec<(ElemOp, &ElemAssertFunc<E>)> = vec![
            (IsNull, &|e| assert_eq!(false, e.is_null())),
            (AsBool, &|e| assert_eq!(None, e.as_bool())),
            (AsAnyInt, &|e| {
                assert_eq!(None, e.as_integer());
                assert_eq!(None, e.as_i64());
                assert_eq!(None, e.as_big_int());
            }),
            (AsF64, &|e| assert_eq!(None, e.as_f64())),
            (AsDecimal, &|e| assert_eq!(None, e.as_decimal())),
            (AsTimestamp, &|e| assert_eq!(None, e.as_timestamp())),
            (AsStr, &|e| assert_eq!(None, e.as_str())),
            (AsSym, &|e| assert_eq!(None, e.as_sym())),
            (AsBytes, &|e| assert_eq!(None, e.as_bytes())),
            (AsSequence, &|e| assert_eq!(None, e.as_sequence())),
            (AsStruct, &|e| assert_eq!(None, e.as_struct())),
        ];

        // produce the table of assertions to operate on, replacing the one specified by
        // the test case
        let valid_ops: HashSet<ElemOp> = input_case.ops.into_iter().collect();
        let op_assertions: Vec<&ElemAssertFunc<E>> = neg_table
            .into_iter()
            .filter(|(op, _)| !valid_ops.contains(op))
            .map(|(_, neg_assert)| neg_assert)
            .chain(once(input_case.op_assert.as_ref()))
            .collect();

        // construct an element to test
        assert_eq!(input_case.ion_type, input_case.elem.ion_type());

        for assert in op_assertions {
            assert(&input_case.elem);
        }

        // assert that a value element as-is is equal to itself
        assert_eq!(input_case.elem, input_case.elem);
    }
}
