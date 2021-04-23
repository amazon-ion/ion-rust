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
//! * The [`loader`] module provides API and implementation to load Ion data into [`Element`]
//!   instances.
//!
//! ## Examples
//! In general, users will use the [`loader::Loader`] trait to load in data:
//!
//! ```
//! use ion_rs::IonType;
//! use ion_rs::result::IonResult;
//! use ion_rs::value::{Element, Struct};
//! use ion_rs::value::loader::loader;
//! use ion_rs::value::loader::Loader;
//!
//! fn main() -> IonResult<()> {
//!     let mut iter = loader().iterate_over(br#""hello!"#)?;
//!     if let Some(Ok(elem)) = iter.next() {
//!         assert_eq!(IonType::String, elem.ion_type());
//!         assert_eq!("hello!", elem.as_str().unwrap());
//!     }
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
//! use ion_rs::value::SymbolToken;
//! use ion_rs::value::borrowed::BorrowedSymbolToken;
//! use ion_rs::value::owned::OwnedSymbolToken;
//!
//! fn extract_text<T: SymbolToken>(tok: &T) -> String {
//!     tok.text().unwrap().into()
//! }
//!
//! let owned_token: OwnedSymbolToken = "hello".into();
//!
//! // owned value to emphasize lifetime
//! let text = String::from("hello");
//! let borrowed_token: BorrowedSymbolToken = text.as_str().into();
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
//! use ion_rs::value::{Element, SymbolToken};
//! use ion_rs::value::borrowed::{BorrowedValue, BorrowedElement, local_sid_token as borrowed_local_sid_token, text_token as borrowed_text_token};
//! use ion_rs::value::owned::{OwnedValue, OwnedElement, local_sid_token as owned_local_sid_token, text_token as owned_text_token};
//!
//! fn extract_annotations<T: Element>(elem: &T) -> Vec<Option<String>> {
//!     elem.annotations().map(
//!         |tok| tok.text().map(|text_ref| text_ref.to_string())
//!     ).collect()
//! }
//!
//! let owned_elem = OwnedElement::new(
//!     vec![
//!         owned_local_sid_token(300).with_source("foo", 12),
//!         owned_text_token("hello")
//!     ],
//!     OwnedValue::String("world".into())
//! );
//!
//! // owned values to emphasize lifetime
//! let strings: Vec<String> =
//!     vec!["hello", "world"].iter().map(|x| x.to_string()).collect();
//! let borrowed_elem = BorrowedElement::new(
//!     vec![
//!         borrowed_local_sid_token(200).with_source("bar", 9),
//!         borrowed_text_token(&strings[0])
//!     ],
//!     BorrowedValue::String(&strings[1])
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

use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::IonType;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

pub mod borrowed;
pub mod loader;
pub mod owned;

/// The shared symbol table source of a given [`SymbolToken`].
pub trait ImportSource {
    /// The name of the shared symbol table that the token is from.
    fn table(&self) -> &str;

    /// The ID within the shared symbol table that the token is positioned in.
    fn sid(&self) -> SymbolId;
}

/// A view of a symbolic token.
/// This can be either a symbol value itself, an annotation, or an field name.
/// A token may have `text`, a symbol `id`, or both.
/// here text as `None` represents SID $0
///
/// ## `PartialEq` Implementation Notes
/// Implementations of [`SymbolToken`] that implement [`PartialEq`] should do so without
/// violating the transitivity rule of [`PartialEq`].  Specifically, this means that
/// one cannot use [`PartialEq`] to implement the [Ion data model][symbol-data-model]
/// definition of equivalence for symbolic tokens.
///
/// Consider the following pseudo-code describing Ion data model semantics:
///
/// ```plain
///     //   (<text>, <local id>, <source>)
///     
///     a := (nil, 200, ("my_table", 1))
///     b := ("foobar", 200, ("my_table", 1))
///     c := ("foobar", nil, nil)
///
///     a == b, b == a // true -- source matches
///     b == c, c == b // true -- text matches
///
///     a == c         // false - text + no source != no text with source
/// ```
///
/// The problem above is that `a != c` violates the contract for `PartialEq` as equality
/// must be *transitive*.
///
/// A reasonable definition for [`PartialEq`] is that any symbol with text is equal to
/// any other symbol with text, but in the case that a symbol does not have text,
/// it is equal to another symbol if and only if that symbol does not have text and
/// the source is the same.
///
/// In practice the above difference from the [Ion data model][symbol-data-model]
/// should only affect esoteric use cases of the API.  For example, a use case where
/// data is read from a context in which a shared symbol table is not available and
/// is mixed with data was resolved with the shared symbol table being present.
/// Such a context implies more than one symbol table catalog in use by an application
/// which is not a typical (but certainly valid) usage pattern.
///
/// [symbol-data-model]: https://amzn.github.io/ion-docs/docs/symbols.html#data-model
pub trait SymbolToken {
    type ImportSource: ImportSource + ?Sized;

    /// The text of the token, which may be `None` if no text is associated with the token
    /// (e.g. lack of a shared symbol table import for a given SID).
    fn text(&self) -> Option<&str>;

    /// The ID of the token, which may be `None` if no ID is associated with the token
    /// (e.g. Ion text symbols).
    fn local_sid(&self) -> Option<SymbolId>;

    /// The source of this token, which may be `None` if the symbol is locally defined.
    fn source(&self) -> Option<&Self::ImportSource>;
}

/// Provides convenient integer accessors for integer values that are like [`AnyInt`]
pub trait IntAccess {
    /// Returns the value as an `i64` if it can be represented as such.
    ///
    /// ## Usage
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::owned::*;
    /// # use ion_rs::value::borrowed::*;
    /// # use num_bigint::*;
    /// let big_any = AnyInt::BigInt(BigInt::from(100));
    /// let i64_any = AnyInt::I64(100);
    /// assert_eq!(big_any.as_i64(), i64_any.as_i64());
    ///
    /// // works on element too
    /// let big_elem: OwnedElement = OwnedValue::Integer(big_any).into();
    /// let i64_elem: BorrowedElement = BorrowedValue::Integer(i64_any).into();
    ///
    /// assert_eq!(big_elem.as_i64(), i64_elem.as_i64());
    /// ```
    fn as_i64(&self) -> Option<i64>;

    /// Returns a reference as a [`BigInt`] if it is represented as such.  Note that this
    /// method may return `None` if the underlying representation *is not* stored in a [`BigInt`]
    /// such as if it is represented as an `i64` so it is somewhat asymmetric with respect
    /// to [`IntAccess::as_i64`].
    ///
    /// ## Usage
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::owned::*;
    /// # use ion_rs::value::borrowed::*;
    /// # use num_bigint::*;
    /// # use std::str::FromStr;
    /// let big_any = AnyInt::BigInt(BigInt::from(100));
    /// assert_eq!(BigInt::from_str("100").unwrap(), *big_any.as_big_int().unwrap());
    /// let i64_any = AnyInt::I64(100);
    /// assert_eq!(None, i64_any.as_big_int());
    ///
    /// // works on element too
    /// let big_elem: BorrowedElement = BorrowedValue::Integer(big_any).into();
    /// assert_eq!(BigInt::from_str("100").unwrap(), *big_elem.as_big_int().unwrap());
    /// let i64_elem: OwnedElement = OwnedValue::Integer(i64_any).into();
    /// assert_eq!(None, i64_elem.as_big_int());
    /// ```
    fn as_big_int(&self) -> Option<&BigInt>;
}

/// Container for either an integer that can fit in a 64-bit word or an arbitrarily sized
/// [`BigInt`].
///
/// See [`IntAccess`] for common operations.
#[derive(Debug, Clone)]
pub enum AnyInt {
    I64(i64),
    BigInt(BigInt),
}

impl IntAccess for AnyInt {
    #[inline]
    fn as_i64(&self) -> Option<i64> {
        match &self {
            AnyInt::I64(i) => Some(*i),
            AnyInt::BigInt(big) => big.to_i64(),
        }
    }

    #[inline]
    fn as_big_int(&self) -> Option<&BigInt> {
        match &self {
            AnyInt::I64(_) => None,
            AnyInt::BigInt(big) => Some(big),
        }
    }
}

impl PartialEq for AnyInt {
    fn eq(&self, other: &Self) -> bool {
        use AnyInt::*;
        match self {
            I64(my_i64) => match other {
                I64(other_i64) => my_i64 == other_i64,
                BigInt(other_bi) => Some(*my_i64) == other_bi.to_i64(),
            },
            BigInt(my_bi) => match other {
                I64(other_i64) => my_bi.to_i64() == Some(*other_i64),
                BigInt(other_bi) => my_bi == other_bi,
            },
        }
    }
}

impl Eq for AnyInt {}

/// Represents a either a borrowed or owned Ion datum.  There are/will be specific APIs for
/// _borrowed_ and _owned_ implementations, but this trait unifies operations on either.
pub trait Element {
    type SymbolToken: SymbolToken + ?Sized;
    type Sequence: Sequence<Element = Self> + ?Sized;
    type Struct: Struct<FieldName = Self::SymbolToken, Element = Self> + ?Sized;
    type Builder: Builder<Element = Self> + ?Sized;

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
    /// fn annotation_strings<T: Element>(elem: &T) -> Vec<String> {
    ///     elem.annotations().map(|tok| tok.text().unwrap().into()).collect()
    /// }
    ///
    /// let strs = vec!["a", "b", "c"];
    /// let owned_elem = OwnedElement::new(
    ///     strs.iter().map(|s| (*s).into()).collect(),
    ///     OwnedValue::String("moo".into())
    /// );
    /// let borrowed_elem = BorrowedElement::new(
    ///     strs.iter().map(|s| (*s).into()).collect(),
    ///     BorrowedValue::String("moo")
    /// );
    ///
    /// let expected: Vec<String> = strs.iter().map(|s| (*s).into()).collect();
    /// assert_eq!(expected, annotation_strings(&owned_elem));
    /// assert_eq!(expected, annotation_strings(&borrowed_elem));
    /// ```
    ///
    /// Note that this uses a `Box<dyn Iterator<...>>` to capture the borrow cleanly without
    /// without [generic associated types (GAT)][gat].  In theory, when GAT lands, this could
    /// be replaced with static polymorphism.
    ///
    /// [gat]: https://rust-lang.github.io/rfcs/1598-generic_associated_types.html
    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::SymbolToken> + 'a>;

    /// Returns whether this element is a `null` value
    fn is_null(&self) -> bool;

    /// Returns a reference to the underlying [`AnyInt`] for this element.
    ///
    /// This will return `None` if the type is not `int` or the value is any `null`.
    fn as_any_int(&self) -> Option<&AnyInt>;

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

impl<T> IntAccess for T
where
    T: Element,
{
    fn as_i64(&self) -> Option<i64> {
        match self.as_any_int() {
            Some(any) => any.as_i64(),
            _ => None,
        }
    }

    fn as_big_int(&self) -> Option<&BigInt> {
        match self.as_any_int() {
            Some(any) => any.as_big_int(),
            _ => None,
        }
    }
}

/// Represents the _value_ of sequences of Ion elements (i.e. `list` and `sexp`).
pub trait Sequence {
    type Element: Element + ?Sized;

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
pub trait Struct {
    type FieldName: SymbolToken + ?Sized;
    type Element: Element + ?Sized;

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
    /// let fields: Vec<(&str, BorrowedValue)>= vec![("e", "f"), ("g", "h")]
    ///     .into_iter().map(|(k, v)| (k, BorrowedValue::String(v))).collect();
    /// let borrowed: BorrowedStruct = fields.into_iter().collect();
    /// assert_eq!("h", borrowed.get("g".to_string()).map(|e| e.as_str()).flatten().unwrap());
    /// ```
    ///
    /// Using the [owned] API:
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::owned::*;
    /// let fields: Vec<(&str, OwnedValue)>= vec![("a", "b"), ("c", "d")]
    ///     .into_iter().map(|(k, v)| (k, OwnedValue::String(v.into()))).collect();
    /// let owned: OwnedStruct = fields.into_iter().collect();
    /// assert_eq!("d", owned.get("c".to_string()).map(|e| e.as_str()).flatten().unwrap());
    /// ```
    fn get<T: AsRef<str>>(&self, field_name: T) -> Option<&Self::Element>;

    /// Returns an iterator with all the values corresponding to the field_name in the struct or
    /// returns an empty iterator if the field_name does not exist in the struct
    ///
    /// ## Usage
    /// Using the [borrowed] API:
    /// ```
    /// # use ion_rs::value::*;
    /// # use ion_rs::value::borrowed::*;
    /// let fields: Vec<(&str, BorrowedValue)>= vec![("a", "b"), ("c", "d"), ("c", "e")]
    ///     .into_iter().map(|(k, v)| (k, BorrowedValue::String(v))).collect();
    /// let borrowed: BorrowedStruct = fields.into_iter().collect();
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
    /// let fields: Vec<(&str, OwnedValue)>= vec![("d", "e"), ("d", "f"), ("g", "h")]
    ///     .into_iter().map(|(k, v)| (k, OwnedValue::String(v.into()))).collect();
    /// let owned: OwnedStruct = fields.into_iter().collect();
    /// assert_eq!(
    ///     vec!["e", "f"],
    ///     owned.get_all("d").flat_map(|e| e.as_str()).collect::<Vec<&str>>()
    /// );
    /// ```
    fn get_all<'a, T: AsRef<str>>(
        &'a self,
        field_name: T,
    ) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a>;
}

pub trait Builder {
    type Element: Element + ?Sized;
    type Sequence: Sequence<Element = Self::Element> + ?Sized;

    /// Build a `null` from IonType using Builder
    fn new_null(e_type: IonType) -> Self::Element;

    /// Build a `clob` using Builder
    fn new_clob(bytes: &'static [u8]) -> Self::Element;

    /// Build a `blob` using Builder
    fn new_blob(bytes: &'static [u8]) -> Self::Element;

    /// Build a `list` from Sequence using Builder
    fn new_list(seq: Self::Sequence) -> Self::Element;

    /// Build a `sexp` from Sequence using Builder
    fn new_sexp(seq: Self::Sequence) -> Self::Element;
}
