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
//! use ion_rs::value::{Element, Struct};
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
//! # use ion_rs::value::{Element, Struct};
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
//! # use ion_rs::value::{Element, IntAccess, Struct};
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
//! ```
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
use std::fmt::Debug;

pub mod borrowed;
pub mod owned;
pub mod reader;
pub mod writer;

/// The shared symbol table source of a given [`SymbolToken`].
pub trait ImportSource: Debug + PartialEq {
    /// The name of the shared symbol table that the token is from.
    fn table(&self) -> &str;

    /// The ID within the shared symbol table that the token is positioned in.
    fn sid(&self) -> SymbolId;
}

/// A view of a symbolic token.
///
/// This can be either a content associated with a symbol value itself, an annotation,
/// or a field name.
///
/// A token may have `text`, a symbol `id`, both, or neither.  Optionally, a token may have
/// some shared import `source` from whence it came.
///
/// Symbol `$0`, for example, is represented with a symbol that has no `source`
/// and no `text`, and whose `local_id` is `0` (but could also have some other `local_id` implying
/// that a symbol with *unknown text* was defined in some local context.  
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
pub trait SymbolToken: Debug + PartialEq {
    type ImportSource: ImportSource + ?Sized;

    /// The text of the token, which may be `None` if no text is associated with the token
    /// (e.g. lack of a shared symbol table import for a given SID).
    fn text(&self) -> Option<&str>;

    /// The ID of the token, which may be `None` if no ID is associated with the token
    /// (e.g. Ion text symbols).
    fn local_sid(&self) -> Option<SymbolId>;

    /// The source of this token, which may be `None` if the symbol is locally defined.
    fn source(&self) -> Option<&Self::ImportSource>;

    /// Decorates the [`SymbolToken`] with text.
    fn with_text(self, text: &'static str) -> Self;

    /// Decorates the [`SymbolToken`] with a local ID.
    fn with_local_sid(self, local_sid: SymbolId) -> Self;

    /// Decorates the [`SymbolToken`] with an [`ImportSource`].
    fn with_source(self, table: &'static str, sid: SymbolId) -> Self;

    /// Constructs an [`SymbolToken`] with just text.
    /// A common case for text and synthesizing tokens.
    fn text_token(text: &'static str) -> Self;

    /// Constructs an [`SymbolToken`] with unknown text and a local ID.
    /// A common case for binary parsing (though technically relevant in text).
    fn local_sid_token(local_sid: SymbolId) -> Self;
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
pub trait Element
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
    type SymbolToken: SymbolToken + Debug + PartialEq;
    type Sequence: Sequence<Element = Self> + ?Sized + Debug + PartialEq;
    type Struct: Struct<FieldName = Self::SymbolToken, Element = Self> + ?Sized + Debug + PartialEq;
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

    /// Return an `Element` with given annotations
    fn with_annotations<I: IntoIterator<Item = Self::SymbolToken>>(self, annotations: I) -> Self;

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
pub trait Sequence: Debug + PartialEq {
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
pub trait Struct: Debug + PartialEq {
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
    type SymbolToken: SymbolToken + PartialEq;
    type Sequence: Sequence<Element = Self::Element> + ?Sized;
    type Struct: Struct<FieldName = Self::SymbolToken, Element = Self::Element> + ?Sized;
    type ImportSource: ImportSource;

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
    use crate::value::{Element, IntAccess};
    use crate::{value, IonType};
    use chrono::*;
    use rstest::*;
    use std::iter::{once, Once};

    /// Makes a timestamp from an RFC-3339 string and panics if it can't
    fn make_timestamp<T: AsRef<str>>(text: T) -> Timestamp {
        DateTime::parse_from_rfc3339(text.as_ref()).unwrap().into()
    }

    struct CaseAnnotations<E: Element> {
        elem: E,
        annotations: Vec<E::SymbolToken>,
    }

    fn annotations_text_case<E: Element>() -> CaseAnnotations<E> {
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

    fn annotations_local_sid_case<E: Element>() -> CaseAnnotations<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        CaseAnnotations {
            elem: E::Builder::new_i64(10).with_annotations(vec![
                E::SymbolToken::local_sid_token(21),
                E::SymbolToken::local_sid_token(22),
            ]),
            annotations: vec![
                E::SymbolToken::local_sid_token(21),
                E::SymbolToken::local_sid_token(22),
            ],
        }
    }

    fn annotations_source_case<E: Element>() -> CaseAnnotations<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        CaseAnnotations {
            elem: E::Builder::new_i64(10).with_annotations(vec![
                E::SymbolToken::local_sid_token(21).with_source("greetings", 1),
                E::SymbolToken::local_sid_token(22).with_source("greetings", 2),
            ]),
            annotations: vec![
                E::SymbolToken::local_sid_token(21).with_source("greetings", 1),
                E::SymbolToken::local_sid_token(22).with_source("greetings", 2),
            ],
        }
    }

    fn no_annotations_case<E: Element>() -> CaseAnnotations<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        CaseAnnotations {
            elem: E::Builder::new_i64(10),
            annotations: vec![],
        }
    }

    #[rstest]
    #[case::owned_annotations_text(annotations_text_case::<OwnedElement>())]
    #[case::borrowed_annotations_text(annotations_text_case::<BorrowedElement>())]
    #[case::owned_annotations_local_sid(annotations_local_sid_case::<OwnedElement>())]
    #[case::borrowed_annotations_local_sid(annotations_local_sid_case::<BorrowedElement>())]
    #[case::owned_annotations_source(annotations_source_case::<OwnedElement>())]
    #[case::borrowed_annotations_source(annotations_source_case::<BorrowedElement>())]
    #[case::owned_no_annotations(no_annotations_case::<OwnedElement>())]
    #[case::borrowed_no_annotations(no_annotations_case::<BorrowedElement>())]
    fn annotations_with_element<E: Element>(#[case] input: CaseAnnotations<E>) {
        let actual: Vec<&E::SymbolToken> = input.elem.annotations().map(|tok| tok).collect();
        let expected: Vec<&E::SymbolToken> = input.annotations.iter().collect();
        assert_eq!(actual, expected);
    }

    struct CaseSym<E: Element> {
        eq_annotations: Vec<E::SymbolToken>,
        ne_annotations: Vec<E::SymbolToken>,
    }

    fn sym_text_case<E: Element>() -> CaseSym<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        // SymbolTokens with same text are equivalent
        CaseSym {
            eq_annotations: vec![
                E::SymbolToken::text_token("foo"),
                E::SymbolToken::text_token("foo").with_local_sid(10),
                E::SymbolToken::text_token("foo")
                    .with_local_sid(10)
                    .with_source("greetings", 2),
            ],
            ne_annotations: vec![
                E::SymbolToken::text_token("bar"),
                E::SymbolToken::local_sid_token(10).with_source("greetings", 1),
                E::SymbolToken::local_sid_token(10).with_source("hello_table", 2),
                E::SymbolToken::local_sid_token(10),
            ],
        }
    }

    fn sym_local_sid_case<E: Element>() -> CaseSym<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        // local sids with no text are equivalent to each other and to SID $0
        CaseSym {
            eq_annotations: vec![
                E::SymbolToken::local_sid_token(200),
                E::SymbolToken::local_sid_token(100),
            ],
            ne_annotations: vec![
                E::SymbolToken::local_sid_token(200).with_source("greetings", 2),
                E::SymbolToken::text_token("foo").with_local_sid(200),
            ],
        }
    }

    fn sym_source_case<E: Element>() -> CaseSym<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        // SymbolTokens with no text are equivalent only if their source is equivalent
        CaseSym {
            eq_annotations: vec![
                E::SymbolToken::local_sid_token(200).with_source("greetings", 1),
                E::SymbolToken::local_sid_token(100).with_source("greetings", 1),
            ],
            ne_annotations: vec![
                E::SymbolToken::local_sid_token(200).with_source("greetings", 2),
                E::SymbolToken::local_sid_token(200).with_source("hello_table", 1),
                E::SymbolToken::local_sid_token(200),
                E::SymbolToken::text_token("greetings"),
                // due to the transitivity rule this is not equivalent to any member from above vector,
                // even though it has the same import source
                E::SymbolToken::local_sid_token(100)
                    .with_source("greetings", 1)
                    .with_text("foo"),
            ],
        }
    }

    /// Each case is a set of tokens that are the same, and a set of tokens that are not ever equal to the first.
    /// This should test symmetry/transitivity/commutativity
    #[rstest]
    #[case::owned_sym_text(sym_text_case::<OwnedElement>())]
    #[case::borrowed_sym_text(sym_text_case::<BorrowedElement>())]
    #[case::owned_sym_local_sid(sym_local_sid_case::<OwnedElement>())]
    #[case::borrowed_sym_local_sid(sym_local_sid_case::<BorrowedElement>())]
    #[case::owned_sym_source(sym_source_case::<OwnedElement>())]
    #[case::borrowed_sym_source(sym_source_case::<BorrowedElement>())]
    fn symbol_token_eq<E: Element>(#[case] input: CaseSym<E>) {
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

    use std::collections::HashSet;
    use std::fmt::Debug;
    use std::str::FromStr;
    use ElemOp::*;

    type ElemAssertFunc<E> = dyn Fn(&E) -> ();

    struct Case<E: Element> {
        elem: E,
        ion_type: IonType,
        ops: Vec<ElemOp>,
        op_assert: Box<dyn Fn(&E)>,
    }

    fn null_case<E: Element>() -> Case<E> {
        Case {
            elem: E::Builder::new_null(IonType::Null),
            ion_type: IonType::Null,
            ops: vec![IsNull],
            op_assert: Box::new(|e: &E| assert_eq!(true, e.is_null())),
        }
    }

    fn bool_case<E: Element>() -> Case<E> {
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

    fn i64_case<E: Element>() -> Case<E> {
        Case {
            elem: 100.into(),
            ion_type: IonType::Integer,
            ops: vec![AsAnyInt],
            op_assert: Box::new(|e: &E| {
                let expected = &E::Builder::new_i64(100);
                assert_eq!(Some(&AnyInt::I64(100)), e.as_any_int());
                assert_eq!(Some(100), e.as_i64());
                assert_eq!(None, e.as_big_int());
                assert_eq!(expected, e);
            }),
        }
    }

    fn big_int_case<E: Element>() -> Case<E> {
        Case {
            elem: BigInt::from(100).into(),
            ion_type: IonType::Integer,
            ops: vec![AsAnyInt],
            op_assert: Box::new(|e: &E| {
                let expected = &E::Builder::new_big_int(BigInt::from(100));
                assert_eq!(Some(&AnyInt::BigInt(BigInt::from(100))), e.as_any_int());
                assert_eq!(BigInt::from_str("100").unwrap(), *e.as_big_int().unwrap());
                assert_eq!(expected, e);
            }),
        }
    }

    fn f64_case<E: Element>() -> Case<E> {
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

    fn timestamp_case<E: Element>() -> Case<E> {
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

    fn decimal_case<E: Element>() -> Case<E> {
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

    fn string_case<E: Element>() -> Case<E> {
        Case {
            elem: E::Builder::new_string("hello"),
            ion_type: IonType::String,
            ops: vec![AsStr],
            op_assert: Box::new(|e: &E| assert_eq!(Some("hello"), e.as_str())),
        }
    }

    fn symbol_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_symbol(E::SymbolToken::text_token("foo").with_local_sid(10)),
            ion_type: IonType::Symbol,
            ops: vec![AsSym, AsStr],
            op_assert: Box::new(|e: &E| {
                assert_eq!(Some("foo"), e.as_sym().unwrap().text());
                assert_eq!(Some("foo"), e.as_str());
            }),
        }
    }

    fn symbol_with_local_sid_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_symbol(E::SymbolToken::local_sid_token(10)),
            ion_type: IonType::Symbol,
            ops: vec![AsSym, AsStr],
            op_assert: Box::new(|e: &E| assert_eq!(Some(10), e.as_sym().unwrap().local_sid())),
        }
    }

    fn symbol_with_import_source_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
        <<E as value::Element>::SymbolToken as value::SymbolToken>::ImportSource: Debug + PartialEq,
    {
        Case {
            elem: E::Builder::new_symbol(
                E::SymbolToken::local_sid_token(10).with_source("greetings", 1),
            ),
            ion_type: IonType::Symbol,
            ops: vec![AsSym, AsStr],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_sym();
                let expected = E::Builder::new_symbol(
                    E::SymbolToken::local_sid_token(10).with_source("greetings", 1),
                );
                let actual_source = actual.unwrap().source();
                let expected_source = expected.as_sym().unwrap().source();
                assert_eq!(expected_source, actual_source);
                assert_eq!(
                    expected_source.unwrap().table(),
                    actual_source.unwrap().table()
                );
                assert_eq!(expected_source.unwrap().sid(), actual_source.unwrap().sid());
                assert_eq!(actual, expected.as_sym());
            }),
        }
    }

    fn symbol_with_import_source_and_text_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_symbol(
                E::SymbolToken::local_sid_token(10)
                    .with_source("greetings", 1)
                    .with_text("foo"),
            ),
            ion_type: IonType::Symbol,
            ops: vec![AsSym, AsStr],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_sym();
                let expected = E::Builder::new_symbol(
                    E::SymbolToken::local_sid_token(10)
                        .with_source("greetings", 1)
                        .with_text("foo"),
                );
                assert_eq!(actual, expected.as_sym());
            }),
        }
    }

    fn blob_case<E: Element>() -> Case<E> {
        Case {
            elem: E::Builder::new_blob(b"hello"),
            ion_type: IonType::Blob,
            ops: vec![AsBytes],
            op_assert: Box::new(|e: &E| assert_eq!(Some("hello".as_bytes()), e.as_bytes())),
        }
    }

    fn clob_case<E: Element>() -> Case<E> {
        Case {
            elem: E::Builder::new_clob(b"goodbye"),
            ion_type: IonType::Clob,
            ops: vec![AsBytes],
            op_assert: Box::new(|e: &E| assert_eq!(Some("goodbye".as_bytes()), e.as_bytes())),
        }
    }

    fn list_case<E: Element>() -> Case<E> {
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

    fn sexp_case<E: Element>() -> Case<E> {
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

    fn struct_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_struct(
                vec![(
                    E::SymbolToken::text_token("greetings"),
                    E::Builder::new_string("hello"),
                )]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct().unwrap();
                assert_eq!(
                    actual.get("greetings"),
                    Some(&E::Builder::new_string("hello"))
                );
            }),
        }
    }

    fn struct_with_local_sid_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_struct(
                vec![(
                    E::SymbolToken::local_sid_token(21),
                    E::Builder::new_string("hello"),
                )]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct();
                let expected = E::Builder::new_struct(
                    vec![(
                        E::SymbolToken::local_sid_token(21),
                        E::Builder::new_string("hello"),
                    )]
                    .into_iter(),
                );
                assert_eq!(actual, expected.as_struct());
            }),
        }
    }

    // SymbolToken with local SID and no text are equivalent to each other and to SID $0
    fn struct_with_different_local_sid_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_struct(
                vec![(
                    E::SymbolToken::local_sid_token(21),
                    E::Builder::new_string("hello"),
                )]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct();
                let expected = E::Builder::new_struct(
                    vec![(
                        E::SymbolToken::local_sid_token(22),
                        E::Builder::new_string("hello"),
                    )]
                    .into_iter(),
                );
                assert_eq!(actual, expected.as_struct());
            }),
        }
    }

    fn struct_with_import_source_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_struct(
                vec![(
                    E::SymbolToken::local_sid_token(21).with_source("hello_table", 2),
                    E::Builder::new_string("hello"),
                )]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct();
                let expected = E::Builder::new_struct(
                    vec![(
                        E::SymbolToken::local_sid_token(21).with_source("hello_table", 2),
                        E::Builder::new_string("hello"),
                    )]
                    .into_iter(),
                );
                assert_eq!(actual, expected.as_struct());
            }),
        }
    }

    fn struct_with_import_source_not_equal_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_struct(
                vec![(
                    E::SymbolToken::local_sid_token(21).with_source("hello_table", 2),
                    E::Builder::new_string("hello"),
                )]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct();
                let expected = E::Builder::new_struct(
                    vec![(
                        E::SymbolToken::local_sid_token(21).with_source("hey_table", 2),
                        E::Builder::new_string("hello"),
                    )]
                    .into_iter(),
                );
                assert_ne!(actual, expected.as_struct());
            }),
        }
    }

    fn struct_with_multiple_fields_case<E: Element>() -> Case<E>
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
                        E::Builder::new_string("Ion"),
                    ),
                ]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct().unwrap();
                // expected struct has unordered struct
                let unordered_struct = E::Builder::new_struct(
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
                );
                let expected = unordered_struct.as_struct().unwrap();
                assert_eq!(actual.get("name"), expected.get("name"));
                assert_eq!(actual.get("greetings"), expected.get("greetings"));
                assert_eq!(actual, expected);
            }),
        }
    }

    fn struct_with_unordered_multiple_fields_case<E: Element>() -> Case<E>
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
                        E::Builder::new_string("Ion"),
                    ),
                ]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct().unwrap();
                // expected struct has unordered struct
                let unordered_struct = E::Builder::new_struct(
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
                );
                let expected = unordered_struct.as_struct().unwrap();
                assert_eq!(actual.get("name"), expected.get("name"));
                assert_eq!(actual.get("greetings"), expected.get("greetings"));
                assert_eq!(actual, expected);
            }),
        }
    }

    fn struct_with_multiple_fields_not_equal_case<E: Element>() -> Case<E>
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
                        E::Builder::new_string("Ion"),
                    ),
                ]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct().unwrap();
                // expected struct with different value for field name: "greetings"
                let not_equal_struct = E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::text_token("greetings"),
                            E::Builder::new_string("hey"),
                        ),
                        (
                            E::SymbolToken::text_token("name"),
                            E::Builder::new_string("Ion"),
                        ),
                    ]
                    .into_iter(),
                );
                let expected = not_equal_struct.as_struct().unwrap();
                assert_eq!(actual.get("name"), expected.get("name"));
                assert_ne!(actual.get("greetings"), expected.get("greetings"));
                assert_ne!(actual, expected);
            }),
        }
    }

    fn struct_with_text_and_duplicates_case<E: Element>() -> Case<E>
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
                        E::SymbolToken::text_token("greetings"),
                        E::Builder::new_string("world"),
                    ),
                ]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct();
                let struct_with_duplicates = E::Builder::new_struct(
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
                );
                let expected = struct_with_duplicates.as_struct();
                assert_eq!(actual, expected);
            }),
        }
    }

    fn struct_with_unordered_text_and_duplicates_case<E: Element>() -> Case<E>
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
                        E::SymbolToken::text_token("greetings"),
                        E::Builder::new_string("world"),
                    ),
                ]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct();
                let unordered_struct = E::Builder::new_struct(
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
                );
                let expected = unordered_struct.as_struct();
                assert_eq!(actual, expected);
            }),
        }
    }

    fn struct_with_unordered_no_text_and_duplicates_case<E: Element>() -> Case<E>
    where
        E::Builder: Builder<SymbolToken = E::SymbolToken>,
    {
        Case {
            elem: E::Builder::new_struct(
                vec![
                    (
                        E::SymbolToken::local_sid_token(21),
                        E::Builder::new_string("hello"),
                    ),
                    (
                        E::SymbolToken::local_sid_token(21),
                        E::Builder::new_string("world"),
                    ),
                ]
                .into_iter(),
            ),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &E| {
                let actual = e.as_struct();
                let unordered_struct = E::Builder::new_struct(
                    vec![
                        (
                            E::SymbolToken::local_sid_token(21),
                            E::Builder::new_string("world"),
                        ),
                        (
                            E::SymbolToken::local_sid_token(21),
                            E::Builder::new_string("hello"),
                        ),
                    ]
                    .into_iter(),
                );
                let expected = unordered_struct.as_struct();
                assert_eq!(actual, expected);
            }),
        }
    }
    // TODO add more tests to remove the separate Owned/Borrowed tests and only keep generic tests

    #[rstest]
    #[case::owned_null(null_case::<OwnedElement>())]
    #[case::borrowed_null(null_case::<BorrowedElement>())]
    #[case::owned_bool(bool_case::<OwnedElement>())]
    #[case::borrowed_bool(bool_case::<BorrowedElement>())]
    #[case::owned_i64(i64_case::<OwnedElement>())]
    #[case::borrowed_i64(i64_case::<BorrowedElement>())]
    #[case::owned_big_int(big_int_case::<OwnedElement>())]
    #[case::borrowed_big_int(big_int_case::<BorrowedElement>())]
    #[case::owned_f64(f64_case::<OwnedElement>())]
    #[case::borrowed_f64(f64_case::<BorrowedElement>())]
    #[case::owned_decimal(decimal_case::<OwnedElement>())]
    #[case::borrowed_decimal(decimal_case::<BorrowedElement>())]
    #[case::owned_timestamp(timestamp_case::<OwnedElement>())]
    #[case::borrowed_timestamp(timestamp_case::<BorrowedElement>())]
    #[case::owned_string(string_case::<OwnedElement>())]
    #[case::borrowed_string(string_case::<BorrowedElement>())]
    #[case::owned_blob(blob_case::<OwnedElement>())]
    #[case::borrowed_blob(blob_case::<BorrowedElement>())]
    #[case::owned_clob(clob_case::<OwnedElement>())]
    #[case::borrowed_clob(clob_case::<BorrowedElement>())]
    #[case::owned_list(list_case::<OwnedElement>())]
    #[case::borrowed_list(list_case::<BorrowedElement>())]
    #[case::owned_sexp(sexp_case::<OwnedElement>())]
    #[case::borrowed_sexp(sexp_case::<BorrowedElement>())]
    #[case::owned_struct(struct_case::<OwnedElement>())]
    #[case::borrowed_struct(struct_case::<BorrowedElement>())]
    #[case::owned_symbol(symbol_case::<OwnedElement>())]
    #[case::borrowed_symbol(symbol_case::<BorrowedElement>())]
    #[case::owned_symbol_with_local_sid(symbol_with_local_sid_case::<OwnedElement>())]
    #[case::borrowed_symbol_with_local_sid(symbol_with_local_sid_case::<BorrowedElement>())]
    #[case::owned_symbol_with_import_source(symbol_with_import_source_case::<OwnedElement>())]
    #[case::borrowed_symbol_with_import_source(symbol_with_import_source_case::<BorrowedElement>())]
    #[case::owned_symbol_with_import_source_and_text(symbol_with_import_source_and_text_case::<OwnedElement>())]
    #[case::borrowed_symbol_with_import_source_and_text(symbol_with_import_source_and_text_case::<BorrowedElement>())]
    #[case::owned_struct_with_local_sid(struct_with_local_sid_case::<OwnedElement>())]
    #[case::borrowed_struct_with_local_sid(struct_with_local_sid_case::<BorrowedElement>())]
    #[case::owned_struct_with_different_local_sid(struct_with_different_local_sid_case::<OwnedElement>())]
    #[case::borrowed_struct_with_different_local_sid(struct_with_different_local_sid_case::<BorrowedElement>())]
    #[case::owned_struct_with_import_source(struct_with_import_source_case::<OwnedElement>())]
    #[case::borrowed_struct_with_import_source(struct_with_import_source_case::<BorrowedElement>())]
    #[case::owned_struct_with_import_source_not_equal(struct_with_import_source_not_equal_case::<OwnedElement>())]
    #[case::borrowed_struct_with_import_source_not_equal(struct_with_import_source_not_equal_case::<BorrowedElement>())]
    #[case::owned_struct_with_multiple_fields(struct_with_multiple_fields_case::<OwnedElement>())]
    #[case::borrowed_struct_with_multiple_fields(struct_with_multiple_fields_case::<BorrowedElement>())]
    #[case::owned_struct_with_unordered_multiple_fields(struct_with_unordered_multiple_fields_case::<OwnedElement>())]
    #[case::borrowed_struct_with_unordered_multiple_fields(struct_with_unordered_multiple_fields_case::<BorrowedElement>())]
    #[case::owned_struct_with_multiple_fields_not_equal(struct_with_multiple_fields_not_equal_case::<OwnedElement>())]
    #[case::borrowed_struct_with_multiple_fields_not_equal(struct_with_multiple_fields_not_equal_case::<BorrowedElement>())]
    #[case::owned_struct_with_text_and_duplicates(struct_with_text_and_duplicates_case::<OwnedElement>())]
    #[case::borrowed_struct_with_text_and_duplicates(struct_with_text_and_duplicates_case::<BorrowedElement>())]
    #[case::owned_struct_with_unordered_text_and_duplicates(struct_with_unordered_text_and_duplicates_case::<OwnedElement>())]
    #[case::borrowed_struct_with_unordered_text_and_duplicates(struct_with_unordered_text_and_duplicates_case::<BorrowedElement>())]
    #[case::owned_struct_with_unordered_no_text_and_duplicates(struct_with_unordered_no_text_and_duplicates_case::<OwnedElement>())]
    #[case::borrowed_struct_with_unordered_no_text_and_duplicates(struct_with_unordered_no_text_and_duplicates_case::<BorrowedElement>())]
    fn element_accessors<E: Element>(#[case] input_case: Case<E>) {
        // table of negative assertions for each operation
        let neg_table: Vec<(ElemOp, &ElemAssertFunc<E>)> = vec![
            (IsNull, &|e| assert_eq!(false, e.is_null())),
            (AsBool, &|e| assert_eq!(None, e.as_bool())),
            (AsAnyInt, &|e| {
                assert_eq!(None, e.as_any_int());
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
