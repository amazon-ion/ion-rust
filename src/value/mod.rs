// Copyright Amazon.com, Inc. or its affiliates.

//! Provides a in-memory tree representation of Ion values that can be operated on in
//! a dynamically typed way.
//!
//! References:
//! * [`simd_json`'s `Value` API][simd-json-value]
//! * [`serde_json`'s `Value` API][serde-json-value]
//!
//! [simd-json-value]: https://docs.rs/simd-json/0.3.25/simd_json/value/index.html
//! [serde-json-value]: https://docs.serde.rs/serde_json/value/enum.Value.html

use crate::types::SymbolId;
use crate::IonType;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

pub mod borrowed;
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
    fn as_i64(&self) -> Option<i64>;

    /// Returns a reference as a [`BigInt`] if it is represented as such.  Note that this
    /// method may return `None` if the underlying representation *is not* stored in a [`BigInt`]
    /// such as if it is represented as an `i64` so it is somewhat asymmetric with respect
    /// to [`IntAccess::as_i64`].
    fn as_big_int(&self) -> Option<&BigInt>;
}

/// Container for either an integer that can fit in a 64-bit word or an arbitrarily sized
/// [`BigInt`].
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

/// Represents a either a borrowed or owned Ion datum.  There are/will be specific APIs for
/// _borrowed_ and _owned_ implementations, but this trait unifies operations on either.
pub trait Element {
    type SymbolToken: SymbolToken + ?Sized;
    type Sequence: Sequence + ?Sized;
    type Struct: Struct + ?Sized;

    /// The type of data this element represents.
    fn ion_type(&self) -> IonType;

    /// The annotations for this element.
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

    /// Returns a reference to the [`Sequence`] of this element.
    ///
    /// This will return `None` in the case that the type is not `sexp`/`list` or
    /// if the value is any `null`.
    fn as_sequence(&self) -> Option<&Self::Sequence>;

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

    // TODO add a get by index method
}

/// Represents the _value_ of `struct` of Ion elements.
pub trait Struct {
    // TODO implement me!
}

// TODO this is a placeholder until we actually fill it in!
impl Struct for () {}
