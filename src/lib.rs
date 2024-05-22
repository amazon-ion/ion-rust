#![allow(dead_code)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::bare_urls)]
// Warn if example code in the doc tests contains unused imports/variables
#![doc(test(attr(warn(unused))))]
//! # Reading and writing `Element`s
//!
//! The [Element] API offers a convenient way to read and write Ion data when its exact shape is
//! not known ahead of time.
//!
//! Each `Element` represents an `(annotations, value)` pair. If the value is a container (an Ion
//! `list`, `sexp`, or `struct`), then it will contain its own collection of `Element`s. `Element`s
//! can be nested to arbitrary depth.
//!
//! ## Constructing an `Element`
//!
//! ### From text Ion
//! The [Element::read_one] method will parse the provided data and requires that it contain exactly
//! one Ion value.
//! ```
//! # use ion_rs::IonResult;
//! # fn main() -> IonResult<()> {
//! use ion_rs::{Element, IonType};
//! let ion_data = "[1, 2, 3]";
//! let element = Element::read_one(ion_data)?;
//! assert_eq!(element.ion_type(), IonType::List);
//! # Ok(())
//! # }
//! ```
//!
//! [Element::read_all] will read any number of Ion values and return them as a `Vec<Element>`.
//!
//! [Element::read_first] will read the first Ion value without requiring that the stream have
//! exactly one value.
//!
//! ### From a Rust value
//! Most Rust primitives implement `Into<Element>`, allowing them to be converted to an Ion [Element]
//! directly.
//! ```
//! # use ion_rs::IonResult;
//! # fn main() -> IonResult<()> {
//! use ion_rs::Element;
//!
//! let int: Element = 5.into();
//! assert_eq!(Element::read_one("5")?, int);
//!
//! let boolean: Element = true.into();
//! assert_eq!(Element::read_one("true")?, boolean);
//!
//! let string: Element = "hello".into();
//! assert_eq!(Element::read_one("\"hello\"")?, string);
//!
//! let ion_version_marker: &[u8] = &[0xE0, 0x01, 0x00, 0xEA]; // Ion 1.0 version marker
//! let blob: Element = ion_version_marker.into();
//! assert_eq!(Element::read_one("{{4AEA6g==}}")?, blob);
//! # Ok(())
//! # }
//! ```
//!
//! ### Using macros
//!
//! When constructing a container [Element], you can use the [`ion_list!`], [`ion_sexp!`],
//! and [`ion_struct!`] macros.
//!
//! ```
//! # use ion_rs::IonResult;
//! # fn main() -> IonResult<()> {
//! use ion_rs::{Element, ion_list, ion_sexp, ion_struct};
//!
//! // Variable names are allowed
//! let six = 6i64;
//! let list: Element = ion_list! [true, six, "foo"].into();
//! assert_eq!(Element::read_one("[true, 6, \"foo\"]")?, list);
//!
//! // Nested use of macros is allowed
//! // Notice that ion_sexp! uses ()s without commas
//! let sexp: Element = ion_sexp! (true six ion_list!["foo", "bar"]).into();
//! assert_eq!(Element::read_one("(true 6 [\"foo\", \"bar\"])")?, sexp);
//!
//! let field_name = "bar";
//! let struct_: Element = ion_struct! {
//!   "foo": six,
//!   field_name: false
//! }.into();
//! assert_eq!(Element::read_one("{foo: 6, bar: false}")?, struct_);
//! # Ok(())
//! # }
//! ```
//!
//! ### From a stream
//!
//! ```no_run
//! # use ion_rs::IonResult;
//! # fn main() -> IonResult<()> {
//! use ion_rs::Element;
//! use std::fs::File;
//! let ion_file = File::open("/foo/bar/baz.ion").unwrap();
//! // A simple pretty-printer
//! for element in Element::iter(ion_file)? {
//!     println!("{}", element?)
//! }
//! # Ok(())
//! # }
//! ```
//!
//! ## Traversing an `Element`
//!
//! ```
//! # use ion_rs::IonResult;
//! # fn main() -> IonResult<()> {
//! use ion_rs::{Element, Value, ion_list, ion_struct};
//! let element: Element = ion_struct! {
//!   "foo": "hello",
//!   "bar": true,
//!   "baz": ion_list! [4, 5, 6]
//! }
//! .into();
//!
//! if let Value::Struct(s) = element.value() {
//!     if let Some(Value::List(l)) = s.get("baz").map(|b| b.value()) {
//!         for (index, element) in l.elements().enumerate() {
//!             println!("{}. {}", index + 1, element);
//!             // 1) 4
//!             // 2) 5
//!             // 3) 6
//!         }
//!     }
//! }
//! # Ok(())
//! # }
//! ```

// XXX this top-level import is required because of the macro factoring of rstest_reuse
// XXX Clippy incorrectly indicates that this is redundant
#[cfg(test)]
#[allow(unused_imports)]
#[allow(clippy::single_component_path_imports)]
use rstest_reuse;

// Exposed to allow benchmark comparisons between the 1.0 primitives and 1.1 primitives
pub use catalog::{Catalog, MapCatalog};
pub use element::builders::{SequenceBuilder, StructBuilder};
pub use element::{
    element_writer::ElementWriter, reader::ElementReader, Annotations, Element,
    IntoAnnotatedElement, IntoAnnotations, Sequence, Value,
};
pub use ion_data::IonData;
pub use lazy::value_ref::ValueRef;

#[doc(inline)]
pub use result::{IonError, IonResult};
pub use shared_symbol_table::SharedSymbolTable;
pub use symbol_ref::SymbolRef;
#[doc(inline)]
pub use types::{
    decimal::Decimal, Blob, Bytes, Clob, Int, IonType, List, Null, SExp, Str, Struct, Symbol,
    SymbolId, Timestamp, TimestampPrecision, UInt,
};
// Allow access to less commonly used types like decimal::coefficient::{Coefficient, Sign}
pub use types::decimal;

pub use crate::text::text_formatter::{IoFmtShim, IonValueFormatter};

// Private modules that serve to organize implementation details.
pub(crate) mod binary;
mod catalog;
mod constants;
mod ion_data;
mod raw_symbol_token_ref;
mod shared_symbol_table;
mod symbol_ref;
mod symbol_table;
mod text;

// Publicly-visible modules with nested items which users may choose to import
mod element;
pub(crate) mod result;
mod types;

mod position;
mod read_config;
#[cfg(feature = "experimental-serde")]
pub mod serde;
pub(crate) mod unsafe_helpers;

#[cfg(feature = "experimental-ion-hash")]
pub mod ion_hash;
mod lazy;
mod write_config;

#[cfg(feature = "experimental-reader-writer")]
pub use crate::{
    lazy::encoder::annotate::Annotatable, lazy::encoder::writer::Writer, lazy::reader::Reader,
    raw_symbol_token_ref::RawSymbolRef, symbol_table::SymbolTable, write_config::WriteConfig,
};

pub mod v1_0 {
    #[cfg(feature = "experimental-tooling-apis")]
    pub use crate::{
        binary::uint::DecodedUInt, binary::var_int::VarInt, binary::var_uint::VarUInt,
        lazy::binary::immutable_buffer::ImmutableBuffer,
    };

    #[cfg(feature = "experimental-reader-writer")]
    pub use crate::{
        lazy::encoder::writer::{BinaryWriter_1_0 as BinaryWriter, TextWriter_1_0 as TextWriter},
        lazy::encoding::{BinaryEncoding_1_0 as Binary, TextEncoding_1_0 as Text},
        lazy::reader::{BinaryReader_1_0 as BinaryReader, TextReader_1_0 as TextReader},
    };
}

pub mod v1_1 {
    #[cfg(feature = "experimental-tooling-apis")]
    pub use crate::{
        lazy::encoder::binary::v1_1::flex_int::FlexInt,
        lazy::encoder::binary::v1_1::flex_uint::FlexUInt,
    };

    #[cfg(feature = "experimental-reader-writer")]
    pub use crate::{
        lazy::encoder::writer::{BinaryWriter_1_1 as BinaryWriter, TextWriter_1_1 as TextWriter},
        lazy::encoding::{BinaryEncoding_1_1 as Binary, TextEncoding_1_1 as Text},
        lazy::reader::{BinaryReader_1_1 as BinaryReader, TextReader_1_1 as TextReader},
    };
}

/// Whether or not the text spacing is generous/human-friendly or something more compact.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
#[non_exhaustive]
pub enum TextKind {
    Compact,
    Lines,
    #[default]
    Pretty,
}

/// Supported Ion encodings.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Format {
    Text(TextKind),
    Binary,
    // TODO: Json(TextKind)
}
