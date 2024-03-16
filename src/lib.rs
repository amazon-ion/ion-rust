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

// Private modules that serve to organize implementation details.
mod binary;
mod blocking_reader;
mod catalog;
mod constants;
mod data_source;
mod ion_data;
mod ion_reader;
mod ion_writer;
mod raw_reader;
mod raw_symbol_token;
mod raw_symbol_token_ref;
mod reader;
mod shared_symbol_table;
mod symbol_ref;
mod symbol_table;
mod system_reader;
mod text;

// Publicly-visible modules with nested items which users may choose to import
mod element;
pub mod result;
mod types;

#[cfg(feature = "experimental-ion-hash")]
pub mod ion_hash;

#[cfg(feature = "experimental-lazy-reader")]
pub mod lazy;
// Experimental Streaming APIs
mod position;
#[cfg(feature = "experimental-serde")]
pub mod serde;
pub(crate) mod unsafe_helpers;

pub use catalog::{Catalog, MapCatalog};
pub use element::builders::{SequenceBuilder, StructBuilder};
pub use element::{
    reader::ElementReader, writer::ElementWriter, Annotations, Element, IntoAnnotatedElement,
    IntoAnnotations, Sequence, Value,
};
pub use ion_data::IonData;
pub use shared_symbol_table::SharedSymbolTable;
pub use symbol_ref::SymbolRef;
#[doc(inline)]
pub use types::{
    decimal::Decimal, Blob, Bytes, Clob, Int, IonType, List, Null, SExp, Str, Struct, Symbol,
    SymbolId, Timestamp, TimestampPrecision, UInt,
};

// Allow access to less commonly used types like decimal::coefficient::{Coefficient, Sign}
pub use types::decimal;

// These re-exports are only visible if the "experimental-reader" feature is enabled.
#[cfg(feature = "experimental-reader")]
pub use {
    binary::non_blocking::raw_binary_reader::RawBinaryReader,
    blocking_reader::{BlockingRawBinaryReader, BlockingRawReader, BlockingRawTextReader},
    ion_reader::IonReader,
    raw_reader::{BufferedRawReader, RawReader, RawStreamItem},
    raw_symbol_token::RawSymbolToken,
    raw_symbol_token_ref::RawSymbolTokenRef,
    // Public as a workaround for: https://github.com/amazon-ion/ion-rust/issues/484
    reader::integration_testing,
    reader::{Reader, ReaderBuilder, StreamItem, UserReader},
    symbol_table::SymbolTable,
    system_reader::{SystemReader, SystemStreamItem},
    text::non_blocking::raw_text_reader::RawTextReader,
    text::raw_text_writer::{RawTextWriter, RawTextWriterBuilder},
};

// These re-exports are only visible if the "experimental-writer" feature is enabled.
#[cfg(feature = "experimental-writer")]
pub use {
    binary::binary_writer::{BinaryWriter, BinaryWriterBuilder},
    binary::raw_binary_writer::RawBinaryWriter,
    ion_writer::IonWriter,
    text::text_writer::{TextWriter, TextWriterBuilder},
};

// Exposed to allow benchmark comparisons between the 1.0 primitives and 1.1 primitives
#[cfg(feature = "experimental-lazy-reader")]
pub use {
    binary::int::DecodedInt, binary::non_blocking::type_descriptor::Header,
    binary::uint::DecodedUInt, binary::var_int::VarInt, binary::var_uint::VarUInt,
    element::writer::WriteConfig, lazy::binary::immutable_buffer::ImmutableBuffer,
    lazy::encoder::binary::v1_1::flex_int::FlexInt,
    lazy::encoder::binary::v1_1::flex_uint::FlexUInt,
};

#[doc(inline)]
pub use result::{IonError, IonResult};

/// Whether or not the text spacing is generous/human-friendly or something more compact.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum TextKind {
    Compact,
    Lines,
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
