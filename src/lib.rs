#![allow(dead_code)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::bare_urls)]
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
//! use ion_rs::element::Element;
//! use ion_rs::IonType;
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
//! use ion_rs::element::Element;
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
//! use ion_rs::element::Element;
//! use ion_rs::{ion_list, ion_sexp, ion_struct};
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
//! use ion_rs::element::reader::ElementReader;
//! use ion_rs::element::Element;
//! use ion_rs::ReaderBuilder;
//! use std::fs::File;
//! let ion_file = File::open("/foo/bar/baz.ion").unwrap();
//! let mut reader = ReaderBuilder::default().build(ion_file)?;
//! // A simple pretty-printer
//! for element in reader.elements() {
//!     println!("{}", element?)
//! }
//! # Ok(())
//! # }
//! ```
//!
//! ## Traversing an `Element`
//!
//! ```
//! use ion_rs::IonResult;
//! # fn main() -> IonResult<()> {
//! use ion_rs::element::{Element, IntoAnnotatedElement, Value};
//! use ion_rs::{ion_list, ion_struct};
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
//!
//! ## Writing an `Element` to an `io::Write`
//!
//! ```
//! use ion_rs::IonResult;
//! # fn main() -> IonResult<()> {
//! use ion_rs::element::writer::ElementWriter;
//! use ion_rs::element::{Element, IntoAnnotatedElement, Value};
//! use ion_rs::{ion_list, ion_struct, IonWriter, TextWriterBuilder};
//! let element: Element = ion_struct! {
//!   "foo": "hello",
//!   "bar": true,
//!   "baz": ion_list! [4, 5, 6]
//! }
//! .into();
//!
//! let mut buffer: Vec<u8> = Vec::new();
//! let mut writer = TextWriterBuilder::default().build(&mut buffer)?;
//! writer.write_element(&element)?;
//! writer.flush()?;
//! assert_eq!(
//!     "{foo: \"hello\", bar: true, baz: [4, 5, 6]}".as_bytes(),
//!     writer.output().as_slice()
//! );
//! # Ok(())
//! # }
//! ```

// This import is used in the doc comments and test code above. Clippy incorrectly
// declares it an unused import.
#[allow(unused_imports)]
use element::Element;

pub mod result;

pub mod binary;
pub mod data_source;
pub mod element;
pub mod raw_reader;
pub mod text;
pub mod types;

mod ion_data;
#[cfg(feature = "ion-hash")]
pub mod ion_hash;

mod blocking_reader;
mod catalog;
// Public as a workaround for: https://github.com/amazon-ion/ion-rust/issues/484
pub mod constants;
mod raw_symbol_token;
mod raw_symbol_token_ref;
// Public as a workaround for: https://github.com/amazon-ion/ion-rust/issues/484
pub mod reader;
mod shared_symbol_table;
mod stream_reader;
mod symbol_ref;
mod symbol_table;
mod system_reader;
mod writer;

#[cfg(feature = "experimental-lazy-reader")]
pub mod lazy;

#[cfg(feature = "experimental-streaming")]
pub(crate) mod thunk;

#[doc(inline)]
pub use data_source::IonDataSource;
#[doc(inline)]
pub use raw_symbol_token::RawSymbolToken;
#[doc(inline)]
pub use raw_symbol_token_ref::RawSymbolTokenRef;

pub use symbol_ref::SymbolRef;
pub use symbol_table::SymbolTable;

pub use types::{Decimal, Int, IonType, Str, Symbol, Timestamp};

pub use ion_data::IonData;

pub use binary::binary_writer::{BinaryWriter, BinaryWriterBuilder};
pub use text::text_writer::{TextWriter, TextWriterBuilder};
pub use writer::IonWriter;

pub use binary::raw_binary_writer::RawBinaryWriter;
pub use blocking_reader::{BlockingRawBinaryReader, BlockingRawReader, BlockingRawTextReader};
pub use raw_reader::{RawReader, RawStreamItem};
pub use reader::{Reader, ReaderBuilder, StreamItem, UserReader};
pub use stream_reader::IonReader;
pub use system_reader::{SystemReader, SystemStreamItem};
pub use text::raw_text_writer::{RawTextWriter, RawTextWriterBuilder};

pub use result::{IonError, IonResult};

/// Re-exports of third party dependencies that are part of our public API.
///
/// See also: <https://github.com/amazon-ion/ion-rust/issues/302>
pub mod external {
    pub use bigdecimal;
}
