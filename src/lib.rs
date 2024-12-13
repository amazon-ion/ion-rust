#![allow(dead_code)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::bare_urls)]
#![deny(rust_2018_idioms)]
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
//! [Element::read_all] will read any number of Ion values and return them as a [`Sequence`].
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
pub use catalog::{Catalog, EmptyCatalog, MapCatalog};
pub use element::builders::{SequenceBuilder, StructBuilder};
pub use element::{
    element_writer::ElementWriter, reader::ElementReader, Annotations, Element,
    IntoAnnotatedElement, IntoAnnotations, OwnedSequenceIterator, Sequence, Value,
};
pub use ion_data::IonData;

#[doc(inline)]
pub use result::{ConversionOperationError, ConversionOperationResult, IonError, IonResult};
pub use shared_symbol_table::SharedSymbolTable;
pub use symbol_ref::SymbolRef;
#[doc(inline)]
pub use types::{
    decimal::Decimal, Blob, Bytes, Clob, Int, IonType, List, Null, SExp, Str, Struct, Symbol,
    SymbolId, Timestamp, TimestampPrecision, UInt,
};
// Allow access to less commonly used types like decimal::coefficient::{Coefficient, Sign}
pub use types::decimal;

#[cfg(feature = "experimental-tooling-apis")]
pub use crate::text::text_formatter::{FmtValueFormatter, IoValueFormatter};

// Private modules that serve to organize implementation details.
pub(crate) mod binary;
pub(crate) mod catalog;
pub(crate) mod constants;
mod ion_data;
mod raw_symbol_ref;
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
pub(crate) mod lazy;
mod write_config;

pub use crate::lazy::any_encoding::AnyEncoding;
pub use crate::lazy::decoder::{HasRange, HasSpan};
pub use crate::lazy::span::Span;
macro_rules! v1_x_reader_writer {
    ($visibility:vis) => {
       #[allow(unused_imports)]
        $visibility use crate::{
            lazy::streaming_raw_reader::{IonInput, IonSlice, IonStream},
            lazy::decoder::Decoder,
            lazy::encoder::Encoder,
            lazy::encoding::Encoding,
            lazy::encoder::annotate::Annotatable,
            lazy::encoder::write_as_ion::WriteAsIon,
            lazy::encoder::writer::Writer,
            lazy::reader::Reader,
            raw_symbol_ref::RawSymbolRef,
            symbol_table::SymbolTable,
            lazy::value::LazyValue,
            lazy::value_ref::ValueRef,
            lazy::r#struct::{LazyStruct, LazyField},
            lazy::sequence::{LazyList, LazySExp},
            lazy::encoder::value_writer::{ValueWriter, ContextWriter, StructWriter, SequenceWriter, EExpWriter},
            lazy::any_encoding::IonEncoding,
            lazy::expanded::compiler::TemplateCompiler,
            lazy::expanded::template::TemplateMacro,
            lazy::expanded::template::TemplateBodyExpr,
            lazy::expanded::template::TemplateBodyExprKind,
            lazy::expanded::macro_table::Macro,
            lazy::expanded::macro_evaluator::MacroEvaluator,
            lazy::expanded::macro_evaluator::MacroExpansionKind,
            lazy::expanded::macro_table::MacroKind,
            lazy::expanded::macro_table::MacroTable,
            lazy::expanded::EncodingContext,
            lazy::any_encoding::IonVersion,
            lazy::binary::raw::reader::LazyRawBinaryReader_1_0,
            lazy::binary::raw::v1_1::reader::LazyRawBinaryReader_1_1,
            lazy::expanded::macro_evaluator::RawEExpression,
            lazy::expanded::macro_evaluator::ValueExpr,
            lazy::expanded::macro_evaluator::MacroExpr,
            lazy::expanded::macro_evaluator::MacroExprKind,
        };
    };
}

pub use crate::write_config::WriteConfig;

macro_rules! v1_0_reader_writer {
    ($visibility:vis) => {
        #[allow(unused_imports)]
        $visibility use crate::{
            lazy::encoder::writer::{BinaryWriter_1_0 as BinaryWriter, TextWriter_1_0 as TextWriter},
        };
    };
}

macro_rules! v1_1_reader_writer {
    ($visibility:vis) => {
        #[allow(unused_imports)]
        $visibility use crate::{
            lazy::encoder::writer::{BinaryWriter_1_1 as BinaryWriter, TextWriter_1_1 as TextWriter},
            lazy::encoding::{BinaryEncoding_1_1 as Binary, TextEncoding_1_1 as Text},
        };
    };
}

macro_rules! v1_x_tooling_apis {
    ($visibility:vis) => {
        #[allow(unused_imports)]
        $visibility use crate::{
            lazy::raw_stream_item::RawStreamItem,
            lazy::any_encoding::{
                LazyRawAnyVersionMarker, LazyRawAnyVersionMarkerKind,
                LazyRawAnyValue, LazyRawValueKind,
                LazyRawAnyList, LazyRawListKind,
                LazyRawAnySExp, LazyRawSExpKind,
                LazyRawAnyStruct, LazyRawStructKind,
                LazyRawAnyFieldName, LazyRawFieldNameKind,
                LazyRawAnyEExpression, LazyRawAnyEExpressionKind,
            },
            lazy::decoder::{
                LazyRawSequence,
                LazyRawStruct,
                LazyRawFieldExpr,
                LazyRawFieldName,
                LazyRawValue,
                LazyRawReader,
                RawVersionMarker,
                LazyRawContainer,
            },
            lazy::encoder::{
                LazyRawWriter,
            },
            lazy::encoder::value_writer_config::{
                ValueWriterConfig,
                ContainerEncoding,
                SymbolValueEncoding,
                AnnotationsEncoding,
                FieldNameEncoding,
            },
            lazy::expanded::r#struct::{
                LazyExpandedStruct, ExpandedStructSource,
                LazyExpandedField,
                LazyExpandedFieldName
            },
            lazy::expanded::e_expression::{EExpression, EExpressionArgsIterator, EExpArgGroup, EExpArgGroupIterator},
            lazy::expanded::sequence::{Environment, ExpandedListSource, ExpandedSExpSource, LazyExpandedList, LazyExpandedSExp},
            lazy::expanded::{ExpandedStreamItem, LazyExpandedValue, ExpandingReader, ExpandedValueSource, ExpandedAnnotationsSource, ExpandedValueRef},
            lazy::system_stream_item::SystemStreamItem,
            lazy::system_reader::{SystemReader},
        };
    };
}

macro_rules! v1_0_tooling_apis {
    ($visibility:vis) => {
        #[allow(unused_imports)]
        $visibility use crate::{
            binary::uint::DecodedUInt,
            binary::var_int::VarInt,
            binary::var_uint::VarUInt,
            lazy::binary::immutable_buffer::{BinaryBuffer, AnnotationsWrapper},
            lazy::binary::raw::type_descriptor::Header,
            lazy::raw_value_ref::RawValueRef,
            lazy::encoder::binary::v1_0::writer::LazyRawBinaryWriter_1_0 as RawBinaryWriter,
            lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0 as RawTextWriter,
            lazy::binary::raw::sequence::{
                LazyRawBinaryList_1_0 as LazyRawBinaryList,
                LazyRawBinarySExp_1_0 as LazyRawBinarySExp
            },
            lazy::binary::raw::r#struct::{LazyRawBinaryStruct_1_0 as LazyRawBinaryStruct, LazyRawBinaryFieldName_1_0 as LazyRawBinaryFieldName},
            lazy::binary::raw::value::{
                EncodedBinaryValue,
                LazyRawBinaryValue_1_0 as LazyRawBinaryValue,
                LazyRawBinaryVersionMarker_1_0 as LazyRawBinaryVersionMarker,
                EncodedBinaryValueData_1_0 as EncodedBinaryValueData,
                EncodedBinaryAnnotations_1_0 as EncodedBinaryAnnotations
            },
        };
    };
}

macro_rules! v1_1_tooling_apis {
    ($visibility:vis) => {
        #[allow(unused_imports)]
        $visibility use crate::{
            lazy::encoder::binary::v1_1::flex_int::FlexInt,
            lazy::encoder::binary::v1_1::flex_uint::FlexUInt,
            lazy::encoder::binary::v1_1::writer::LazyRawBinaryWriter_1_1 as RawBinaryWriter,
            lazy::encoder::text::v1_1::writer::LazyRawTextWriter_1_1 as RawTextWriter,
            lazy::binary::raw::v1_1::sequence::{
                LazyRawBinaryList_1_1 as LazyRawBinaryList,
                LazyRawBinarySExp_1_1 as LazyRawBinarySExp
            },
            lazy::binary::raw::v1_1::r#struct::{LazyRawBinaryStruct_1_1 as LazyRawBinaryStruct, LazyRawBinaryFieldName_1_1 as LazyRawBinaryFieldName},
            lazy::binary::raw::v1_1::value::{
                LazyRawBinaryValue_1_1 as LazyRawBinaryValue,
                LazyRawBinaryVersionMarker_1_1 as LazyRawBinaryVersionMarker,
            },
        };
    };
}

#[cfg(feature = "experimental-reader-writer")]
v1_x_reader_writer!(pub);

#[cfg(not(feature = "experimental-reader-writer"))]
v1_x_reader_writer!(pub(crate));

#[cfg(feature = "experimental-tooling-apis")]
v1_x_tooling_apis!(pub);

#[cfg(not(feature = "experimental-tooling-apis"))]
v1_x_tooling_apis!(pub(crate));

pub mod v1_0 {
    #[cfg(feature = "experimental-tooling-apis")]
    v1_0_tooling_apis!(pub);

    #[cfg(not(feature = "experimental-tooling-apis"))]
    v1_0_tooling_apis!(pub(crate));

    #[cfg(feature = "experimental-reader-writer")]
    v1_0_reader_writer!(pub);

    #[cfg(not(feature = "experimental-reader-writer"))]
    v1_0_reader_writer!(pub(crate));

    pub use crate::lazy::encoding::{BinaryEncoding_1_0 as Binary, TextEncoding_1_0 as Text};
}

#[cfg(feature = "experimental-ion-1-1")]
pub mod v1_1 {
    pub use crate::constants::v1_1::constants;
    pub use crate::constants::v1_1::system_symbols;

    #[cfg(feature = "experimental-tooling-apis")]
    v1_1_tooling_apis!(pub);

    #[cfg(not(feature = "experimental-tooling-apis"))]
    v1_1_tooling_apis!(pub(crate));

    #[cfg(feature = "experimental-reader-writer")]
    v1_1_reader_writer!(pub);

    #[cfg(not(feature = "experimental-reader-writer"))]
    v1_1_reader_writer!(pub(crate));
}

#[cfg(not(feature = "experimental-ion-1-1"))]
pub(crate) mod v1_1 {
    #[cfg(feature = "experimental-tooling-apis")]
    v1_1_tooling_apis!(pub);

    #[cfg(not(feature = "experimental-tooling-apis"))]
    v1_1_tooling_apis!(pub(crate));

    #[cfg(feature = "experimental-reader-writer")]
    v1_1_reader_writer!(pub);

    #[cfg(not(feature = "experimental-reader-writer"))]
    v1_1_reader_writer!(pub(crate));
}

/// Whether or not the text spacing is generous/human-friendly or something more compact.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
#[non_exhaustive]
pub enum TextFormat {
    Compact,
    Lines,
    #[default]
    Pretty,
}

/// Supported Ion encodings.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Format {
    Text(TextFormat),
    Binary,
    // TODO: Json(TextKind)
}

/// Early returns `Some(Err(_))` if the provided expression returns an `Err(_)`.
///
/// Acts as an ersatz `?` operator in methods that return `Option<IonResult<T>>`.
macro_rules! try_or_some_err {
    ($expr:expr) => {
        match $expr {
            Ok(v) => v,
            Err(e) => return Some(Err(e)),
        }
    };
}

pub(crate) use try_or_some_err;

/// Tries to get the next value from an expression of type `Option<Result<_>>`, early returning if
/// the expression is `None` or `Some(Err(_))`. This is useful in the context of iterator
/// implementations that produce an `Option<Result>>` and so cannot easily use the `?` operator.
///
/// If the expression evaluates to `None`, early returns `None`.
/// If the expression evaluates to `Some(Err(e))`, early returns `Some(Err(e))`.
/// If the expression evaluates to `Some(Ok(value))`, evaluates to `value`.
macro_rules! try_next {
    ($expr:expr) => {
        match $expr {
            Some(Ok(v)) => v,
            None => return None,
            Some(Err(e)) => return Some(Err(e)),
        }
    };
}

pub(crate) use try_next;
