#![allow(non_camel_case_types)]

use std::fmt::Debug;
use std::io;

use crate::lazy::any_encoding::LazyRawAnyValue;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::{LazyRawBinaryFieldName_1_0, LazyRawBinaryStruct_1_0};
use crate::lazy::binary::raw::reader::LazyRawBinaryReader_1_0;
use crate::lazy::binary::raw::sequence::{LazyRawBinaryList_1_0, LazyRawBinarySExp_1_0};
use crate::lazy::binary::raw::v1_1::r#struct::LazyRawBinaryFieldName_1_1;
use crate::lazy::binary::raw::v1_1::reader::LazyRawBinaryReader_1_1;
use crate::lazy::binary::raw::v1_1::value::LazyRawBinaryVersionMarker_1_1;
use crate::lazy::binary::raw::v1_1::{
    r#struct::LazyRawBinaryStruct_1_1,
    sequence::{LazyRawBinaryList_1_1, LazyRawBinarySExp_1_1},
    value::LazyRawBinaryValue_1_1,
    RawBinaryAnnotationsIterator_1_1,
};
use crate::lazy::binary::raw::value::{LazyRawBinaryValue_1_0, LazyRawBinaryVersionMarker_1_0};
use crate::lazy::decoder::Decoder;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::Encoder;
use crate::lazy::never::Never;
use crate::lazy::text::raw::r#struct::{LazyRawTextFieldName_1_0, LazyRawTextStruct_1_0};
use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
use crate::lazy::text::raw::sequence::{LazyRawTextList_1_0, LazyRawTextSExp_1_0};
use crate::lazy::text::raw::v1_1::reader::{
    LazyRawTextFieldName_1_1, LazyRawTextList_1_1, LazyRawTextReader_1_1, LazyRawTextSExp_1_1,
    LazyRawTextStruct_1_1, RawTextEExpression_1_1,
};
use crate::lazy::text::value::{
    LazyRawTextValue, LazyRawTextValue_1_0, LazyRawTextValue_1_1, LazyRawTextVersionMarker_1_0,
    LazyRawTextVersionMarker_1_1, RawTextAnnotationsIterator,
};

use crate::{IonResult, TextFormat, WriteConfig};

/// Marker trait for types that represent an Ion encoding.
pub trait Encoding: Encoder + Decoder {
    type Output: 'static + OutputFromBytes + AsRef<[u8]>;

    fn encode<V: WriteAsIon>(value: V) -> IonResult<Self::Output> {
        let bytes = Self::encode_to(value, Vec::new())?;
        Ok(Self::Output::from_bytes(bytes))
    }

    fn encode_all<V: WriteAsIon, I: IntoIterator<Item = V>>(values: I) -> IonResult<Self::Output> {
        let bytes = Self::encode_all_to(values, Vec::new())?;
        Ok(Self::Output::from_bytes(bytes))
    }

    fn encode_to<V: WriteAsIon, W: io::Write>(value: V, output: W) -> IonResult<W> {
        Self::default_write_config().encode_to(value, output)
    }

    fn encode_all_to<V: WriteAsIon, I: IntoIterator<Item = V>, W: io::Write>(
        values: I,
        output: W,
    ) -> IonResult<W> {
        Self::default_write_config().encode_all_to(output, values)
    }
    fn name() -> &'static str;
    fn default_write_config() -> WriteConfig<Self>;
}

// Similar to a simple `From` implementation, but can be defined for both String and Vec<u8> because
// this crate owns the trait.
pub trait OutputFromBytes {
    fn from_bytes(bytes: Vec<u8>) -> Self;
}

impl OutputFromBytes for Vec<u8> {
    fn from_bytes(bytes: Vec<u8>) -> Self {
        bytes
    }
}

impl OutputFromBytes for String {
    fn from_bytes(bytes: Vec<u8>) -> Self {
        String::from_utf8(bytes).expect("writer produced invalid UTF-8 bytes")
    }
}

// These types derive trait implementations in order to allow types that containing them
// to also derive trait implementations.

/// The Ion 1.0 binary encoding.
#[derive(Copy, Clone, Debug, Default)]
pub struct BinaryEncoding_1_0;

/// The Ion 1.1 binary encoding.
#[derive(Copy, Clone, Debug, Default)]
pub struct BinaryEncoding_1_1;

impl<'top> BinaryEncoding<'top> for BinaryEncoding_1_0 {}
impl<'top> BinaryEncoding<'top> for BinaryEncoding_1_1 {}

/// The Ion 1.0 text encoding.
#[derive(Copy, Clone, Debug, Default)]
pub struct TextEncoding_1_0;

impl TextEncoding_1_0 {
    fn with_format(self, format: TextFormat) -> WriteConfig<Self> {
        WriteConfig::<Self>::new(format)
    }
}

/// The Ion 1.1 text encoding.
#[derive(Copy, Clone, Debug, Default)]
pub struct TextEncoding_1_1;

impl TextEncoding_1_1 {
    fn with_format(self, format: TextFormat) -> WriteConfig<Self> {
        WriteConfig::<Self>::new(format)
    }
}

impl Encoding for BinaryEncoding_1_0 {
    type Output = Vec<u8>;

    fn name() -> &'static str {
        "binary Ion v1.0"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new()
    }
}
impl Encoding for BinaryEncoding_1_1 {
    type Output = Vec<u8>;

    fn name() -> &'static str {
        "binary Ion v1.1"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new()
    }
}
impl Encoding for TextEncoding_1_0 {
    type Output = String;
    fn name() -> &'static str {
        "text Ion v1.0"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new(<TextFormat as Default>::default())
    }
}
impl Encoding for TextEncoding_1_1 {
    type Output = String;
    fn name() -> &'static str {
        "text Ion v1.1"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new(<TextFormat as Default>::default())
    }
}

/// Marker trait for binary encodings of any version.
pub trait BinaryEncoding<'top>: Encoding<Output = Vec<u8>> + Decoder {}

/// Marker trait for text encodings.
pub trait TextEncoding<'top>:
    Encoding<Output = String>
    + Decoder<
        AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>,
        Value<'top> = LazyRawTextValue<'top, Self>,
    >
{
    // No methods, just a marker
}
impl<'top> TextEncoding<'top> for TextEncoding_1_0 {}
impl<'top> TextEncoding<'top> for TextEncoding_1_1 {}

/// Marker trait for encodings that support macros.
pub trait EncodingWithMacroSupport {}
impl EncodingWithMacroSupport for TextEncoding_1_1 {}

impl Decoder for BinaryEncoding_1_0 {
    type Reader<'data> = LazyRawBinaryReader_1_0<'data>;
    type ReaderSavedState = ();
    type Value<'top> = LazyRawBinaryValue_1_0<'top>;
    type SExp<'top> = LazyRawBinarySExp_1_0<'top>;
    type List<'top> = LazyRawBinaryList_1_0<'top>;
    type Struct<'top> = LazyRawBinaryStruct_1_0<'top>;
    type FieldName<'top> = LazyRawBinaryFieldName_1_0<'top>;
    type AnnotationsIterator<'top> = RawBinaryAnnotationsIterator<'top>;
    // Macros are not supported in Ion 1.0
    type EExp<'top> = Never;
    type VersionMarker<'top> = LazyRawBinaryVersionMarker_1_0<'top>;
}

impl Decoder for TextEncoding_1_0 {
    type Reader<'data> = LazyRawTextReader_1_0<'data>;
    type ReaderSavedState = ();
    type Value<'top> = LazyRawTextValue_1_0<'top>;
    type SExp<'top> = LazyRawTextSExp_1_0<'top>;
    type List<'top> = LazyRawTextList_1_0<'top>;
    type Struct<'top> = LazyRawTextStruct_1_0<'top>;
    type FieldName<'top> = LazyRawTextFieldName_1_0<'top>;
    type AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>;
    // Macros are not supported in Ion 1.0
    type EExp<'top> = Never;
    type VersionMarker<'top> = LazyRawTextVersionMarker_1_0<'top>;
}

impl Decoder for TextEncoding_1_1 {
    type Reader<'data> = LazyRawTextReader_1_1<'data>;
    type ReaderSavedState = ();
    type Value<'top> = LazyRawTextValue_1_1<'top>;
    type SExp<'top> = LazyRawTextSExp_1_1<'top>;
    type List<'top> = LazyRawTextList_1_1<'top>;
    type Struct<'top> = LazyRawTextStruct_1_1<'top>;
    type FieldName<'top> = LazyRawTextFieldName_1_1<'top>;
    type AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>;
    type EExp<'top> = RawTextEExpression_1_1<'top>;
    type VersionMarker<'top> = LazyRawTextVersionMarker_1_1<'top>;
}

impl Decoder for BinaryEncoding_1_1 {
    type Reader<'data> = LazyRawBinaryReader_1_1<'data>;
    type ReaderSavedState = ();
    type Value<'top> = LazyRawBinaryValue_1_1<'top>;
    type SExp<'top> = LazyRawBinarySExp_1_1<'top>;
    type List<'top> = LazyRawBinaryList_1_1<'top>;
    type FieldName<'top> = LazyRawBinaryFieldName_1_1<'top>;
    type Struct<'top> = LazyRawBinaryStruct_1_1<'top>;
    type AnnotationsIterator<'top> = RawBinaryAnnotationsIterator_1_1<'top>;
    // TODO: implement macros in 1.1
    type EExp<'top> = Never;
    type VersionMarker<'top> = LazyRawBinaryVersionMarker_1_1<'top>;
}

/// Marker trait for types that represent value literals in an Ion stream of some encoding.
// This trait is used to provide generic conversion implementation of types used as a
// `LazyDecoder::Value` to `ExpandedValueSource`. That is:
//
//     impl<'top, 'data, V: RawValueLiteral, D: LazyDecoder<'data, Value = V>> From<V>
//         for ExpandedValueSource<'top, D>
//
// If we do not confine the implementation to types with a marker trait, rustc complains that
// someone may someday use `ExpandedValueSource` as a `LazyDecoder::Value`, and then the
// implementation will conflict with the core `impl<T> From<T> for T` implementation.
pub trait RawValueLiteral {}

impl<'top, E: TextEncoding<'top>> RawValueLiteral for LazyRawTextValue<'top, E> {}
impl<'top> RawValueLiteral for LazyRawBinaryValue_1_0<'top> {}
impl<'top> RawValueLiteral for LazyRawBinaryValue_1_1<'top> {}
impl<'top> RawValueLiteral for LazyRawAnyValue<'top> {}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::lazy::encoding::TextEncoding;
    use crate::{
        ion_list, ion_seq, ion_sexp, ion_struct, v1_0, v1_1, IonResult, Sequence, TextFormat,
        WriteConfig,
    };

    #[rstest]
    #[case::pretty_v1_0(
        v1_0::Text.with_format(TextFormat::Pretty),
        "{\n  foo: 1,\n  bar: 2,\n}\n[\n  1,\n  2,\n]\n(\n  1\n  2\n)\n"
    )]
    #[case::pretty_v1_1(
        v1_1::Text.with_format(TextFormat::Pretty),
        "$ion_1_1\n{\n  foo: 1,\n  bar: 2,\n}\n[\n  1,\n  2,\n]\n(\n  1\n  2\n)\n"
    )]
    #[case::compact_v1_0(
        v1_0::Text.with_format(TextFormat::Compact),
        "{foo: 1, bar: 2, } [1, 2, ] (1 2 ) "
    )]
    #[case::compact_v1_1(
        v1_1::Text.with_format(TextFormat::Compact),
        "$ion_1_1 {foo: 1, bar: 2, } [1, 2, ] (1 2 ) "
    )]
    #[case::lines_v1_0(
        v1_0::Text.with_format(TextFormat::Lines),
        "{foo: 1, bar: 2, }\n[1, 2, ]\n(1 2 )\n"
    )]
    #[case::lines_v1_1(
        v1_1::Text.with_format(TextFormat::Lines),
        "$ion_1_1\n{foo: 1, bar: 2, }\n[1, 2, ]\n(1 2 )\n"
    )]
    fn encode_formatted_text<'a, E: TextEncoding<'a>>(
        #[case] config: impl Into<WriteConfig<E>>,
        #[case] expected: &str,
    ) -> IonResult<()> {
        let sequence: Sequence = ion_seq![
            ion_struct! {
                "foo" : 1,
                "bar" : 2,
            },
            ion_list![1, 2],
            ion_sexp! (1 2),
        ];

        // The goal of this test is to confirm that the value was serialized using the requested text format.
        // This string equality checks are unfortunately specific/fragile and can be modified if/when
        // changes are made to the text formatting.

        let text = sequence.encode_as(config)?;
        assert_eq!(text, expected);
        Ok(())
    }
}
