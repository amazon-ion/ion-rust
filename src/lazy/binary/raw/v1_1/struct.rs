#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::Range;

use crate::lazy::binary::raw::v1_1::annotations_iterator::RawBinaryAnnotationsIterator_1_1;
use crate::lazy::binary::raw::v1_1::{
    immutable_buffer::{BinaryBuffer, ParseResult},
    value::{DelimitedContents, LazyRawBinaryValue_1_1},
    OpcodeType,
};
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, HasRange, HasSpan, LazyRawContainer, LazyRawFieldExpr, LazyRawFieldName,
    LazyRawStruct, LazyRawValueExpr, RawValueExpr,
};
use crate::lazy::encoding::BinaryEncoding_1_1;
use crate::lazy::span::Span;
use crate::{result::IonFailure, IonResult, RawSymbolRef};

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryFieldName_1_1<'top> {
    // The field name has to be read in order to discover its length, so we store it here to avoid
    // needing to re-read it.
    field_name: RawSymbolRef<'top>,
    // For viewing the span/range of the field name
    matched: BinaryBuffer<'top>,
}

impl<'top> LazyRawBinaryFieldName_1_1<'top> {
    pub fn new(field_name: RawSymbolRef<'top>, matched: BinaryBuffer<'top>) -> Self {
        Self {
            field_name,
            matched,
        }
    }
}

impl<'top> HasSpan<'top> for LazyRawBinaryFieldName_1_1<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.matched.offset(), self.matched.bytes())
    }
}

impl HasRange for LazyRawBinaryFieldName_1_1<'_> {
    fn range(&self) -> Range<usize> {
        self.matched.range()
    }
}

impl<'top> LazyRawFieldName<'top, BinaryEncoding_1_1> for LazyRawBinaryFieldName_1_1<'top> {
    fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        Ok(self.field_name)
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawBinaryStruct_1_1<'top> {
    pub(crate) value: &'top LazyRawBinaryValue_1_1<'top>,
    pub(crate) delimited_field_expr_cache:
        Option<&'top [LazyRawFieldExpr<'top, BinaryEncoding_1_1>]>,
}

impl<'top> IntoIterator for &LazyRawBinaryStruct_1_1<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_1>>;
    type IntoIter = RawBinaryStructIterator_1_1<'top>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl Debug for LazyRawBinaryStruct_1_1<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for field in self {
            let (name, lazy_value) = field?.expect_name_value()?;
            let value = lazy_value.read()?;
            write!(f, "{:?}:{:?},", name, value)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<'top> LazyRawBinaryStruct_1_1<'top> {
    fn annotations(&self) -> RawBinaryAnnotationsIterator_1_1<'top> {
        self.value.annotations()
    }

    pub fn iter(&self) -> RawBinaryStructIterator_1_1<'top> {
        if self.value.is_delimited() {
            RawBinaryStructIterator_1_1::new(
                self.value.encoded_value.header.ion_type_code,
                self.value.input.consume(1),
                self.delimited_field_expr_cache,
            )
        } else {
            let buffer_slice = self.value.value_body_buffer();
            RawBinaryStructIterator_1_1::new(
                self.value.encoded_value.header.ion_type_code,
                buffer_slice,
                None,
            )
        }
    }
}

impl<'top> LazyContainerPrivate<'top, BinaryEncoding_1_1> for LazyRawBinaryStruct_1_1<'top> {
    fn from_value(value: &'top LazyRawBinaryValue_1_1<'top>) -> Self {
        let delimited_field_expr_cache = match value.delimited_contents {
            DelimitedContents::None => None,
            DelimitedContents::Fields(fields) => Some(fields),
            DelimitedContents::Values(_) => unreachable!("struct contained sequence values"),
        };
        LazyRawBinaryStruct_1_1 {
            value,
            delimited_field_expr_cache,
        }
    }
}

impl<'top> LazyRawContainer<'top, BinaryEncoding_1_1> for LazyRawBinaryStruct_1_1<'top> {
    fn as_value(&self) -> <BinaryEncoding_1_1 as Decoder>::Value<'top> {
        self.value
    }
}

impl<'top> LazyRawStruct<'top, BinaryEncoding_1_1> for LazyRawBinaryStruct_1_1<'top> {
    type Iterator = RawBinaryStructIterator_1_1<'top>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator_1_1<'top> {
        self.annotations()
    }

    fn iter(&self) -> Self::Iterator {
        self.iter()
    }
}

#[derive(Debug, Copy, Clone)]
enum StructMode {
    FlexSym,
    SymbolAddress,
}

enum SymAddressFieldName<'top> {
    ModeChange,
    FieldName(LazyRawBinaryFieldName_1_1<'top>),
}

#[derive(Debug, Copy, Clone)]
pub struct RawBinaryStructIterator_1_1<'top> {
    source: BinaryBuffer<'top>,
    mode: StructMode,
    field_expr_index: usize,
    field_expr_cache: Option<&'top [LazyRawFieldExpr<'top, BinaryEncoding_1_1>]>,
}

impl<'top> RawBinaryStructIterator_1_1<'top> {
    pub(crate) fn new(
        opcode_type: OpcodeType,
        input: BinaryBuffer<'top>,
        field_expr_cache: Option<&'top [LazyRawFieldExpr<'top, BinaryEncoding_1_1>]>,
    ) -> RawBinaryStructIterator_1_1<'top> {
        RawBinaryStructIterator_1_1 {
            source: input,
            mode: match opcode_type {
                OpcodeType::Struct => StructMode::SymbolAddress,
                OpcodeType::StructDelimited => StructMode::FlexSym,
                _ => unreachable!("Unexpected opcode for structure"),
            },
            field_expr_cache,
            field_expr_index: 0,
        }
    }

    /// Helper function called by [`Self::peek_field`] in order to parse a FlexSym encoded
    /// struct field names. If no field is available, None is returned, otherwise the symbol and an
    /// [`BinaryBuffer`] positioned after the field name is returned.
    ///
    /// The opcode variant of the FlexSym is not currently implemented.
    fn peek_field_flexsym(
        buffer: BinaryBuffer<'top>,
    ) -> IonResult<Option<(LazyRawBinaryFieldName_1_1<'top>, BinaryBuffer<'top>)>> {
        use crate::lazy::encoder::binary::v1_1::flex_sym::FlexSymValue;

        if buffer.is_empty() {
            return Ok(None);
        }

        let (flex_sym, after) = buffer.read_flex_sym()?;
        let (sym, after) = match flex_sym.value() {
            FlexSymValue::SymbolRef(sym_ref) => (sym_ref, after),
            FlexSymValue::Opcode(o) if o.is_delimited_end() => return Ok(None),
            _ => unreachable!(),
        };

        let matched_field_id = buffer.slice(0, flex_sym.size_in_bytes());
        let field_name = LazyRawBinaryFieldName_1_1::new(sym, matched_field_id);
        Ok(Some((field_name, after)))
    }

    /// Helper function called by [`Self::peek_field`] in order to parse a symbol address encoded
    /// struct field names. If no field is available, None is returned, otherwise the symbol and an
    /// [`BinaryBuffer`] positioned after the field name is returned.
    fn peek_field_symbol_addr(
        buffer: BinaryBuffer<'top>,
    ) -> IonResult<Option<(SymAddressFieldName<'top>, BinaryBuffer<'top>)>> {
        if buffer.is_empty() {
            return Ok(None);
        }

        let (symbol_address, after) = buffer.read_flex_uint()?;
        let field_id = symbol_address.value() as usize;

        if field_id == 0 {
            // Mode switch.
            Ok(Some((SymAddressFieldName::ModeChange, after)))
        } else {
            let matched_field_id = buffer.slice(0, symbol_address.size_in_bytes());
            let field_name =
                LazyRawBinaryFieldName_1_1::new(RawSymbolRef::SymbolId(field_id), matched_field_id);
            Ok(Some((SymAddressFieldName::FieldName(field_name), after)))
        }
    }

    /// Helper function called by [`Self::peek_field`] in order to parse a struct field's value.
    /// If a value is parsed successfully, it is returned along with an [`BinaryBuffer`]
    /// positioned after the value. If the value consists of NOPs, no value is returned but a
    /// buffer positioned after the NOPs is returned.
    fn peek_value_expr(
        buffer: BinaryBuffer<'top>,
    ) -> IonResult<(
        Option<LazyRawValueExpr<'top, BinaryEncoding_1_1>>,
        BinaryBuffer<'top>,
    )> {
        let opcode = buffer.expect_opcode()?;
        if opcode.is_nop() {
            let after_nops = buffer.consume_nop_padding(opcode)?.1;
            Ok((None, after_nops))
        } else {
            buffer.read_sequence_value_expr()
        }
    }

    /// Helper function called from [`Self::next`] to parse the current field and value from the
    /// struct. On success, returns both the field pair via [`LazyRawFieldExpr`] as well as the
    /// total bytes needed to skip the field.
    fn peek_field(
        input: BinaryBuffer<'top>,
        mut mode: StructMode,
    ) -> ParseResult<'top, Option<(LazyRawFieldExpr<'top, BinaryEncoding_1_1>, StructMode)>> {
        let mut buffer = input;
        loop {
            // Peek at our field name.
            let peek_result = match mode {
                StructMode::SymbolAddress => match Self::peek_field_symbol_addr(buffer)? {
                    Some((SymAddressFieldName::ModeChange, after)) => {
                        mode = StructMode::FlexSym;
                        Self::peek_field_flexsym(after)?
                    }
                    Some((SymAddressFieldName::FieldName(fieldname), after)) => {
                        Some((fieldname, after))
                    }
                    None => None,
                },
                StructMode::FlexSym => Self::peek_field_flexsym(buffer)?,
            };

            let Some((field_name, after_name)) = peek_result else {
                return Ok((None, buffer));
            };

            if after_name.is_empty() {
                return IonResult::incomplete("found field name but no value", after_name.offset());
            }

            let (value_expr, after_value) = match Self::peek_value_expr(after_name)? {
                (None, after_value) => {
                    if after_value.is_empty() {
                        return IonResult::incomplete(
                            "found field name but no value",
                            after_value.offset(),
                        );
                    }
                    buffer = after_value;
                    continue; // No value for this field, loop to try next field.
                }
                (Some(value_expr), after) => (value_expr, after),
            };

            let field_expr = match value_expr {
                RawValueExpr::ValueLiteral(value) => LazyRawFieldExpr::NameValue(field_name, value),
                RawValueExpr::EExp(eexp) => LazyRawFieldExpr::NameEExp(field_name, eexp),
            };

            return Ok((Some((field_expr, mode)), after_value));
        }
    }
}

impl<'top> Iterator for RawBinaryStructIterator_1_1<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(field_cache) = self.field_expr_cache {
            let field = field_cache.get(self.field_expr_index)?;
            self.field_expr_index += 1;
            Some(Ok(*field))
        } else {
            let (field_expr, after, mode) = match Self::peek_field(self.source, self.mode) {
                Ok((Some((value, mode)), after)) => (Some(Ok(value)), after, mode),
                Ok((None, after)) => (None, after, self.mode),
                Err(e) => return Some(Err(e)),
            };
            self.source = after;
            self.mode = mode;
            field_expr
        }
    }
}

#[cfg(feature = "experimental-ion-1-1")]
#[cfg(test)]
mod tests {
    use crate::{
        v1_1, AnyEncoding, Element, ElementReader, IonResult, MacroTable, Reader, SequenceWriter,
        StructWriter, ValueWriter, Writer,
    };

    #[test]
    fn field_value_eexp() -> IonResult<()> {
        let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
        let encoding_directive = Element::read_one(
            r#"
                $ion_encoding::(
                    (symbol_table $ion_encoding)
                    (macro_table
                        $ion_encoding
                        (macro greet (name) (.make_string "hello, " (%name)))
                    )
                )
            "#,
        )?;
        writer.write(&encoding_directive)?;
        let macro_id = MacroTable::FIRST_USER_MACRO_ID;
        let mut struct_writer = writer.struct_writer()?;

        let field_writer = struct_writer.field_writer("Waldo");
        let mut eexp_writer = field_writer.eexp_writer(macro_id)?;
        eexp_writer.write("Waldo")?;
        eexp_writer.close()?;

        let field_writer = struct_writer.field_writer("Winnifred");
        let mut eexp_writer = field_writer.eexp_writer(macro_id)?;
        eexp_writer.write("Winnifred")?;
        eexp_writer.close()?;

        let field_writer = struct_writer.field_writer("Winston");
        let mut eexp_writer = field_writer.eexp_writer(macro_id)?;
        eexp_writer.write("Winston")?;
        eexp_writer.close()?;

        struct_writer.close()?;

        let bytes = writer.close()?;

        let mut reader = Reader::new(AnyEncoding, bytes)?;
        assert_eq!(
            reader.read_one_element()?,
            Element::read_one(
                r#"
                    {
                        Waldo    : "hello, Waldo",
                        Winnifred: "hello, Winnifred",
                        Winston  : "hello, Winston",
                    }
                "#
            )?
        );
        Ok(())
    }
}
