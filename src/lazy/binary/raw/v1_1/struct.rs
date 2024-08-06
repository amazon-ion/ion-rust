#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::Range;

use crate::lazy::binary::raw::v1_1::annotations_iterator::RawBinaryAnnotationsIterator_1_1;
use crate::lazy::binary::raw::v1_1::{
    immutable_buffer::{ImmutableBuffer, ParseResult},
    value::{DelimitedContents, LazyRawBinaryValue_1_1},
    OpcodeType,
};
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, HasRange, HasSpan, LazyRawContainer, LazyRawFieldExpr, LazyRawFieldName, LazyRawStruct,
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
    matched: ImmutableBuffer<'top>,
}

impl<'top> LazyRawBinaryFieldName_1_1<'top> {
    pub fn new(field_name: RawSymbolRef<'top>, matched: ImmutableBuffer<'top>) -> Self {
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

impl<'top> HasRange for LazyRawBinaryFieldName_1_1<'top> {
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
}

impl<'a, 'top> IntoIterator for &'a LazyRawBinaryStruct_1_1<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_1>>;
    type IntoIter = RawBinaryStructIterator_1_1<'top>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'top> Debug for LazyRawBinaryStruct_1_1<'top> {
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
                self.value.delimited_contents,
            )
        } else {
            let buffer_slice = self.value.value_body_buffer();
            RawBinaryStructIterator_1_1::new(
                self.value.encoded_value.header.ion_type_code,
                buffer_slice,
                self.value.delimited_contents,
            )
        }
    }
}

impl<'top> LazyContainerPrivate<'top, BinaryEncoding_1_1> for LazyRawBinaryStruct_1_1<'top> {
    fn from_value(value: &'top LazyRawBinaryValue_1_1<'top>) -> Self {
        LazyRawBinaryStruct_1_1 { value }
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

#[derive(Clone, Copy)]
enum StructMode {
    FlexSym,
    SymbolAddress,
}

enum SymAddressFieldName<'top> {
    ModeChange,
    FieldName(LazyRawBinaryFieldName_1_1<'top>),
}

pub struct RawBinaryStructIterator_1_1<'top> {
    source: ImmutableBuffer<'top>,
    // bytes_to_skip: usize,
    mode: StructMode,
    delimited_contents: DelimitedContents<'top>,
    delimited_iter: Option<std::slice::Iter<'top, LazyRawFieldExpr<'top, BinaryEncoding_1_1>>>,
}

impl<'top> RawBinaryStructIterator_1_1<'top> {
    pub(crate) fn new(
        opcode_type: OpcodeType,
        input: ImmutableBuffer<'top>,
        delimited_contents: DelimitedContents<'top>,
    ) -> RawBinaryStructIterator_1_1<'top> {
        RawBinaryStructIterator_1_1 {
            source: input,
            // bytes_to_skip: 0,
            mode: match opcode_type {
                OpcodeType::Struct => StructMode::SymbolAddress,
                OpcodeType::StructDelimited => StructMode::FlexSym,
                _ => unreachable!("Unexpected opcode for structure"),
            },
            delimited_contents,
            delimited_iter: match &delimited_contents {
                DelimitedContents::Fields(fields) => Some(fields.iter()),
                _ => None,
            },
        }
    }

    /// Helper function called by [`Self::peek_field`] in order to parse a FlexSym encoded
    /// struct field names. If no field is available, None is returned, otherwise the symbol and an
    /// [`ImmutableBuffer`] positioned after the field name is returned.
    ///
    /// The opcode variant of the FlexSym is not currently implemented.
    fn peek_field_flexsym(
        buffer: ImmutableBuffer<'top>,
    ) -> IonResult<Option<(LazyRawBinaryFieldName_1_1<'top>, ImmutableBuffer<'top>)>> {
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

        let matched_field_id = buffer.slice(0, after.offset() - buffer.offset());
        let field_name = LazyRawBinaryFieldName_1_1::new(sym, matched_field_id);
        Ok(Some((field_name, after)))
    }

    /// Helper function called by [`Self::peek_field`] in order to parse a symbol address encoded
    /// struct field names. If no field is available, None is returned, otherwise the symbol and an
    /// [`ImmutableBuffer`] positioned after the field name is returned.
    fn peek_field_symbol_addr(
        buffer: ImmutableBuffer<'top>,
    ) -> IonResult<Option<(SymAddressFieldName<'top>, ImmutableBuffer<'top>)>> {
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
    /// If a value is parsed successfully, it is returned along with an [`ImmutableBuffer`]
    /// positioned after the value. If the value consists of NOPs, no value is returned but a
    /// buffer positioned after the NOPs is returned.
    fn peek_value(
        buffer: ImmutableBuffer<'top>,
    ) -> IonResult<(Option<LazyRawBinaryValue_1_1<'top>>, ImmutableBuffer<'top>)> {
        let opcode = buffer.expect_opcode()?;
        if opcode.is_nop() {
            let after_nops = buffer.consume_nop_padding(opcode)?.1;
            if after_nops.is_empty() {
                // Non-NOP field wasn't found, nothing remaining.
                return Ok((None, after_nops));
            }
            Ok((None, after_nops))
        } else {
            buffer
                .read_value(opcode)
                .map(|(v, remaining)| (Some(v), remaining))
        }
    }

    /// Helper function called from [`Self::next`] to parse the current field and value from the
    /// struct. On success, returns both the field pair via [`LazyRawFieldExpr`] as well as the
    /// total bytes needed to skip the field.
    fn peek_field(
        input: ImmutableBuffer<'top>,
        mut mode: StructMode,
    ) -> ParseResult<Option<(LazyRawFieldExpr<'top, BinaryEncoding_1_1>, StructMode)>> {
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

            let (value, after_value) = match Self::peek_value(after_name)? {
                (None, after) => {
                    if after.is_empty() {
                        return IonResult::incomplete(
                            "found field name but no value",
                            after.offset(),
                        );
                    }
                    buffer = after;
                    continue; // No value for this field, loop to try next field.
                }
                (Some(value), after) => (&*after.context().allocator().alloc_with(|| value), after),
            };

            return Ok((
                Some((LazyRawFieldExpr::NameValue(field_name, value), mode)),
                after_value,
            ));
        }
    }
}

impl<'top> Iterator for RawBinaryStructIterator_1_1<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut inner_iter) = &mut self.delimited_iter {
            inner_iter.next().map(|val| Ok(*val))
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
