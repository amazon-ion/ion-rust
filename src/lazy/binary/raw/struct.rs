#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::Range;

use crate::lazy::binary::immutable_buffer::BinaryBuffer;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::reader::DataSource;
use crate::lazy::binary::raw::value::LazyRawBinaryValue_1_0;
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, HasRange, HasSpan, LazyRawContainer, LazyRawFieldExpr, LazyRawFieldName, LazyRawStruct,
};
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::lazy::span::Span;
use crate::{IonResult, RawSymbolRef, SymbolId};

#[derive(Copy, Clone)]
pub struct LazyRawBinaryStruct_1_0<'top> {
    pub(crate) value: LazyRawBinaryValue_1_0<'top>,
}

impl<'top> LazyRawBinaryStruct_1_0<'top> {
    pub fn as_value(&self) -> LazyRawBinaryValue_1_0<'top> {
        self.value
    }
}

impl<'a, 'top> IntoIterator for &'a LazyRawBinaryStruct_1_0<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_0>>;
    type IntoIter = RawBinaryStructIterator_1_0<'top>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'top> Debug for LazyRawBinaryStruct_1_0<'top> {
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

impl<'top> LazyRawBinaryStruct_1_0<'top> {
    fn annotations(&self) -> RawBinaryAnnotationsIterator<'top> {
        self.value.annotations()
    }

    pub fn iter(&self) -> RawBinaryStructIterator_1_0<'top> {
        // Get as much of the struct's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawBinaryStructIterator_1_0::new(buffer_slice)
    }
}

impl<'top> LazyContainerPrivate<'top, BinaryEncoding_1_0> for LazyRawBinaryStruct_1_0<'top> {
    fn from_value(value: LazyRawBinaryValue_1_0<'top>) -> Self {
        LazyRawBinaryStruct_1_0 { value }
    }
}

impl<'top> LazyRawContainer<'top, BinaryEncoding_1_0> for LazyRawBinaryStruct_1_0<'top> {
    fn as_value(&self) -> <BinaryEncoding_1_0 as Decoder>::Value<'top> {
        self.value
    }
}

impl<'top> LazyRawStruct<'top, BinaryEncoding_1_0> for LazyRawBinaryStruct_1_0<'top> {
    type Iterator = RawBinaryStructIterator_1_0<'top>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'top> {
        self.annotations()
    }

    fn iter(&self) -> Self::Iterator {
        self.iter()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawBinaryStructIterator_1_0<'top> {
    source: DataSource<'top>,
}

impl<'top> RawBinaryStructIterator_1_0<'top> {
    pub(crate) fn new(input: BinaryBuffer<'top>) -> RawBinaryStructIterator_1_0<'top> {
        RawBinaryStructIterator_1_0 {
            source: DataSource::new(input),
        }
    }
}

impl<'top> Iterator for RawBinaryStructIterator_1_0<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_0>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.source
            .try_parse_next_field(BinaryBuffer::peek_field)
            .transpose()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryFieldName_1_0<'top> {
    // The field ID has to be read in order to discover its length, so we store it here to avoid
    // needing to re-read it.
    field_id: SymbolId,
    matched: BinaryBuffer<'top>,
}

impl<'top> LazyRawBinaryFieldName_1_0<'top> {
    pub fn new(field_id: SymbolId, matched: BinaryBuffer<'top>) -> Self {
        Self { field_id, matched }
    }
}

impl<'top> HasSpan<'top> for LazyRawBinaryFieldName_1_0<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.matched.offset(), self.matched.bytes())
    }
}

impl<'top> HasRange for LazyRawBinaryFieldName_1_0<'top> {
    fn range(&self) -> Range<usize> {
        self.matched.range()
    }
}

impl<'top> LazyRawFieldName<'top, BinaryEncoding_1_0> for LazyRawBinaryFieldName_1_0<'top> {
    fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        Ok(RawSymbolRef::SymbolId(self.field_id))
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;

    use crate::lazy::binary::raw::reader::LazyRawBinaryReader_1_0;
    use crate::IonResult;

    use super::*;

    #[test]
    #[allow(clippy::single_range_in_vec_init)]
    fn field_name_ranges() -> IonResult<()> {
        // For each pair below, we'll confirm that the top-level struct's field names are found to
        // occupy the specified input ranges.
        type FieldNameAndRange<'a> = (RawSymbolRef<'a>, Range<usize>);
        type FieldTest<'a> = (&'a [u8], &'a [FieldNameAndRange<'a>]);
        let tests: &[FieldTest] = &[
            // (Ion input, expected ranges of the struct's field names)
            (
                &[0xD2, 0x84, 0x80], // {name: ""}
                &[(RawSymbolRef::SymbolId(4), 1..2)],
            ),
        ];
        for (input, field_name_ranges) in tests {
            let mut reader = LazyRawBinaryReader_1_0::new(input);
            let struct_ = reader.next()?.expect_value()?.read()?.expect_struct()?;
            for (field_result, (expected_name, range)) in
                struct_.iter().zip(field_name_ranges.iter())
            {
                let name = field_result?.name();
                assert_eq!(
                    name.read()?,
                    *expected_name,
                    "span failure for input {input:0X?} -> field {name:?}"
                );
                assert_eq!(
                    name.range(),
                    *range,
                    "range failure for input {input:0X?} -> field {name:?}"
                );
                println!(
                    "SUCCESS: input {:0X?} -> field {:?} -> {:0X?} ({:?})",
                    input,
                    expected_name,
                    name.span(),
                    name.range()
                );
            }
        }
        Ok(())
    }
}
