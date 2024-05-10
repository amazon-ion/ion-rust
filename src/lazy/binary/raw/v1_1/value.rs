#![allow(non_camel_case_types)]

use std::ops::Range;

use crate::lazy::decoder::{HasRange, HasSpan, RawVersionMarker};
use crate::lazy::span::Span;
use crate::{
    lazy::{
        binary::{
            encoded_value::{EncodedHeader, EncodedValue},
            raw::{
                v1_1::{
                    annotations_iterator::RawBinaryAnnotationsIterator_1_1,
                    immutable_buffer::ImmutableBuffer, Header, OpcodeType,
                },
                value::ValueParseResult,
            },
        },
        decoder::{LazyDecoder, LazyRawValue},
        encoding::BinaryEncoding_1_1,
        raw_value_ref::RawValueRef,
    },
    result::IonFailure,
    types::SymbolId,
    IonError, IonResult, IonType, RawSymbolTokenRef,
};

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryVersionMarker_1_1<'top> {
    major: u8,
    minor: u8,
    input: ImmutableBuffer<'top>,
}

impl<'top> LazyRawBinaryVersionMarker_1_1<'top> {
    pub fn new(input: ImmutableBuffer<'top>, major: u8, minor: u8) -> Self {
        Self {
            major,
            minor,
            input,
        }
    }
}

impl<'top> HasSpan<'top> for LazyRawBinaryVersionMarker_1_1<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl<'top> HasRange for LazyRawBinaryVersionMarker_1_1<'top> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> RawVersionMarker<'top> for LazyRawBinaryVersionMarker_1_1<'top> {
    fn version(&self) -> (u8, u8) {
        (self.major, self.minor)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryValue_1_1<'top> {
    pub(crate) encoded_value: EncodedValue<Header>,
    pub(crate) input: ImmutableBuffer<'top>,
}

impl<'top> HasSpan<'top> for LazyRawBinaryValue_1_1<'top> {
    fn span(&self) -> Span<'top> {
        let range = self.range();
        let local_range = (range.start - self.input.offset())..(range.end - self.input.offset());
        let bytes = &self.input.bytes()[local_range];
        Span::with_offset(range.start, bytes)
    }
}

impl<'top> HasRange for LazyRawBinaryValue_1_1<'top> {
    fn range(&self) -> Range<usize> {
        self.encoded_value.annotated_value_range()
    }
}

impl<'top> LazyRawValue<'top, BinaryEncoding_1_1> for LazyRawBinaryValue_1_1<'top> {
    fn ion_type(&self) -> IonType {
        self.ion_type()
    }

    fn is_null(&self) -> bool {
        self.is_null()
    }

    fn annotations(&self) -> <BinaryEncoding_1_1 as LazyDecoder>::AnnotationsIterator<'top> {
        self.annotations()
    }

    fn read(&self) -> IonResult<RawValueRef<'top, BinaryEncoding_1_1>> {
        self.read()
    }
}

impl<'top> LazyRawBinaryValue_1_1<'top> {
    /// Indicates the Ion data type of this value. Calling this method does not require additional
    /// parsing of the input stream.
    pub fn ion_type(&self) -> IonType {
        self.encoded_value.ion_type()
    }

    pub fn is_null(&self) -> bool {
        self.encoded_value.header().is_null()
    }

    /// Returns `true` if this value has a non-empty annotations sequence; otherwise, returns `false`.
    fn has_annotations(&self) -> bool {
        self.encoded_value.has_annotations()
    }

    /// Returns an `ImmutableBuffer` that contains the bytes comprising this value's encoded
    /// annotations sequence.
    fn annotations_sequence(&self) -> ImmutableBuffer<'top> {
        let offset_and_length = self
            .encoded_value
            .annotations_sequence_offset()
            .map(|offset| {
                (
                    offset,
                    self.encoded_value.annotations_sequence_length().unwrap(),
                )
            });
        let (sequence_offset, sequence_length) = match offset_and_length {
            None => {
                // If there are no annotations, return an empty slice starting at the opcode.
                return self.input.slice(0, 0);
            }
            Some(offset_and_length) => offset_and_length,
        };
        let local_sequence_offset = sequence_offset - self.input.offset();

        self.input.slice(local_sequence_offset, sequence_length)
    }

    /// Returns an iterator over this value's unresolved annotation symbols.
    pub fn annotations(&self) -> RawBinaryAnnotationsIterator_1_1<'top> {
        RawBinaryAnnotationsIterator_1_1::new(self.annotations_sequence())
    }

    /// Reads this value's data, returning it as a [`RawValueRef`]. If this value is a container,
    /// calling this method will not read additional data; the `RawValueRef` will provide a
    /// [`LazyRawBinarySequence_1_1`](crate::lazy::binary::raw::v1_1::sequence::LazyRawBinarySequence_1_1)
    /// or [`LazyStruct`](crate::lazy::struct::LazyStruct) that can be traversed to access the container's contents.
    pub fn read(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        if self.is_null() {
            let raw_value_ref = RawValueRef::Null(self.ion_type());
            return Ok(raw_value_ref);
        }

        match self.ion_type() {
            IonType::Null => unreachable!("all null types handled above"),
            IonType::Bool => self.read_bool(),
            IonType::Int => self.read_int(),
            IonType::Float => self.read_float(),
            IonType::Decimal => self.read_decimal(),
            IonType::Timestamp => self.read_timestamp(),
            IonType::Symbol => self.read_symbol(),
            IonType::String => self.read_string(),
            IonType::Clob => self.read_clob(),
            IonType::Blob => self.read_blob(),
            IonType::List => self.read_list(),
            IonType::SExp => self.read_sexp(),
            IonType::Struct => self.read_struct(),
        }
    }

    /// Returns the encoded byte slice representing this value's data.
    fn value_body(&self) -> IonResult<&'top [u8]> {
        let value_total_length = self.encoded_value.total_length();
        if self.input.len() < value_total_length {
            return IonResult::incomplete(
                "only part of the requested value is available in the buffer",
                self.input.offset(),
            );
        }
        let value_body_length = self.encoded_value.value_body_length();
        let value_offset = value_total_length - value_body_length;
        Ok(self.input.bytes_range(value_offset, value_body_length))
    }

    /// Returns an [`ImmutableBuffer`] containing whatever bytes of this value's body are currently
    /// available. This method is used to construct lazy containers, which are not required to be
    /// fully buffered before reading begins.
    pub(crate) fn available_body(&self) -> ImmutableBuffer<'top> {
        let value_total_length = self.encoded_value.total_length();
        let value_body_length = self.encoded_value.value_body_length();
        let value_offset = value_total_length - value_body_length;

        let bytes_needed = std::cmp::min(self.input.len() - value_offset, value_body_length);
        let buffer_slice = self.input.slice(value_offset, bytes_needed);
        buffer_slice
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a bool.
    fn read_bool(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Bool);
        let header = &self.encoded_value.header();
        let representation = header.type_code();
        let value = match (representation, header.length_code) {
            (OpcodeType::Boolean, 0xE) => true,
            (OpcodeType::Boolean, 0xF) => false,
            _ => unreachable!("found a boolean value with an illegal length code."),
        };
        Ok(RawValueRef::Bool(value))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as an int.
    fn read_int(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        use crate::lazy::encoder::binary::v1_1::fixed_int::FixedInt;
        debug_assert!(self.encoded_value.ion_type() == IonType::Int);

        let header = &self.encoded_value.header();
        let representation = header.type_code();
        let value = match (representation, header.length_code as usize) {
            (OpcodeType::Integer, 0x0) => 0.into(),
            (OpcodeType::Integer, n) => {
                // We have n bytes following that make up our integer.
                self.input.consume(1).read_fixed_int(n)?.0.into()
            }
            (OpcodeType::LargeInteger, 0x5) => {
                // We have a FlexUInt size, then big int.
                let value_bytes = self.value_body()?;
                FixedInt::read(value_bytes, value_bytes.len(), 0)?.into()
            }
            _ => unreachable!("integer encoding with illegal length_code found"),
        };
        Ok(RawValueRef::Int(value))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a float.
    fn read_float(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Float);

        let value = match self.encoded_value.value_body_length {
            8 => {
                let mut buffer = [0; 8];
                let val_bytes = self.input.bytes_range(1, 8);
                buffer[..8].copy_from_slice(val_bytes);

                f64::from_le_bytes(buffer)
            }
            4 => {
                let mut buffer = [0; 4];
                let val_bytes = self.input.bytes_range(1, 4);
                buffer[..4].copy_from_slice(val_bytes);

                f32::from_le_bytes(buffer).into()
            }
            2 => todo!("implement half-precision floats"),
            0 => 0.0f64,
            _ => unreachable!("found a float value with illegal byte size"),
        };
        Ok(RawValueRef::Float(value))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a decimal.
    fn read_decimal(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        todo!();
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a timestamp.
    fn read_timestamp(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        todo!();
    }

    /// Helper method called by [`Self::read_symbol`]. Reads the current value as a symbol ID.
    fn read_symbol_id(&self) -> IonResult<SymbolId> {
        let biases: [usize; 3] = [0, 256, 65792];
        let length_code = self.encoded_value.header.length_code;
        if (1..=3).contains(&length_code) {
            let (id, _) = self.input.consume(1).read_fixed_uint(length_code.into())?;
            let id = usize::try_from(id.value())?;
            Ok(id + biases[(length_code - 1) as usize])
        } else {
            unreachable!("invalid length code for symbol ID");
        }
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a symbol.
    fn read_symbol(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Symbol);
        let type_code = self.encoded_value.header.ion_type_code;
        if type_code == OpcodeType::InlineSymbol {
            let raw_bytes = self.value_body()?;
            let text = std::str::from_utf8(raw_bytes)
                .map_err(|_| IonError::decoding_error("found symbol with invalid UTF-8 data"))?;
            Ok(RawValueRef::Symbol(RawSymbolTokenRef::from(text)))
        } else if type_code == OpcodeType::SymbolAddress {
            let symbol_id = self.read_symbol_id()?;
            Ok(RawValueRef::Symbol(RawSymbolTokenRef::SymbolId(symbol_id)))
        } else {
            unreachable!("invalid Opcode type found for symbol");
        }
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a string.
    fn read_string(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        use crate::lazy::str_ref::StrRef;

        debug_assert!(self.encoded_value.ion_type() == IonType::String);
        let raw_bytes = self.value_body()?;
        let text = std::str::from_utf8(raw_bytes)
            .map_err(|_| IonError::decoding_error("found string with invalid UTF-8 data"))?;
        Ok(RawValueRef::String(StrRef::from(text)))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a blob.
    fn read_blob(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Blob);

        let raw_bytes = self.value_body()?;
        Ok(RawValueRef::Blob(raw_bytes.into()))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a clob.
    fn read_clob(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Clob);

        let raw_bytes = self.value_body()?;
        Ok(RawValueRef::Clob(raw_bytes.into()))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as an S-expression.
    fn read_sexp(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        todo!();
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a list.
    fn read_list(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        todo!();
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a struct.
    fn read_struct(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        todo!();
    }
}
