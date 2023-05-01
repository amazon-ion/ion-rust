use std::io::Write;
use std::ops::Range;
use std::{io, mem};

use bytes::BufMut;
use num_bigint::Sign;
use num_traits::Zero;

use crate::binary::constants::v1_0::IVM;
use crate::binary::uint::DecodedUInt;
use crate::binary::var_uint::VarUInt;
use crate::raw_symbol_token_ref::{AsRawSymbolTokenRef, RawSymbolTokenRef};
use crate::result::{illegal_operation, IonResult};
use crate::types::{ContainerType, Decimal, SymbolId, Timestamp};
use crate::writer::IonWriter;
use crate::{Int, IonType};

use super::decimal::DecimalBinaryEncoder;
use super::timestamp::TimestampBinaryEncoder;
use super::uint;

pub struct RawBinaryWriterBuilder {
    // Nothing yet
}

impl RawBinaryWriterBuilder {
    pub fn new() -> Self {
        RawBinaryWriterBuilder {}
    }

    /// Creates a new RawBinaryWriter that will write its encoded output to the provided
    /// io::Write sink.
    pub fn build<W: Write>(self, out: W) -> IonResult<RawBinaryWriter<W>> {
        let mut levels = Vec::with_capacity(INITIAL_ENCODING_LEVELS_CAPACITY);
        // Create an EncodingLevel to represent the top level. It has no annotations.
        levels.push(EncodingLevel::new(ContainerType::TopLevel, None, 0, 0));
        // Create an empty IoRange for top-level leading scalar values.
        let mut io_ranges = Vec::with_capacity(INITIAL_IO_RANGE_CAPACITY);
        io_ranges.push(0usize..0);
        let raw_binary_writer = RawBinaryWriter {
            buffer: Vec::with_capacity(INITIAL_ENCODING_BUFFER_CAPACITY),
            io_ranges,
            levels,
            out,
            annotations_all_levels: Vec::with_capacity(INITIAL_ANNOTATIONS_CAPACITY),
            num_annotations_current_value: 0,
            field_id: None,
            contiguous_encoding: Vec::with_capacity(INITIAL_ENCODING_BUFFER_CAPACITY),
        };

        // Currently, this method cannot fail. However, the other builder APIs return an
        // IonResult, so we've followed suit here.
        Ok(raw_binary_writer)
    }
}

impl Default for RawBinaryWriterBuilder {
    fn default() -> Self {
        RawBinaryWriterBuilder::new()
    }
}

// Ion's length prefixing requires that elements in a stream be encoded out of order.
// For example, to write the annotated list $ion::["foo", "bar"], the writer must:
//   1. Encode "foo"
//   2. Encode "bar"
//   3. Use the combined length of "foo" and "bar" to encode the header for the list
//   4. Encode the annotation sequence '$ion'
//   5. Encode the length of the annotation sequence
//   5. Use the combined length of 'foo' and the list to write the annotations wrapper
//
// The BinarySystemWriter encodes these out-of-order byte sequences in a temporary buffer and tracks
// which slices of the buffer should be written out first by maintaining a queue of Range<usize>
// entries. These entries are referred to as `IoRange`s, as they are the buffer ranges that
// are actually sent to `io::write` whenever `flush()` is called.
type IoRange = Range<usize>;

// When encoding the above example data, the buffer with out-of-order byte sequences might look
// like this:
//
// [offset] 0             4             8             12   13   14   15
// buffer : e0 01 00 ea | 83 66 6f 6f | 83 62 61 72 | b8 | 81 | 81 | eb
//          ^             ^             ^             ^    ^    ^    ^-- 11-byte annotation wrapper
//          |             |             |             |    |    +------- Annotation seq length 1
//          |             |             |             |    +------------ Annotation 1 ('$ion')
//          |             |             |             +----------------- 8-byte list header
//          |             |             +------------------------------- 3-byte string "bar"
//          |             +--------------------------------------------- 3-byte string "foo"
//          +----------------------------------------------------------- Ion 1.0 version marker
//
// Meanwhile, the writer's IoRange queue would look like this:
//
//     0..4, 15..16, 14..15, 13..14, 12..13, 4..12
//
// Ranges have inclusive starts and exclusive ends, so the range 14..15 includes a single byte at
// index 14.
//
// When the writer's `flush()` method is called, each IoRange is turned into a slice of the buffer
// and written to the io::Write sink.
//
//     e0 01 00 ea eb 81 81 b8 83 66 6f 6f 83 62 61 72

// Stores information about each level into which the writer has stepped, including its
// annotations, field_id, and container type.
#[derive(Debug)]
struct EncodingLevel {
    container_type: ContainerType,
    field_id: Option<SymbolId>,
    // Annotations are stored in a common Vec on the BinarySystemWriter. Each EncodingLevel tracks
    // how many annotations it had, allowing that Vec to be treated as a stack. Stepping into
    // a new level pushes `num_annotations` symbol IDs onto the Vec and stepping out pops
    // `num_annotations` back off the stack.
    num_annotations: u8,
    // Index of the IoRange for this container's type descriptor and length. When the writer
    // steps out of this level, the type descriptor IoRange will be retrieved and populated.
    td_io_range_index: usize,
}

impl EncodingLevel {
    fn new(
        container_type: ContainerType,
        field_id: Option<SymbolId>,
        num_annotations: u8,
        td_io_range_index: usize,
    ) -> EncodingLevel {
        EncodingLevel {
            container_type,
            field_id,
            num_annotations,
            td_io_range_index,
        }
    }

    // Visits all of the IoRanges belonging to this EncodingLevel and notes their total length.
    // This length will be written out as a length prefix for the container.
    fn calculate_final_size(&self, io_ranges: &mut [Range<usize>]) -> usize {
        io_ranges[self.td_io_range_index..]
            .iter()
            .map(|r| r.len())
            .sum()
    }
}

/// A system-level streaming binary Ion writer. This writer does not provide symbol table
/// management; symbol-related operations (e.g. setting field IDs and annotations or writing symbol
/// values) require a valid symbol ID to be provided by the caller.
///
/// To produce a valid binary Ion stream, the writer MUST call
/// [RawBinaryWriter::write_ion_version_marker] before writing any data.
#[derive(Debug)]
pub struct RawBinaryWriter<W: Write> {
    // A byte buffer to encode individual components of the stream.
    buffer: Vec<u8>,
    // Slices of the buffer to write out in order when flush() is called.
    io_ranges: Vec<IoRange>,
    // Stack for tracking step_in/step_out
    levels: Vec<EncodingLevel>,
    // An io::Write implementation to be used as a sink for encoded data.
    out: W,
    // The field ID of the current value. If the writer is not in a struct, this will be None.
    field_id: Option<SymbolId>,
    // A Vec into which all EncodingLevels can store their annotations. Sharing this Vec avoids
    // allocating new space for each container the writer steps into.
    annotations_all_levels: Vec<SymbolId>,
    // The number of annotations at the tail of `annotations_all_levels` belonging to the current
    // value.
    num_annotations_current_value: u8,
    // Scratch space for the flush() method to rearrange the contents of `buffer` before writing
    // the data to `out`.
    contiguous_encoding: Vec<u8>,
}

// The largest possible 'L' (length) value that can be written directly in a type descriptor byte.
// Larger length values will need to be written as a VarUInt following the type descriptor.
pub(crate) const MAX_INLINE_LENGTH: usize = 13;

// The number of IoRanges needed to write out an annotations wrapper, not including the IoRange
// belonging to the wrapped value. (One IoRange for each of: the annotations sequence, the length
// of the annotations sequence, and the annotations wrapper header.)
const IO_RANGES_PER_ANNOTATION_WRAPPER: usize = 3;

// These values are initial sizes for various `Vec`s that will be resized if necessary.
const INITIAL_ENCODING_BUFFER_CAPACITY: usize = 8 * 1024;
const INITIAL_ENCODING_LEVELS_CAPACITY: usize = 16;
const INITIAL_IO_RANGE_CAPACITY: usize = 128;
const INITIAL_ANNOTATIONS_CAPACITY: usize = 4;

impl<W: Write> RawBinaryWriter<W> {
    // Uses the provided closure to encode data to the buffer. Returns the range of the buffer
    // now occupied by the encoded bytes.
    #[inline]
    fn encode_to_buffer(
        &mut self,
        mut encode_fn: impl FnMut(&mut Self) -> IonResult<()>,
    ) -> IonResult<IoRange> {
        let start = self.buffer.len();
        encode_fn(self)?;
        let end = self.buffer.len();
        Ok(start..end)
    }

    // Returns true if the last container that the writer stepped into was a struct; false otherwise.
    #[inline]
    fn is_in_struct(&self) -> bool {
        self.levels
            .last()
            .map(|level| level.container_type == ContainerType::Struct)
            .unwrap_or(false)
    }

    // Modifies the last IoRange to include the next `number_of_bytes`.
    // Used when writing scalars, which can always extend the most recent range instead of adding
    // a new one.
    #[inline]
    fn extend_last_range(&mut self, number_of_bytes: usize) {
        let last_range = self
            .io_ranges
            .last_mut()
            .expect("io_ranges unexpectedly empty.");
        last_range.end += number_of_bytes;
    }

    // Handles before-and-after tasks common to writing all non-container values, like encoding
    // field IDs and annotation wrappers.
    fn write_scalar(
        &mut self,
        mut write_fn: impl FnMut(&mut Vec<u8>) -> IonResult<()>,
    ) -> IonResult<()> {
        // If we're in a struct, encode the field ID first.
        if self.is_in_struct() {
            let field_id = self.expect_field_id()? as u64;
            let bytes_written = VarUInt::write_u64(&mut self.buffer, field_id)?;
            self.extend_last_range(bytes_written);
            self.field_id = None;
        }

        if self.has_annotations() {
            return self.encode_annotated_scalar(write_fn);
        }

        let encoded_range = self.encode_to_buffer(|writer| write_fn(&mut writer.buffer))?;
        self.extend_last_range(encoded_range.len());

        Ok(())
    }

    // Uses the provided closure to encode a scalar value, then encodes the annotation wrapper
    // based on the encoded value's length and the configured annotations sequence.
    fn encode_annotated_scalar(
        &mut self,
        mut scalar_write_fn: impl FnMut(&mut Vec<u8>) -> IonResult<()>,
    ) -> IonResult<()> {
        // Encode the scalar into the buffer, but do not push the IoRange yet.
        let value_io_range: IoRange =
            self.encode_to_buffer(|writer| scalar_write_fn(&mut writer.buffer))?;

        // Create ranges that will ultimately point to the encoded components of the annotations
        // wrapper for the value.
        let mut header_io_range: Range<usize> = 0..0;
        let mut annotations_seq_length_io_range: Range<usize> = 0..0;
        let mut annotations_seq_io_range: Range<usize> = 0..0;

        // Using the encoded length of the value, encode the annotations wrapper and populate
        // the IO ranges we created above.
        self.encode_annotation_wrapper(
            &mut header_io_range,
            &mut annotations_seq_length_io_range,
            &mut annotations_seq_io_range,
            value_io_range.len(),
        )?;

        // Push the IO ranges in the correct order so the encoded bytes will be written in the
        // correct order when the user calls `flush()`.
        self.io_ranges.extend_from_slice(&[
            header_io_range,
            annotations_seq_length_io_range,
            annotations_seq_io_range,
            value_io_range,
        ]);

        self.push_empty_io_range();

        Ok(())
    }

    // Writes the annotations wrapper for a value of a given length. Callers should encode the
    // value to the buffer, call this method with the value's encoded length, then push
    // the populated IoRanges in the necessary order.
    fn encode_annotation_wrapper(
        &mut self,
        header_io_range: &mut IoRange,
        annotations_seq_length_io_range: &mut IoRange,
        annotations_seq_io_range: &mut IoRange,
        wrapped_value_length: usize,
    ) -> IonResult<()> {
        // Encode the sequence of annotations and make a note of the encoded length.
        // The return value of mem::replace is the original range value, which is always 0..0.
        // We can safely ignore it.
        let _ = mem::replace(
            annotations_seq_io_range,
            self.encode_to_buffer(|writer| {
                let range = writer.current_value_annotations_range();
                let annotations = &writer.annotations_all_levels[range];
                for annotation_id in annotations {
                    VarUInt::write_u64(&mut writer.buffer, *annotation_id as u64)?;
                }
                Ok(())
            })?,
        );
        let annotation_sequence_encoded_length = annotations_seq_io_range.len();

        // Encode the length of the annotations sequence as a VarUInt.
        let _ = mem::replace(
            annotations_seq_length_io_range,
            self.encode_to_buffer(|writer| {
                let _num_bytes = VarUInt::write_u64(
                    &mut writer.buffer,
                    annotation_sequence_encoded_length as u64,
                )?;
                Ok(())
            })?,
        );

        // The length of the wrapper is the sum total of:
        // 1. The length of the encoded annotations sequence
        // 2. The length of the VarUInt representation of #1 above.
        // 3. The length of the value being annotated.
        let wrapper_length = annotations_seq_io_range.len()
            + annotations_seq_length_io_range.len()
            + wrapped_value_length;

        // Now that we know the wrapper length, encode the annotation wrapper header.
        let _ = mem::replace(
            header_io_range,
            self.encode_to_buffer(|writer| {
                let type_descriptor: u8;
                if wrapper_length <= MAX_INLINE_LENGTH {
                    // Use inline length encoding
                    type_descriptor = 0xE0 | wrapper_length as u8;
                    writer.buffer.push(type_descriptor);
                } else {
                    type_descriptor = 0xEE; // VarUInt length encoding
                    writer.buffer.push(type_descriptor);
                    VarUInt::write_u64(&mut writer.buffer, wrapper_length as u64)?;
                }
                Ok(())
            })?,
        );

        self.clear_annotations();
        Ok(())
    }

    // Returns the range of annotations in `annotations_all_levels` that belong to the current value.
    // This function originally borrowed a slice of `annotations_all_levels`, but this lead to ownership
    // conflicts; all of `self` would remain borrowed. Returning the range instead allows the compiler
    // to see that only `self.annotations_all_levels` is being borrowed.
    #[inline]
    fn current_value_annotations_range(&self) -> Range<usize> {
        let end = self.annotations_all_levels.len();
        let start = end - self.num_annotations_current_value as usize;
        start..end
    }

    #[inline]
    pub fn clear_annotations(&mut self) {
        if self.num_annotations_current_value > 0 {
            let new_length =
                self.annotations_all_levels.len() - self.num_annotations_current_value as usize;
            self.annotations_all_levels.truncate(new_length);
            self.num_annotations_current_value = 0;
        }
    }

    #[inline]
    pub fn has_annotations(&self) -> bool {
        self.num_annotations_current_value > 0
    }

    pub fn write_symbol_id(&mut self, symbol_id: SymbolId) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            const SYMBOL_BUFFER_SIZE: usize = mem::size_of::<u64>();
            let mut buffer = [0u8; SYMBOL_BUFFER_SIZE];
            let mut writer = io::Cursor::new(&mut buffer).writer();
            let encoded_length = DecodedUInt::write_u64(&mut writer, symbol_id as u64)?;

            let type_descriptor: u8;
            if encoded_length <= MAX_INLINE_LENGTH {
                type_descriptor = 0x70 | encoded_length as u8;
                enc_buffer.push(type_descriptor);
            } else {
                type_descriptor = 0x7E;
                enc_buffer.push(type_descriptor);
                VarUInt::write_u64(enc_buffer, encoded_length as u64)?;
            }
            let raw_buffer = writer.into_inner().into_inner();
            enc_buffer.extend_from_slice(&raw_buffer[..encoded_length]);
            Ok(())
        })
    }

    fn write_lob(enc_buffer: &mut Vec<u8>, value: &[u8], type_code: u8) -> IonResult<()> {
        let encoded_length = value.len();
        let type_descriptor: u8;
        if encoded_length <= MAX_INLINE_LENGTH {
            type_descriptor = type_code | encoded_length as u8;
            enc_buffer.push(type_descriptor);
        } else {
            type_descriptor = type_code | 0x0E;
            enc_buffer.push(type_descriptor);
            VarUInt::write_u64(enc_buffer, encoded_length as u64)?;
        }
        enc_buffer.extend_from_slice(value);
        Ok(())
    }

    // Creates an empty IoRange starting from the next unoccupied byte in the buffer.
    fn push_empty_io_range(&mut self) {
        let next_byte_index = self.buffer.len();
        self.io_ranges.push(next_byte_index..next_byte_index);
    }

    pub fn set_field_id(&mut self, field_id: SymbolId) {
        self.field_id = Some(field_id);
    }

    // Called when the writer is in a struct and a missing field ID is an error
    fn expect_field_id(&self) -> IonResult<usize> {
        match self.field_id {
            Some(field_id) => Ok(field_id),
            None => {
                illegal_operation("`set_field_id()` must be called before each field in a struct.")
            }
        }
    }

    // When step_out() is called and the container has been written, this function uses the encoded
    // length to write the container's annotations wrapper.
    fn encode_container_annotations(
        &mut self,
        td_io_range_index: usize,
        container_size: usize,
    ) -> IonResult<()> {
        // Create IoRanges that will ultimately point to the encoded components of the annotations
        // wrapper for the value.
        let mut header_io_range: Range<usize> = 0..0;
        let mut annotations_seq_length_io_range: Range<usize> = 0..0;
        let mut annotations_seq_io_range: Range<usize> = 0..0;

        // Encode the annotation wrapper, populating the ranges above in the process.
        self.encode_annotation_wrapper(
            &mut header_io_range,
            &mut annotations_seq_length_io_range,
            &mut annotations_seq_io_range,
            container_size,
        )?;

        // Populate each of the reserved annotation IO ranges using the results from above.
        let header_io_range_index = td_io_range_index - IO_RANGES_PER_ANNOTATION_WRAPPER;
        let _ = mem::replace(&mut self.io_ranges[header_io_range_index], header_io_range);

        let annotations_seq_length_io_range_index = header_io_range_index + 1;
        let _ = mem::replace(
            &mut self.io_ranges[annotations_seq_length_io_range_index],
            annotations_seq_length_io_range,
        );

        let annotations_seq_io_range_index = header_io_range_index + 2;
        let _ = mem::replace(
            &mut self.io_ranges[annotations_seq_io_range_index],
            annotations_seq_io_range,
        );

        Ok(())
    }

    /// Returns a reference to the underlying io::Write implementation.
    pub fn output(&self) -> &W {
        &self.out
    }

    /// Returns a mutable reference to the underlying io::Write implementation. Modifying the
    /// underlying sink is an inherently risky operation and can result in unexpected behavior.
    /// It is not recommended for most use cases.
    pub fn output_mut(&mut self) -> &mut W {
        &mut self.out
    }

    fn reserve_io_ranges_for_annotations(&mut self) {
        // Annotations type descriptor and wrapper length
        self.push_empty_io_range();
        // The VarUInt length of the encoded sequence of annotations
        self.push_empty_io_range();
        // The encoded sequence of annotations
        self.push_empty_io_range();
    }

    pub fn add_annotation<A: AsRawSymbolTokenRef>(&mut self, annotation: A) {
        let symbol_id = match annotation.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(symbol_id) => symbol_id,
            RawSymbolTokenRef::Text(text) => panic!(
                "The RawBinaryWriter can only accept symbol ID annotations, not text ('{text}')."
            ),
        };
        self.annotations_all_levels.push(symbol_id);
        self.num_annotations_current_value += 1;
    }
}

impl<W: Write> IonWriter for RawBinaryWriter<W> {
    type Output = W;

    fn ion_version(&self) -> (u8, u8) {
        (1, 0)
    }

    fn write_ion_version_marker(&mut self, major: u8, minor: u8) -> IonResult<()> {
        if self.depth() > 0 {
            return illegal_operation("can only write an IVM at the top level");
        }
        if major == 1 && minor == 0 {
            return Ok(self.out.write_all(&IVM)?);
        }
        illegal_operation("Only Ion 1.0 is supported.")
    }

    fn supports_text_symbol_tokens(&self) -> bool {
        // In Ion 1.0, the binary format requires that field names, annotations, and symbol values
        // be encoded as symbol IDs. The raw writer does not have a symbol table and so cannot
        // convert a String to a symbol ID.
        false
    }

    fn set_annotations<I, A>(&mut self, annotations: I)
    where
        A: AsRawSymbolTokenRef,
        I: IntoIterator<Item = A>,
    {
        self.clear_annotations();
        for annotation in annotations {
            self.add_annotation(annotation);
        }
    }

    /// Writes an Ion null of the specified type.
    fn write_null(&mut self, ion_type: IonType) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            let byte: u8 = match ion_type {
                IonType::Null => 0x0F,
                IonType::Bool => 0x1F,
                IonType::Int => 0x2F,
                IonType::Float => 0x4F,
                IonType::Decimal => 0x5F,
                IonType::Timestamp => 0x6F,
                IonType::Symbol => 0x7F,
                IonType::String => 0x8F,
                IonType::Clob => 0x9F,
                IonType::Blob => 0xAF,
                IonType::List => 0xBF,
                IonType::SExp => 0xCF,
                IonType::Struct => 0xDF,
            };
            enc_buffer.push(byte);
            Ok(())
        })
    }

    /// Writes an Ion boolean with the specified value.
    fn write_bool(&mut self, value: bool) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            let byte: u8 = if value { 0x11 } else { 0x10 };
            enc_buffer.push(byte);
            Ok(())
        })
    }

    /// Writes an Ion integer with the specified value.
    fn write_i64(&mut self, value: i64) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            // Get the absolute value of the i64 and store it in a u64.
            let magnitude: u64 = value.unsigned_abs();
            let encoded = uint::encode_u64(magnitude);
            let bytes_to_write = encoded.as_bytes();

            // The encoded length will never be larger than 8 bytes, so it will
            // always fit in the Int's type descriptor byte.
            let encoded_length = bytes_to_write.len();
            let type_descriptor: u8 = if value >= 0 {
                0x20 | (encoded_length as u8)
            } else {
                0x30 | (encoded_length as u8)
            };
            enc_buffer.push(type_descriptor);
            enc_buffer.extend_from_slice(bytes_to_write);

            Ok(())
        })
    }

    /// Writes an Ion integer with the specified value.
    fn write_int(&mut self, value: &Int) -> IonResult<()> {
        // If the `value` is an `i64`, use `write_i64` and return.
        let value = match value {
            Int::I64(i) => return self.write_i64(*i),
            Int::BigInt(i) => i,
        };

        // From here on, `value` is a `BigInt`.
        self.write_scalar(|enc_buffer| {
            if value.is_zero() {
                enc_buffer.push(0x20);
                return Ok(());
            }

            let (sign, magnitude_be_bytes) = value.to_bytes_be();

            let mut type_descriptor: u8 = match sign {
                Sign::Plus | Sign::NoSign => 0x20,
                Sign::Minus => 0x30,
            };

            let encoded_length = magnitude_be_bytes.len();
            if encoded_length <= 13 {
                type_descriptor |= encoded_length as u8;
                enc_buffer.push(type_descriptor);
            } else {
                type_descriptor |= 0xEu8;
                enc_buffer.push(type_descriptor);
                VarUInt::write_u64(enc_buffer, encoded_length as u64)?;
            }

            enc_buffer.extend_from_slice(magnitude_be_bytes.as_slice());

            Ok(())
        })
    }

    /// Writes an Ion float with the specified value.
    fn write_f32(&mut self, value: f32) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            if value == 0f32 && !value.is_sign_negative() {
                enc_buffer.push(0x40);
                return Ok(());
            }

            enc_buffer.push(0x44);
            enc_buffer.extend_from_slice(&value.to_be_bytes());
            Ok(())
        })
    }

    /// Writes an Ion float with the specified value.
    fn write_f64(&mut self, value: f64) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            if value == 0f64 && !value.is_sign_negative() {
                enc_buffer.push(0x40);
                return Ok(());
            }

            enc_buffer.push(0x48);
            enc_buffer.extend_from_slice(&value.to_be_bytes());
            Ok(())
        })
    }

    /// Writes an Ion decimal with the specified value.
    fn write_decimal(&mut self, value: &Decimal) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            let _ = enc_buffer.encode_decimal_value(value)?;
            Ok(())
        })
    }

    /// Writes an Ion timestamp with the specified value.
    fn write_timestamp(&mut self, value: &Timestamp) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            let _ = enc_buffer.encode_timestamp_value(value)?;
            Ok(())
        })
    }

    fn write_symbol<A: AsRawSymbolTokenRef>(&mut self, value: A) -> IonResult<()> {
        match value.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(sid) => self.write_symbol_id(sid),
            RawSymbolTokenRef::Text(_text) => {
                illegal_operation("The RawBinaryWriter cannot write text symbols.")
            }
        }
    }

    fn write_string<S: AsRef<str>>(&mut self, value: S) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            let text: &str = value.as_ref();
            let encoded_length = text.len(); // The number of utf8 bytes

            let type_descriptor: u8;
            if encoded_length <= MAX_INLINE_LENGTH {
                type_descriptor = 0x80 | encoded_length as u8;
                enc_buffer.push(type_descriptor);
            } else {
                type_descriptor = 0x8E;
                enc_buffer.push(type_descriptor);
                VarUInt::write_u64(enc_buffer, encoded_length as u64)?;
            }
            enc_buffer.extend_from_slice(text.as_bytes());
            Ok(())
        })
    }

    fn write_clob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            let bytes: &[u8] = value.as_ref();
            // The clob type descriptor's high nibble is type code 9
            RawBinaryWriter::<W>::write_lob(enc_buffer, bytes, 0x90)
        })
    }

    fn write_blob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        self.write_scalar(|enc_buffer| {
            let bytes: &[u8] = value.as_ref();
            // The blob type descriptor's high nibble is type code 10
            RawBinaryWriter::<W>::write_lob(enc_buffer, bytes, 0xA0)
        })
    }

    /// Starts a container of the specified Ion type. If `ion_type` is not a List, SExpression,
    /// or Struct, `step_in` will return an Err.
    fn step_in(&mut self, ion_type: IonType) -> IonResult<()> {
        use IonType::*;
        let container_type = match ion_type {
            List => ContainerType::List,
            SExp => ContainerType::SExpression,
            Struct => ContainerType::Struct,
            _ => return illegal_operation("Cannot step into a scalar Ion type."),
        };

        // If this is a field in a struct, encode the field ID at the end of the last IO range.
        if self.is_in_struct() {
            let field_id_io_range = self.encode_to_buffer(|writer| {
                let field_id = writer.expect_field_id()? as u64;
                VarUInt::write_u64(&mut writer.buffer, field_id)?;
                Ok(())
            })?;
            self.extend_last_range(field_id_io_range.len());
        }

        // If the container is annotated, reserve IO ranges to hold the annotations
        // wrapper components that will ultimately precede the value.
        if self.num_annotations_current_value > 0 {
            self.reserve_io_ranges_for_annotations();
        }

        // An empty placeholder range that we'll fill in during step_out(). It will point to the
        // type descriptor byte and any length bytes.
        let header_io_range_index = self.io_ranges.len();
        self.push_empty_io_range();

        let new_encoding_level = EncodingLevel::new(
            container_type,
            self.field_id,
            self.num_annotations_current_value,
            header_io_range_index,
        );
        self.num_annotations_current_value = 0;
        self.levels.push(new_encoding_level);

        self.push_empty_io_range(); // Scalars can append to this
        Ok(())
    }

    fn set_field_name<A: AsRawSymbolTokenRef>(&mut self, name: A) {
        if self.parent_type() != Some(IonType::Struct) {
            panic!("Attempted to set field name when the writer was not in a struct.");
        }
        match name.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(sid) => self.set_field_id(sid),
            RawSymbolTokenRef::Text(text) => panic!(
                "The RawBinaryWriter can only accept Symbol ID field names, not text ('{text}')."
            ),
        }
    }

    fn parent_type(&self) -> Option<IonType> {
        // `self.levels` always has at least one value: the top level.
        // This means we can `unwrap()` the last value safely.
        match self.levels.last().unwrap().container_type {
            ContainerType::TopLevel => None,
            ContainerType::Struct => Some(IonType::Struct),
            ContainerType::List => Some(IonType::List),
            ContainerType::SExpression => Some(IonType::SExp),
        }
    }

    fn depth(&self) -> usize {
        // The top level is always present
        self.levels.len() - 1
    }

    /// Ends the current container. If the writer is at the top level, `step_out` will return an Err.
    fn step_out(&mut self) -> IonResult<()> {
        if self.levels.len() <= 1 {
            return illegal_operation(
                "Cannot call step_out() unless the writer is positioned within a container.",
            );
        }
        self.clear_annotations();
        let container = self.levels.pop().unwrap();
        self.num_annotations_current_value = container.num_annotations;
        self.field_id = container.field_id;
        let container_size = container.calculate_final_size(&mut self.io_ranges);

        use crate::types::ContainerType::*;
        let mut type_descriptor: u8 = match container.container_type {
            List => 0xB0,
            SExpression => 0xC0,
            Struct => 0xD0,
            _ => return illegal_operation("Cannot step into a scalar Ion type."),
        };

        // Encode the type descriptor byte, and optional length
        let header_io_range = self.encode_to_buffer(|writer| {
            if container_size <= MAX_INLINE_LENGTH {
                type_descriptor |= container_size as u8;
                writer.buffer.push(type_descriptor);
            } else {
                type_descriptor |= 0x0E; // VarUInt encoding
                writer.buffer.push(type_descriptor);
                VarUInt::write_u64(&mut writer.buffer, container_size as u64)?;
            }
            Ok(())
        })?;

        // Now that we know how large the container's header is, add its length to the
        // calculated container size.
        let container_size = container_size + header_io_range.len();

        // Retrieve this container's header byte range from io_ranges
        let td_io_range = self
            .io_ranges
            .get_mut(container.td_io_range_index)
            .expect("Missing type descriptor IO range for {}");

        // Update the IO range to point to the bytes we just encoded
        let _ = mem::replace(td_io_range, header_io_range);

        // If this container had annotations, retrieve the IO ranges that were reserved to store
        // them and use them to encode the annotations wrapper.
        if container.num_annotations > 0 {
            self.encode_container_annotations(container.td_io_range_index, container_size)?;
        }

        // Create an empty IO Range that will hold the bytes of any scalar values that will follow
        // now that we've stepped out.
        self.push_empty_io_range();

        Ok(())
    }

    /// Writes any buffered data to the sink. This method can only be called when the writer is at
    /// the top level.
    fn flush(&mut self) -> IonResult<()> {
        if self.depth() > 0 {
            return illegal_operation(
                "Cannot call flush() while the writer is positioned within a container.",
            );
        }

        // We don't call finalize() on the top level because it has no length prefix.
        // Instead, its io_range represents the bytes of any leading scalar values.

        // For each io_range in order, copy the specified bytes into a contiguous buffer that
        // we'll write to output.

        for io_range in self.io_ranges.drain(..) {
            self.contiguous_encoding
                .extend_from_slice(&self.buffer[io_range]);
        }

        // TODO: When io::Write#is_write_vectored[1] or trait specialization[2] stabilize,
        //      we can use vectored writes instead of making a contiguous encoding
        //      buffer.
        //      [1] https://github.com/rust-lang/rust/issues/69941
        //      [2] https://github.com/rust-lang/rust/issues/31844

        self.out.write_all(self.contiguous_encoding.as_slice())?;

        self.contiguous_encoding.clear();
        self.push_empty_io_range();

        Ok(())
    }

    fn output(&self) -> &Self::Output {
        &self.out
    }

    fn output_mut(&mut self) -> &mut Self::Output {
        &mut self.out
    }
}

#[cfg(test)]
mod writer_tests {
    use std::fmt::Debug;

    use crate::StreamItem;

    use rstest::*;

    use super::*;
    use crate::raw_symbol_token::{local_sid_token, RawSymbolToken};
    use crate::reader::{Reader, ReaderBuilder};
    use crate::types::{Blob, Clob, Symbol};
    use crate::IonReader;
    use num_bigint::BigInt;
    use num_traits::Float;
    use std::convert::TryInto;
    use std::str::FromStr;

    type TestWriter<'a> = RawBinaryWriter<&'a mut Vec<u8>>;
    type TestReader<'a> = Reader<'a>;

    /// A reusable test outline for verifying BinarySystemWriter behavior.
    fn binary_writer_test(
        mut write_fn: impl FnMut(&mut TestWriter) -> IonResult<()>,
        mut read_fn: impl FnMut(&mut TestReader) -> IonResult<()>,
    ) -> IonResult<()> {
        // Create a BinarySystemWriter that writes to a byte vector.
        let mut buffer = vec![];
        let mut writer = RawBinaryWriterBuilder::new().build(&mut buffer)?;
        writer.write_ion_version_marker(1, 0)?;

        // Call the user's writing function
        write_fn(&mut writer)?;
        writer.flush()?;

        // Create a BinaryReader that reads from the BinarySystemWriter's output.
        let data = buffer.as_slice();
        let mut reader = ReaderBuilder::new().build(data)?;

        // Call the user's verification function
        read_fn(&mut reader)
    }

    /// A reusable test outline for verifying BinarySystemWriter scalar encoding behavior.
    fn binary_writer_scalar_test<T, U>(
        values: &[T],
        ion_type: IonType,
        mut write_fn: impl FnMut(&mut TestWriter, &T) -> IonResult<()>,
        mut read_fn: impl FnMut(&mut TestReader) -> IonResult<U>,
    ) -> IonResult<()>
    where
        T: Debug,
        U: std::cmp::PartialEq<T> + Debug,
    {
        binary_writer_test(
            |writer| {
                for value in values {
                    write_fn(writer, value)?;
                }
                Ok(())
            },
            |reader| {
                for value in values {
                    assert_eq!(reader.next()?, StreamItem::Value(ion_type));
                    let reader_value = read_fn(reader)?;
                    assert_eq!(
                        reader_value, *value,
                        "Value read back in (left) was not equal to the original value (right)"
                    );
                }
                Ok(())
            },
        )
    }

    #[test]
    fn binary_writer_nulls() -> IonResult<()> {
        let ion_types = &[
            IonType::Null,
            IonType::Bool,
            IonType::Int,
            IonType::Float,
            IonType::Decimal,
            IonType::Timestamp,
            IonType::Symbol,
            IonType::String,
            IonType::Clob,
            IonType::Blob,
            IonType::List,
            IonType::SExp,
            IonType::Struct,
        ];

        binary_writer_test(
            |writer| {
                for ion_type in ion_types {
                    writer.write_null(*ion_type)?;
                }
                Ok(())
            },
            |reader| {
                for ion_type in ion_types {
                    assert_eq!(reader.next()?, StreamItem::Null(*ion_type));
                }
                Ok(())
            },
        )
    }

    #[test]
    fn binary_writer_bools() -> IonResult<()> {
        binary_writer_scalar_test(
            &[true, false],
            IonType::Bool,
            |writer, v| writer.write_bool(*v),
            |reader| reader.read_bool(),
        )
    }

    #[test]
    fn binary_writer_ints() -> IonResult<()> {
        binary_writer_scalar_test(
            &[-24_601, -17, -1, 0, 1, 17, 24_601],
            IonType::Int,
            |writer, v| writer.write_i64(*v),
            |reader| reader.read_i64(),
        )
    }

    #[test]
    fn binary_writer_floats() -> IonResult<()> {
        binary_writer_scalar_test(
            &[-24.601, -1.7, -1.0, -0.0, 0.0, 1.0, 1.7, 24.601],
            IonType::Float,
            |writer, v| writer.write_f64(*v),
            |reader| reader.read_f64(),
        )
    }

    #[rstest]
    #[case::year(Timestamp::with_year(2021).build().unwrap())]
    #[case::year_month(Timestamp::with_year(2021).with_month(1).build().unwrap())]
    #[case::year_month_day(Timestamp::with_ymd(2021, 1, 8).build().unwrap())]
    #[case::ymd_hm_unknown(Timestamp::with_ymd(2021, 1, 8).with_hour_and_minute(14, 12).build_at_unknown_offset().unwrap())]
    #[case::ymd_hm_est(Timestamp::with_ymd(2021, 1, 8).with_hour_and_minute(14, 12).build_at_offset(-5 * 60).unwrap())]
    #[case::ymd_hms_unknown(Timestamp::with_ymd(2021, 1, 8).with_hms(14, 12, 36).build_at_unknown_offset().unwrap())]
    #[case::ymd_hms_est(Timestamp::with_ymd(2021, 1, 8).with_hms(14, 12, 36).build_at_offset(-5 * 60).unwrap())]
    #[case::ymd_hms_millis_unknown(Timestamp::with_ymd(2021, 1, 8).with_hms(14, 12, 36).with_milliseconds(888).build_at_unknown_offset().unwrap())]
    #[case::ymd_hms_millis_est(Timestamp::with_ymd(2021, 1, 8).with_hms(14, 12, 36).with_milliseconds(888).build_at_offset(-5 * 60).unwrap())]
    #[case::ymd_hms_nanos_unknown(Timestamp::with_ymd(2021, 1, 8).with_hms(14, 12, 36).with_nanoseconds(888888888).build_at_unknown_offset().unwrap())]
    #[case::ymd_hms_nanos_est(Timestamp::with_ymd(2021, 1, 8).with_hms(14, 12, 36).with_nanoseconds(888888888).build_at_offset(-5 * 60).unwrap())]
    fn binary_writer_timestamps(#[case] timestamp: Timestamp) -> IonResult<()> {
        binary_writer_scalar_test(
            &[timestamp],
            IonType::Timestamp,
            |writer, v| writer.write_timestamp(v),
            |reader| reader.read_timestamp(),
        )
    }

    #[rstest]
    #[case(24.601)]
    #[case(-24.601)]
    #[case(1.7)]
    #[case(-1.7)]
    #[case(1.0)]
    #[case(-1.0)]
    #[case::positive_zero(0.0)]
    #[case::negative_zero(f64::neg_zero())]
    fn binary_writer_decimals(#[case] value: f64) -> IonResult<()> {
        let decimal: Decimal = value.try_into().unwrap();
        binary_writer_scalar_test(
            &[decimal],
            IonType::Decimal,
            |writer, v| writer.write_decimal(v),
            |reader| reader.read_decimal(),
        )
    }

    #[test]
    fn binary_writer_symbols() -> IonResult<()> {
        let symbol_ids: Vec<RawSymbolToken> = [0, 5, 10, 31, 111, 556, 1024, 74_991, 111_448]
            .iter()
            .map(|sid| local_sid_token(*sid))
            .collect();
        binary_writer_scalar_test(
            symbol_ids.as_slice(),
            IonType::Symbol,
            |writer, v| writer.write_symbol_id(v.local_sid().unwrap()),
            |reader| reader.read_raw_symbol(),
        )
    }

    #[test]
    fn binary_writer_strings() -> IonResult<()> {
        binary_writer_scalar_test(
            &["", "foo", "bar", "baz", "quux", "Winnipeg", "😂😂😂"],
            IonType::String,
            |writer, v| writer.write_string(*v),
            |reader| reader.read_string(),
        )
    }

    #[test]
    fn binary_writer_lobs() -> IonResult<()> {
        let values: Vec<&[u8]> = ["", "foo", "bar", "baz", "quux", "Winnipeg", "😂😂😂"]
            .iter()
            .map(|s| s.as_bytes())
            .collect();

        let clobs: Vec<Clob> = values.iter().map(|b| Clob::from(*b)).collect();
        let blobs: Vec<Blob> = values.iter().map(|b| Blob::from(*b)).collect();

        binary_writer_scalar_test(
            clobs.as_slice(),
            IonType::Clob,
            |writer, v| writer.write_clob(v),
            |reader| reader.read_clob(),
        )?;

        binary_writer_scalar_test(
            blobs.as_slice(),
            IonType::Blob,
            |writer, v| writer.write_blob(v),
            |reader| reader.read_blob(),
        )
    }

    fn expect_scalar<T: Debug, U: PartialEq<T> + Debug>(
        reader: &mut TestReader,
        ion_type: IonType,
        mut read_fn: impl FnMut(&mut TestReader) -> IonResult<U>,
        expected_value: T,
    ) {
        let next = reader.next().unwrap_or_else(|_| {
            panic!("Expected to read {expected_value:?}, but the stream was empty.")
        });
        assert_eq!(next, StreamItem::Value(ion_type));
        let value = read_fn(reader)
            .unwrap_or_else(|_| panic!("Failed to read in expected value: {expected_value:?}"));
        assert_eq!(value, expected_value);
    }

    fn expect_bool(reader: &mut TestReader, value: bool) {
        expect_scalar(reader, IonType::Bool, |r| r.read_bool(), value);
    }

    fn expect_integer(reader: &mut TestReader, value: i64) {
        expect_scalar(reader, IonType::Int, |r| r.read_i64(), value);
    }

    fn expect_big_integer(reader: &mut TestReader, value: &BigInt) {
        expect_scalar(
            reader,
            IonType::Int,
            |r| r.read_int(),
            Int::BigInt(value.clone()),
        );
    }

    fn expect_float(reader: &mut TestReader, value: f64) {
        expect_scalar(reader, IonType::Float, |r| r.read_f64(), value);
    }

    fn expect_symbol_id(reader: &mut TestReader, value: SymbolId) {
        expect_scalar(
            reader,
            IonType::Symbol,
            |r| r.read_raw_symbol(),
            local_sid_token(value),
        );
    }

    fn expect_string(reader: &mut TestReader, value: &str) {
        expect_scalar(reader, IonType::String, |r| r.read_string(), value);
    }

    fn expect_null(reader: &mut TestReader) {
        assert_eq!(
            reader.next().expect("Failed to read null."),
            StreamItem::Null(IonType::Null)
        );
    }

    fn expect_container(reader: &mut TestReader, ion_type: IonType) {
        assert_eq!(
            reader.next().expect("Failed to read container."),
            StreamItem::Value(ion_type)
        );
    }

    fn expect_list(reader: &mut TestReader) {
        expect_container(reader, IonType::List);
    }

    fn expect_s_expression(reader: &mut TestReader) {
        expect_container(reader, IonType::SExp);
    }

    fn expect_struct(reader: &mut TestReader) {
        expect_container(reader, IonType::Struct);
    }

    fn expect_field_name(reader: &TestReader, field_name: &str) {
        assert!(reader.field_name().is_ok());
        assert_eq!(reader.field_name().unwrap(), field_name);
    }

    fn expect_annotations(reader: &TestReader, annotations: &[&str]) {
        assert_eq!(
            reader
                .annotations()
                .map(|opt| opt.expect("Annotation with unknown text."))
                .collect::<Vec<Symbol>>()
                .as_slice(),
            annotations
        );
    }

    fn write_lst<W: Write>(writer: &mut RawBinaryWriter<W>, symbols: &[&str]) -> IonResult<()> {
        // $ion_symbol_table::{symbols: ["your", "strings", "here"]}
        writer.set_annotations([3]); // $ion_symbol_table
        writer.step_in(IonType::Struct)?;
        writer.set_field_id(7); // symbols
        writer.step_in(IonType::List)?;
        for symbol in symbols {
            writer.write_string(symbol)?;
        }
        writer.step_out()?;
        writer.step_out()?;
        Ok(())
    }

    #[test]
    fn binary_writer_large_integers() -> IonResult<()> {
        // 11 byte UInt
        let big_positive = BigInt::from_str("123456789123456789123456789").unwrap();
        // 19 byte UInt
        let very_big_positive =
            BigInt::from_str("123456789123456789123456789123456789123456789").unwrap();
        let big_negative = -big_positive.clone();
        let very_big_negative = -very_big_positive.clone();
        binary_writer_test(
            |writer| {
                writer.write_int(&Int::BigInt(BigInt::zero()))?;
                writer.write_int(&Int::BigInt(big_positive.clone()))?;
                writer.write_int(&Int::BigInt(very_big_positive.clone()))?;
                writer.write_int(&Int::BigInt(big_negative.clone()))?;
                writer.write_int(&Int::BigInt(very_big_negative.clone()))?;
                Ok(())
            },
            |reader| {
                expect_big_integer(reader, &BigInt::zero());
                expect_big_integer(reader, &big_positive);
                expect_big_integer(reader, &very_big_positive);
                expect_big_integer(reader, &big_negative);
                expect_big_integer(reader, &very_big_negative);
                Ok(())
            },
        )
    }

    #[test]
    fn binary_writer_mixed_scalars() -> IonResult<()> {
        // The tests above write streams containing a single type of Ion value. This test writes
        // a mix.
        binary_writer_test(
            |writer| {
                writer.write_i64(42)?;
                writer.write_string("Hello")?;
                writer.write_symbol_id(12)?;
                writer.write_f32(2.5)?;
                writer.write_f64(7.5)?;
                writer.write_bool(false)
            },
            |reader| {
                expect_integer(reader, 42);
                expect_string(reader, "Hello");
                expect_symbol_id(reader, 12);
                expect_float(reader, 2.5);
                expect_float(reader, 7.5);
                expect_bool(reader, false);
                Ok(())
            },
        )
    }

    #[test]
    fn binary_writer_annotated_scalars() -> IonResult<()> {
        binary_writer_test(
            |writer| {
                write_lst(writer, &["foo", "bar", "baz", "quux", "quuz", "waldo"])?;

                writer.set_annotations([10]);
                writer.write_bool(true)?;

                writer.set_annotations([11, 12]);
                writer.write_i64(42)?;

                writer.set_annotations([13, 14, 15]);
                writer.write_string("Hello")
            },
            |reader| {
                expect_bool(reader, true);
                expect_annotations(reader, &["foo"]);

                expect_integer(reader, 42);
                expect_annotations(reader, &["bar", "baz"]);

                expect_string(reader, "Hello");
                expect_annotations(reader, &["quux", "quuz", "waldo"]);
                Ok(())
            },
        )
    }

    #[test]
    fn binary_writer_annotated_containers() -> IonResult<()> {
        binary_writer_test(
            |writer| {
                write_lst(
                    writer,
                    &["foo", "bar", "baz", "quux", "quuz", "waldo", "gary"],
                )?;

                // foo::(true)
                writer.set_annotations([10]);
                writer.step_in(IonType::SExp)?;
                writer.write_bool(true)?;
                writer.step_out()?;

                // bar::baz::[11]
                writer.set_annotations([11, 12]);
                writer.step_in(IonType::List)?;
                writer.write_i64(11)?;
                writer.step_out()?;

                // quux::quuz::waldo::{gary: "foo"}
                writer.set_annotations([13, 14, 15]);
                writer.step_in(IonType::Struct)?;
                writer.set_field_id(16);
                writer.write_string("foo")?;
                writer.step_out()
            },
            |reader| {
                expect_s_expression(reader);
                expect_annotations(reader, &["foo"]);
                reader.step_in()?;
                expect_bool(reader, true);
                reader.step_out()?;

                expect_list(reader);
                expect_annotations(reader, &["bar", "baz"]);
                reader.step_in()?;
                expect_integer(reader, 11);
                reader.step_out()?;

                expect_struct(reader);
                expect_annotations(reader, &["quux", "quuz", "waldo"]);
                reader.step_in()?;
                expect_string(reader, "foo");
                expect_field_name(reader, "gary");
                reader.step_out()?;
                Ok(())
            },
        )
    }

    #[test]
    fn binary_writer_nested_annotated_containers() -> IonResult<()> {
        binary_writer_test(
            |writer| {
                write_lst(writer, &["foo", "bar", "baz", "quux"])?;
                // foo::{bar: baz::[quux::"quuz"]]}
                writer.set_annotations([10]);
                writer.step_in(IonType::Struct)?;
                writer.set_field_id(11);
                writer.set_annotations([12]);
                writer.step_in(IonType::List)?;
                writer.set_annotations([13]);
                writer.write_string("quuz")?;
                writer.step_out()?; // End of list
                writer.step_out() // End of struct
            },
            |reader| {
                expect_struct(reader);
                expect_annotations(reader, &["foo"]);
                reader.step_in()?;
                expect_list(reader);
                expect_field_name(reader, "bar");
                expect_annotations(reader, &["baz"]);
                reader.step_in()?;
                expect_string(reader, "quuz");
                expect_annotations(reader, &["quux"]);
                reader.step_out()?;
                reader.step_out()?;
                Ok(())
            },
        )
    }

    #[test]
    fn binary_writer_list() -> IonResult<()> {
        binary_writer_test(
            |writer| {
                // [42, "Hello"]
                writer.step_in(IonType::List)?;
                writer.write_i64(42)?;
                writer.write_string("Hello")?;
                writer.step_out()
            },
            |reader| {
                expect_list(reader);
                reader.step_in()?;
                expect_integer(reader, 42);
                expect_string(reader, "Hello");
                reader.step_out()
            },
        )
    }

    #[test]
    fn binary_writer_nested_list() -> IonResult<()> {
        binary_writer_test(
            |writer| {
                // [42, ["Hello"], "foo"]
                writer.step_in(IonType::List)?;
                writer.write_i64(42)?;
                writer.step_in(IonType::List)?;
                writer.write_string("Hello")?;
                writer.step_out()?;
                writer.write_string("foo")?;
                writer.step_out()
            },
            |reader| {
                expect_list(reader);
                reader.step_in()?;
                expect_integer(reader, 42);
                expect_list(reader);
                reader.step_in()?;
                expect_string(reader, "Hello");
                reader.step_out()?;
                expect_string(reader, "foo");
                reader.step_out()
            },
        )
    }

    #[test]
    fn binary_writer_nested_structs() -> IonResult<()> {
        binary_writer_test(
            |writer| {
                write_lst(writer, &["foo", "bar", "baz", "quux"])?;

                // {foo: true, bar: {quux: 7}, baz: null}
                writer.step_in(IonType::Struct)?;
                writer.set_field_id(10);
                writer.write_bool(true)?;
                writer.set_field_id(11);
                writer.step_in(IonType::Struct)?;
                writer.set_field_id(13);
                writer.write_i64(7)?;
                writer.step_out()?; // End of nested struct
                writer.set_field_id(12);
                writer.write_null(IonType::Null)?;
                writer.step_out() // End of top-level struct
            },
            |reader| {
                expect_struct(reader);
                reader.step_in()?;
                expect_bool(reader, true);
                expect_field_name(reader, "foo");
                expect_struct(reader);
                expect_field_name(reader, "bar");
                reader.step_in()?;
                expect_integer(reader, 7);
                expect_field_name(reader, "quux");
                reader.step_out()?;
                expect_null(reader);
                expect_field_name(reader, "baz");
                reader.step_out()
            },
        )
    }
}
