use bytes::BigEndian;
use bytes::ByteOrder;
use delegate::delegate;
use std::fmt::Display;

use crate::raw_reader::RawStreamItem;
use crate::{
    binary::{
        constants::v1_0::length_codes,
        header::{create_header_byte_jump_table, Header},
        int::DecodedInt,
        uint::DecodedUInt,
        var_int::VarInt,
        var_uint::VarUInt,
        IonTypeCode,
    },
    data_source::IonDataSource,
    result::{decoding_error, illegal_operation, illegal_operation_raw, IonResult},
    types::{IonType, SymbolId},
};
use std::io;

use crate::raw_symbol_token::RawSymbolToken;
use crate::result::{decoding_error_raw, IonError};
use crate::stream_reader::StreamReader;
use crate::types::decimal::Decimal;
use crate::types::integer::{IntAccess, Integer};
use crate::types::timestamp::Timestamp;
use num_traits::Zero;
use std::ops::Range;

/// Information about the value over which the RawBinaryReader is currently positioned.
#[derive(Clone, Debug)]
struct EncodedValue {
    // `EncodedValue` instances are moved during `step_in` and `step_out` operations.
    // If the compiler decides that a value is too large to be moved with inline code,
    // it will relocate the value using memcpy instead. This can be quite slow by comparison.
    //
    // Be cautious when adding new member fields or modifying the data types of existing member
    // fields, as this may cause the in-memory size of `EncodedValue` instances to grow.
    //
    // See the Rust Performance Book section on measuring type sizes[1] for more information.
    // [1] https://nnethercote.github.io/perf-book/type-sizes.html#measuring-type-sizes
    ion_type: IonType,
    header: Header,
    is_null: bool,
    index_at_depth: usize,
    field_id: Option<RawSymbolToken>,

    // The `number_of_annotations` field stores the number of annotations associated with
    // the current value in the Ion stream.
    //
    // The CursorState struct uses a single Vec to store the annotations of the current
    // EncodedValue and any parent EncodedValues that have been stepped into. To read the
    // annotations associated with the current EncodedValue, the cursor will iterate over the
    // last `number_of_fields` entries in the annotations Vec. Each time that next() or step_out()
    // are called, the cursor will truncate `number_of_annotations` values from the end of
    // the annotations Vec.
    //
    // This approach allows us to re-use a single Vec for all annotations over the course
    // of the entire Ion stream. It also minimizes the size of the `EncodedValue` struct
    // (as calculated with `mem::size_of::<EncodedValue>()`); a Vec takes 24 bytes to
    // represent on the stack, while storing the number of annotations takes 1 byte.
    number_of_annotations: u8,

    // Each encoded value has up to five components, appearing in the following order:
    //
    // [ field_id? | annotations? | header (type descriptor) | header_length? | value ]
    //
    // Components shown with a `?` are optional.
    //
    // EncodedValue stores the offset of the type descriptor byte from the beginning of the
    // data source (`header_offset`). The lengths of the other fields can be used to calculate
    // their positions relative to the type descriptor byte.

    // The number of bytes used to encode the field ID (if present) preceding the Ion value. If
    // `field_id` is undefined, `field_id_length` will be zero.
    field_id_length: u8,
    // The number of bytes used to encode the annotations wrapper (if present) preceding the Ion
    // value. If `annotations` is empty, `field_id_length` will be zero.
    annotations_length: u8,
    // Type descriptor byte location.
    header_offset: usize,
    // The number of bytes used to encode the header not including the type descriptor byte.
    header_length: u8,
    // The number of bytes used to encode the value itself, not including the header byte
    // or length fields.
    value_length: usize,
}

impl EncodedValue {
    /// Returns the offset of the current value's type descriptor byte.
    fn header_offset(&self) -> usize {
        self.header_offset as usize
    }

    /// Returns the length of this value's header, including the type descriptor byte and any
    /// additional bytes used to encode the value's length.
    fn header_length(&self) -> usize {
        // The `header_length` field does not include the type descriptor byte, so add 1.
        self.header_length as usize + 1
    }

    /// Returns an offset Range containing this value's type descriptor
    /// byte and any additional bytes used to encode the `length`.
    fn header_range(&self) -> Range<usize> {
        let start = self.header_offset;
        let end = start + self.header_length();
        start..end
    }

    /// Returns the number of bytes used to encode this value's data.
    /// If the value can fit in the type descriptor byte (e.g. `true`, `false`, `null`, `0`),
    /// this function will return 0.
    #[inline(always)]
    fn value_length(&self) -> usize {
        self.value_length
    }

    /// The offset of the first byte following the header (and length, if present).
    /// If `value_length()` returns zero, this offset is actually the first byte of
    /// the next encoded value and should not be read.
    fn value_offset(&self) -> usize {
        self.header_offset + self.header_length as usize + 1_usize
    }

    /// Returns an offset Range containing any bytes following the header.
    fn value_range(&self) -> Range<usize> {
        let start = self.value_offset();
        let end = start + self.value_length;
        start..end
    }

    /// Returns the index of the first byte that is beyond the end of the current value's encoding.
    fn value_end_exclusive(&self) -> usize {
        self.value_offset() + self.value_length
    }

    /// Returns the number of bytes used to encode this value's field ID, if present.
    fn field_id_length(&self) -> Option<usize> {
        self.field_id.as_ref()?;
        Some(self.field_id_length as usize)
    }

    /// Returns the offset of the first byte used to encode this value's field ID, if present.
    fn field_id_offset(&self) -> Option<usize> {
        self.field_id.as_ref()?;
        Some(self.header_offset - self.annotations_length as usize - self.field_id_length as usize)
    }

    /// Returns an offset Range that contains the bytes used to encode this value's field ID,
    /// if present.
    fn field_id_range(&self) -> Option<Range<usize>> {
        if let Some(start) = self.field_id_offset() {
            let end = start + self.field_id_length as usize;
            return Some(start..end);
        }
        None
    }

    /// Returns the number of bytes used to encode this value's annotations, if any.
    /// While annotations envelope the value that they decorate, this function does not include
    /// the length of the value itself.
    fn annotations_length(&self) -> Option<usize> {
        if self.number_of_annotations == 0 {
            return None;
        }
        Some(self.annotations_length as usize)
    }

    /// Returns the offset of the beginning of the annotations wrapper, if present.
    fn annotations_offset(&self) -> Option<usize> {
        if self.number_of_annotations == 0 {
            return None;
        }
        Some(self.header_offset - self.annotations_length as usize)
    }

    /// Returns an offset Range that includes the bytes used to encode this value's annotations,
    /// if any. While annotations envelope the value that they modify, this function does not
    /// include the bytes of the encoded value itself.
    fn annotations_range(&self) -> Option<Range<usize>> {
        if let Some(start) = self.annotations_offset() {
            let end = start + self.annotations_length as usize;
            return Some(start..end);
        }
        None
    }
}

impl Default for EncodedValue {
    fn default() -> EncodedValue {
        EncodedValue {
            ion_type: IonType::Null,
            header: Header {
                ion_type: None,
                ion_type_code: IonTypeCode::NullOrNop,
                length_code: length_codes::NULL,
            },
            field_id: None,
            is_null: true,
            index_at_depth: 0,
            field_id_length: 0,
            annotations_length: 0,
            header_offset: 0,
            header_length: 0,
            value_length: 0,
            number_of_annotations: 0,
        }
    }
}

// A low-level reader that offers no symbol management.
pub struct RawBinaryReader<R>
where
    R: IonDataSource,
{
    // The file, socket, array, or other data source containing binary Ion bytes
    data_source: R,
    // Used for individual data_source.read() calls independent of input buffering
    buffer: Vec<u8>,
    // Tracks our position in the stream and information about the current value
    cursor: CursorState,
    // A jump table of pre-parsed header bytes
    header_cache: Vec<IonResult<Option<Header>>>,
}

/* CursorState is broken out from the BinaryIonCursor struct to allow it to be cloned
 * or replaced as part of a seek operation.
 * See: https://github.com/amzn/ion-rust/issues/21
 */
#[derive(Clone, Debug)]
pub struct CursorState {
    // Indicates whether the reader is positioned over an IVM, a value, or nothing.
    current_item: RawStreamItem,
    // The (major, minor) version pair of the stream being read. Defaults to (1, 0)
    ion_version: (u8, u8),
    // How many bytes we've read from our data source
    bytes_read: usize,
    // How deeply nested the cursor is at the moment
    depth: usize,
    // The number of values that have been read at the current depth
    index_at_depth: usize,
    // Whether the cursor is currently traversing a struct's fields
    is_in_struct: bool,
    // Information about the value on which the cursor is currently sitting
    value: EncodedValue,
    // All of the values into which the cursor has stepped. Empty at the top level.
    parents: Vec<EncodedValue>,
    // All of the annotations on values in `parents` and the current value.
    // Having a single, reusable Vec reduces allocations and keeps the size of
    // the EncodedValue type (which is frequently moved) small.
    annotations: Vec<RawSymbolToken>,
}

/// Verifies that the current value is of the expected type and that the bytes representing that
/// value have not yet been consumed from the data source. This macro is called by the
/// RawBinaryReader#read_{typename} methods.
macro_rules! read_safety_checks {
    ( $raw_binary_reader:ident, $ion_type:expr ) => {
        // Make sure that:
        // * the type descriptor's IonType aligns with what the Cursor expects to read
        // * the value under the cursor is not a null, even if the IonType lines up
        if $raw_binary_reader.cursor.value.ion_type != $ion_type
            || $raw_binary_reader.cursor.value.is_null
        {
            return Err($raw_binary_reader.expected(format!("{} value", $ion_type)));
        }
        // Make sure the cursor hasn't already advanced beyond the encoded bytes for this value.
        if $raw_binary_reader.finished_reading_value() {
            return illegal_operation(format!(
                "You cannot read the same {:?} value more than once.",
                $ion_type
            ));
        }
    };
}

impl<R: IonDataSource> StreamReader for RawBinaryReader<R> {
    type Item = RawStreamItem;
    type Symbol = RawSymbolToken;

    fn ion_version(&self) -> (u8, u8) {
        self.cursor.ion_version
    }

    #[inline]
    // `next()` resembles `Iterator::next`, generating a clippy warning.
    #[allow(clippy::should_implement_trait)]
    fn next(&mut self) -> IonResult<RawStreamItem> {
        // Skip the remaining bytes of the current value, if any.
        let _ = self.skip_current_value()?;

        if let Some(parent) = self.cursor.parents.last() {
            // If the cursor is nested inside a parent object, don't attempt to read beyond the end of
            // the parent. Users can call '.step_out()' to progress beyond the container.
            if self.cursor.bytes_read >= parent.value_end_exclusive() {
                return Ok(self.set_current_item(RawStreamItem::Nothing));
            }
        }

        // If we're in a struct, read the field id that must precede each value.
        self.cursor.value.field_id = if self.cursor.is_in_struct {
            Some(RawSymbolToken::SymbolId(self.read_field_id()?))
        } else {
            self.cursor.value.field_id_length = 0;
            None
        };

        // Pull the next byte from the data source and interpret it as a value header
        let mut header = match self.read_next_value_header()? {
            Some(header) => header,
            None => return Ok(self.set_current_item(RawStreamItem::Nothing)),
        };
        self.cursor.value.header = header;

        // Skip over consecutive NOP padding, but don't handle nulls
        if header.is_nop() {
            let number_of_bytes = self.read_standard_length()?;

            // If we're in a container, validate that the NOP pad doesn't overrun the container end
            if let Some(parent) = self.cursor.parents.last() {
                // The NOP padding described starts on the byte *after* the NOP header
                let nop_offset = self.cursor.bytes_read;
                let nop_range = (nop_offset)..(nop_offset + number_of_bytes);
                let container_range = parent.value_range();

                if nop_range.end > container_range.end {
                    // This NOP is malformed, let's assemble data for error reporting
                    return decoding_error(&format!(
                        "{bytes}-byte NOP padding on byte range {nop_range:?} is {over} \
                        byte{s} past container content range {container_range:?}",
                        bytes = number_of_bytes,
                        nop_range = nop_range,
                        over = nop_range.end - container_range.end,
                        s = if number_of_bytes == 1 { "" } else { "s" },
                        container_range = container_range,
                    ));
                }
            }

            self.skip_bytes(number_of_bytes)?;

            //TODO: Find a way to do this non-recursively when we clean up/refactor next()
            return self.next();
        }

        self.clear_annotations();
        let mut expected_annotated_value_length = None;
        if header.ion_type_code == IonTypeCode::AnnotationOrIvm {
            if header.length_code == 0 {
                // This is actually the first byte in an Ion Version Marker
                let ivm = self.read_ivm()?;
                return Ok(self.set_current_item(ivm));
            }
            // We've found an annotated value. Read all of the annotation symbols leading
            // up to the value
            expected_annotated_value_length = Some(self.read_annotations()?);
            // Now read the next header representing the value itself.
            header = match self.read_next_value_header()? {
                Some(header) => header,
                None => return Ok(self.set_current_item(RawStreamItem::Nothing)),
            };
            if header.is_nop() {
                return decoding_error(&format!(
                    "The annotation wrapper starting at byte {} contains NOP padding, which is illegal.",
                    self.cursor.bytes_read
                ));
            }
            self.cursor.value.header = header;
        }

        let _ = self.process_header_by_type_code(header)?;

        self.cursor.index_at_depth += 1;
        self.cursor.value.index_at_depth = self.cursor.index_at_depth;

        // If this value had an annotations wrapper, make sure the length of the value we just
        // found is the expected size.
        if let Some(expected_length) = expected_annotated_value_length {
            let value = &self.cursor.value;
            let encoded_length = value.header_length() + value.value_length();
            if encoded_length != expected_length {
                return decoding_error(format!(
                    "annotations wrapper expected a {}-byte value, but found a {}-byte {}",
                    expected_length, encoded_length, value.ion_type
                ));
            }
        }

        let item = RawStreamItem::nullable_value(self.cursor.value.ion_type, self.is_null());
        Ok(self.set_current_item(item))
    }

    fn current(&self) -> Self::Item {
        self.cursor.current_item
    }

    fn ion_type(&self) -> Option<IonType> {
        use RawStreamItem::*;
        match self.current() {
            Value(ion_type) | Null(ion_type) => Some(ion_type),
            _ => None,
        }
    }

    fn is_null(&self) -> bool {
        self.cursor.value.is_null
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'a> {
        let num_annotations = self.cursor.value.number_of_annotations as usize;
        if num_annotations == 0 {
            return Box::new(EMPTY_SLICE_RAW_SYMBOL_TOKEN.iter().cloned().map(Ok));
        }
        let end = self.cursor.annotations.len();
        let start = end - num_annotations;
        let annotations = &self.cursor.annotations[start..end];
        Box::new(annotations.iter().cloned().map(Ok))
    }

    fn has_annotations(&self) -> bool {
        self.cursor.value.number_of_annotations > 0
    }

    fn number_of_annotations(&self) -> usize {
        self.cursor.value.number_of_annotations as usize
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        if let Some(ref symbol) = self.cursor.value.field_id {
            return Ok(symbol.clone());
        }
        illegal_operation(
            format!(
                "field_name() can only be called when the reader is positioned inside a struct; current parent: {:?}",
                self.parent_type()
            )
        )
    }

    fn read_null(&mut self) -> IonResult<IonType> {
        if self.is_null() {
            return Ok(self.cursor.value.ion_type);
        }
        Err(self.expected("null value"))
    }

    fn read_bool(&mut self) -> IonResult<bool> {
        read_safety_checks!(self, IonType::Boolean);

        // No reading from the stream occurs -- the header contains all of the information we need.
        let representation = self.cursor.value.header.length_code;

        match representation {
            0 => Ok(false),
            1 => Ok(true),
            _ => decoding_error(&format!(
                "Found a boolean value with an illegal representation: {}",
                representation
            )),
        }
    }

    fn read_integer(&mut self) -> IonResult<Integer> {
        read_safety_checks!(self, IonType::Integer);

        let uint = self.read_value_as_uint()?;
        let value = Integer::from(uint);

        use self::IonTypeCode::*;
        let value = match (self.cursor.value.header.ion_type_code, value) {
            (PositiveInteger, integer) => integer,
            (NegativeInteger, integer) if integer.is_zero() => {
                return decoding_error("found a negative integer (typecode=3) with a value of 0");
            }
            (NegativeInteger, integer) => -integer,
            itc => unreachable!("Unexpected IonTypeCode: {:?}", itc),
        };

        Ok(value)
    }

    fn read_i64(&mut self) -> IonResult<i64> {
        self.read_integer()?
            .as_i64()
            .ok_or_else(|| decoding_error_raw("integer was too large to fit in an i64"))
    }

    fn read_f32(&mut self) -> IonResult<f32> {
        match self.read_f64() {
            Ok(value) => Ok(value as f32), // Lossy if the value was 64 bits
            Err(e) => Err(e),
        }
    }

    fn read_f64(&mut self) -> IonResult<f64> {
        read_safety_checks!(self, IonType::Float);

        let number_of_bytes = self.cursor.value.value_length;

        self.read_slice(number_of_bytes, |buffer: &[u8]| {
            let value = match number_of_bytes {
                0 => 0f64,
                4 => f64::from(BigEndian::read_f32(buffer)),
                8 => BigEndian::read_f64(buffer),
                _ => {
                    return decoding_error(&format!(
                        "Encountered an illegal value for a Float length: {}",
                        number_of_bytes
                    ))
                }
            };
            Ok(value)
        })
    }

    fn read_decimal(&mut self) -> IonResult<Decimal> {
        read_safety_checks!(self, IonType::Decimal);

        if self.cursor.value.value_length == 0 {
            return Ok(Decimal::new(0i32, 0i64));
        }

        let exponent_var_int = self.read_var_int()?;
        let coefficient_size_in_bytes =
            self.cursor.value.value_length - exponent_var_int.size_in_bytes();

        let exponent = exponent_var_int.value() as i64;
        let coefficient = self.read_int(coefficient_size_in_bytes)?;

        if coefficient.is_negative_zero() {
            return Ok(Decimal::negative_zero_with_exponent(exponent));
        }

        Ok(Decimal::new(coefficient, exponent))
    }

    fn read_string(&mut self) -> IonResult<String> {
        self.map_string(|s| s.to_owned())
    }

    fn map_string<F, U>(&mut self, f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&str) -> U,
    {
        self.map_string_bytes(|buffer| match std::str::from_utf8(buffer) {
            Ok(utf8_text) => Ok(f(utf8_text)),
            Err(utf8_error) => {
                return decoding_error(&format!(
                    "The requested string was not valid UTF-8: {:?}",
                    utf8_error
                ))
            }
        })?
    }

    fn map_string_bytes<F, U>(&mut self, f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        read_safety_checks!(self, IonType::String);

        let length_in_bytes = self.cursor.value.value_length;
        self.read_slice(length_in_bytes, |buffer: &[u8]| Ok(f(buffer)))
    }

    #[inline(always)]
    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        read_safety_checks!(self, IonType::Symbol);

        let uint = self.read_value_as_uint()?;
        let symbol_id = usize::try_from(uint.value())?;
        Ok(RawSymbolToken::SymbolId(symbol_id))
    }

    fn read_blob(&mut self) -> IonResult<Vec<u8>> {
        self.map_blob(|b| Vec::from(b))
    }

    fn map_blob<F, U>(&mut self, f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        read_safety_checks!(self, IonType::Blob);

        let number_of_bytes = self.cursor.value.value_length;
        self.read_slice(number_of_bytes, |buffer: &[u8]| Ok(f(buffer)))
    }

    fn read_clob(&mut self) -> IonResult<Vec<u8>> {
        self.map_clob(|c| Vec::from(c))
    }

    fn map_clob<F, U>(&mut self, f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        read_safety_checks!(self, IonType::Clob);

        let number_of_bytes = self.cursor.value.value_length;
        self.read_slice(number_of_bytes, |buffer: &[u8]| Ok(f(buffer)))
    }

    fn read_timestamp(&mut self) -> IonResult<Timestamp> {
        read_safety_checks!(self, IonType::Timestamp);

        let datetime_start_offset = self.cursor.bytes_read;

        let offset = self.read_var_int()?;
        let is_known_offset = !offset.is_negative_zero();
        let offset_minutes = offset.value() as i32;
        let year = self.read_var_uint()?.value() as u32;

        // Year precision

        let builder = Timestamp::with_year(year);
        if self.finished_reading_value() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        // Month precision

        let month = self.read_var_uint()?.value() as u32;
        let builder = builder.with_month(month);
        if self.finished_reading_value() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        // Day precision

        let day = self.read_var_uint()?.value() as u32;
        let builder = builder.with_day(day);
        if self.finished_reading_value() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        // Hour-and-minute precision

        let hour = self.read_var_uint()?.value() as u32;
        if self.finished_reading_value() {
            return decoding_error("timestamps with an hour must also specify a minute");
        }
        let minute = self.read_var_uint()?.value() as u32;
        let builder = builder.with_hour_and_minute(hour, minute);
        if self.finished_reading_value() {
            let timestamp = if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            return Ok(timestamp);
        }

        // Second precision

        let second = self.read_var_uint()?.value() as u32;
        let builder = builder.with_second(second);
        if self.finished_reading_value() {
            let timestamp = if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            return Ok(timestamp);
        }

        // Fractional second precision

        let subsecond_exponent = self.read_var_int()?.value();
        // The remaining bytes represent the coefficient. We need to determine how many bytes
        // we've read to know how many remain.
        let value_bytes_read = self.cursor.bytes_read - datetime_start_offset;
        let coefficient_size_in_bytes = self.cursor.value.value_length - value_bytes_read;
        let subsecond_coefficient = if coefficient_size_in_bytes == 0 {
            DecodedInt::zero()
        } else {
            self.read_int(coefficient_size_in_bytes)?
        };

        let builder = builder
            .with_fractional_seconds(Decimal::new(subsecond_coefficient, subsecond_exponent));
        let timestamp = if is_known_offset {
            builder.build_utc_fields_at_offset(offset_minutes)
        } else {
            builder.build_at_unknown_offset()
        }?;

        Ok(timestamp)
    }

    #[inline]
    fn step_in(&mut self) -> IonResult<()> {
        use self::IonType::*;
        use std::mem;
        self.cursor.is_in_struct = match self.cursor.value.ion_type {
            Struct => true,
            List | SExpression => false,
            _ => panic!("You cannot step into a(n) {:?}", self.cursor.value.ion_type),
        };
        self.cursor.parents.push(EncodedValue::default());
        // We've just push()ed a value onto the `parents` Vec, so it's safe to call
        // last_mut().unwrap() below.
        mem::swap(
            &mut self.cursor.value,
            self.cursor.parents.last_mut().unwrap(),
        );
        self.cursor.depth += 1;
        self.cursor.index_at_depth = 0;
        Ok(())
    }

    #[inline]
    fn step_out(&mut self) -> IonResult<()> {
        use std::mem;

        // Clear annotations belonging to the current value before we step out.
        self.clear_annotations();

        // EncodedLevel is a fairly large struct. Using Vec::pop() to remove the last item causes
        // the last EncodedLevel to be moved to the stack before it's swap()ped into
        // self.cursor.value, which is surprisingly expensive. As an optimization, we can get
        // an in-place reference to the last parent in the Vec and perform the swap() there.
        // We then truncate the Vec to discard the old value that was swapped into the last
        // Vec position.

        // Get an in-place handle to parent
        let parent = self
            .cursor
            .parents
            .last_mut()
            .ok_or_else(|| illegal_operation_raw("You cannot step out of the root level."))?;

        // We're stepping out of the container, so we need to skip to the end of it.
        let value_end_excl = parent.value_end_exclusive();
        let bytes_read = self.cursor.bytes_read;
        let bytes_to_skip = value_end_excl - bytes_read;

        // Set the parent as the current value
        mem::swap(&mut self.cursor.value, parent);

        // Drop the last entry in the parents Vec in-place to avoid another move.
        let len_without_last = self.cursor.parents.len() - 1;
        self.cursor.parents.truncate(len_without_last);

        // Check to see what the new top of the parents stack is.
        if let Some(parent) = self.cursor.parents.last() {
            self.cursor.is_in_struct = parent.ion_type == IonType::Struct;
        } else {
            self.cursor.is_in_struct = false;
        }

        self.cursor.index_at_depth = self.cursor.value.index_at_depth;
        self.cursor.depth -= 1;
        self.skip_bytes(bytes_to_skip)?;
        Ok(())
    }

    fn parent_type(&self) -> Option<IonType> {
        self.cursor.parents.last().map(|value| value.ion_type)
    }

    fn depth(&self) -> usize {
        self.cursor.depth
    }
}

const EMPTY_SLICE_U8: &[u8] = &[];
const EMPTY_SLICE_RAW_SYMBOL_TOKEN: &[RawSymbolToken] = &[];

/// Additional functionality that's only available if the data source is in-memory, such as a
/// Vec<u8> or &[u8]).
impl<T> RawBinaryReader<io::Cursor<T>>
where
    T: AsRef<[u8]>,
{
    delegate! {
        to self.cursor.value {
            pub fn field_id_length(&self) -> Option<usize>;
            pub fn field_id_offset(&self) -> Option<usize>;
            pub fn field_id_range(&self) -> Option<Range<usize>>;

            pub fn annotations_length(&self) -> Option<usize>;
            pub fn annotations_offset(&self) -> Option<usize>;
            pub fn annotations_range(&self) -> Option<Range<usize>>;

            pub fn header_length(&self) -> usize;
            pub fn header_offset(&self) -> usize;
            pub fn header_range(&self) -> Range<usize>;

            pub fn value_length(&self) -> usize;
            pub fn value_offset(&self) -> usize;
            pub fn value_range(&self) -> Range<usize>;
        }
    }

    /// Returns a slice containing the entirety of this encoded value, including its field ID
    /// (if present), its annotations (if present), its header, and the encoded value itself.
    /// Calling this function does not advance the cursor.
    pub fn raw_bytes(&self) -> Option<&[u8]> {
        self.ion_type()?;
        let start: usize;
        if let Some(field_id_offset) = self.cursor.value.field_id_offset() {
            start = field_id_offset;
        } else if let Some(annotations_offset) = self.cursor.value.annotations_offset() {
            start = annotations_offset;
        } else {
            start = self.cursor.value.header_offset;
        }
        let end = self.cursor.value.value_end_exclusive();
        let bytes = self.data_source.get_ref().as_ref();
        Some(&bytes[start..end])
    }

    /// Returns a slice containing the current value's header's raw bytes without advancing the
    /// cursor. Includes the type descriptor byte and any bytes used to represent the `length`
    /// field.
    pub fn raw_header_bytes(&self) -> Option<&[u8]> {
        self.ion_type()?;
        let bytes = self.data_source.get_ref().as_ref();
        Some(&bytes[self.cursor.value.header_range()])
    }

    /// Returns a slice containing the current value's raw bytes (not including its field ID,
    /// annotations, or type descriptor byte) without advancing the cursor.
    pub fn raw_value_bytes(&self) -> Option<&[u8]> {
        self.ion_type()?;
        let bytes = self.data_source.get_ref().as_ref();
        Some(&bytes[self.cursor.value.value_range()])
    }

    /// Returns a slice containing the current value's raw field ID bytes (if present) without
    /// advancing the cursor.
    pub fn raw_field_id_bytes(&self) -> Option<&[u8]> {
        self.ion_type()?;
        if let Some(range) = self.cursor.value.field_id_range() {
            let bytes = self.data_source.get_ref().as_ref();
            return Some(&bytes[range]);
        }
        None
    }

    /// Returns a slice containing the current value's annotations (if any) without advancing the
    /// cursor.
    pub fn raw_annotations_bytes(&self) -> Option<&[u8]> {
        self.ion_type()?;
        if let Some(range) = self.cursor.value.annotations_range() {
            let bytes = self.data_source.get_ref().as_ref();
            return Some(&bytes[range]);
        }
        None
    }
}

impl<R> RawBinaryReader<R>
where
    R: IonDataSource,
{
    pub fn new(data_source: R) -> Self {
        RawBinaryReader {
            data_source,
            buffer: vec![0; 4096],
            cursor: CursorState {
                current_item: RawStreamItem::Nothing,
                ion_version: (1, 0),
                bytes_read: 0,
                depth: 0,
                index_at_depth: 0,
                is_in_struct: false,
                value: Default::default(),
                parents: Vec::new(),
                annotations: Vec::new(),
            },
            header_cache: create_header_byte_jump_table(),
        }
    }

    /// Helper method to record the [RawStreamItem] over which the reader is currently
    /// positioned before returning from [next].
    fn set_current_item(&mut self, item: RawStreamItem) -> RawStreamItem {
        self.cursor.current_item = item;
        item
    }

    pub fn is_null(&self) -> bool {
        self.cursor.value.is_null
    }

    fn finished_reading_value(&mut self) -> bool {
        self.cursor.value.value_length > 0
            && self.cursor.bytes_read >= self.cursor.value.value_end_exclusive()
    }

    fn clear_annotations(&mut self) {
        if self.cursor.value.number_of_annotations > 0 {
            // Drop the annotations belonging to the last value read from the annotations Vec
            let prev_num_annotations = self.cursor.value.number_of_annotations as usize;
            let new_annotations_len = self.cursor.annotations.len() - prev_num_annotations;
            self.cursor.annotations.truncate(new_annotations_len);
            self.cursor.value.number_of_annotations = 0;
            self.cursor.value.annotations_length = 0;
        }
    }

    fn read_ivm(&mut self) -> IonResult<RawStreamItem> {
        if self.depth() > 0 {
            return decoding_error("found a binary IVM inside a container");
        }
        let (major, minor) = self.read_slice(3, |bytes| match *bytes {
            [major, minor, 0xEA] => Ok((major, minor)),
            [major, minor, other] => decoding_error(format!(
                "Illegal IVM: 0xE0 0x{:X} 0x{:X} 0x{:X}",
                major, minor, other
            )),
            _ => unreachable!("read_slice did not return the requested number of bytes"),
        })?;

        if !matches!((major, minor), (1, 0)) {
            decoding_error(format!("Unsupported Ion version {:X}.{:X}", major, minor))
        } else {
            self.cursor.ion_version = (major, minor);
            Ok(RawStreamItem::VersionMarker(major, minor))
        }
    }

    #[inline(always)]
    fn read_var_uint(&mut self) -> IonResult<VarUInt> {
        let var_uint = VarUInt::read(&mut self.data_source)?;
        self.cursor.bytes_read += var_uint.size_in_bytes();
        Ok(var_uint)
    }

    #[inline(always)]
    fn read_var_int(&mut self) -> IonResult<VarInt> {
        let var_int = VarInt::read(&mut self.data_source)?;
        self.cursor.bytes_read += var_int.size_in_bytes() as usize;
        Ok(var_int)
    }

    // Useful when the entire value (all bytes after the type/length header) are represented by
    // a single UInt. (i.e. Integer and Symbol)
    #[inline(always)]
    fn read_value_as_uint(&mut self) -> IonResult<DecodedUInt> {
        let number_of_bytes = self.cursor.value.value_length;
        self.read_uint(number_of_bytes)
    }

    #[inline(always)]
    fn read_uint(&mut self, number_of_bytes: usize) -> IonResult<DecodedUInt> {
        let uint = DecodedUInt::read(&mut self.data_source, number_of_bytes)?;
        self.cursor.bytes_read += uint.size_in_bytes();
        Ok(uint)
    }

    #[inline(always)]
    fn read_int(&mut self, number_of_bytes: usize) -> IonResult<DecodedInt> {
        let int = DecodedInt::read(&mut self.data_source, number_of_bytes)?;
        self.cursor.bytes_read += int.size_in_bytes();
        Ok(int)
    }

    fn process_header_by_type_code(&mut self, header: Header) -> IonResult<()> {
        // TODO: Is cursor.value.ion_type redundant?
        self.cursor.value.ion_type = header.ion_type.ok_or_else(|| {
            decoding_error_raw(format!(
                "found an invalid type code: {:?}",
                header.ion_type_code
            ))
        })?;
        self.cursor.value.header = header;
        self.cursor.value.is_null = header.length_code == length_codes::NULL;

        // We've already read the header byte, so it's now behind the cursor.
        self.cursor.value.header_offset = self.cursor.bytes_read - 1;

        use IonTypeCode::*;
        let length = match header.ion_type_code {
            NullOrNop | Boolean => 0,
            PositiveInteger | NegativeInteger | Decimal | String | Symbol | List | SExpression
            | Clob | Blob => self.read_standard_length()?,
            Timestamp => {
                let length = self.read_standard_length()?;
                if length <= 1 && !self.cursor.value.is_null {
                    return decoding_error(
                        "found a non-null timestamp (typecode=6) with a length <= 1",
                    );
                }
                length
            }
            Float => self.read_float_length()?,
            Struct => self.read_struct_length()?,
            AnnotationOrIvm => return decoding_error("found an annotation wrapping an annotation"),
            Reserved => return decoding_error("found an Ion Value with a Reserved type code"),
        };

        self.cursor.value.header_length =
            (self.cursor.bytes_read - self.cursor.value.header_offset - 1) as u8;
        self.cursor.value.value_length = length;
        Ok(())
    }

    #[inline(always)]
    fn read_standard_length(&mut self) -> IonResult<usize> {
        let length = match self.cursor.value.header.length_code {
            length_codes::NULL => 0,
            length_codes::VAR_UINT => self.read_var_uint()?.value(),
            magnitude => magnitude as usize,
        };

        Ok(length)
    }

    fn read_float_length(&mut self) -> IonResult<usize> {
        let length = match self.cursor.value.header.length_code {
            0 => 0,
            4 => 4,
            8 => 8,
            length_codes::NULL => 0,
            _ => {
                return decoding_error(format!(
                    "Found a Float value with an illegal length: {}",
                    self.cursor.value.header.length_code
                ))
            }
        };
        Ok(length)
    }

    fn read_struct_length(&mut self) -> IonResult<usize> {
        let length = match self.cursor.value.header.length_code {
            length_codes::NULL => 0,
            // If the length code is `1`, it indicates an ordered struct. This is a special case
            // of struct; it cannot be empty, and its fields must appear in ascending order of
            // symbol ID. For the time being, the binary reader doesn't implement any special
            // handling for it.
            1 => {
                let length = self.read_var_uint()?.value();
                if length == 0 {
                    return decoding_error("found an empty ordered struct");
                }
                length
            }
            length_codes::VAR_UINT => self.read_var_uint()?.value(),
            magnitude => magnitude as usize,
        };

        Ok(length)
    }

    #[inline(always)]
    fn read_next_value_header(&mut self) -> IonResult<Option<Header>> {
        let next_byte: u8 = match self.next_byte() {
            Ok(Some(byte)) => byte,      // This is the one-byte header of the next value.
            Ok(None) => return Ok(None), // There's no more data to read.
            Err(error) => return Err(error), // Something went wrong while reading the next byte.
        };

        self.header_cache[next_byte as usize].clone()
    }

    fn next_byte(&mut self) -> IonResult<Option<u8>> {
        let byte = self.data_source.next_byte();
        self.cursor.bytes_read += 1;
        byte
    }

    fn skip_bytes(&mut self, number_of_bytes: usize) -> IonResult<()> {
        if number_of_bytes == 0 {
            return Ok(());
        }

        self.data_source.skip_bytes(number_of_bytes)?;
        self.cursor.bytes_read += number_of_bytes;
        Ok(())
    }

    fn skip_current_value(&mut self) -> IonResult<()> {
        let position = self.cursor.bytes_read;
        let end = self.cursor.value.value_end_exclusive();

        // Don't skip a value if we haven't called `next()` at the current level
        if self.cursor.index_at_depth > 0 {
            // NOPs are not values, so bytes_read can be past the last consumed value (`end`).
            // This is an artifact of consuming NOP sleds with recursive `next()`, and could be
            // fixed with refactoring.
            // `saturating_sub` avoids underflow by returning 0 if `position` > `end`.
            let bytes_to_skip = end.saturating_sub(position);
            self.skip_bytes(bytes_to_skip)
        } else {
            Ok(())
        }
    }

    fn read_field_id(&mut self) -> IonResult<SymbolId> {
        let var_uint = self.read_var_uint()?;
        let field_id = var_uint.value();
        self.cursor.value.field_id_length = var_uint.size_in_bytes() as u8;
        Ok(field_id)
    }

    /// Reads the annotations in the annotations wrapper and returns the expected length of the
    /// wrapped value that will follow.
    fn read_annotations(&mut self) -> IonResult<usize> {
        let num_annotations_before = self.cursor.annotations.len();
        // The first byte of the annotations envelope is now behind the cursor
        let annotations_offset = self.cursor.bytes_read - 1;
        let annotations_and_value_length = self.read_standard_length()?;
        let annotations_length = self.read_var_uint()?;
        if annotations_length.value() == 0 {
            return decoding_error("found an annotations wrapper with no annotations");
        }
        let expected_value_length = annotations_and_value_length
            - annotations_length.size_in_bytes()
            - annotations_length.value();
        if expected_value_length == 0 {
            return decoding_error("found an annotation wrapper with no value");
        }
        let mut bytes_read: usize = 0;

        while bytes_read < annotations_length.value() {
            let var_uint = self.read_var_uint()?;
            bytes_read += var_uint.size_in_bytes();
            let annotation_symbol_id = var_uint.value();
            self.cursor
                .annotations
                .push(RawSymbolToken::SymbolId(annotation_symbol_id));
        }
        let new_annotations_count = self.cursor.annotations.len() - num_annotations_before;
        self.cursor.value.number_of_annotations = new_annotations_count as u8;

        // The annotations type descriptor byte + the length of the annotations sequence
        self.cursor.value.annotations_length = (self.cursor.bytes_read - annotations_offset) as u8;
        Ok(expected_value_length)
    }

    fn read_exact(&mut self, number_of_bytes: usize) -> IonResult<()> {
        // Grow the cursor's reusable Vec<u8> if needed, filling it with zeros
        let buffer: &mut [u8] = if self.buffer.len() < number_of_bytes {
            self.buffer.resize(number_of_bytes, 0);
            self.buffer.as_mut()
        } else {
            // Otherwise, split the Vec's underlying storage to get a &mut [u8] slice of the
            // required size.
            let (required_buffer, _) = self.buffer.split_at_mut(number_of_bytes);
            required_buffer
        };

        // Ask the data source to populate our appropriately-sized slice.
        self.data_source.read_exact(buffer)?;
        self.cursor.bytes_read += number_of_bytes;
        Ok(())
    }

    /// See IonDataSource#read_slice.
    fn read_slice<T, F>(&mut self, number_of_bytes: usize, slice_processor: F) -> IonResult<T>
    where
        F: FnOnce(&[u8]) -> IonResult<T>,
    {
        self.cursor.bytes_read += number_of_bytes;
        self.data_source
            .read_slice(number_of_bytes, &mut self.buffer, slice_processor)
    }

    /// Constructs an [IonError::IllegalOperation] which explains that the reader was asked to
    /// perform an action that is only allowed when it is positioned over the item type described
    /// by the parameter `expected`.
    fn expected<E: Display>(&self, expected: E) -> IonError {
        illegal_operation_raw(format!(
            "type mismatch: expected a(n) {} but positioned over a(n) {}",
            expected,
            self.current()
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::io;

    use crate::binary::constants::v1_0::IVM;
    use crate::binary::raw_binary_reader::RawBinaryReader;
    use crate::raw_reader::{RawStreamItem, RawStreamItem::*};
    use crate::raw_symbol_token::local_sid_token;
    use crate::result::{IonError, IonResult};
    use crate::stream_reader::StreamReader;
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;
    use crate::types::IonType;

    type TestDataSource = io::Cursor<Vec<u8>>;

    // Create a growable byte vector that starts with the Ion 1.0 version marker
    fn ion_data(bytes: &[u8]) -> Vec<u8> {
        let mut data = Vec::new();
        data.extend_from_slice(&IVM);
        data.extend_from_slice(bytes);
        data
    }

    // Prepends an Ion Version Marker to the provided data and wraps it in an io::Cursor.
    fn data_source_for(bytes: &[u8]) -> TestDataSource {
        let data = ion_data(bytes);
        io::Cursor::new(data)
    }

    // Prepends an Ion 1.0 IVM to the provided data and then creates a BinaryIonCursor over it
    fn ion_cursor_for(bytes: &[u8]) -> RawBinaryReader<TestDataSource> {
        let mut binary_reader = RawBinaryReader::new(data_source_for(bytes));
        assert_eq!(binary_reader.ion_type(), None);
        assert_eq!(binary_reader.next(), Ok(VersionMarker(1, 0)));
        assert_eq!(binary_reader.ion_version(), (1u8, 0u8));
        binary_reader
    }

    #[test]
    fn test_parse_ivm() -> IonResult<()> {
        ion_cursor_for(&[]);
        Ok(())
    }

    #[test]
    fn test_parse_unsupported_version_in_ivm() -> IonResult<()> {
        let data: [u8; 4] = [0xE0, 0x01, 0x01, 0xEA]; // Ion version 1.1 is not supported
        let mut cursor = RawBinaryReader::new(io::Cursor::new(data));
        assert_eq!(cursor.ion_type(), None);
        assert!(matches!(cursor.next(), Err(IonError::DecodingError { .. })));
        Ok(())
    }

    #[test]
    fn test_parse_invalid_ivm() -> IonResult<()> {
        let data: [u8; 4] = [0xE0, 0x01, 0x00, 0xE0]; // IVM should end '0xEA' not '0xE0'
        let mut cursor = RawBinaryReader::new(io::Cursor::new(data));
        assert_eq!(cursor.ion_type(), None);
        assert!(matches!(cursor.next(), Err(IonError::DecodingError { .. })));
        Ok(())
    }

    #[test]
    fn test_read_null_null() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x0F]);
        assert_eq!(cursor.next()?, Null(IonType::Null));
        assert_eq!(cursor.read_null()?, IonType::Null);
        assert!(cursor.is_null());
        Ok(())
    }

    #[test]
    fn test_read_null_string() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x8F]);
        assert_eq!(cursor.next()?, Null(IonType::String));
        assert_eq!(cursor.read_null()?, IonType::String);
        assert!(cursor.is_null());
        Ok(())
    }

    #[test]
    fn test_read_bool_false() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x10]);
        assert_eq!(cursor.next()?, Value(IonType::Boolean));
        assert_eq!(cursor.read_bool()?, false);
        Ok(())
    }

    #[test]
    fn test_read_bool_true() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x11]);
        assert_eq!(cursor.next()?, Value(IonType::Boolean));
        assert_eq!(cursor.read_bool()?, true);
        Ok(())
    }

    #[test]
    fn test_read_i64_zero() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x20]);
        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.read_i64()?, 0i64);
        Ok(())
    }

    #[test]
    fn test_read_i64_positive() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x21, 0x01]);
        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.read_i64()?, 1i64);
        Ok(())
    }

    #[test]
    fn test_read_i64_negative() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x31, 0x01]);
        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.read_i64()?, -1i64);
        Ok(())
    }

    #[test]
    fn test_read_f64_zero() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x40]);
        assert_eq!(cursor.next()?, Value(IonType::Float));
        assert_eq!(cursor.read_f64()?, 0f64);
        Ok(())
    }

    #[test]
    fn test_read_decimal_zero() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x50]);
        assert_eq!(cursor.next()?, Value(IonType::Decimal));
        assert_eq!(cursor.read_decimal()?, Decimal::new(0, 0));
        Ok(())
    }

    #[test]
    fn test_read_decimal_negative_zero() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x52, 0x80, 0x80]);
        assert_eq!(cursor.next()?, Value(IonType::Decimal));
        assert_eq!(cursor.read_decimal()?, Decimal::negative_zero());
        Ok(())
    }

    #[test]
    fn test_read_decimal_positive_exponent() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x52, 0x81, 0x02]);
        assert_eq!(cursor.next()?, Value(IonType::Decimal));
        assert_eq!(cursor.read_decimal()?, 20.into());
        Ok(())
    }

    #[test]
    fn test_read_decimal_negative_exponent() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x52, 0xC1, 0x02]);
        assert_eq!(cursor.next()?, Value(IonType::Decimal));
        assert_eq!(cursor.read_decimal()?, Decimal::new(2, -1));
        Ok(())
    }

    #[test]
    fn test_read_timestamp() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x68, 0x80, 0x0F, 0xD0, 0x81, 0x81, 0x80, 0x80, 0x80]);
        assert_eq!(cursor.next()?, Value(IonType::Timestamp));
        let expected = Timestamp::with_ymd_hms(2000, 1, 1, 0, 0, 0).build_at_offset(0)?;
        assert_eq!(cursor.read_timestamp()?, expected);
        Ok(())
    }

    #[test]
    fn test_read_timestamp_year() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x63, 0xC0, 0x0F, 0xC6]);
        assert_eq!(cursor.next()?, Value(IonType::Timestamp));
        let expected = Timestamp::with_year(1990).build()?;
        assert_eq!(cursor.read_timestamp()?, expected);
        Ok(())
    }

    #[test]
    fn test_read_timestamp_year_month() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x64, 0xC0, 0x0F, 0xE2, 0x86]);
        assert_eq!(cursor.next()?, Value(IonType::Timestamp));
        let expected = Timestamp::with_year(2018).with_month(6).build()?;
        assert_eq!(cursor.read_timestamp()?, expected);
        Ok(())
    }

    #[test]
    fn test_read_timestamp_year_month_day() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x65, 0xC0, 0x0F, 0xE2, 0x86, 0x83]);
        assert_eq!(cursor.next()?, Value(IonType::Timestamp));
        let expected = Timestamp::with_ymd(2018, 6, 3).build()?;
        assert_eq!(cursor.read_timestamp()?, expected);
        Ok(())
    }

    #[test]
    fn test_read_timestamp_year_month_day_hour_minute() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x67, 0x80, 0x0F, 0xE2, 0x86, 0x83, 0x8F, 0xA1]);
        assert_eq!(cursor.next()?, Value(IonType::Timestamp));
        let expected = Timestamp::with_ymd(2018, 6, 3)
            .with_hour_and_minute(15, 33)
            .build_at_offset(0)?;
        assert_eq!(cursor.read_timestamp()?, expected);
        Ok(())
    }

    #[test]
    fn test_read_timestamp_year_month_day_hour_minute_second() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x68, 0x80, 0x0F, 0xE2, 0x86, 0x83, 0x8F, 0xA1, 0x8B]);
        assert_eq!(cursor.next()?, Value(IonType::Timestamp));
        let expected = Timestamp::with_ymd(2018, 6, 3)
            .with_hms(15, 33, 11)
            .build_at_offset(0)?;
        assert_eq!(cursor.read_timestamp()?, expected);
        Ok(())
    }

    #[test]
    fn test_read_timestamp_year_month_day_hour_minute_second_ms() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[
            0x6B, 0x80, 0x0F, 0xE2, 0x86, 0x83, 0x8F, 0xA1, 0x8B, 0xC3, 0x02, 0x29,
        ]);
        assert_eq!(cursor.next()?, Value(IonType::Timestamp));
        let expected = Timestamp::with_ymd(2018, 6, 3)
            .with_hms(15, 33, 11)
            .with_milliseconds(553)
            .build_at_offset(0)?;
        assert_eq!(cursor.read_timestamp()?, expected);
        Ok(())
    }

    #[test]
    fn test_read_symbol_10() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x71, 0x0A]);
        assert_eq!(cursor.next()?, Value(IonType::Symbol));
        assert_eq!(cursor.read_symbol()?, local_sid_token(10));
        Ok(())
    }

    #[test]
    fn test_read_string_empty() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x80]);
        assert_eq!(cursor.next()?, Value(IonType::String));
        assert_eq!(cursor.read_string()?, String::from(""));
        Ok(())
    }

    #[test]
    fn test_read_string_foo() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x83, 0x66, 0x6f, 0x6f]);
        assert_eq!(cursor.next()?, Value(IonType::String));
        assert_eq!(cursor.read_string()?, String::from("foo"));
        Ok(())
    }

    #[test]
    fn test_read_string_foo_twice_fails() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x83, 0x66, 0x6f, 0x6f]);
        assert_eq!(cursor.next()?, Value(IonType::String));
        assert_eq!(cursor.read_string()?, String::from("foo"));
        // We've already consumed the string from the data source, so this should fail.
        assert!(cursor.read_string().is_err());
        Ok(())
    }

    #[test]
    fn test_read_clob_empty() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x90]);
        assert_eq!(cursor.next()?, Value(IonType::Clob));
        assert_eq!(cursor.read_clob()?, vec![]);
        Ok(())
    }

    #[test]
    fn test_read_clob_abc() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0x93, 0x61, 0x62, 0x63]);
        assert_eq!(cursor.next()?, Value(IonType::Clob));
        assert_eq!(cursor.read_clob()?.as_slice(), "abc".as_bytes());
        Ok(())
    }

    #[test]
    fn test_read_blob_empty() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0xA0]);
        assert_eq!(cursor.next()?, Value(IonType::Blob));
        assert_eq!(cursor.read_blob()?, vec![]);
        Ok(())
    }

    #[test]
    fn test_read_blob_123() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0xA3, 0x01, 0x02, 0x03]);
        assert_eq!(cursor.next()?, Value(IonType::Blob));
        assert_eq!(cursor.read_blob()?, vec![1u8, 2, 3]);
        Ok(())
    }

    #[test]
    fn test_read_list_empty() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0xB0]);
        assert_eq!(cursor.next()?, Value(IonType::List));
        cursor.step_in()?;
        assert_eq!(cursor.next()?, Nothing);
        cursor.step_out()?;
        Ok(())
    }

    #[test]
    fn test_read_list_123() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0xB6, 0x21, 0x01, 0x21, 0x02, 0x21, 0x03]);
        assert_eq!(cursor.next()?, Value(IonType::List));
        let mut list = vec![];
        cursor.step_in()?;
        while let Value(IonType::Integer) = cursor.next()? {
            list.push(cursor.read_i64()?);
        }
        cursor.step_out()?;
        assert_eq!(list, vec![1i64, 2, 3]);
        Ok(())
    }

    #[test]
    fn test_read_s_expression_empty() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0xC0]);
        assert_eq!(cursor.next()?, Value(IonType::SExpression));
        cursor.step_in()?;
        assert_eq!(cursor.next()?, Nothing);
        cursor.step_out()?;
        Ok(())
    }

    #[test]
    fn test_read_s_expression_123() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0xC6, 0x21, 0x01, 0x21, 0x02, 0x21, 0x03]);
        assert_eq!(cursor.next()?, Value(IonType::SExpression));
        let mut sexp = vec![];
        cursor.step_in()?;
        while let Value(IonType::Integer) = cursor.next()? {
            sexp.push(cursor.read_i64()?);
        }
        cursor.step_out()?;
        assert_eq!(sexp, vec![1i64, 2, 3]);
        Ok(())
    }

    #[test]
    fn test_read_struct_empty() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[0xD0]);
        assert_eq!(cursor.next()?, Value(IonType::Struct));
        cursor.step_in()?;
        assert_eq!(cursor.next()?, Nothing);
        cursor.step_out()?;
        Ok(())
    }

    #[test]
    fn test_read_struct() -> IonResult<()> {
        // Note: technically invalid Ion because the symbol IDs referenced are never added to the
        // symbol table.

        // {$10: 1, $11: 2, $12: 3}
        let mut cursor = ion_cursor_for(&[
            0xD9, // 9-byte struct
            0x8A, // Field ID 10
            0x21, 0x01, // Integer 1
            0x8B, // Field ID 11
            0x21, 0x02, // Integer 2
            0x8C, // Field ID 12
            0x21, 0x03, // Integer 3
        ]);
        assert_eq!(cursor.next()?, Value(IonType::Struct));
        cursor.step_in()?;
        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.field_name()?, local_sid_token(10));
        assert_eq!(cursor.read_i64()?, 1i64);
        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.field_name()?, local_sid_token(11usize));
        assert_eq!(cursor.read_i64()?, 2i64);
        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.field_name()?, local_sid_token(12usize));
        assert_eq!(cursor.read_i64()?, 3i64);
        cursor.step_out()?;
        Ok(())
    }

    #[test]
    fn test_read_list_in_struct() -> IonResult<()> {
        // Note: technically invalid Ion because the symbol IDs referenced are never added to the
        // symbol table.

        // {$11: [1, 2, 3], $10: 1}
        let mut cursor = ion_cursor_for(&[
            0xDB, // 11-byte struct
            0x8B, // Field ID 11
            0xB6, // 6-byte List
            0x21, 0x01, // Integer 1
            0x21, 0x02, // Integer 2
            0x21, 0x03, // Integer 3
            0x8A, // Field ID 10
            0x21, 0x01, // Integer 1
        ]);

        assert_eq!(cursor.next()?, Value(IonType::Struct));
        cursor.step_in()?;

        assert_eq!(cursor.next()?, Value(IonType::List));
        assert_eq!(cursor.field_name()?, local_sid_token(11usize));
        cursor.step_in()?;

        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.read_i64()?, 1i64);

        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.read_i64()?, 2i64);

        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.read_i64()?, 3i64);

        assert_eq!(cursor.next()?, Nothing); // End of the list's values
        cursor.step_out()?; // Step out of list

        assert_eq!(cursor.next()?, Value(IonType::Integer));
        assert_eq!(cursor.field_name()?, local_sid_token(10usize));
        assert_eq!(cursor.read_i64()?, 1i64);

        assert_eq!(cursor.next()?, Nothing); // End of the struct's values
        cursor.step_out()?; // Step out of struct

        // End of the stream
        assert_eq!(cursor.next()?, Nothing);

        Ok(())
    }

    #[test]
    fn test_raw_bytes() -> IonResult<()> {
        // Note: technically invalid Ion because the symbol IDs referenced are never added to the
        // symbol table.

        // {$11: [1, 2, 3], $10: 1}
        let ion_data = &[
            // First top-level value in the stream
            0xDB, // 11-byte struct
            0x8B, // Field ID 11
            0xB6, // 6-byte List
            0x21, 0x01, // Integer 1
            0x21, 0x02, // Integer 2
            0x21, 0x03, // Integer 3
            0x8A, // Field ID 10
            0x21, 0x01, // Integer 1
            // Second top-level value in the stream
            0xE3, // 3-byte annotations envelope
            0x81, // * Annotations themselves take 1 byte
            0x8C, // * Annotation w/SID $12
            0x10, // Boolean false
        ];
        let mut cursor = ion_cursor_for(ion_data);
        assert_eq!(RawStreamItem::Value(IonType::Struct), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[0..12]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[0..=0]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[1..12]));
        cursor.step_in()?;
        assert_eq!(RawStreamItem::Value(IonType::List), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[1..9]));
        assert_eq!(cursor.raw_field_id_bytes(), Some(&ion_data[1..=1]));
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[2..=2]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[3..9]));
        cursor.step_in()?;
        assert_eq!(RawStreamItem::Value(IonType::Integer), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[3..=4]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[3..=3]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[4..=4]));
        assert_eq!(RawStreamItem::Value(IonType::Integer), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[5..=6]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[5..=5]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[6..=6]));
        assert_eq!(RawStreamItem::Value(IonType::Integer), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[7..=8]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[7..=7]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[8..=8]));

        cursor.step_out()?; // Step out of list

        assert_eq!(RawStreamItem::Value(IonType::Integer), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[9..=11]));
        assert_eq!(cursor.raw_field_id_bytes(), Some(&ion_data[9..=9]));
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[10..=10]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[11..=11]));

        cursor.step_out()?; // Step out of struct

        // Second top-level value
        assert_eq!(RawStreamItem::Value(IonType::Boolean), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[12..16]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), Some(&ion_data[12..=14]));
        assert_eq!(cursor.annotations().next().unwrap()?, local_sid_token(12));
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[15..=15]));
        assert_eq!(
            cursor.raw_value_bytes(),
            Some(&ion_data[15..15] /*That is, zero bytes*/)
        );
        Ok(())
    }

    #[test]
    fn test_clear_annotations() -> IonResult<()> {
        // Verifies that byte offset bookkeeping is correct when the cursor reads a field with
        // annotations, then a field with no annotations, and finally a value with neither a
        // field ID nor annotations.

        #[rustfmt::skip]
        let ion_data = &[
            0xee, 0x98, 0x81, 0x83, // $ion_symbol_table::
            0xde, 0x94,             // {                    // 20-byte struct
            0x87,                   //   symbols:           // $7:
            0xbe, 0x91,             //   [                  // 17-byte list
            0x83, 0x66, 0x6f, 0x6f, //     "foo",
            0x83, 0x62, 0x61, 0x72, //     "bar",
            0x83, 0x62, 0x61, 0x7a, //     "baz",
            0x84, 0x71, 0x75, 0x75, //     "quux",
            0x78,                   //
                                    //   ]
                                    // }
            0xda,                   // {                    // 10-byte struct
            0x8a,                   //    foo:              // $10:
            0xe5, 0x82, 0x8b, 0x8c, //    bar::baz::        // $11::$12::
            0x21, 0x05,             //    5,
            0x8d,                   //    quux:
            0x21, 0x07,             //    7,
                                    // }
            0x10,                   // false
        ];

        let mut cursor = ion_cursor_for(ion_data);

        // Local symbol table. We don't interpret any symbols for this test, so we can skip over it.
        assert_eq!(RawStreamItem::Value(IonType::Struct), cursor.next()?);

        // The first user-level value appears at byte offset 26
        // Top-level struct {
        assert_eq!(RawStreamItem::Value(IonType::Struct), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[26..37]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[26..=26]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[27..37]));

        cursor.step_in()?;

        // foo: bar::baz::5
        assert_eq!(RawStreamItem::Value(IonType::Integer), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[27..34]));
        assert_eq!(cursor.raw_field_id_bytes(), Some(&ion_data[27..=27]));
        assert_eq!(cursor.raw_annotations_bytes(), Some(&ion_data[28..32]));
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[32..=32]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[33..=33]));
        assert_eq!(cursor.read_i64()?, 5);

        // quux: 7
        assert_eq!(RawStreamItem::Value(IonType::Integer), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[34..37]));
        assert_eq!(cursor.raw_field_id_bytes(), Some(&ion_data[34..=34]));
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[35..=35]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[36..=36]));
        assert_eq!(cursor.read_i64()?, 7);

        // End of top-level struct
        cursor.step_out()?;

        // false
        assert_eq!(RawStreamItem::Value(IonType::Boolean), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[37..=37]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[37..=37]));
        assert_eq!(
            cursor.raw_value_bytes(),
            Some(&ion_data[37..37] /* empty */)
        );
        assert_eq!(cursor.read_bool()?, false);

        Ok(())
    }

    #[test]
    fn test_nop_pad_adjacent_to_top_level() -> IonResult<()> {
        // name::true with a byte of NOP padding on either side of it
        let mut cursor = ion_cursor_for(&[
            0x00, // NOP code, 1 byte NOP
            0xE3, // 3-byte annotations envelope
            0x81, // * Annotations themselves take 1 byte
            0x84, // * Annotation w/SID $4 ("name")
            0x11, // boolean true
            0x00, // NOP code, 1 byte NOP. Also NOP at EOF :)
        ]);

        assert_eq!(cursor.next()?, Value(IonType::Boolean));
        assert_eq!(cursor.next()?, Nothing);

        Ok(())
    }

    #[test]
    fn test_nop_pad_with_varuint_len() -> IonResult<()> {
        // 3 bytes of NOP padding followed by boolean true
        let mut cursor = ion_cursor_for(&[
            0x0E, // NOP code, length to follow
            0x81, // single octet VarUInt, 1 (so 1 byte of padding follows)
            0xFF, // not a legal type code, but this is ignored padding
            0x11, // boolean true
        ]);

        assert_eq!(cursor.next()?, Value(IonType::Boolean));
        assert_eq!(cursor.next()?, Nothing);

        Ok(())
    }

    #[test]
    fn test_nop_pad_in_struct() -> IonResult<()> {
        // {$4: "a", <4 bytes of (NOP + 2 bytes padding)>}
        let mut cursor = ion_cursor_for(&[
            0xD7, // 7-byte struct
            0x84, // single octet VarUInt, value 4 => field named "name"
            0x81, // string of length 1
            0x61, // "a"
            0x80, // single octet VarUInt, value 0 => unknown symbol, also reserved for NOP padding in structs
            0x02, // two bytes of NOP padding follow
            0x01, 0x02, // not interpreted, this is padding
        ]);

        assert_eq!(cursor.next()?, Value(IonType::Struct));
        cursor.step_in()?;
        assert_eq!(cursor.next()?, Value(IonType::String));
        assert_eq!(cursor.read_string()?, String::from("a"));
        assert_eq!(cursor.next()?, Nothing);
        cursor.step_out()?;

        Ok(())
    }

    #[test]
    fn test_nop_pad_in_struct_beginning() -> IonResult<()> {
        // { <4 bytes of ($0: NOP + 2 bytes padding)>, $4: "a",}
        let mut cursor = ion_cursor_for(&[
            0xD7, // 7-byte struct
            0x80, // single octet VarUInt, value 0 => unknown symbol, also reserved for NOP padding in structs
            0x02, // two bytes of NOP padding follow
            0x01, 0x02, // not interpreted, this is padding
            0x84, // single octet VarUInt, value 4 => field named "name"
            0x81, // string of length 1
            0x61, // "a"
        ]);

        assert_eq!(cursor.next()?, Value(IonType::Struct));
        cursor.step_in()?;
        assert_eq!(cursor.next()?, Value(IonType::String));
        assert_eq!(cursor.read_string()?, String::from("a"));
        assert_eq!(cursor.next()?, Nothing);
        cursor.step_out()?;

        Ok(())
    }

    #[test]
    fn test_nop_pad_not_allowed_inside_annotation_wrapper() -> IonResult<()> {
        let mut cursor = ion_cursor_for(&[
            //0xE3 0x81 0x84 0x00 is the canonical "invalid annotated NOP" from the docs
            0xE3, // 3-byte annotations envelope
            0x81, // * Annotations themselves take 1 byte
            0x84, // * Annotation w/SID $4 ("name")
            0x00, // NOP code, 1 byte NOP
        ]);

        assert!(matches!(cursor.next(), Err(IonError::DecodingError { .. })));

        Ok(())
    }

    #[test]
    fn test_nop_pad_larger_than_struct() -> IonResult<()> {
        // {$4: "a", <4 bytes of ($0: NOP claiming 4 bytes padding when only 2 will fit)>}
        let mut cursor = ion_cursor_for(&[
            0xD7, // 7-byte struct
            0x84, // single octet VarUInt, value 4 => field named "name"
            0x81, // string of length 1
            0x61, // "a"
            0x80, // single octet VarUInt, value 0 => unknown symbol, also reserved for NOP padding in structs
            0x04, // "four" bytes of NOP padding follow, which would overrun the struct
            0x01, 0x02, // not interpreted, this is padding
        ]);

        assert_eq!(cursor.next()?, Value(IonType::Struct));

        cursor.step_in()?;
        assert_eq!(cursor.next()?, Value(IonType::String));
        assert_eq!(cursor.read_string()?, String::from("a"));

        assert!(matches!(cursor.next(), Err(IonError::DecodingError { .. })));

        cursor.step_out()?;

        Ok(())
    }

    #[test]
    fn test_nop_pad_larger_than_list() -> IonResult<()> {
        // {$4: "a", <4 bytes of (NOP + 2 bytes padding)>}
        let mut cursor = ion_cursor_for(&[
            // [0-3] IVM
            0xB2, // [4] 2-byte list
            0x20, // [5] single octet int, 0
            0x01, // [6] "one" bytes of NOP padding follow, which would overrun the list
        ]); // [7] is out of the container

        assert_eq!(cursor.next()?, Value(IonType::List));

        cursor.step_in()?;
        assert_eq!(cursor.next()?, Value(IonType::Integer));

        assert!(matches!(cursor.next(), Err(IonError::DecodingError { .. })));

        cursor.step_out()?;

        Ok(())
    }
}
