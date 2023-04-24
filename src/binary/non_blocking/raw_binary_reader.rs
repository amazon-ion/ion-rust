use crate::binary::constants::v1_0::{length_codes, IVM};
use crate::binary::int::DecodedInt;
use crate::binary::non_blocking::binary_buffer::BinaryBuffer;
use crate::binary::non_blocking::type_descriptor::{Header, TypeDescriptor};
use crate::binary::uint::DecodedUInt;
use crate::binary::var_uint::VarUInt;
use crate::binary::IonTypeCode;
use crate::element::{Blob, Clob};
use crate::result::{
    decoding_error, decoding_error_raw, illegal_operation, illegal_operation_raw,
    incomplete_data_error,
};
use crate::types::integer::IntAccess;
use crate::types::string::Str;
use crate::types::SymbolId;
use crate::{
    raw_reader::BufferedRawReader, Decimal, Int, IonReader, IonResult, IonType, RawStreamItem,
    RawSymbolToken, Timestamp,
};
use bytes::{BigEndian, Buf, ByteOrder};
use num_bigint::BigUint;
use num_traits::Zero;
use std::io::Read;
use std::mem;
use std::ops::Range;

/// Type, offset, and length information about the serialized value over which the
/// NonBlockingRawBinaryReader is currently positioned.
#[derive(Clone, Copy, Debug, PartialEq)]
struct EncodedValue {
    // If the compiler decides that a value is too large to be moved/copied with inline code,
    // it will relocate the value using memcpy instead. This can be quite slow by comparison.
    //
    // Be cautious when adding new member fields or modifying the data types of existing member
    // fields, as this may cause the in-memory size of `EncodedValue` instances to grow.
    //
    // See the Rust Performance Book section on measuring type sizes[1] for more information.
    // [1] https://nnethercote.github.io/perf-book/type-sizes.html#measuring-type-sizes

    // The type descriptor byte that identified this value; includes the type code, length code,
    // and IonType.
    header: Header,

    // Each encoded value has up to five components, appearing in the following order:
    //
    // [ field_id? | annotations? | header (type descriptor) | header_length? | value ]
    //
    // Components shown with a `?` are optional.
    //
    // EncodedValue stores the offset of the type descriptor byte from the beginning of the
    // data source (`header_offset`). The lengths of the other fields can be used to calculate
    // their positions relative to the type descriptor byte. For example, to find the offset of the
    // field ID (if present), we can do:
    //     header_offset - annotations_header_length - field_id_length
    //
    // This allows us to store a single `usize` for the header offset, while other lengths can be
    // packed into a `u8`. Values are not permitted to have a field ID or annotations that take
    // more than 255 bytes to represent.
    //
    // We store the offset for the header byte because it is guaranteed to be present for all values.
    // Field IDs and annotations appear earlier in the stream but are optional.

    // The number of bytes used to encode the field ID (if present) preceding the Ion value. If
    // `field_id` is undefined, `field_id_length` will be zero.
    field_id_length: u8,
    // If this value is inside a struct, `field_id` will contain the SymbolId that represents
    // its field name.
    field_id: Option<SymbolId>,
    // The number of bytes used to encode the annotations wrapper (if present) preceding the Ion
    // value. If `annotations` is empty, `annotations_header_length` will be zero.
    annotations_header_length: u8,
    // The number of bytes used to encode the series of symbol IDs inside the annotations wrapper.
    annotations_sequence_length: u8,
    // Type descriptor byte location.
    header_offset: usize,
    // The number of bytes used to encode the header not including the type descriptor byte.
    header_length: u8,
    // The number of bytes used to encode the value itself, not including the header byte
    // or length fields.
    value_length: usize,
    // The sum total of:
    //     field_id_length + annotations_header_length + header_length + value_length
    // While this can be derived from the above fields, storing it for reuse offers a modest
    // optimization. `total_length` is needed when stepping into a value, skipping a value,
    // and reading a value's data.
    total_length: usize,
}

impl EncodedValue {
    /// Returns the offset of the current value's type descriptor byte.
    fn header_offset(&self) -> usize {
        self.header_offset
    }

    /// Returns the length of this value's header, including the type descriptor byte and any
    /// additional bytes used to encode the value's length.
    fn header_length(&self) -> usize {
        // The `header_length` field does not include the type descriptor byte, so add 1.
        self.header_length as usize + 1
    }

    /// Returns an offset Range that contains this value's type descriptor byte and any additional
    /// bytes used to encode the `length`.
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

    /// The offset of the first byte following the header (including length bytes, if present).
    /// If `value_length()` returns zero, this offset is actually the first byte of
    /// the next encoded value and should not be read.
    fn value_offset(&self) -> usize {
        self.header_offset + self.header_length()
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
        Some(
            self.header_offset
                - self.annotations_header_length as usize
                - self.field_id_length as usize,
        )
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
    fn annotations_header_length(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.annotations_header_length as usize)
    }

    /// Returns the number of bytes used to encode the series of VarUInt annotation symbol IDs, if
    /// any.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#annotations>
    fn annotations_sequence_length(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.annotations_sequence_length as usize)
    }

    /// Returns the offset of the beginning of the annotations wrapper, if present.
    fn annotations_offset(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.header_offset - self.annotations_header_length as usize)
    }

    /// Returns an offset Range that includes the bytes used to encode this value's annotations,
    /// if any. While annotations envelope the value that they modify, this function does not
    /// include the bytes of the encoded value itself.
    fn annotations_range(&self) -> Option<Range<usize>> {
        if let Some(start) = self.annotations_offset() {
            let end = start + self.annotations_header_length as usize;
            return Some(start..end);
        }
        None
    }

    /// Returns the total number of bytes used to represent the current value, including the
    /// field ID (if any), its annotations (if any), its header (type descriptor + length bytes),
    /// and its value.
    fn total_length(&self) -> usize {
        self.total_length
    }

    fn ion_type(&self) -> IonType {
        self.header.ion_type
    }
}

/// Constructs an 'empty' EncodedValue that the reader can populate while parsing.
impl Default for EncodedValue {
    fn default() -> EncodedValue {
        EncodedValue {
            header: Header {
                ion_type: IonType::Null,
                ion_type_code: IonTypeCode::NullOrNop,
                length_code: length_codes::NULL,
            },
            field_id: None,
            field_id_length: 0,
            annotations_header_length: 0,
            annotations_sequence_length: 0,
            header_offset: 0,
            header_length: 0,
            value_length: 0,
            total_length: 0,
        }
    }
}

/// Tracks whether the non-blocking binary reader is currently positioned...
#[derive(Debug, PartialEq, Clone)]
enum ReaderState {
    /// ...on a type descriptor byte offset, ready to attempt parsing...
    ///
    ///   The reader will be in this state
    ///     * before it begins reading from the stream
    ///     * after stepping into a container
    ///     * after stepping out of a container
    ///     * at the end of a stream
    Ready,
    /// ...on the first byte of an IVM...
    OnIvm,
    /// ...on the first byte of a value...
    ///
    ///   Depending on the value, this byte will be the first of:
    ///     * the field ID (if present)
    ///     * the annotations wrapper (if present)
    ///     * the value's type descriptor byte
    OnValue(EncodedValue),
    /// ...or between stream items. The nested `usize` indicates how many bytes must be read
    /// before we can attempt parsing again.
    ///
    ///   If the reader's state is `Skipping(n)`, it means that the reader ran out of data before it
    ///   was able to read the next item in the stream; more data will have to be made available to
    ///   the reader before parsing can resume.
    Skipping(usize),
    /// ... on the first byte of a non-container value, but need more data to materialize (or skip) it ...
    ///
    ///   If the reader's state is `WaitingForData`, we're on the first byte of a value and have
    ///   successfully parsed the value's length, but require more data in order to materialize the
    ///   value.
    WaitingForData(EncodedValue),
}

/// Represents the subset of [IonType] variants that are containers.
#[derive(Debug, PartialEq, Clone, Copy)]
enum ContainerType {
    List,
    SExpression,
    Struct,
}

impl ContainerType {
    /// Returns the [IonType] that corresponds to this [ContainerType].
    pub fn ion_type(&self) -> IonType {
        match self {
            ContainerType::List => IonType::List,
            ContainerType::SExpression => IonType::SExp,
            ContainerType::Struct => IonType::Struct,
        }
    }
}

/// Represents a container into which the reader has stepped.
#[derive(Debug, PartialEq, Clone, Copy)]
struct Container {
    kind: ContainerType,
    /// The offset of the first byte *after* the parent container. For example: if the container
    /// starts at index 0 and is 4 bytes long, `exclusive_end` will be `4`.
    exclusive_end: usize,
}

impl Container {
    /// Returns the [IonType] that corresponds to this [Container].
    pub fn ion_type(&self) -> IonType {
        self.kind.ion_type()
    }
}

/// A raw binary reader that pulls input bytes from a fixed buffer.
///
/// If any read operation fails due to the buffer containing incomplete data, that method will
/// return [`IonError::Incomplete`](crate::IonError::Incomplete).
///
/// If the buffer (generic type `A`) is a [`Vec<u8>`], then data can be appended to it between read
/// operations. This can be useful when reading from a data source that is growing over time, such
/// as when tailing a growing file, reading over the network, or waiting for user input.
/// Applications can read from the buffer until they encounter an `Incomplete`. Then, when more
/// data is available, they can use [read_from](Self::read_from) or
/// [append_bytes](Self::append_bytes) to add that data to the buffer.
/// Finally, they can retry the read operation that had previously failed.
///
/// Note that if the buffer runs out of data between top level values, this will be interpreted
/// as the end of the stream. Applications can still add more data to the buffer and resume reading.
#[derive(Debug)]
pub struct RawBinaryReader<A: AsRef<[u8]>> {
    ion_version: (u8, u8),
    state: ReaderState,
    buffer: BinaryBuffer<A>,
    parents: Vec<Container>,
    is_eos: bool,
}

impl BufferedRawReader for RawBinaryReader<Vec<u8>> {
    /// Copies the provided bytes to end of the reader's input buffer.
    fn append_bytes(&mut self, bytes: &[u8]) -> IonResult<()> {
        self.buffer.append_bytes(bytes);
        Ok(())
    }

    /// Tries to read `length` bytes from `source`. Unlike [append_bytes](Self::append_bytes),
    /// this method does not do any copying. A slice of the reader's buffer is handed to `source`
    /// so it can be populated directly.
    fn read_from<R: Read>(&mut self, source: R, length: usize) -> IonResult<usize> {
        self.buffer.read_from(source, length)
    }

    fn stream_complete(&mut self) {
        self.is_eos = true;
    }

    fn is_stream_complete(&self) -> bool {
        self.is_eos
    }
}

impl From<Vec<u8>> for RawBinaryReader<Vec<u8>> {
    fn from(source: Vec<u8>) -> Self {
        RawBinaryReader::new(source)
    }
}

impl<A: AsRef<[u8]>> RawBinaryReader<A> {
    /// Constructs a RawBinaryReader from a value that can be viewed as a byte slice.
    pub fn new(source: A) -> RawBinaryReader<A> {
        RawBinaryReader {
            ion_version: (1, 0),
            state: ReaderState::Ready,
            buffer: BinaryBuffer::new(source),
            parents: Vec::new(), // Does not allocate yet
            is_eos: false,
        }
    }

    /// Constructs a disposable view of the buffer's current contents that can be used to find the
    /// next item in the stream. If the TxReader encounters a problem like invalid or incomplete
    /// data, it can be discarded without affecting the RawBinaryReader that created it.
    fn transaction_reader(&mut self) -> TxReader<A> {
        // Temporarily break apart `self` to get simultaneous mutable references to the buffer,
        // the reader state, and the parents.
        let RawBinaryReader {
            state,
            buffer,
            parents,
            ..
        } = self;

        // Create a slice of the main buffer that has its own records of how many bytes have been
        // read and how many remain.
        let tx_buffer = buffer.slice();
        TxReader {
            state,
            parent: parents.last(),
            tx_buffer,
            encoded_value: Default::default(),
            nop_bytes_count: 0,
        }
    }

    /// Moves the reader to the first byte of the next item in the stream.
    /// If it succeeds, the reader's state will be [ReaderState::Ready].
    /// If there is not enough data in the buffer to reach the next item, the reader's state will
    /// be [ReaderState::Skipping], indicating that it is mid-stream and awaiting more data.
    fn advance_to_next_item(&mut self) -> IonResult<()> {
        use ReaderState::*;
        let bytes_to_skip = match self.state {
            Ready => return Ok(()),
            Skipping(bytes_to_skip) => bytes_to_skip,
            OnIvm => IVM.len(),
            OnValue(encoded_value) => encoded_value.total_length(),
            // This function will not be called while the reader is in the WaitingForData state.
            WaitingForData(_) => unreachable!(),
        };

        let bytes_available = self.buffer.remaining();
        if bytes_available >= bytes_to_skip {
            self.buffer.consume(bytes_to_skip);
            self.state = Ready;
            Ok(())
        } else {
            self.buffer.consume(bytes_available);
            self.state = Skipping(bytes_to_skip - bytes_available);
            incomplete_data_error("ahead to next item", self.buffer.total_consumed())
        }
    }

    /// Creates an iterator that lazily reads the VarUInt symbol IDs in this value's annotations
    /// wrapper. If the reader is not on a value or the current value does not have annotations,
    /// the iterator will be empty.
    pub fn annotations_iter(&self) -> impl Iterator<Item = IonResult<RawSymbolToken>> + '_ {
        // If the reader is currently on a value...
        if let ReaderState::OnValue(encoded_value) = &self.state {
            // ...and that value has one or more annotations...
            if let Some(length) = encoded_value.annotations_sequence_length() {
                // ...then we'll create an iterator over those annotations.
                // Find the relative offset of the value's header byte within the buffer.
                let header_relative_offset =
                    encoded_value.header_offset - self.buffer.total_consumed();
                // The annotations sequence immediately precedes the header byte in the buffer.
                // Subtract its length to find the beginning of the sequence.
                let start = header_relative_offset - length;
                // Get the slice of the buffer that contains the VarUInt annotations sequence.
                let annotations_bytes = &self.buffer.bytes()[start..header_relative_offset];
                // Construct an annotations iterator over that slice.
                return AnnotationsIterator::new(annotations_bytes);
            }
        }
        // If the reader is either not on a value or the current value has no annotations.else
        // Return an iterator over an arbitrary empty slice.
        AnnotationsIterator::new(&self.buffer.bytes()[0..0])
    }

    /// If the reader is currently positioned on a value, returns `Some(&value)`.
    /// Otherwise, returns `None`.
    #[inline]
    fn encoded_value(&self) -> Option<&EncodedValue> {
        match &self.state {
            ReaderState::OnValue(encoded_value) => Some(encoded_value),
            _ => None,
        }
    }

    /// Returns an IonError::IllegalOperation describing why the current operation could not be
    /// performed in the reader's current state.
    #[inline(never)]
    // This method performs allocations/formatting that compile to non-trivial instructions.
    // It will only be called as a result of user error; making it `inline(never)` keeps the
    // compiler from bloating functions on the hot path with its (rarely used) expansion.
    fn expected<T>(&self, expected: IonType) -> IonResult<T> {
        illegal_operation(format!(
            "type mismatch: expected a(n) {} but positioned over a(n) {}",
            expected,
            self.current()
        ))
    }

    /// Verifies that the reader is currently positioned over an Ion value of the expected type.
    /// If it is, returns a reference to the corresponding `&EncodedValue` and the slice of input
    /// bytes that represents the body of the value.
    /// If it is not, returns [`IllegalOperation`](crate::result::IonError::IllegalOperation).
    #[inline]
    fn value_and_bytes(&self, expected_ion_type: IonType) -> IonResult<(&EncodedValue, &[u8])> {
        // Get a reference to the EncodedValue. This is only possible if the reader is parked
        // on a value.
        let encoded_value = if let Some(encoded_value) = self.encoded_value() {
            // If the value we're parked on is not of the type we're expecting to read, return an error.
            if encoded_value.ion_type() != expected_ion_type {
                return self.expected(expected_ion_type);
            }
            encoded_value
        } else {
            return self.expected(expected_ion_type);
        };

        let value_total_length = encoded_value.total_length();
        if self.buffer.remaining() < value_total_length {
            return incomplete_data_error(
                "only part of the requested value is available in the buffer",
                self.buffer.total_consumed(),
            );
        }

        // Get the slice of buffer bytes that represent the value. This slice may be empty.
        let value_offset = value_total_length - encoded_value.value_length();
        let bytes = self
            .buffer
            .bytes_range(value_offset, encoded_value.value_length());

        Ok((encoded_value, bytes))
    }

    /// Like [`value_and_bytes`](Self::value_and_bytes), but wraps the byte slice in a
    /// `BinaryBuffer` to make it easy to read a series of encoding primitives from the slice.
    #[inline]
    fn value_and_buffer(
        &mut self,
        expected_ion_type: IonType,
    ) -> IonResult<(&EncodedValue, BinaryBuffer<&[u8]>)> {
        let (encoded_value, bytes) = self.value_and_bytes(expected_ion_type)?;
        // Wrap the &[u8] representing the body of the value in a stack-allocated BinaryBuffer.
        Ok((encoded_value, BinaryBuffer::new(bytes)))
    }

    /// If the reader is currently positioned on a symbol value, parses that value into a `SymbolId`.
    pub fn read_symbol_id(&mut self) -> IonResult<SymbolId> {
        let (_encoded_value, bytes) = self.value_and_bytes(IonType::Symbol)?;
        if bytes.len() > mem::size_of::<usize>() {
            return decoding_error("found a symbol Id that was too large to fit in a usize");
        }
        let magnitude = DecodedUInt::small_uint_from_slice(bytes);
        // This cast is safe because we've confirmed the value was small enough to fit in a usize.
        Ok(magnitude as usize)
    }

    /// Tries to downgrade the provided BigUint to a SymbolId (usize).
    #[inline(never)]
    // This method performs allocations/computation that compile to non-trivial instructions.
    // It will only be called if the input stream contains unreadable data; making it `inline(never)`
    // keeps the compiler from bloating functions on the hot path with its (rarely used) expansion.
    fn try_symbol_id_from_big_uint(big_uint: &BigUint) -> IonResult<SymbolId> {
        // This will only succeed if the value in the big_uint was small enough to have been
        // in a `usize`. This can happen if (e.g.) the encoding was padded with extra zeros.
        if let Ok(sid) = big_uint.try_into() {
            Ok(sid)
        } else {
            decoding_error("found a big_uint symbol ID that was too large to fit in a usize")
        }
    }

    /// If the reader is currently positioned on a string, returns the slice of bytes that represents
    /// that string's *UNVALIDATED* utf-8 bytes. This method is available for performance optimization
    /// in scenarios where utf-8 validation may be unnecessary and/or a bottleneck. It is strongly
    /// recommended that you use [read_str](Self::read_str) unless absolutely necessary.
    pub fn read_str_bytes(&mut self) -> IonResult<&[u8]> {
        let (_encoded_value, bytes) = self.value_and_bytes(IonType::String)?;
        Ok(bytes)
    }

    /// If the reader is currently positioned on a blob, returns a slice containing its bytes.
    pub fn read_blob_bytes(&mut self) -> IonResult<&[u8]> {
        let (_encoded_value, bytes) = self.value_and_bytes(IonType::Blob)?;
        Ok(bytes)
    }

    /// If the reader is currently positioned on a clob, returns a slice containing its bytes.
    pub fn read_clob_bytes(&mut self) -> IonResult<&[u8]> {
        let (_encoded_value, bytes) = self.value_and_bytes(IonType::Clob)?;
        Ok(bytes)
    }

    pub fn header_length(&self) -> usize {
        if let Some(val) = self.encoded_value() {
            val.header_length.into()
        } else {
            0
        }
    }

    /// Returns a slice containing the current value's bytes. In the case of a container the raw
    /// bytes will consist of its field ID (if present), its annotations (if present), and its
    /// header. In the case of a non-container value, the bytes for the value itself is also
    /// included.
    pub fn raw_bytes(&self) -> Option<&[u8]> {
        let start: usize;
        let value = self.encoded_value()?;

        if let Some(field_id_offset) = value.field_id_offset() {
            start = field_id_offset;
        } else if let Some(annotations_offset) = value.annotations_offset() {
            start = annotations_offset;
        } else {
            start = value.header_offset();
        }

        let end = if value.ion_type().is_container() {
            value.header_range().end
        } else {
            value.value_end_exclusive()
        };

        let bytes = &self.buffer.raw_bytes()[start..end];
        Some(bytes)
    }

    pub fn raw_field_id_bytes(&self) -> Option<&[u8]> {
        let value = self.encoded_value()?;
        let range = value.field_id_range()?;
        let bytes = &self.buffer.raw_bytes()[range.start..range.end];
        Some(bytes)
    }

    pub fn raw_header_bytes(&self) -> Option<&[u8]> {
        let value = self.encoded_value()?;
        let header_range = value.header_range();
        let bytes = &self.buffer.raw_bytes()[header_range.start..header_range.end];
        Some(bytes)
    }

    pub fn raw_value_bytes(&self) -> Option<&[u8]> {
        let value = self.encoded_value()?;
        let value_range = value.value_range();
        if value.ion_type().is_container() {
            None
        } else {
            let bytes = &self.buffer.raw_bytes()[value_range.start..value_range.end];
            Some(bytes)
        }
    }

    pub fn raw_annotations_bytes(&self) -> Option<&[u8]> {
        self.ion_type()?;
        let value = self.encoded_value().unwrap();
        let range = value.annotations_range()?;
        let bytes = &self.buffer.raw_bytes()[range.start..range.end];
        Some(bytes)
    }

    pub fn field_id_length(&self) -> Option<usize> {
        self.ion_type()?;
        let value = self.encoded_value().unwrap();
        Some(value.field_id_length.into())
    }

    pub fn field_id_offset(&self) -> Option<usize> {
        let value = self.encoded_value()?;
        Some(
            value.header_offset
                - value.annotations_sequence_length as usize
                - value.field_id_length as usize,
        )
    }

    pub fn field_id_range(&self) -> Option<std::ops::Range<usize>> {
        let value = self.encoded_value()?;
        let start = value.field_id_offset()?;
        let end = start + value.field_id_length as usize;
        Some(start..end)
    }

    pub fn annotations_length(&self) -> Option<usize> {
        let value = self.encoded_value()?;
        value.annotations_sequence_length()
    }

    pub fn annotations_offset(&self) -> Option<usize> {
        let value = self.encoded_value()?;
        value.annotations_offset()
    }

    pub fn annotations_range(&self) -> Option<std::ops::Range<usize>> {
        let value = self.encoded_value()?;
        value.annotations_range()
    }

    pub fn header_offset(&self) -> usize {
        if let Some(value) = self.encoded_value() {
            value.header_offset()
        } else {
            0
        }
    }

    pub fn header_range(&self) -> std::ops::Range<usize> {
        if let Some(value) = self.encoded_value() {
            value.header_range()
        } else {
            0..0
        }
    }

    pub fn value_length(&self) -> usize {
        if let Some(value) = self.encoded_value() {
            value.value_length()
        } else {
            0
        }
    }

    pub fn value_offset(&self) -> usize {
        if let Some(value) = self.encoded_value() {
            value.value_offset()
        } else {
            0
        }
    }

    pub fn value_range(&self) -> std::ops::Range<usize> {
        if let Some(value) = self.encoded_value() {
            value.value_range()
        } else {
            0..0
        }
    }
}

impl<A: AsRef<[u8]>> IonReader for RawBinaryReader<A> {
    type Item = RawStreamItem;
    type Symbol = RawSymbolToken;

    fn ion_version(&self) -> (u8, u8) {
        self.ion_version
    }

    #[inline]
    fn next(&mut self) -> IonResult<Self::Item> {
        if let ReaderState::WaitingForData(value) = self.state {
            if self.buffer.remaining() < value.total_length() {
                return incomplete_data_error("ahead to next item", self.buffer.total_consumed());
            } else {
                self.state = ReaderState::OnValue(value);
                if value.header.is_null() {
                    return Ok(RawStreamItem::Null(value.ion_type()));
                } else {
                    return Ok(RawStreamItem::Value(value.ion_type()));
                }
            }
        } else {
            // `advance_to_next_item` is the only method that can modify `self.buffer`. It causes the
            // bytes representing the current stream item to be consumed.
            //
            // If the buffer contains enough data, the reader's new position will be the first byte of
            // the next type descriptor byte (which may represent a field_id, annotation wrapper, value
            // header, or NOP bytes) and its state will be set to `Ready`.
            //
            // If there is not enough data, `self.state` will be set to `Skipping(n)` to keep track of
            // how many more bytes we would need to add to the buffer before we could reach the next
            // type descriptor. If `self.state` is `Skipping(n)`, the only way to advance is to add
            // more data to the buffer.
            self.advance_to_next_item()?;

            if let Some(parent) = self.parents.last() {
                // We're inside a container. If we've reached its end, return `Nothing`.
                if self.buffer.total_consumed() >= parent.exclusive_end {
                    return Ok(RawStreamItem::Nothing);
                }
            } else {
                // We're at the top level. If we're out of data (`buffer.is_empty()`) and aren't waiting
                // on more data (`Skipping(n)`), we return `Nothing` to indicate that we're at EOF.
                if self.buffer.is_empty() && self.state == ReaderState::Ready {
                    return Ok(RawStreamItem::Nothing);
                }
            }
        }

        let bytes_remaining = self.buffer.remaining();

        // Make a 'transaction' reader. This is a disposable view of the reader's main input buffer;
        // it's reading the same bytes, but keeps its own records of how many bytes have been
        // consumed. If reading fails at some point due to incomplete data or another error, the
        // `tx_reader` can be discarded without affecting `self.buffer`. The next attempt at
        // parsing will create a fresh transaction reader starting from the last good state.
        let mut tx_reader = self.transaction_reader();

        let item_result = tx_reader.read_next_item();
        let nop_bytes_count = tx_reader.nop_bytes_count as usize;

        // If we do not have enough bytes to materialize the next value, return an incomplete
        // error. This is to match the behavior of the text reader where incomplets will only come
        // from step-out and next calls.
        if let ReaderState::OnValue(encoded_value) = tx_reader.state {
            if !encoded_value.ion_type().is_container()
                && bytes_remaining < encoded_value.total_length()
            {
                *tx_reader.state = ReaderState::WaitingForData(*encoded_value);
                self.buffer.consume(nop_bytes_count);
                return incomplete_data_error("ahead to next item", self.buffer.total_consumed());
            }
        }

        // If we encountered any leading NOP bytes during this transaction, consume them.
        // This guarantees that the first byte in the buffer is the first byte of the current item.
        self.buffer.consume(nop_bytes_count);

        item_result
    }

    fn current(&self) -> Self::Item {
        use ReaderState::*;
        match self.state {
            OnIvm => RawStreamItem::VersionMarker(self.ion_version.0, self.ion_version.1),
            OnValue(ref encoded_value) => {
                let ion_type = encoded_value.header.ion_type;
                if encoded_value.header.is_null() {
                    RawStreamItem::Null(ion_type)
                } else {
                    RawStreamItem::Value(ion_type)
                }
            }
            Ready | Skipping(_) | WaitingForData(_) => RawStreamItem::Nothing,
        }
    }

    fn ion_type(&self) -> Option<IonType> {
        self.encoded_value().map(|ev| ev.ion_type())
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'a> {
        Box::new(self.annotations_iter())
    }

    fn has_annotations(&self) -> bool {
        self.encoded_value()
            .map(|v| v.annotations_sequence_length > 0)
            .unwrap_or(false)
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        // If the reader is parked on a value...
        self.encoded_value()
            .ok_or_else(|| illegal_operation_raw("the reader is not positioned on a value"))
            // and that value has a field ID (because it's inside a struct)...
            .and_then(|ev|
                // ...then convert that field ID into a RawSymbolToken.
                ev.field_id
                .map(RawSymbolToken::SymbolId)
                .ok_or_else(|| illegal_operation_raw("the current value is not inside a struct")))
    }

    fn is_null(&self) -> bool {
        self.encoded_value()
            .map(|ev| ev.header.is_null())
            .unwrap_or(false)
    }

    fn read_null(&mut self) -> IonResult<IonType> {
        if let Some(value) = self.encoded_value() {
            // If the reader is on a value, the IonType is present.
            let ion_type = value.header.ion_type;
            return if value.header.is_null() {
                Ok(ion_type)
            } else {
                illegal_operation(format!(
                    "cannot read null; reader is currently positioned on a non-null {ion_type}"
                ))
            };
        }
        Err(illegal_operation_raw(
            "the reader is not currently positioned on a value",
        ))
    }

    fn read_bool(&mut self) -> IonResult<bool> {
        let (encoded_value, _) = self.value_and_bytes(IonType::Bool)?;

        let representation = encoded_value.header.length_code;
        match representation {
            0 => Ok(false),
            1 => Ok(true),
            _ => decoding_error(
                "found a boolean value with an illegal representation (must be 0 or 1): {}",
            ),
        }
    }

    fn read_i64(&mut self) -> IonResult<i64> {
        self.read_int().and_then(|i| {
            i.as_i64()
                .ok_or_else(|| decoding_error_raw("integer was too large to fit in an i64"))
        })
    }

    fn read_int(&mut self) -> IonResult<Int> {
        let (encoded_value, bytes) = self.value_and_bytes(IonType::Int)?;
        let value: Int = if bytes.len() <= mem::size_of::<u64>() {
            DecodedUInt::small_uint_from_slice(bytes).into()
        } else {
            DecodedUInt::big_uint_from_slice(bytes).into()
        };

        use self::IonTypeCode::*;
        let value = match (encoded_value.header.ion_type_code, value) {
            (PositiveInteger, integer) => integer,
            (NegativeInteger, integer) if integer.is_zero() => {
                return decoding_error("found a negative integer (typecode=3) with a value of 0");
            }
            (NegativeInteger, integer) => -integer,
            _itc => return decoding_error("unexpected ion type code"),
        };

        Ok(value)
    }

    fn read_f32(&mut self) -> IonResult<f32> {
        self.read_f64().map(|f| f as f32)
    }

    fn read_f64(&mut self) -> IonResult<f64> {
        let (encoded_value, bytes) = self.value_and_bytes(IonType::Float)?;
        let number_of_bytes = encoded_value.value_length();
        let value = match number_of_bytes {
            0 => 0f64,
            4 => f64::from(BigEndian::read_f32(bytes)),
            8 => BigEndian::read_f64(bytes),
            _ => return decoding_error("encountered a float with an illegal length"),
        };
        Ok(value)
    }

    fn read_decimal(&mut self) -> IonResult<Decimal> {
        let (encoded_value, mut buffer) = self.value_and_buffer(IonType::Decimal)?;

        if encoded_value.value_length() == 0 {
            return Ok(Decimal::new(0i32, 0i64));
        }

        let exponent_var_int = buffer.read_var_int()?;
        let coefficient_size_in_bytes =
            encoded_value.value_length() - exponent_var_int.size_in_bytes();

        let exponent = exponent_var_int.value();
        let coefficient = buffer.read_int(coefficient_size_in_bytes)?;

        if coefficient.is_negative_zero() {
            return Ok(Decimal::negative_zero_with_exponent(exponent));
        }

        Ok(Decimal::new(coefficient, exponent))
    }

    fn read_string(&mut self) -> IonResult<Str> {
        self.read_str().map(|s| s.into())
    }

    /// If the reader is currently positioned on a string, returns a [&str] containing its text.
    fn read_str(&mut self) -> IonResult<&str> {
        self.read_str_bytes().and_then(|bytes| {
            std::str::from_utf8(bytes)
                .map_err(|_| decoding_error_raw("encountered a string with invalid utf-8 data"))
        })
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        self.read_symbol_id().map(RawSymbolToken::SymbolId)
    }

    fn read_blob(&mut self) -> IonResult<Blob> {
        self.read_blob_bytes().map(Vec::from).map(Blob::from)
    }

    fn read_clob(&mut self) -> IonResult<Clob> {
        self.read_clob_bytes().map(Vec::from).map(Clob::from)
    }

    fn read_timestamp(&mut self) -> IonResult<Timestamp> {
        let (encoded_value, mut buffer) = self.value_and_buffer(IonType::Timestamp)?;

        let offset = buffer.read_var_int()?;
        let is_known_offset = !offset.is_negative_zero();
        let offset_minutes = offset.value() as i32;
        let year = buffer.read_var_uint()?.value() as u32;

        // Year precision

        let builder = Timestamp::with_year(year);
        if buffer.is_empty() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        // Month precision

        let month = buffer.read_var_uint()?.value() as u32;
        let builder = builder.with_month(month);
        if buffer.is_empty() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        // Day precision

        let day = buffer.read_var_uint()?.value() as u32;
        let builder = builder.with_day(day);
        if buffer.is_empty() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        // Hour-and-minute precision

        let hour = buffer.read_var_uint()?.value() as u32;
        if buffer.is_empty() {
            return decoding_error("timestamps with an hour must also specify a minute");
        }
        let minute = buffer.read_var_uint()?.value() as u32;
        let builder = builder.with_hour_and_minute(hour, minute);
        if buffer.is_empty() {
            let timestamp = if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            return Ok(timestamp);
        }

        // Second precision

        let second = buffer.read_var_uint()?.value() as u32;
        let builder = builder.with_second(second);
        if buffer.is_empty() {
            let timestamp = if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            return Ok(timestamp);
        }

        // Fractional second precision

        let subsecond_exponent = buffer.read_var_int()?.value();
        // The remaining bytes represent the coefficient.
        let coefficient_size_in_bytes = encoded_value.value_length() - buffer.total_consumed();
        let subsecond_coefficient = if coefficient_size_in_bytes == 0 {
            DecodedInt::zero()
        } else {
            buffer.read_int(coefficient_size_in_bytes)?
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

    fn step_in(&mut self) -> IonResult<()> {
        let value = self.encoded_value().ok_or_else(|| {
            illegal_operation_raw("cannot step in; the reader is not positioned over a container")
        })?;

        let container_type = match value.header.ion_type {
            IonType::List => ContainerType::List,
            IonType::SExp => ContainerType::SExpression,
            IonType::Struct => ContainerType::Struct,
            _other => {
                return illegal_operation(
                    "cannot step in; the reader is not positioned over a container",
                )
            }
        };

        let total_length = value.total_length();

        let container = Container {
            kind: container_type,
            exclusive_end: self.buffer.total_consumed() + total_length,
        };

        // Move the reader to the first byte within the container's value.
        // Here, `bytes_to_skip` is the sum of the container's number of field ID bytes, annotation
        // wrapper bytes, and header bytes.
        let bytes_to_skip = total_length - value.value_length();
        // The buffer will always contain enough bytes to perform this skip; it had to read all of
        // those bytes in order to be parked on this container in the first place.
        self.buffer.consume(bytes_to_skip);
        // The reader is no longer positioned over a value
        self.state = ReaderState::Ready;
        // Add the container to the `parents` stack.
        self.parents.push(container);

        Ok(())
    }

    fn step_out(&mut self) -> IonResult<()> {
        let parent = match self.parents.pop() {
            Some(parent) => parent,
            None => return illegal_operation("reader cannot step out at the top level (depth=0)"),
        };

        // We need to advance the reader to the first byte beyond the end of the parent container.
        // We'll skip as many bytes as we can from the current buffer, which may or may not be enough.
        let bytes_to_skip = parent.exclusive_end - self.buffer.total_consumed();
        let bytes_available = self.buffer.remaining();

        // Calculate the number of bytes we'll consume based on what's available in the buffer.
        if bytes_to_skip <= bytes_available {
            // All of the bytes we need to skip are in the buffer.
            self.state = ReaderState::Ready;
            self.buffer.consume(bytes_to_skip);
            Ok(())
        } else {
            // Only some of the bytes we need to skip are in the buffer.
            let bytes_left_to_skip = bytes_to_skip - bytes_available;
            self.state = ReaderState::Skipping(bytes_left_to_skip);
            // Skip what we can; and return `Incomplete` so more data can be added.
            self.buffer.consume(bytes_left_to_skip);
            incomplete_data_error("ahead to next item", self.buffer.total_consumed())
        }
    }

    fn parent_type(&self) -> Option<IonType> {
        self.parents.last().map(|c| c.kind.ion_type())
    }

    fn depth(&self) -> usize {
        self.parents.len()
    }
}

/// Iterates over a slice of bytes, lazily reading them as a sequence of VarUInt symbol IDs.
struct AnnotationsIterator<'a> {
    data: std::io::Cursor<&'a [u8]>,
}

impl<'a> AnnotationsIterator<'a> {
    pub(crate) fn new(bytes: &[u8]) -> AnnotationsIterator {
        AnnotationsIterator {
            data: std::io::Cursor::new(bytes),
        }
    }
}

impl<'a> Iterator for AnnotationsIterator<'a> {
    type Item = IonResult<RawSymbolToken>;

    fn next(&mut self) -> Option<Self::Item> {
        let remaining = self.data.remaining();
        if remaining == 0 {
            return None;
        }
        // This iterator cannot be created unless the reader is currently parked on a value.
        // If the reader is parked on a value, the complete annotations sequence is in the buffer.
        // Therefore, reading symbol IDs from this byte slice cannot fail. This allows us to safely
        // unwrap the result of this `read` call.
        let var_uint = VarUInt::read(&mut self.data).unwrap();
        // If this var_uint was longer than the declared annotations wrapper length, return an error.
        if var_uint.size_in_bytes() > remaining {
            Some(decoding_error(
                "found an annotation that exceeded the wrapper's declared length",
            ))
        } else {
            Some(Ok(RawSymbolToken::SymbolId(var_uint.value())))
        }
    }
}

/// A disposable view of the RawBinaryReader's position.
///
/// The TxReader holds a borrowed (immutable) reference to the RawBinaryReader's buffer
/// and a mutable reference to its state.
///
/// By making a slice (view) of the buffer, it is able to read ahead in the buffer without affecting
/// the RawBinaryReader. If it is able to find the next item in the stream, it can then update
/// the RawBinaryReader's state.
///
/// In this way, the RawBinaryReader will never be in a bad state. It only updates when the
/// TxReader has already found the next item.
struct TxReader<'a, A: AsRef<[u8]>> {
    state: &'a mut ReaderState,
    parent: Option<&'a Container>,
    tx_buffer: BinaryBuffer<&'a A>,
    encoded_value: EncodedValue,
    nop_bytes_count: u32,
}

impl<'a, A: AsRef<[u8]>> TxReader<'a, A> {
    /// Begins reading ahead to find the next item.
    #[inline]
    pub(crate) fn read_next_item(&mut self) -> IonResult<RawStreamItem> {
        let type_descriptor = self.tx_buffer.peek_type_descriptor()?;

        match self.parent.map(|p| p.ion_type()) {
            // We're at the top level; check to see if this is an 0xE0
            None if type_descriptor.is_ivm_start() => self.read_ivm(),
            // We're inside a struct; the next item must be a (fieldID, value_header) pair.
            Some(IonType::Struct) => self.read_struct_field_header(),
            // We're...
            //   * At the top level (but not at an IVM)
            //   * Inside a list
            //   * Inside an s-expression
            // The next item must be a (potentially annotated) value.
            _ => self.read_sequence_item(type_descriptor),
        }
    }

    /// Looks for zero or more NOP pads followed by either:
    /// * an annotated value
    /// * a value
    #[inline]
    fn read_sequence_item(
        &mut self,
        mut type_descriptor: TypeDescriptor,
    ) -> IonResult<RawStreamItem> {
        if type_descriptor.is_nop() {
            if let Some(item) = self.consume_nop_padding(&mut type_descriptor)? {
                // We may encounter the end of the file or container while reading NOP padding,
                // in which case `item` will be RawStreamItem::Nothing.
                return Ok(item);
            }
            // Note that if `consume_nop_padding` reads NOP bytes but doesn't hit EOF, it will
            // have updated `type_descriptor` by the time we continue on below.
        }

        if type_descriptor.is_annotation_wrapper() {
            self.read_annotated_value_header(type_descriptor)
        } else {
            self.read_unannotated_value_header(type_descriptor, None)
        }
    }

    /// Looks for zero or more (fieldId, NOP pad) pairs followed by a (fieldId, fieldValue) pair.
    fn read_struct_field_header(&mut self) -> IonResult<RawStreamItem> {
        let mut field_id: VarUInt;
        // NOP padding makes this slightly convoluted. We always read the field ID, but if the value
        // is a NOP then we discard the field ID, read past the NOP, and then start the process again.
        let mut type_descriptor;
        loop {
            // If we've reached the end of the parent struct, return `Nothing`. Note that a struct
            // can be empty (no values) but still contain NOP pads.
            if self.is_at_end_of_container() {
                return Ok(RawStreamItem::Nothing);
            }
            // If there are any bytes in this container (even NOP bytes), there must be a field ID.
            field_id = self.tx_buffer.read_var_uint()?;
            // If there was a field ID, there must be at least one more byte for the NOP or value.
            type_descriptor = self.tx_buffer.peek_type_descriptor()?;
            if type_descriptor.is_nop() {
                let bytes_skipped = self.tx_buffer.read_nop_pad()?;
                self.nop_bytes_count += (field_id.size_in_bytes() + bytes_skipped) as u32;
            } else {
                // We've moved beyond any NOP pads. The last field ID we read was a real one.
                // Record its length and offset information.
                self.encoded_value.field_id_length = match u8::try_from(field_id.size_in_bytes()) {
                    Ok(length) => length,
                    Err(_e) => return decoding_error("found a field ID with more than 255 bytes"),
                };
                self.encoded_value.field_id = Some(field_id.value());
                return if type_descriptor.is_annotation_wrapper() {
                    self.read_annotated_value_header(type_descriptor)
                } else {
                    self.read_unannotated_value_header(type_descriptor, None)
                };
            }
        }
    }

    /// Reads an annotation wrapper followed by a mandatory unannotated value.
    fn read_annotated_value_header(
        &mut self,
        mut type_descriptor: TypeDescriptor,
    ) -> IonResult<RawStreamItem> {
        // Read the annotations envelope from tx_buffer
        let expected_value_length = self.read_annotations_wrapper(type_descriptor)?;
        // If there's no type descriptor after the annotations envelope, return Incomplete.
        type_descriptor = self.tx_buffer.peek_type_descriptor()?;
        // Read the value's header from tx_buffer
        self.read_unannotated_value_header(type_descriptor, Some(expected_value_length))
    }

    /// Reads the unannotated header byte (and any length bytes) for the next value.
    fn read_unannotated_value_header(
        &mut self,
        type_descriptor: TypeDescriptor,
        expected_length: Option<usize>,
    ) -> IonResult<RawStreamItem> {
        // Resolve the TypeDescriptor to a value Header. A Header holds the same information but,
        // because we know it's a value (not a NOP, IVM, or annotation wrapper), it holds an
        // `IonType` instead of an `Option<IonType>`.
        let header: Header = type_descriptor
            .to_header()
            .ok_or_else(|| decoding_error_raw("found a non-value in value position"))?;

        // Add the header to the encoded value we're constructing
        self.encoded_value.header = header;
        // Record the *absolute* offset of the type descriptor -- its offset from the beginning of
        // the stream.
        self.encoded_value.header_offset = self.tx_buffer.total_consumed();
        // Advance beyond the type descriptor
        self.tx_buffer.consume(1);

        // Record the header's offset/length information.
        let length: VarUInt = self.tx_buffer.read_value_length(header)?;
        self.encoded_value.header_length = u8::try_from(length.size_in_bytes()).map_err(|_e| {
            decoding_error_raw("found a value with a header length field over 255 bytes long")
        })?;
        self.encoded_value.value_length = length.value();
        self.encoded_value.total_length = self.encoded_value.field_id_length as usize
            + self.encoded_value.annotations_header_length as usize
            + self.encoded_value.header_length()
            + self.encoded_value.value_length();

        // If this value was annotated, make sure that the length declared in the header matches
        // the one that was declared in the preceding annotations wrapper.
        if let Some(expected_length) = expected_length {
            if expected_length
                != self.encoded_value.header_length() + self.encoded_value.value_length()
            {
                return decoding_error(
                    "annotations wrapper length did not align with value length",
                );
            }
        }

        // Now that we've successfully read the field ID (if present), annotations wrapper (if
        // present), and value header, update the reader's state to hold the EncodedValue we created.
        *self.state = ReaderState::OnValue(self.encoded_value);

        if type_descriptor.is_null() {
            Ok(RawStreamItem::Null(header.ion_type))
        } else {
            Ok(RawStreamItem::Value(header.ion_type))
        }
    }

    #[inline(never)]
    // NOP padding is not widely used in Ion 1.0. This method is annotated with `inline(never)`
    // to avoid the compiler bloating other methods on the hot path with its rarely used
    // instructions.
    fn consume_nop_padding(
        &mut self,
        type_descriptor: &mut TypeDescriptor,
    ) -> IonResult<Option<RawStreamItem>> {
        // Skip over any number of NOP regions
        while type_descriptor.is_nop() {
            // We're not on a value, but we are at a place where the reader can safely resume
            // reading if necessary.
            let bytes_skipped = self.tx_buffer.read_nop_pad()?;
            self.nop_bytes_count += bytes_skipped as u32;
            // If we don't reach a value header by the end of this method, make a note to discard
            // these NOP bytes before we do our next attempt. We don't want the reader to have to
            // hold NOP bytes in the buffer if we've already processed them.
            if self.is_eof() || self.is_at_end_of_container() {
                return Ok(Some(RawStreamItem::Nothing));
            }
            *type_descriptor = self.tx_buffer.peek_type_descriptor()?;
        }
        Ok(None)
    }

    /// Populates the annotations-related offsets in the `EncodedValue` based on the information
    /// read from the annotations envelope. This method does not read the annotations themselves.
    /// Returns the expected length of the annotated value nested inside the envelope.
    fn read_annotations_wrapper(&mut self, type_descriptor: TypeDescriptor) -> IonResult<usize> {
        let initial_consumed = self.tx_buffer.total_consumed();
        // Consume the first byte; its contents are already in the `type_descriptor` parameter.
        self.tx_buffer.consume(1);

        // Read the combined length of the annotations sequence and the value that follows it
        let annotations_and_value_length = match type_descriptor.length_code {
            length_codes::NULL => 0,
            length_codes::VAR_UINT => self.tx_buffer.read_var_uint()?.value(),
            length => length as usize,
        };

        // Read the length of the annotations sequence
        let annotations_length = self.tx_buffer.read_var_uint()?;

        // Validate that the annotations sequence is not empty.
        if annotations_length.value() == 0 {
            return decoding_error("found an annotations wrapper with no annotations");
        }

        // Validate that the annotated value is not missing.
        let expected_value_length = annotations_and_value_length
            - annotations_length.size_in_bytes()
            - annotations_length.value();

        if expected_value_length == 0 {
            return decoding_error("found an annotation wrapper with no value");
        }

        // Skip over the annotations sequence itself; the reader will return to it if/when the
        // reader asks to iterate over those symbol IDs.
        self.tx_buffer.consume(annotations_length.value());

        // Record the important offsets/lengths so we can revisit the annotations sequence later.
        self.encoded_value.annotations_header_length =
            u8::try_from(self.tx_buffer.total_consumed() - initial_consumed).map_err(|_e| {
                decoding_error_raw("found an annotations header greater than 255 bytes long")
            })?;
        self.encoded_value.annotations_sequence_length = u8::try_from(annotations_length.value())
            .map_err(|_e| {
            decoding_error_raw("found an annotations sequence greater than 255 bytes long")
        })?;

        Ok(expected_value_length)
    }

    /// Reads a four-byte Ion v1.0 version marker.
    #[inline(never)]
    fn read_ivm(&mut self) -> IonResult<RawStreamItem> {
        if let Some(container) = self.parent {
            return decoding_error(format!(
                "found an Ion version marker inside a {container:?}"
            ));
        };
        let (major, minor) = self.tx_buffer.read_ivm()?;
        if !matches!((major, minor), (1, 0)) {
            return decoding_error(format!("unsupported Ion version {major:X}.{minor:X}"));
        }
        *self.state = ReaderState::OnIvm;
        Ok(RawStreamItem::VersionMarker(major, minor))
    }

    /// Returns `true` if the reader is currently positioned inside a struct. Otherwise, returns false.
    fn is_in_struct(&self) -> bool {
        self.parent
            .map(|p| p.kind == ContainerType::Struct)
            .unwrap_or(false)
    }

    /// Returns `true` if the reader is inside a container and has consumed enough bytes to have
    /// reached the end.
    fn is_at_end_of_container(&self) -> bool {
        if let Some(parent) = self.parent {
            let position = self.tx_buffer.total_consumed();
            if position >= parent.exclusive_end {
                return true;
            }
        }
        false
    }

    /// Returns `true` if, at this point in the read transaction, the reader is:
    /// * At the top level
    /// * Not inside an annotations wrapper (where a value would be expected)
    /// * Out of tx_buffer bytes
    fn is_eof(&self) -> bool {
        // We're at the top level
        self.parent.is_none()
            && self.encoded_value.annotations_header_length == 0
            && self.tx_buffer.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use crate::binary::non_blocking::raw_binary_reader::RawBinaryReader;
    use crate::text::text_value::IntoRawAnnotations;
    use crate::{IonError, IonResult};
    use std::fmt::Debug;

    use super::*;

    fn expect_incomplete<T: Debug>(result: IonResult<T>) {
        if let Err(IonError::Incomplete { .. }) = result {
            // do nothing
        } else {
            panic!("expected incomplete, found: {result:?}")
        }
    }

    fn expect_eof(result: IonResult<RawStreamItem>) {
        if let Ok(RawStreamItem::Nothing) = result {
            // do nothing
        } else {
            panic!("expected RawStreamItem::Nothing, found: {result:?}")
        }
    }

    fn expect_value(result: IonResult<RawStreamItem>, ion_type: IonType) {
        if let Ok(RawStreamItem::Value(result_ion_type)) = result {
            assert_eq!(result_ion_type, ion_type);
        } else {
            panic!("expected a value, but got: {result:?}");
        }
    }

    fn expect_annotations<A: AsRef<[u8]>, I: IntoRawAnnotations>(
        reader: &RawBinaryReader<A>,
        annotations: I,
    ) {
        let expected = annotations.into_annotations();
        let actual = reader
            .annotations_iter()
            .collect::<IonResult<Vec<RawSymbolToken>>>()
            .unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn read_complete_ivm() -> IonResult<()> {
        let data = &[0xE0, 1, 0, 0xEA];
        let mut reader = RawBinaryReader::new(data);
        assert_eq!(RawStreamItem::VersionMarker(1, 0), reader.next()?);
        Ok(())
    }

    #[test]
    fn read_incomplete_ivm() -> IonResult<()> {
        let data = vec![0xE0];
        let mut reader = RawBinaryReader::new(data);
        // The buffer doesn't contain an entire item
        expect_incomplete(reader.next());
        // We can call .next() again safely any number of times; the result will be the same
        // as the underlying buffer data hasn't changed.
        expect_incomplete(reader.next());
        expect_incomplete(reader.next());
        // We can append data as it becomes available even if it doesn't produce a complete item.
        reader.append_bytes(&[1, 0])?;
        expect_incomplete(reader.next());
        // Finally, when we have enough data to produce an item, a call to next() works as expected.
        reader.append_bytes(&[0xEA])?;
        assert_eq!(RawStreamItem::VersionMarker(1, 0), reader.next().unwrap());
        Ok(())
    }

    #[test]
    fn read_int_header() -> IonResult<()> {
        let data = vec![0x21, 0x03];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Int);
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn read_incomplete_int() -> IonResult<()> {
        let data = vec![0x21];
        let mut reader = RawBinaryReader::new(data);
        // We can no longer read the header successfully on next, we need all of the value's data
        // as well.
        expect_incomplete(reader.next());
        // This byte completes the int, but we still don't have another value to move to.
        reader.append_bytes(&[0x03])?;
        expect_value(reader.next(), IonType::Int);
        expect_eof(reader.next());

        // Now there's an empty string after the int
        reader.append_bytes(&[0x80])?;
        expect_value(reader.next(), IonType::String);

        Ok(())
    }

    #[test]
    fn read_many_ints() -> IonResult<()> {
        let data = vec![
            0x21, 0x01, // 1
            0x21, 0x02, // 2
            0x21, 0x03, // 3
        ];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Int);
        assert_eq!(reader.read_int()?, Int::I64(1));
        expect_value(reader.next(), IonType::Int);
        assert_eq!(reader.read_int()?, Int::I64(2));
        expect_value(reader.next(), IonType::Int);
        assert_eq!(reader.read_int()?, Int::I64(3));
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_floats() -> IonResult<()> {
        let data = vec![
            0x48, 0x40, 0x16, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // 5.5e0
            0x48, 0x40, 0x92, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, // 1.2e3
            0x48, 0xc0, 0x20, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, // -8.125e0
        ];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Float);
        assert_eq!(reader.read_f64()?, 5.5f64);
        expect_value(reader.next(), IonType::Float);
        assert_eq!(reader.read_f64()?, 1200f64);
        expect_value(reader.next(), IonType::Float);
        assert_eq!(reader.read_f64()?, -8.125f64);
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_decimals() -> IonResult<()> {
        let data = vec![
            0x50, // 0.
            0x52, 0xc1, 0x33, // 5.1
            0x52, 0x80, 0xe4, // -100.
            0x52, 0x80, 0x1c, // 28.
        ];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Decimal);
        assert_eq!(reader.read_decimal()?, Decimal::new(0, 0));
        expect_value(reader.next(), IonType::Decimal);
        assert_eq!(reader.read_decimal()?, Decimal::new(51, -1));
        expect_value(reader.next(), IonType::Decimal);
        assert_eq!(reader.read_decimal()?, Decimal::new(-1, 2));
        expect_value(reader.next(), IonType::Decimal);
        assert_eq!(reader.read_decimal()?, Decimal::new(28, 0));
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_timestamps() -> IonResult<()> {
        let data = vec![
            0x63, 0xc0, 0x0f, 0xe6, // 2022T
            0x64, 0xc0, 0x0f, 0xe6, 0x86, // 2022-06T
            0x65, 0xc0, 0x0f, 0xe6, 0x86, 0x92, // 2022-06-18
            0x67, 0xc0, 0x0f, 0xe6, 0x86, 0x92, 0x8b, 0x9e, // 2022-06-18T11:30+00:00
            0x6b, 0x42, 0xac, 0x0f, 0xe6, 0x86, 0x92, 0x90, // 2022-06-18T11:30:51.115-05:00
            0x9e, 0xb3, 0xc3, 0x73, 0x6a, 0x80, 0x0f, 0xe6, 0x86, 0x89, 0x97,
            0x80, // 2022-06-09T23:00:59.045+00:00
            0xbb, 0xc3, 0x2d, 0x69, 0x80, 0x0f, 0xe6, 0x86, 0x89, 0x96,
            0xbb, // 2022-06-09T22:59:59.000+00:00
            0xbb, 0xc3,
        ];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_year(2022).build()?
        );
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_year(2022).with_month(6).build()?
        );
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2022, 6, 18).build()?
        );
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2022, 6, 18)
                .with_hour_and_minute(11, 30)
                .build_at_offset(0)?
        );
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2022, 6, 18)
                .with_hms(11, 30, 51)
                .with_milliseconds(115)
                .build_at_offset(-5 * 60)?
        );
        // 2022-06-09T23:00:59.045+00:00
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2022, 6, 9)
                .with_hms(23, 0, 59)
                .with_milliseconds(45)
                .build_at_offset(0)?
        );
        // 2022-06-09T22:59:59.000+00:00
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2022, 6, 9)
                .with_hms(22, 59, 59)
                .with_milliseconds(0)
                .build_at_offset(0)?
        );
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_symbols() -> IonResult<()> {
        let data = vec![
            0x70, // $0
            0x71, 0x01, // $1
            0x71, 0x02, // $2
            0x72, 0x00, 0x03, // inefficiently encoded $3
        ];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Symbol);
        assert_eq!(reader.read_symbol_id()?, 0);
        expect_value(reader.next(), IonType::Symbol);
        assert_eq!(reader.read_symbol_id()?, 1);
        expect_value(reader.next(), IonType::Symbol);
        assert_eq!(reader.read_symbol_id()?, 2);
        expect_value(reader.next(), IonType::Symbol);
        assert_eq!(reader.read_symbol_id()?, 3);
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_strings() -> IonResult<()> {
        let data = vec![
            0x80, // ""
            0x83, 0x66, 0x6f, 0x6f, // "foo"
            0x83, 0x62, 0x61, 0x72, // "bar"
            0x83, 0x62, 0x61, 0x7a, // "baz"
        ];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::String);
        assert_eq!(reader.read_str()?, "");
        expect_value(reader.next(), IonType::String);
        assert_eq!(reader.read_str()?, "foo");
        expect_value(reader.next(), IonType::String);
        assert_eq!(reader.read_str()?, "bar");
        expect_value(reader.next(), IonType::String);
        assert_eq!(reader.read_str()?, "baz");
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_clobs() -> IonResult<()> {
        let data = vec![
            0x90, // empty
            0x93, 0x66, 0x6f, 0x6f, // b"foo"
            0x93, 0x62, 0x61, 0x72, // b"bar"
            0x93, 0x62, 0x61, 0x7a, // b"baz"
        ];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Clob);
        assert_eq!(reader.read_clob_bytes()?, b"");
        expect_value(reader.next(), IonType::Clob);
        assert_eq!(reader.read_clob_bytes()?, b"foo");
        expect_value(reader.next(), IonType::Clob);
        assert_eq!(reader.read_clob_bytes()?, b"bar");
        expect_value(reader.next(), IonType::Clob);
        assert_eq!(reader.read_clob_bytes()?, b"baz");
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_blobs() -> IonResult<()> {
        let data = vec![
            0xA0, // empty
            0xA3, 0x66, 0x6f, 0x6f, // b"foo"
            0xA3, 0x62, 0x61, 0x72, // b"bar"
            0xA3, 0x62, 0x61, 0x7a, // b"baz"
        ];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Blob);
        assert_eq!(reader.read_blob_bytes()?, b"");
        expect_value(reader.next(), IonType::Blob);
        assert_eq!(reader.read_blob_bytes()?, b"foo");
        expect_value(reader.next(), IonType::Blob);
        assert_eq!(reader.read_blob_bytes()?, b"bar");
        expect_value(reader.next(), IonType::Blob);
        assert_eq!(reader.read_blob_bytes()?, b"baz");
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_annotated_ints() -> IonResult<()> {
        let data = vec![
            0xE4, 0x81, 0x84, 0x21, 0x01, // $4::1
            0xE4, 0x81, 0x85, 0x21, 0x02, // $5::2
            0xE6, 0x83, 0x86, 0x87, 0x88, 0x21, 0x03, // $6::$7::$8::3
        ];
        let mut reader = RawBinaryReader::new(data);

        expect_value(reader.next(), IonType::Int);
        expect_annotations(&reader, [4]);

        expect_value(reader.next(), IonType::Int);
        expect_annotations(&reader, [5]);

        expect_value(reader.next(), IonType::Int);
        expect_annotations(&reader, [6, 7, 8]);
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_list() -> IonResult<()> {
        let data = &[
            0xb4, //  [
            0x21, 0x01, //    1,
            0x21, 0x02, //    2 ]
            0x80, //  "" /*empty string*/
        ];

        // === Skip over list ===
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::List);
        expect_value(reader.next(), IonType::String);
        // Nothing else in the buffer
        expect_eof(reader.next());

        // === Early step out ===
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::List);
        reader.step_in()?;
        expect_value(reader.next(), IonType::Int);
        reader.step_out()?; // Skips second int in list
        expect_value(reader.next(), IonType::String);
        // Nothing else in the buffer
        expect_eof(reader.next());

        // === Visit all values ===
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::List);
        reader.step_in()?;
        expect_value(reader.next(), IonType::Int);
        expect_value(reader.next(), IonType::Int);
        reader.step_out()?;
        // There's an empty string after the list
        expect_value(reader.next(), IonType::String);
        // Nothing else in the buffer
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_empty_list() -> IonResult<()> {
        let data = &[0xB0, 0x80]; // Empty list, empty string
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::List);
        reader.step_in()?;
        // Empty list, calling next() returns Nothing
        assert_eq!(reader.next().unwrap(), RawStreamItem::Nothing);
        reader.step_out()?;
        expect_value(reader.next(), IonType::String);
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_empty_list_with_nop_padding() -> IonResult<()> {
        let data = &[0xB3, 0x00, 0x00, 0x00, 0x80]; // Empty list, empty string
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::List);
        reader.step_in()?;
        // Empty list, calling next() returns Nothing
        assert_eq!(reader.next().unwrap(), RawStreamItem::Nothing);
        reader.step_out()?;
        expect_value(reader.next(), IonType::String);
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_empty_struct() -> IonResult<()> {
        let data = &[0xD0, 0x80]; // Empty struct, empty string
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Struct);
        reader.step_in()?;
        // Empty list, calling next() returns Nothing
        assert_eq!(reader.next().unwrap(), RawStreamItem::Nothing);
        reader.step_out()?;
        expect_value(reader.next(), IonType::String);
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_empty_struct_with_nop_padding() -> IonResult<()> {
        let data = &[
            0xD4, 0x80, 0x00, // $0: NOP,
            0x80, 0x00, // $0: NOP,
            0x80, // Empty string
        ];
        let mut reader = RawBinaryReader::new(data);
        expect_value(reader.next(), IonType::Struct);
        reader.step_in()?;
        // Empty list, calling next() returns Nothing
        assert_eq!(reader.next().unwrap(), RawStreamItem::Nothing);
        reader.step_out()?;
        expect_value(reader.next(), IonType::String);
        expect_eof(reader.next());
        Ok(())
    }

    #[test]
    fn null_string() -> IonResult<()> {
        let data = &[
            0xE0, 0x01, 0x00, 0xEA, // IVM
            0x8F, // null.string
        ];
        let mut reader = RawBinaryReader::new(data);
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::VersionMarker(1, 0));
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::Null(IonType::String));
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::Nothing);
        Ok(())
    }

    #[test]
    fn nop_before_scalar() -> IonResult<()> {
        let data = &[
            0xE0, 0x01, 0x00, 0xEA, // IVM
            0x00, // 1-byte NOP
            0x01, 0xff, // 2-byte NOP
            0x83, 0x66, 0x6f, 0x6f, // "foo"
        ]; // Empty string
        let mut reader = RawBinaryReader::new(data);
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::VersionMarker(1, 0));
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::Value(IonType::String));
        assert_eq!(reader.read_str()?, "foo");
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::Nothing);
        Ok(())
    }

    #[test]
    fn debug() -> IonResult<()> {
        let data = &[
            0xE0, 0x01, 0x00, 0xEA, // IVM
            0xc3, 0xd2, 0x84, 0x11, // ({'name': true})
        ]; // Empty string
        let mut reader = RawBinaryReader::new(data);
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::VersionMarker(1, 0));
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::Value(IonType::SExp));
        reader.step_in()?;
        expect_value(reader.next(), IonType::Struct);
        reader.step_in()?;
        expect_value(reader.next(), IonType::Bool);
        assert_eq!(reader.field_name()?, RawSymbolToken::SymbolId(4));
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::Nothing);
        Ok(())
    }

    #[test]
    fn various_nop_sizes() -> IonResult<()> {
        let data = &[
            0x00, 0x01, 0xff, 0x02, 0xff, 0xff, 0x03, 0xff, 0xff, 0xff, 0x0f,
        ];
        let mut reader = RawBinaryReader::new(data);
        let item = reader.next()?;
        assert_eq!(item, RawStreamItem::Null(IonType::Null));
        Ok(())
    }

    #[test]
    fn incomplete_nops() -> IonResult<()> {
        let data = vec![0x04, 0xff, 0xff];
        let mut reader = RawBinaryReader::new(data);
        expect_incomplete(reader.next());
        // Add another nop byte, but we're still one short
        reader.append_bytes(&[0xff])?;
        expect_incomplete(reader.next());
        // Add another nop byte; the NOP is complete, but there's still no value
        reader.append_bytes(&[0xff])?;
        assert_eq!(reader.next()?, RawStreamItem::Nothing);
        reader.append_bytes(&[0x20])?;
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.read_int()?, Int::I64(0));
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
        let mut cursor = RawBinaryReader::new(ion_data);
        assert_eq!(RawStreamItem::Value(IonType::Struct), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[0..1])); // No value bytes for containers.
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[0..=0]));
        assert_eq!(cursor.raw_value_bytes(), None);
        assert_eq!(cursor.header_offset(), 0);
        cursor.step_in()?;
        assert_eq!(RawStreamItem::Value(IonType::List), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[1..3]));
        assert_eq!(cursor.raw_field_id_bytes(), Some(&ion_data[1..=1]));
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[2..=2]));
        assert_eq!(cursor.raw_value_bytes(), None);
        assert_eq!(cursor.header_offset(), 2);
        assert_eq!(cursor.field_id_offset(), Some(1));
        cursor.step_in()?;
        assert_eq!(RawStreamItem::Value(IonType::Int), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[3..=4]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[3..=3]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[4..=4]));
        assert_eq!(cursor.header_offset(), 3);
        assert_eq!(RawStreamItem::Value(IonType::Int), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[5..=6]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[5..=5]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[6..=6]));
        assert_eq!(cursor.header_offset(), 5);
        assert_eq!(RawStreamItem::Value(IonType::Int), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[7..=8]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[7..=7]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[8..=8]));
        assert_eq!(cursor.header_offset(), 7);

        cursor.step_out()?; // Step out of list

        assert_eq!(RawStreamItem::Value(IonType::Int), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[9..=11]));
        assert_eq!(cursor.raw_field_id_bytes(), Some(&ion_data[9..=9]));
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[10..=10]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[11..=11]));
        assert_eq!(cursor.field_id_offset(), Some(9));

        cursor.step_out()?; // Step out of struct

        // Second top-level value
        assert_eq!(RawStreamItem::Value(IonType::Bool), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[12..16]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), Some(&ion_data[12..=14]));
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[15..=15]));
        assert_eq!(
            cursor.raw_value_bytes(),
            Some(&ion_data[15..15] /*That is, zero bytes*/)
        );
        Ok(())
    }
}
