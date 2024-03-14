use std::cell::UnsafeCell;
use std::fs::File;
use std::io::{BufReader, Read, StdinLock};

use bumpalo::Bump as BumpAllocator;

use crate::lazy::decoder::{LazyDecoder, LazyRawReader};
use crate::lazy::raw_stream_item::LazyRawStreamItem;
use crate::IonResult;

/// Wraps an implementation of [`IonInput`] and reads one top level value at a time from the input.
pub struct StreamingRawReader<Encoding: LazyDecoder, Input: IntoIonInput> {
    // The Ion encoding that this reader recognizes.
    encoding: Encoding,
    // The StreamingRawReader works by reading the next value from the bytes currently available
    // in the buffer using a (non-streaming) raw reader. If the buffer is exhausted, it will read
    // more data into the buffer and create a new raw reader. If any state needs to be preserved
    // when moving from the old raw reader to the new one, that data's type will be set as the
    // `Encoding`'s `ReaderSavedState`.
    // At present, the only encoding that uses this is `AnyEncoding`, which needs to pass a record
    // of the stream's detected encoding from raw reader to raw reader. For all other encodings,
    // this is a zero-sized type and its associated operations are no-ops.
    saved_state: Encoding::ReaderSavedState,
    // The absolute position of the reader within the overall stream. This is the index of the first
    // byte that has not yet been read.
    stream_position: usize,
    // XXX: The `UnsafeCell` wrappers around the field below is a workaround for a limitation in
    //      rustc's borrow checker that prevents mutable references from being conditionally
    //      returned in a loop.
    //
    //      See: https://github.com/rust-lang/rust/issues/70255
    //
    //      There is a rustc fix for this limitation on the horizon.
    //
    //      See: https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/
    //
    //      Indeed, using the experimental `-Zpolonius` flag on the nightly compiler allows the
    //      version of this code without `unsafe` types to work. The alternative to the
    //      hack is wrapping each field in something like `RefCell`, which adds a small amount of
    //      overhead to each access. Given that this is the hottest path in the code and that a
    //      fix is inbound, I think this use of `unsafe` is warranted for now.
    //
    input: UnsafeCell<Input::IonInput>,
}

const DEFAULT_IO_BUFFER_SIZE: usize = 4 * 1024;

impl<Encoding: LazyDecoder, Input: IntoIonInput> StreamingRawReader<Encoding, Input> {
    pub fn new(encoding: Encoding, input: Input) -> StreamingRawReader<Encoding, Input> {
        StreamingRawReader {
            encoding,
            input: input.into_ion_input().into(),
            saved_state: Default::default(),
            stream_position: 0,
        }
    }

    pub fn next<'top>(
        &'top mut self,
        allocator: &'top BumpAllocator,
    ) -> IonResult<LazyRawStreamItem<'top, Encoding>> {
        loop {
            let available_bytes = unsafe { &*self.input.get() }.buffer();
            let unsafe_cell_reader = UnsafeCell::new(<Encoding::Reader<'top> as LazyRawReader<
                'top,
                Encoding,
            >>::resume_at_offset(
                available_bytes,
                self.stream_position,
                self.saved_state,
            ));
            let slice_reader = unsafe { &mut *unsafe_cell_reader.get() };
            let starting_position = slice_reader.position();
            let result = slice_reader.next(allocator);
            // We're done modifying `slice_reader`, but we need to read some of its fields. These
            // fields are _not_ the data to which `result` holds a reference. We have to circumvent
            // the borrow checker's limitation (described in a comment on the StreamingRawReader type)
            // by getting a second (read-only) reference to the reader.
            let slice_reader_ref = unsafe { &*unsafe_cell_reader.get() };
            let end_position = slice_reader_ref.position();
            // For the RawAnyReader, remember what encoding we detected for next time.
            self.saved_state = slice_reader_ref.save_state();

            let bytes_read = end_position - starting_position;
            let input = unsafe { &mut *self.input.get() };
            // If we've exhausted the buffer but not the data source...
            if bytes_read >= available_bytes.len() && !input.stream_has_ended() {
                // ...we need to pull more data from the source and try again to make sure that the
                // buffer didn't contain incomplete data.
                input.fill_buffer()?;
                continue;
            }
            // Mark those input bytes as having been consumed so they are not read again.
            input.consume(bytes_read);
            // Update the streaming reader's position to reflect the number of bytes we
            // just read.
            self.stream_position = end_position;

            return result;
        }
    }
}

/// An input source--typically an implementation of either `AsRef<[u8]>` or `io::Read`--from which
/// Ion can be read, paying the cost of buffering and I/O copies only when necessary.
pub trait IonInput {
    /// Returns a slice of all unread bytes that are currently available in the buffer.
    fn buffer(&self) -> &[u8];

    // /// Indicates whether the data source from which this `IonInput` reads has been exhausted.
    // fn stream_has_ended(&self) -> bool;

    /// Attempts to read more input from the data source into the buffer of available bytes.
    fn fill_buffer(&mut self) -> IonResult<()>;

    /// Marks `number_of_bytes` in the buffer as having been read. The caller is responsible for
    /// confirming that the buffer contains at least `number_of_bytes` bytes.
    fn consume(&mut self, number_of_bytes: usize);
}

/// A fixed slice of Ion data that does not grow; it wraps an implementation of `AsRef<[u8]>` such
/// as `&[u8]`, `Vec<u8>`, `&str`, or `String`.
///
/// Because the input is fixed (and therefore already available in full), this type performs no
/// additional buffering or copying of the input data.
pub struct IonSlice<SliceType> {
    // Typically a `&[u8]`, `&str`, or other byte-array-backed variable.
    source: SliceType,
    // The offset of the first byte that hasn't yet been consumed.
    position: usize,
}

impl<SliceType: AsRef<[u8]>> IonSlice<SliceType> {
    /// Constructs a new `IonSlice` that reads from the input value's backing data.
    pub fn new(bytes: SliceType) -> Self {
        Self {
            source: bytes,
            position: 0,
        }
    }

    /// Helper method that returns the complete input stream's backing byte array, including bytes
    /// that have already been read/consumed.
    #[inline]
    fn stream_bytes(&self) -> &[u8] {
        self.source.as_ref()
    }
}

impl<SliceType: AsRef<[u8]>> IonInput for IonSlice<SliceType> {
    #[inline]
    fn buffer(&self) -> &[u8] {
        // Return the input slice containing all of the as-of-yet unread bytes.
        &self.stream_bytes()[self.position..]
    }

    // fn stream_has_ended(&self) -> bool {
    //     // Because the input is fixed, all of the input data is already available. There is no more
    //     // data to read in, making this trivially `true`.
    //     true
    // }

    fn fill_buffer(&mut self) -> IonResult<()> {
        // For fixed inputs, this is a no-op.
        Ok(())
    }

    fn consume(&mut self, number_of_bytes: usize) {
        self.position += number_of_bytes;
        // In debug/test builds, this will fail noisily if something attempts to consume more data
        // than the backing array contains.
        debug_assert!(
            self.position <= self.stream_bytes().len(),
            "Assert failed: {} <= {}, buffer: {:0x?}",
            self.position,
            self.stream_bytes().len(),
            self.buffer()
        );
    }
}

/// A buffered reader for types that don't implement AsRef<[u8]>
pub struct IonStream<R: Read> {
    // The input source
    input: R,
    // A buffer containing a sliding window of data from `input`.
    buffer: Vec<u8>,
    // The index of the first occupied byte in the buffer. If position==limit, no bytes
    // are occupied.
    position: usize,
    // The index of the first unoccupied byte in the buffer *at or after* `position`.
    limit: usize,
    // // Whether an `input.read()` has returned `0` so far.
    // is_end_of_stream: bool,
}

impl<R: Read> IonStream<R> {
    const DEFAULT_IO_BUFFER_SIZE: usize = 4 * 1024;

    fn new(input: R) -> Self {
        IonStream {
            input,
            buffer: vec![0u8; Self::DEFAULT_IO_BUFFER_SIZE],
            // The index of the first occupied byte in the buffer
            position: 0,
            // The index of the first unoccupied byte in the buffer *at or after* `position`.
            limit: 0,
            // // Whether `input` has returned EOF yet
            // is_end_of_stream: false,
        }
    }
}

impl<R: Read> IonStream<R> {
    /// Moves all of the bytes from `self.position` to `self.limit` to the beginning of the buffer,
    /// reclaiming space that was previously occupied by bytes that have been consumed.
    fn shift_remaining_bytes_to_index_zero(&mut self) {
        // Shift everything after `remaining_data_start_index` to the beginning of the Vec and
        // update the limit.
        let remaining_data_range = self.position..self.limit;
        self.limit = remaining_data_range.len();
        self.position = 0;
        self.buffer.copy_within(remaining_data_range, 0);
        debug_assert!(self.buffer().len() == self.limit - self.position);
    }
}

impl<R: Read> IonInput for IonStream<R> {
    fn buffer(&self) -> &[u8] {
        &self.buffer[self.position..self.limit]
    }

    // fn stream_has_ended(&self) -> bool {
    //     self.is_end_of_stream
    // }

    fn fill_buffer(&mut self) -> IonResult<()> {
        // If
        if self.position > 0 {
            // We've consumed bytes (advancing `position`) and can therefore reclaim some of the
            // space at the beginning of our buffer.
            self.shift_remaining_bytes_to_index_zero();
        }
        if self.buffer.len() == self.limit {
            // If we're out of space, double the size of the buffer and fill it with zeros
            // before proceeding. (The bytes must be set to a value to avoid undefined behavior;
            // zero is a conventional choice. The value will never be used anyway.)
            self.buffer.resize(self.buffer.len() * 2, 0);
        }
        // Attempt to read as many bytes as will fit in the currently allocated capacity beyond
        // `limit`.
        let bytes_read = self.input.read(&mut self.buffer[self.limit..])?;
        // If the input source returns `Ok(0)`, there's no more data coming. We can mark the stream
        // as complete.
        // if bytes_read == 0 {
        //     self.is_end_of_stream = true;
        // }
        // Update `self.limit` to mark the newly read in bytes as available.
        self.limit += bytes_read;
        Ok(())
    }

    fn consume(&mut self, number_of_bytes: usize) {
        self.position += number_of_bytes;
        debug_assert!(self.position <= self.limit);
    }
}

pub trait IntoIonInput {
    type IonInput: IonInput;

    fn into_ion_input(self) -> Self::IonInput;
}

/// Implements `IntoIonInput` for types that represent a complete Ion stream (i.e. that do not and
/// cannot read more data from another source once exhausted).
macro_rules! impl_into_ion_input_for_slice_types {
    ($($ty:ty),* $(,)?) => {
        $(
            impl <'a> IntoIonInput for $ty {
                type IonInput = IonSlice<$ty>;

                fn into_ion_input(self) -> Self::IonInput {
                    IonSlice::new(self)
                }
            }
        )*
    };
}

impl_into_ion_input_for_slice_types!(&'a [u8], &'a str, String, Vec<u8>,);

impl IntoIonInput for File {
    type IonInput = IonStream<BufReader<Self>>;

    fn into_ion_input(self) -> Self::IonInput {
        IonStream::new(BufReader::new(self))
    }
}

impl<R: Read> IntoIonInput for BufReader<R> {
    type IonInput = IonStream<Self>;

    fn into_ion_input(self) -> Self::IonInput {
        IonStream::new(self)
    }
}

impl<'a> IntoIonInput for StdinLock<'a> {
    type IonInput = IonStream<Self>;

    fn into_ion_input(self) -> Self::IonInput {
        IonStream::new(self)
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufReader, Cursor};

    use bumpalo::Bump as BumpAllocator;

    use crate::lazy::any_encoding::AnyEncoding;
    use crate::lazy::decoder::{LazyDecoder, LazyRawValue};
    use crate::lazy::raw_stream_item::LazyRawStreamItem;
    use crate::lazy::raw_value_ref::RawValueRef;
    use crate::lazy::streaming_raw_reader::{IntoIonInput, StreamingRawReader};
    use crate::{IonError, IonResult};

    fn expect_value<'a, D: LazyDecoder>(
        actual: LazyRawStreamItem<'a, D>,
        expected: RawValueRef<'a, D>,
    ) -> IonResult<()> {
        assert_eq!(actual.expect_value()?.read()?, expected);
        Ok(())
    }

    fn expect_string<'a, 'b: 'a>(
        actual: LazyRawStreamItem<'a, AnyEncoding>,
        text: &'b str,
    ) -> IonResult<()> {
        expect_value(actual, RawValueRef::<AnyEncoding>::String(text.into()))
    }

    fn expect_end_of_stream(actual: LazyRawStreamItem<AnyEncoding>) -> IonResult<()> {
        assert!(matches!(
            actual,
            LazyRawStreamItem::<AnyEncoding>::EndOfStream
        ));
        Ok(())
    }

    #[test]
    fn read_empty_slice() -> IonResult<()> {
        let bump = BumpAllocator::new();
        let ion = "";
        let mut reader = StreamingRawReader::new(AnyEncoding, ion.as_bytes());
        // We expect `Ok(EndOfStream)`, not `Err(Incomplete)`.
        expect_end_of_stream(reader.next(&bump)?)?;
        Ok(())
    }

    fn read_example_stream(input: impl IntoIonInput) -> IonResult<()> {
        let bump = BumpAllocator::new();
        let mut reader = StreamingRawReader::new(AnyEncoding, input);
        expect_string(reader.next(&bump)?, "foo")?;
        expect_string(reader.next(&bump)?, "bar")?;
        expect_string(reader.next(&bump)?, "baz")?;
        expect_string(reader.next(&bump)?, "quux")?;
        expect_string(reader.next(&bump)?, "quuz")?;
        expect_end_of_stream(reader.next(&bump)?)
    }

    // This stream is 104 bytes long
    const EXAMPLE_STREAM: &str = r#"
        "foo" // comment 1
        "bar"
        "baz"
        "quux" /* comment 2 
     */ "quuz"
    "#;

    #[test]
    fn read_slice() -> IonResult<()> {
        let str_ = EXAMPLE_STREAM;
        let string = str_.to_string();
        let slice = str_.as_bytes();
        let vec = slice.to_vec();

        read_example_stream(str_)?;
        read_example_stream(string)?;
        read_example_stream(slice)?;
        read_example_stream(vec)
    }

    /// Returns an implementation of io::Read with a buffer small enough to encounter multiple
    /// incomplete values.
    fn tiny_buf_reader(input: &str) -> BufReader<Cursor<&str>> {
        BufReader::with_capacity(1, Cursor::new(input))
    }

    #[test]
    fn read_stream() -> IonResult<()> {
        let input = tiny_buf_reader(EXAMPLE_STREAM);
        read_example_stream(input)
    }

    const INVALID_EXAMPLE_STREAM: &str = "2024-03-12T16:33.000-05:"; // Missing offset minutes

    fn read_invalid_example_stream(input: impl IntoIonInput) -> IonResult<()> {
        let bump = BumpAllocator::new();
        let mut reader = StreamingRawReader::new(AnyEncoding, input);
        let result = reader.next(&bump);
        // Because the input stream is exhausted, the incomplete value is illegal data and raises
        // a decoding error.
        assert!(matches!(result, Err(IonError::Decoding(_))), "{:?}", result);
        Ok(())
    }

    #[test]
    fn read_invalid_stream() -> IonResult<()> {
        read_invalid_example_stream(tiny_buf_reader(INVALID_EXAMPLE_STREAM))
    }

    #[test]
    fn read_invalid_slice() -> IonResult<()> {
        let str_ = INVALID_EXAMPLE_STREAM;
        let string = str_.to_string();
        let slice = str_.as_bytes();
        let vec = slice.to_vec();

        read_invalid_example_stream(str_)?;
        read_invalid_example_stream(string)?;
        read_invalid_example_stream(slice)?;
        read_invalid_example_stream(vec)
    }
}
