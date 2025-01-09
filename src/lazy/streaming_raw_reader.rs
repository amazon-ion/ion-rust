use std::cell::UnsafeCell;
use std::fs::File;
use std::io;
use std::io::{BufReader, Read, StdinLock};
use std::marker::PhantomData;

use crate::lazy::any_encoding::IonEncoding;
use crate::lazy::decoder::{Decoder, LazyRawReader};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::raw_stream_item::LazyRawStreamItem;
use crate::{IonError, IonResult, LazyRawValue};

/// Wraps an implementation of [`IonDataSource`] and reads one top level value at a time from the input.
pub struct StreamingRawReader<Encoding: Decoder, Input: IonInput> {
    // The type of decoder we're using. This type determines which `LazyRawReader` implementation
    // is constructed for each slice of the input buffer.
    decoder: PhantomData<Encoding>,
    // The Ion encoding that this reader has been processing.
    // The StreamingRawReader works by reading the next value from the bytes currently available
    // in the buffer using a (non-streaming) raw reader. If the buffer is exhausted, it will read
    // more data into the buffer and create a new raw reader. If the raw reader uses `AnyEncoding`,
    // the detected Ion encoding will be carried over from raw reader instance to raw reader instance.
    detected_encoding: IonEncoding,
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
    input: UnsafeCell<Input::DataSource>,
}

const DEFAULT_IO_BUFFER_SIZE: usize = 4 * 1024;

pub struct RawReaderState<'a> {
    data: &'a [u8],
    offset: usize,
    is_final_data: bool,
    encoding: IonEncoding,
}

impl<'a> RawReaderState<'a> {
    pub fn new(data: &'a [u8], offset: usize, is_final_data: bool, encoding: IonEncoding) -> Self {
        Self {
            data,
            offset,
            is_final_data,
            encoding,
        }
    }

    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    pub fn is_final_data(&self) -> bool {
        self.is_final_data
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn encoding(&self) -> IonEncoding {
        self.encoding
    }

    pub(crate) fn set_encoding(&mut self, encoding: IonEncoding) {
        self.encoding = encoding;
    }
}

impl<Encoding: Decoder, Input: IonInput> StreamingRawReader<Encoding, Input> {
    pub fn new(_encoding: Encoding, input: Input) -> StreamingRawReader<Encoding, Input> {
        StreamingRawReader {
            decoder: PhantomData,
            // This value will be overwritten if/when the reader detects a new version.
            detected_encoding: Encoding::INITIAL_ENCODING_EXPECTED,
            input: input.into_data_source().into(),
            stream_position: 0,
        }
    }

    /// Gets a reference to the data source and tries to fill its buffer.
    #[inline]
    fn pull_more_data_from_source(&mut self) -> IonResult<usize> {
        self.input.get_mut().fill_buffer()
    }

    /// Returns true if the input buffer is empty.
    #[inline]
    fn buffer_is_empty(&mut self) -> bool {
        self.input.get_mut().buffer().is_empty()
    }

    pub fn next<'top>(
        &'top mut self,
        context: EncodingContextRef<'top>,
    ) -> IonResult<LazyRawStreamItem<'top, Encoding>> {
        self.read_next(context, /*is_peek=*/ false)
    }

    pub fn peek_next<'top>(
        &'top mut self,
        context: EncodingContextRef<'top>,
    ) -> IonResult<LazyRawStreamItem<'top, Encoding>> {
        self.read_next(context, /*is_peek=*/ true)
    }

    fn read_next<'top>(
        &'top mut self,
        context: EncodingContextRef<'top>,
        is_peek: bool,
    ) -> IonResult<LazyRawStreamItem<'top, Encoding>> {
        // If the input is a stream, we assume there may be more data available.
        // If it's a fixed slice, we know it's already complete.
        let mut input_source_exhausted = !Input::DataSource::IS_STREAMING;
        loop {
            // If the input buffer is empty, try to pull more data from the source before proceeding.
            // It's important that we do this _before_ reading from the buffer; any item returned
            // from a successful `slice_reader.next()` will hold a reference to the buffer. We cannot
            // modify it once we have that item.
            if self.buffer_is_empty() {
                self.pull_more_data_from_source()?;
            }

            // We're going to try to read a lazy value from the available input. If we
            // succeed, we'll return it. If the data is incomplete, we'll return to the top
            // of the loop. Conditionally returning a value in a loop is the borrow checker's
            // Achilles' heel (see comment on the `StreamingRawReader` type), so we use an
            // unsafe access to get a reference to the available bytes.
            //
            // SAFETY: If `self.input` needs to be refilled later on, `available_bytes` MUST NOT be
            //         read from in the same loop iteration afterward, since it may refer to a buffer
            //         that has been dropped.
            let available_bytes = unsafe { &*self.input.get() }.buffer();
            let state = RawReaderState::new(
                available_bytes,
                self.stream_position,
                input_source_exhausted,
                self.encoding(),
            );

            // Construct a new raw reader picking up from where the StreamingRawReader left off.
            let mut slice_reader =
                <Encoding::Reader<'top> as LazyRawReader<'top, Encoding>>::resume(context, state);
            let starting_position = slice_reader.position();
            let old_encoding = slice_reader.encoding();

            let result = slice_reader.next();

            let new_encoding = slice_reader.encoding();
            let end_position = slice_reader.position();

            let bytes_read = end_position - starting_position;

            // If we ran out of data before we could get a result...
            if matches!(
                result,
                Err(IonError::Incomplete(_)) | Ok(LazyRawStreamItem::<Encoding>::EndOfStream(_))
            ) {
                if input_source_exhausted {
                    // There's no more data, so the result is final.
                } else {
                    // ...more data may be available, so try to pull from the data source.
                    if self.pull_more_data_from_source()? == 0 {
                        input_source_exhausted = true;
                    }
                    continue;
                }
            } else if let Ok(ref item) = result {
                // We have successfully read something from the buffer.
                //
                // In binary encodings, stream items contain enough data for the reader to tell
                // whether they are complete.
                //
                // In text encodings, it's possible for the buffer to end with data that looks like
                // a complete item but is not. The only way to be certain is to try to read again
                // from the input source to confirm there's no more data. Consider the following
                // examples in which Ion is being pulled from a `File` into a `Vec<u8>`:
                //
                //       foo /* comment */   ::bar::baz::1000
                //       └────────┬───────┘ └────────┬───────┘
                //         buffer contents   remaining in File
                //
                //                     $ion _1_0
                //       └────────┬───────┘ └────────┬───────┘
                //         buffer contents   remaining in File
                //
                //                       75 1.20
                //       └────────┬───────┘ └────────┬───────┘
                //         buffer contents   remaining in File
                //
                // To avoid this, we perform a final check for text readers who have emptied their
                // buffer: we do not consider the item complete unless the input source is exhausted.
                if old_encoding.is_text()
                    && bytes_read == available_bytes.len()
                    && !input_source_exhausted
                {
                    use crate::lazy::raw_stream_item::RawStreamItem::*;
                    match item {
                        // Text containers and e-expressions have closing delimiters that allow us
                        // to tell that they're complete.
                        Value(v) if v.ion_type().is_container() => {}
                        EExp(_eexp) => {}
                        // IVMs (which look like symbols), scalar values, and the end of the
                        // stream are all cases where the reader looking at a fixed slice of the
                        // buffer may reach the wrong conclusion.
                        _ => {
                            // Try to pull more data from the input source.
                            if self.pull_more_data_from_source()? == 0 {
                                input_source_exhausted = true;
                            }
                            continue;
                        }
                    }
                }

                // If this isn't just a peek, update our state to remember what we've already read.
                if !is_peek {
                    // Mark those input bytes as having been consumed so they are not read again.
                    self.input.get_mut().consume(bytes_read);
                    // Update the streaming reader's position to reflect the number of bytes we
                    // just read.
                    self.stream_position = end_position;
                    // If the item read was an IVM, this will be a new value.
                    self.detected_encoding = new_encoding;
                }
            }

            return result;
        }
    }

    pub fn encoding(&self) -> IonEncoding {
        self.detected_encoding
    }
}

/// An input source--typically an implementation of either `AsRef<[u8]>` or `io::Read`--from which
/// Ion can be read, paying the cost of buffering and I/O copies only when necessary.
pub trait IonDataSource {
    /// If `true`, the current contents of the buffer may not be the complete stream.
    const IS_STREAMING: bool;

    /// Returns a slice of all unread bytes that are currently available in the buffer.
    fn buffer(&self) -> &[u8];

    /// Attempts to read more input from the data source into the buffer of available bytes.
    /// A return value of `Ok(0)` indicates that there is no more data, but does not preclude the
    /// possibility that more data will become available in the future.
    fn fill_buffer(&mut self) -> IonResult<usize>;

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

impl<SliceType: AsRef<[u8]>> IonDataSource for IonSlice<SliceType> {
    const IS_STREAMING: bool = false;

    #[inline]
    fn buffer(&self) -> &[u8] {
        // Return the input slice containing all of the as-of-yet unread bytes.
        &self.stream_bytes()[self.position..]
    }

    #[inline]
    fn fill_buffer(&mut self) -> IonResult<usize> {
        // For fixed inputs, this is a no-op.
        Ok(0)
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
}

impl<R: Read> IonStream<R> {
    const DEFAULT_IO_BUFFER_SIZE: usize = 4 * 1024;

    pub fn new(input: R) -> Self {
        IonStream {
            input,
            buffer: vec![0u8; Self::DEFAULT_IO_BUFFER_SIZE],
            // The index of the first occupied byte in the buffer
            position: 0,
            // The index of the first unoccupied byte in the buffer *at or after* `position`.
            limit: 0,
        }
    }
}

impl<R: Read> IonStream<R> {
    /// Moves all of the bytes in the range `self.position..self.limit` to the beginning of the buffer,
    /// reclaiming space that was previously occupied by bytes that have since been consumed.
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

impl<R: Read> IonDataSource for IonStream<R> {
    const IS_STREAMING: bool = true;

    fn buffer(&self) -> &[u8] {
        &self.buffer[self.position..self.limit]
    }

    fn fill_buffer(&mut self) -> IonResult<usize> {
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

        // Update `self.limit` to mark the newly read in bytes as available.
        self.limit += bytes_read;
        Ok(bytes_read)
    }

    fn consume(&mut self, number_of_bytes: usize) {
        self.position += number_of_bytes;
        debug_assert!(self.position <= self.limit);
    }
}

/// Types that can be used as a source of Ion data.
///
/// In general, this trait is implemented by mapping `Self` to either:
///   * [`IonSlice`], if `Self` is an implementation of `AsRef<[u8]>`
///   * [`IonStream`], if `Self` is an implementation of `io::Read`
pub trait IonInput {
    type DataSource: IonDataSource;

    fn into_data_source(self) -> Self::DataSource;
}

impl<SliceType: AsRef<[u8]>> IonInput for IonSlice<SliceType> {
    type DataSource = Self;

    fn into_data_source(self) -> Self::DataSource {
        self
    }
}

impl<Input: Read> IonInput for IonStream<Input> {
    type DataSource = Self;

    fn into_data_source(self) -> Self::DataSource {
        self
    }
}

/// Implements `IonInput` for types that represent a complete Ion stream (i.e. that do not and
/// cannot read more data from another source once exhausted).
macro_rules! impl_ion_input_for_slice_types {
    ($($ty:ty),* $(,)?) => {
        $(
            impl <'a> IonInput for $ty {
                type DataSource = IonSlice<$ty>;

                fn into_data_source(self) -> Self::DataSource {
                    IonSlice::new(self)
                }
            }
        )*
    };
}

impl_ion_input_for_slice_types!(&'a [u8], &'a str, String, &'a String, Vec<u8>, &'a Vec<u8>);

impl IonInput for File {
    type DataSource = IonStream<BufReader<Self>>;

    fn into_data_source(self) -> Self::DataSource {
        IonStream::new(BufReader::new(self))
    }
}

impl<R: Read> IonInput for BufReader<R> {
    type DataSource = IonStream<Self>;

    fn into_data_source(self) -> Self::DataSource {
        IonStream::new(self)
    }
}

impl IonInput for StdinLock<'_> {
    type DataSource = IonStream<Self>;

    fn into_data_source(self) -> Self::DataSource {
        IonStream::new(self)
    }
}

impl<T: Read, U: Read> IonInput for io::Chain<T, U> {
    type DataSource = IonStream<Self>;

    fn into_data_source(self) -> Self::DataSource {
        IonStream::new(self)
    }
}

impl IonInput for Box<dyn Read> {
    type DataSource = IonStream<Self>;

    fn into_data_source(self) -> Self::DataSource {
        IonStream::new(self)
    }
}

#[cfg(test)]
mod tests {
    use std::io;
    use std::io::{BufReader, Cursor, Read};

    use crate::lazy::any_encoding::AnyEncoding;
    use crate::lazy::decoder::{Decoder, LazyRawValue};
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::raw_stream_item::LazyRawStreamItem;
    use crate::lazy::raw_value_ref::RawValueRef;
    use crate::lazy::streaming_raw_reader::{IonInput, StreamingRawReader};
    use crate::raw_symbol_ref::AsRawSymbolRef;
    use crate::{v1_0, Decimal, IonError, IonResult, IonStream, RawSymbolRef, RawVersionMarker};

    fn expect_value<'a, D: Decoder>(
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

    fn expect_end_of_stream(actual: LazyRawStreamItem<'_, AnyEncoding>) -> IonResult<()> {
        assert!(matches!(
            actual,
            LazyRawStreamItem::<AnyEncoding>::EndOfStream(_)
        ));
        Ok(())
    }

    #[test]
    fn read_empty_slice() -> IonResult<()> {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let ion = "";
        let mut reader = StreamingRawReader::new(AnyEncoding, ion.as_bytes());
        // We expect `Ok(EndOfStream)`, not `Err(Incomplete)`.
        expect_end_of_stream(reader.next(context)?)?;
        Ok(())
    }

    fn read_example_stream(input: impl IonInput) -> IonResult<()> {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let mut reader = StreamingRawReader::new(AnyEncoding, input);
        expect_string(reader.next(context)?, "foo")?;
        expect_string(reader.next(context)?, "bar")?;
        expect_string(reader.next(context)?, "baz")?;
        expect_string(reader.next(context)?, "quux")?;
        expect_string(reader.next(context)?, "quuz")?;
        expect_end_of_stream(reader.next(context)?)
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

    fn read_invalid_example_stream(input: impl IonInput) -> IonResult<()> {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let mut reader = StreamingRawReader::new(AnyEncoding, input);
        let result = reader.next(context);
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

    #[test]
    fn incomplete_trailing_values() -> IonResult<()> {
        // Each read() call will return these UTF-8 byte sequences in turn:
        let input_chunks = [
            "$ion", // $ion_1_0
            "_1_0",
            " 87", // 871.25
            "1.25",
            " foo ", // foo::bar::baz::quux
            "   ::bar  :",
            ":baz",
            "::quux",
        ];
        // We achieve this by wrapping each string in an `io::Chain`.
        let mut input: Box<dyn Read> = Box::new(io::empty());
        for input_chunk in input_chunks {
            input = Box::new(input.chain(Cursor::new(input_chunk)));
        }
        // This guarantees that there are several intermediate reading states in which the buffer
        // contains incomplete data that could be misinterpreted by a reader.
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let mut reader = StreamingRawReader::new(v1_0::Text, IonStream::new(input));

        assert_eq!(reader.next(context)?.expect_ivm()?.major_minor(), (1, 0));
        assert_eq!(
            reader
                .next(context)?
                .expect_value()?
                .read()?
                .expect_decimal()?,
            Decimal::new(87125, -2)
        );
        let value = reader.next(context)?.expect_value()?;
        let annotations = value
            .annotations()
            .collect::<IonResult<Vec<RawSymbolRef<'_>>>>()?;
        assert_eq!(
            annotations,
            vec![
                "foo".as_raw_symbol_ref(),
                "bar".as_raw_symbol_ref(),
                "baz".as_raw_symbol_ref(),
            ]
        );
        assert_eq!(value.read()?.expect_symbol()?, "quux".as_raw_symbol_ref());

        Ok(())
    }
}
