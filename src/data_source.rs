use crate::result::IonResult;
use std::io::BufRead;

/// Optimized read operations for parsing Ion.
///
/// The [binary Ion spec](amzn.github.io/ion-docs/docs/binary.html) calls for a number of reading
/// patterns, including:
///
/// * Type descriptor octets (value headers) require that a single byte be read from input.
/// * Variable length integers (both signed and unsigned) require that a single byte at a time be
///   read from the data source until some condition is met.
/// * Fixed length values require that `n` bytes be read from the data source and interpreted as a
///   single value.
/// * Skipping over values, partial or whole, requires that the next `n` bytes of the data source be
///   ignored altogether.
///
/// The IonDataSource trait extends functionality offered by the [BufRead] trait by providing
/// methods that are tailored to these use cases. They have been optimized to prefer operating
/// on data that's already in the input buffer in-place rather than copying it out to another
/// byte array.
pub trait IonDataSource: BufRead {
    /// Ignore the next `number_of_bytes` bytes in the data source.
    fn skip_bytes(&mut self, number_of_bytes: usize) -> IonResult<()>;

    /// Returns the next byte in the data source if available.
    fn next_byte(&mut self) -> IonResult<Option<u8>>;

    /// Calls `byte_processor` on each byte in the data source until it returns false.
    /// Returns the number of bytes that were read and processed.
    fn read_next_byte_while<F>(&mut self, byte_processor: &mut F) -> IonResult<usize>
    where
        F: FnMut(u8) -> bool;

    /// Calls `slice_processor` on a slice containing the next `length` bytes from the
    /// data source. If the required bytes are already in the input buffer, a reference to that
    /// slice of the input buffer will be used. If they are not, the required bytes will be read
    /// into `fallback_buffer` and that will be used instead. If `fallback_buffer` does not have
    /// enough capacity to store the requested data, it will be resized. It will never be shrunk,
    /// however--it is the caller's responsibility to manage this memory.
    fn read_slice<T, F>(
        &mut self,
        length: usize,
        fallback_buffer: &mut Vec<u8>,
        slice_processor: F,
    ) -> IonResult<T>
    where
        F: FnOnce(&[u8]) -> IonResult<T>;
}

// Allows all implementations of `BufRead` to be used as an IonDataSource, including BufReader
// and io::Cursor.
impl<T: BufRead> IonDataSource for T {
    // Moves the cursor within the input buffer until `number_of_bytes` bytes have been skipped.
    // Will read from the underlying data source as needed.
    fn skip_bytes(&mut self, number_of_bytes: usize) -> IonResult<()> {
        let mut bytes_skipped = 0;
        while bytes_skipped < number_of_bytes {
            let buffer = self.fill_buf()?;
            let bytes_in_buffer = buffer.len();
            let bytes_to_skip = (number_of_bytes - bytes_skipped).min(bytes_in_buffer);
            self.consume(bytes_to_skip);
            bytes_skipped += bytes_to_skip;
        }
        Ok(())
    }

    // Returns the next byte in the input buffer if one is available. Otherwise reads one from the
    // underlying data source.
    fn next_byte(&mut self) -> IonResult<Option<u8>> {
        match self.fill_buf()?.first() {
            Some(&byte) => {
                self.consume(1);
                Ok(Some(byte))
            }
            None => Ok(None),
        }
    }

    // Some data types in the binary Ion spec have a length that must be discovered by reading a
    // single byte at a time from the data source. Simply calling
    // [io::Read::read](https://doc.rust-lang.org/std/io/trait.Read.html#tymethod.read)
    // or iterating over the data source's input bytes using
    // [io::Read::bytes](https://doc.rust-lang.org/std/io/trait.Read.html#method.bytes)
    // requires copying and error handling to be performed for each byte read, causing these methods
    // to be prohibitively expensive.
    //
    // This method directly accesses the data source's input buffer, allowing us to process
    // the bytes in-place. No error handling is performed unless the end of the buffer is reached,
    // requiring us to perform a single read() call to refill it.
    //
    // For more information, read the documentation for the BufRead trait's
    // [fill_buf](https://doc.rust-lang.org/std/io/trait.BufRead.html#tymethod.fill_buf)
    // and
    // [consume](https://doc.rust-lang.org/std/io/trait.BufRead.html#tymethod.consume)
    // methods.
    fn read_next_byte_while<F>(&mut self, byte_processor: &mut F) -> IonResult<usize>
    where
        F: FnMut(u8) -> bool,
    {
        // The number of bytes that have been processed by the provided closure
        let mut number_of_bytes_processed: usize = 0;
        // The number of bytes currently available in the data source's input buffer
        let mut number_of_buffered_bytes: usize;
        // The number of bytes that have been flushed from the input buffer after processing them
        let mut number_of_bytes_consumed: usize = 0;

        loop {
            // Get a reference to the data source's input buffer, refilling it if it's empty.
            let buffer = self.fill_buf()?;
            number_of_buffered_bytes = buffer.len();

            // Iterate over the bytes already in the buffer, calling the provided lambda on each
            // one.
            for byte in buffer {
                number_of_bytes_processed += 1;
                if !byte_processor(*byte) {
                    // If the lambda is finished reading, notify the data source of how many bytes
                    // we've read from the buffer so they can be removed.
                    self.consume(number_of_bytes_processed - number_of_bytes_consumed);
                    return Ok(number_of_bytes_processed);
                }
            }

            // If we read all of the available data in the buffer but the lambda isn't finished yet,
            // empty the buffer so the next loop iteration will refill it.
            self.consume(number_of_buffered_bytes);
            number_of_bytes_consumed += number_of_buffered_bytes;
        }
    }

    // Like `read_next_byte_while`, this method will prefer to process the next `number_of_bytes`
    // bytes without copying them out of the input buffer. It can be used to process any Ion value
    // of a known size.
    fn read_slice<V, F>(
        &mut self,
        number_of_bytes: usize,
        fallback_buffer: &mut Vec<u8>,
        slice_processor: F,
    ) -> IonResult<V>
    where
        F: FnOnce(&[u8]) -> IonResult<V>,
    {
        // Get a reference to the data source's input buffer, refilling it if it's empty.
        let buffer = self.fill_buf()?;

        // If the requested value is already in our input buffer, there's no need to copy it out
        // into a separate buffer. We can return a slice of the input buffer and consume() that
        // number of bytes.
        if buffer.len() >= number_of_bytes {
            let result = slice_processor(&buffer[..number_of_bytes]);
            self.consume(number_of_bytes);
            return result;
        }

        // Grow the Vec to accommodate the requested data if needed
        let buffer: &mut [u8] = if fallback_buffer.len() < number_of_bytes {
            fallback_buffer.resize(number_of_bytes, 0);
            // Get a mutable reference to the underlying byte array
            fallback_buffer.as_mut()
        } else {
            // Otherwise, split the Vec's underlying storage to get a &mut [u8] slice of the
            // required size
            let (required_buffer, _) = fallback_buffer.split_at_mut(number_of_bytes);
            required_buffer
        };

        // Fill the fallback buffer with bytes from the data source
        self.read_exact(buffer)?;
        slice_processor(buffer)
    }
}

#[cfg(test)]
mod tests {
    use super::IonDataSource;
    use std::io::BufReader;

    fn test_data(buffer_size: usize, data: &'static [u8]) -> impl IonDataSource {
        BufReader::with_capacity(buffer_size, data)
    }

    #[test]
    fn test_next_byte() {
        let mut data_source = test_data(2, &[1, 2, 3, 4, 5]);

        assert_eq!(Some(1), data_source.next_byte().unwrap());
        assert_eq!(Some(2), data_source.next_byte().unwrap());
        assert_eq!(Some(3), data_source.next_byte().unwrap());
        assert_eq!(Some(4), data_source.next_byte().unwrap());
        assert_eq!(Some(5), data_source.next_byte().unwrap());
    }

    #[test]
    fn test_skip_bytes() {
        let mut data_source = test_data(2, &[1, 2, 3, 4, 5]);
        data_source.skip_bytes(3).unwrap();
        assert_eq!(Some(4), data_source.next_byte().unwrap());
        data_source.skip_bytes(1).unwrap();
        assert_eq!(None, data_source.next_byte().unwrap());
    }

    #[test]
    fn test_read_next_byte_while() {
        let mut data_source = test_data(2, &[1, 2, 3, 4, 5]);
        let mut sum: u64 = 0;
        let processor = &mut |byte: u8| {
            sum += byte as u64;
            byte < 4
        };
        let number_of_bytes_processed = data_source.read_next_byte_while(processor).unwrap();
        assert_eq!(number_of_bytes_processed, 4);
        assert_eq!(sum, 10);
    }

    #[test]
    fn test_read_slice() {
        let mut data_source = test_data(2, &[1, 2, 3, 4, 5]);
        let processor = &mut |data: &[u8]| Ok(data.iter().map(|byte| *byte as i32).sum());
        let sum = data_source
            .read_slice(4, &mut Vec::new(), processor)
            .unwrap();
        assert_eq!(10, sum);
    }
}
