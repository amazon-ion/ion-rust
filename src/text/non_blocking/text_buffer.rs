use crate::result::position::Position;
use crate::IonResult;

use std::io::Read;

use crate::result::IonFailure;
use thiserror::Error;

/// Represents a span of bytes that have been validated as UTF-8 strings.
///
/// The range of bytes is [.0, .1)
#[derive(Debug, Copy, Clone)]
struct ValidUtf8Span(usize, usize);
impl ValidUtf8Span {
    fn increment_start(&self, bytes: usize) -> ValidUtf8Span {
        ValidUtf8Span(self.0.wrapping_add(bytes), self.1)
    }

    fn shift_left(&mut self, bytes: usize) {
        self.0 = self.0.saturating_sub(bytes);
        self.1 = self.1.saturating_sub(bytes);
    }
}

#[derive(Debug, Copy, Clone)]
struct Checkpoint {
    pub line: ValidUtf8Span,
    pub line_number: usize,
    pub offset: usize,
    pub bytes_consumed: usize,
}

/// Calculates the offset into a slice, where a given subslice is located.
/// This is used primarily for identifying where a &str comes from within our
/// TextBuffer's data.
///
/// Taken from <https://stackoverflow.com/a/50781657>
trait SubsliceOffset {
    fn subslice_offset(&self, inner: &Self) -> Option<usize>;
}

impl SubsliceOffset for str {
    fn subslice_offset(&self, inner: &Self) -> Option<usize> {
        let this_start = self.as_ptr() as usize;
        let inner_start = inner.as_ptr() as usize;
        if inner_start < this_start || inner_start > this_start.wrapping_add(self.len()) {
            None
        } else {
            Some(inner_start.wrapping_sub(this_start))
        }
    }
}

#[derive(Debug, Error)]
pub(crate) enum TextError {
    #[error("Incomplete UTF-8 data at {line}:{column}")]
    Incomplete { line: usize, column: usize },

    #[error("Invalid UTF-8 sequence in provided data at byte {offset}")]
    InvalidUtf8 { offset: usize },
}

impl TextError {
    fn utf8_error(offset: usize) -> Self {
        Self::InvalidUtf8 { offset }
    }
}

/// Wrapper around an `AsRef<[u8]>` that provides methods to read text, and track lines.
pub(crate) struct TextBuffer<A: AsRef<[u8]>> {
    data: A,
    /// End of our data buffer. This includes any partial UTF-8 bytes.
    data_end: usize,
    /// Indicates whether or not the data source has been completely read.
    data_exhausted: bool,
    /// The span of our `data` that has been validated as UTF-8.
    data_utf8: ValidUtf8Span,
    /// The total number of bytes that have been consumed.
    bytes_consumed: usize,

    /// The current validated line data (can contain multiple lines).
    line: ValidUtf8Span,
    /// Offset into the current line that has been read.
    line_offset: usize,
    /// Number of lines that have been read.
    line_number: usize,
    /// Tracks what column the line data ended on. This is used when reporting errors.
    line_end_column: usize,
    /// Save point for rolling back. Invalidated by `append_bytes`, and `read_from`.
    checkpoint: Option<Checkpoint>,
}

impl<A: AsRef<[u8]>> TextBuffer<A> {
    /// Constructs a new TextBuffer that will pull lines of text from the provided input.
    pub fn new(data: A) -> Self {
        let data_len = data.as_ref().len();
        Self {
            data,
            data_end: data_len,
            data_exhausted: false,
            data_utf8: ValidUtf8Span(0, 0),
            bytes_consumed: 0,
            line: ValidUtf8Span(0, 0),
            line_offset: 0,
            line_number: 0,
            line_end_column: 0,
            checkpoint: None,
        }
    }

    /// Returns the total number of bytes that have been consumed.
    pub fn bytes_consumed(&self) -> usize {
        self.bytes_consumed
    }

    pub fn get_position(&self) -> Position {
        Position::with_offset(self.bytes_consumed)
            .with_line_and_column(self.line_number, self.line_offset)
    }

    /// Save a checkpoint that can be rolled back to.
    /// This stores the line information (offset, line number, span of our UTF8 data, etc) so that
    /// we can rollback to it later if needed. The data stored here is invalidated on a read_from,
    /// or append_bytes.
    pub fn checkpoint(&mut self) {
        self.checkpoint = Some(Checkpoint {
            line: self.line,
            line_number: self.line_number,
            offset: self.line_offset,
            bytes_consumed: self.bytes_consumed,
        })
    }

    pub fn rollback(&mut self) {
        if let Some(checkpoint) = self.checkpoint.take() {
            self.line_offset = checkpoint.offset;
            self.line = checkpoint.line;
            self.line_number = checkpoint.line_number;
            self.bytes_consumed = checkpoint.bytes_consumed;
        }
    }

    /// Returns the trailing portion of the current line that has not yet been marked as read via
    /// the [`consume`](Self::consume) method.
    pub fn remaining_text(&self) -> &str {
        self.string_view(self.line.increment_start(self.line_offset))
    }

    /// Returns a &str view of the bytes within `data` specified by `span`.
    /// This function assumes prior UTF-8 validation has occurred.
    fn string_view(&self, span: ValidUtf8Span) -> &str {
        use std::str::from_utf8_unchecked;
        unsafe { from_utf8_unchecked(&self.data.as_ref()[span.0..span.1]) }
    }

    /// Returns the amount of data currently available in the buffer that has not been marked as
    /// read via the [`consume`](Self::consume) method. This includes data that has not been
    /// split into lines yet.
    pub fn bytes_remaining(&self) -> usize {
        self.data_end - (self.line.0 + self.line_offset)
    }

    /// Returns the number of lines that have been loaded from input.
    ///
    /// The number returned may be:
    ///   * Greater than the number of lines that have been marked read via
    ///     [`consume`](Self::consume).
    ///   * Less than the number of lines that have been requested via
    ///     [`load_next_line`](Self::load_next_line) and
    ///     [`load_next_n_lines`](Self::load_next_n_lines) if the input stream was exhausted.
    pub fn lines_loaded(&self) -> usize {
        self.line_number
    }

    /// Returns the number of characters into the line that have been consumed.
    pub fn line_offset(&self) -> usize {
        self.line_offset
    }

    pub fn is_exhausted(&self) -> bool {
        self.bytes_remaining() == 0 && self.data_exhausted
    }

    /// Discards `number_of_bytes` bytes from the remaining line.
    ///
    /// If `number_of_bytes` would cause the remaining bytes to be invalid UTF-8,
    /// this method will panic.
    ///
    /// If `number_of_bytes` is greater than the number of bytes remaining in the current line,
    /// this method will panic.
    pub fn consume(&mut self, number_of_bytes: usize) {
        let remaining_line = self.remaining_text();

        assert!(
            number_of_bytes <= remaining_line.len(),
            "Cannot consume() more bytes than are left in the current line."
        );
        assert!(
            remaining_line.is_char_boundary(number_of_bytes),
            "Cannot consume() a number of bytes that will leave invalid UTF-8 in the current line."
        );
        self.line_offset += number_of_bytes;
        self.bytes_consumed += number_of_bytes;
    }

    /// Loads a single line from the underlying data source into the buffer.
    pub fn load_next_line(&mut self) -> Result<usize, TextError> {
        self.load_next_n_lines(1)
    }

    /// Loads up to `number_of_lines` lines from the underlying data source into the buffer.
    /// If there are fewer lines this function will load what is available and return success.
    ///
    /// If the data source ends on a character boundary, but not an end of line, the data will be
    /// considered a complete line and loaded. If the data source ends between character boundaries
    /// for a multi-byte character, an error of TextError::Incomplete is returned.
    pub fn load_next_n_lines(&mut self, number_of_lines: usize) -> Result<usize, TextError> {
        use std::str::from_utf8_unchecked;
        if self.data_utf8.1 == 0 {
            // We haven't validated any data..
            self.validate_data()?;
        }

        if self.line.1 >= self.data_end {
            self.data_exhausted = true;
            return Ok(0);
        }

        // Safe: `data_utf8` contains the span of `data` that is valid UTF-8. `line` is
        // contained within the `data_utf8` span. The start of `line` is calculated by finding the
        // offset into our data after we walk UTF-8 characters and find EOLs, ensuring that we are
        // always aligned to the start of UTF-8 sequences.
        let source =
            unsafe { from_utf8_unchecked(&self.data.as_ref()[self.line.1..self.data_utf8.1]) };

        let (count, line) = source
            .split_inclusive('\n')
            .take(number_of_lines)
            .enumerate()
            .last()
            .take()
            .unwrap_or((0, ""));

        let bytes_read = match source.subslice_offset(line) {
            Some(n) => {
                // We return the resulting valid data, even if the line is not ended and we have
                // a trailing incomplete sequence.
                self.line.0 += self.line_offset;
                self.line.1 += n + line.bytes().len();

                self.line_end_column = line.chars().count();
                n + line.bytes().len()
            }
            None => {
                // We did not find any lines within source. This means that the data we have
                // remaining is an incomplete sequence.
                return Err(TextError::Incomplete {
                    line: self.line_number,
                    column: self.line_end_column,
                });
            }
        };
        self.line_number += count;
        if line.ends_with('\n') {
            self.line_number += 1;
            self.line_end_column -= 1;
        }
        self.line_offset = 0;

        self.data_utf8.0 = self.line.0;
        Ok(bytes_read)
    }

    /// This function validates the UTF-8, and trims any trailing data that causes the UTF8
    /// validation to fail. This is to help in the case of updating the data as new data is
    /// obtained asynchronously.
    fn validate_data(&mut self) -> Result<(), TextError> {
        use std::str::from_utf8;
        // If we've already validated data, and new data was appended, we only have to validate the
        // appended data with any partial data that was invalid before the append.
        let ValidUtf8Span(valid_start, valid_end) = self.data_utf8;

        let new_end = match from_utf8(&self.data.as_ref()[valid_end..self.data_end]) {
            Ok(_valid) => {
                // All of the data is valid UTF-8.
                self.data_end
            }
            Err(error) => {
                let last_valid_offset = error.valid_up_to();
                if last_valid_offset > 0 && error.error_len().is_none() {
                    // There is an incomplete multi-byte sequence at the end of the data.
                    // We'll assume the remaining bytes for that sequence will be appended later
                    // and mark everything up to the start of that sequence as valid.
                    last_valid_offset + valid_end
                } else {
                    // The input contained an invalid UTF-8 sequence.
                    Err(TextError::utf8_error(last_valid_offset))?
                }
            }
        };

        self.data_utf8 = ValidUtf8Span(valid_start, new_end);
        Ok(())
    }
}

impl TextBuffer<Vec<u8>> {
    /// Moves any unread bytes to the front of the `Vec<u8>`, making room for more data at the
    /// tail. This method should only be called when the bytes remaining in the buffer represent an
    /// incomplete value; as such, the required `memcpy` should typically be quite small.
    ///
    /// This function will invalidate any data returned by `remaining_text` as the bytes in the
    /// buffer will have shifted.
    fn restack(&mut self) {
        let shift_offset = self.line.0 + self.line_offset;

        // Shift off all of our consumed data, leaving the buffer to start with the current line's
        // unconsumed data.
        self.data.copy_within(shift_offset..self.data_end, 0);
        self.data_end -= shift_offset;

        // The shift invalidates all of our ValidUtf8Spans.. so we need to adjust.
        self.data_utf8.shift_left(shift_offset);
        self.line.shift_left(shift_offset);
        self.line_offset = 0;
    }

    /// Copies the provided bytes to the end of the input buffer.
    pub fn append_bytes(&mut self, bytes: &[u8]) -> Result<(), TextError> {
        self.checkpoint = None;
        self.restack();
        let remaining = self.data.len() - self.data_end;
        if bytes.len() > remaining {
            let needed = bytes.len() - remaining;
            self.data.resize(self.data.len() + needed, 0);
        }
        let dst = &mut self.data[self.data_end..self.data_end + bytes.len()];
        dst.copy_from_slice(bytes);
        self.data_end += bytes.len();
        self.data_exhausted = false;
        self.validate_data()
    }

    /// Tries to read `length` bytes from `source`. Unlike [`append_bytes`](Self::append_bytes),
    /// this method does not do any copying. A slice of the reader's buffer is handed to `source`
    /// so it can be populated directly.
    pub fn read_from<R: Read>(&mut self, mut source: R, length: usize) -> IonResult<usize> {
        self.checkpoint = None;
        self.restack();
        self.reserve_capacity(length);

        let read_buffer = &mut self.data.as_mut_slice()[self.data_end..(self.data_end + length)];
        let bytes_read = source.read(read_buffer)?;
        self.data_end += bytes_read;

        // We have new data, so we need to ensure that it is valid UTF-8.
        if self.validate_data().is_err() {
            return IonResult::decoding_error("Invalid UTF-8 sequence in data");
        }

        self.data_exhausted = self.data_end == 0;

        Ok(bytes_read)
    }

    /// Extends the underlying `Vec<u8>` so that there are `length` bytes available beyond
    /// `self.end`. This block of zeroed out bytes can then be used as an input I/O buffer for
    /// calls to `read_from`.
    fn reserve_capacity(&mut self, length: usize) {
        let capacity = self.data.len() - self.data_end;
        if capacity < length {
            self.data.resize(self.data.len() + length - capacity, 0);
        }
    }
}

impl<A: AsRef<[u8]>> From<A> for TextBuffer<A> {
    fn from(data: A) -> Self {
        Self::new(data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text_buffer(source: &str) -> TextBuffer<&[u8]> {
        TextBuffer::new(source.as_bytes())
    }

    #[test]
    fn restack() {
        let source = "first line\nsecond line\n";
        let mut input = TextBuffer::new(source.as_bytes().to_owned());
        // Should be reading: "first line"
        match input.load_next_line() {
            Ok(11) => (),
            wrong => panic!("Unexpected result from load_next_line: {wrong:?}"),
        }
        assert_eq!(input.remaining_text(), "first line\n");
        input.consume(11);

        match input.load_next_line() {
            Ok(12) => (),
            wrong => panic!("Unexpected result from load_next_line: {wrong:?}"),
        }
        assert_eq!(input.remaining_text(), "second line\n");

        input.restack();

        assert_eq!(input.remaining_text(), "second line\n");

        input.consume(12);
        input.restack();
        assert_eq!(input.remaining_text(), "");
    }

    #[test]
    fn append() {
        let source = "first line\nsecond line\n";
        let mut input = TextBuffer::new(source.as_bytes().to_owned());
        let size = input.load_next_line().unwrap();
        assert_eq!(input.remaining_text(), "first line\n");
        assert_eq!(input.lines_loaded(), 1);
        input.consume(size);

        input
            .append_bytes("third line\n".as_bytes())
            .expect("Invalid UTF-8 detected on append");

        let size = input.load_next_line().unwrap();
        assert_eq!(input.remaining_text().trim(), "second line");
        assert_eq!(input.lines_loaded(), 2);
        input.consume(size);

        let size = input.load_next_line().unwrap();
        assert_eq!(input.remaining_text().trim(), "third line");
        assert_eq!(input.lines_loaded(), 3);
        input.consume(size);
    }

    #[test]
    fn read_from() {
        let source = "first line\n";
        let mut input = TextBuffer::new(source.as_bytes().to_owned());
        let size = input.load_next_line().unwrap();
        assert_eq!(input.remaining_text(), "first line\n");
        assert_eq!(input.data_end, 11);
        input.consume(size);

        // At this point our buffer should be sized to fit the first line, but since we have
        // consumed all of the first line, reading `more.len()` bytes will grow the buffer by
        // the whatever is needed to accomodate the diffence in `more`'s size.
        let more = "second line\n";
        match input.read_from(more.as_bytes(), more.len()) {
            Ok(x) if x == more.len() => (),
            wrong => panic!("Unexpected response from read_from: {wrong:?}"),
        }
        assert_eq!(input.data_end, 12);

        input.load_next_line().unwrap();
        assert_eq!(input.remaining_text(), more);
        assert_eq!(input.lines_loaded(), 2);
    }

    #[test]
    fn partial_utf8() {
        // atom_modified is a multi-byte unicode character with a variation.
        // The first 3 bytes represent the character '⚛' (atom). The trailing
        // 3 bytes represent the variation which adds a purple background.
        let atom_modified = &[0xe2, 0x9a, 0x9b, 0xef, 0xb8, 0x8f];
        let source: &str = "We Love Ion! ";
        let mut input = TextBuffer::new(source.as_bytes().to_owned());
        // Add only part of our atom character, copying all but the last byte of the modifier.
        input
            .append_bytes(&atom_modified[..=4])
            .expect("unable to add partial UTF-8 character");

        // This should succeed, and provide access to all of the data up to the start of the
        // incomplete sequence. Unfortunately, the 'invalid' sequence starts with the modifier, so
        // the atom symbol is returned.
        match input.load_next_line() {
            Ok(16) => (),
            wrong => panic!("Unexpected result from load_next_line: {wrong:?}"),
        }

        input
            .append_bytes(&atom_modified[5..])
            .expect("unable to fix UTF-8 character..");
        // This read should read the remaining 3 bytes of the modifier, and our remaining text
        // should match the entire sequence.
        match input.load_next_line() {
            Ok(3) => {
                assert_eq!(&input.remaining_text().as_bytes()[..13], source.as_bytes());
                assert_eq!(&input.remaining_text().as_bytes()[13..], atom_modified);
            }
            wrong => panic!("Unexpected result from load_next_line: {wrong:?}"),
        }
    }

    #[test]
    fn incremental_utf8_validation() {
        // In this test we add partial data that is valid UTF-8, and advance the line. This will
        // cause the validation span to be updated. Next we add the remaining data which contains
        // an invalid UTF-8 sequence. This will update the valid span to include the valid portion
        // of the newly added data. After updating the line again, we should have valid UTF-8 data,
        // and the invalid sequence should be left in the buffer. This test is in response to GH
        // issue 461, which found that the remaining_text after this operation did not contain the
        // validated span, and resulted in an invalid UTF-8 sequence created unchecked.
        let source = " from";
        let data = &[0x20, 0x27, 0xe8, 0xa9, 0xb1, 0xe8, 0xa9, 0xb1, 0x20, 0xe8];
        let mut input = TextBuffer::new(source.as_bytes().to_owned());
        assert!(input.load_next_line().is_ok());
        assert!(input.append_bytes(data).is_ok());
        assert!(input.load_next_line().is_ok());

        let text = input.remaining_text();
        let bytes = text.as_bytes();
        match std::str::from_utf8(bytes) {
            Ok(_) => {}
            Err(_) => panic!("Invalid UTF-8 sequence"),
        }
        assert_eq!(text.len(), 14);
    }

    #[test]
    fn consume() {
        let source = r#"first line"#;
        let mut input = TextBuffer::new(source.as_bytes().to_owned());
        input.load_next_line().unwrap();

        assert_eq!(input.remaining_text(), "first line");

        input.consume(6);
        assert_eq!(input.remaining_text(), "line");
    }

    #[test]
    #[should_panic]
    fn invalid_utf8_consume() {
        let source = "😎";
        let mut input = TextBuffer::new(source.as_bytes().to_owned());
        input.load_next_line().unwrap();
        // This jumps into the middle of the emoji.
        // If it were to succeed, the next call to remaining_text() would panic.
        input.consume(1);
    }

    #[test]
    #[should_panic]
    fn consume_too_many_bytes() {
        let source = "foo";
        let mut input = TextBuffer::new(source.as_bytes().to_owned());
        input.load_next_line().unwrap();
        // There are only 3 bytes in the buffer.
        // We cannot consume more bytes than are available.
        input.consume(75);
    }

    #[test]
    fn validate_subslice_offset() {
        let data = "foo bar baz halb blah";
        let subdata = &data[4..7];
        assert_eq!(subdata, "bar");
        assert_eq!(data.subslice_offset(subdata), Some(4));
        assert_eq!(data.subslice_offset(&data[8..11]), Some(8));

        let bogus = unsafe {
            let slice = std::slice::from_raw_parts(data.as_ptr().wrapping_add(50), 10);
            std::str::from_utf8_unchecked(slice)
        };
        assert_eq!(data.subslice_offset(bogus), None);
        let otherdata = "something entirely different";
        let othersubdata = &otherdata[4..7];
        assert_eq!(data.subslice_offset(othersubdata), None);
    }

    #[test]
    fn load_next_line() {
        let mut buffer = text_buffer("foo\nbar\nbaz\nquux\n");
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        assert_eq!(buffer.remaining_text(), "foo\n");
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        assert_eq!(buffer.remaining_text(), "foo\nbar\n");
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        assert_eq!(buffer.remaining_text(), "foo\nbar\nbaz\n");
        assert_eq!(buffer.load_next_line().unwrap(), 5);
        assert_eq!(buffer.remaining_text(), "foo\nbar\nbaz\nquux\n");
        // EOF is indicated by Ok(0); no bytes were read.
        assert_eq!(buffer.load_next_line().unwrap(), 0);
        // Calling load_next_line() after EOF continues to result in Ok(0)
        assert_eq!(buffer.load_next_line().unwrap(), 0);
        assert_eq!(buffer.load_next_line().unwrap(), 0);
    }

    #[test]
    fn load_next_n_lines() {
        let mut buffer = text_buffer("foo\nbar\nbaz\nquux\n");
        assert_eq!(buffer.load_next_n_lines(3).unwrap(), 12);
        assert_eq!(buffer.remaining_text(), "foo\nbar\nbaz\n");
        assert_eq!(buffer.lines_loaded(), 3);
        // There's only one line left, but we request two.
        // load_next_n_lines() should report success, saying that 5 bytes were read.
        assert_eq!(buffer.load_next_n_lines(2).unwrap(), 5);
        // If we check lines_loaded(), however, we can see that only 4 total lines have been loaded.
        assert_eq!(buffer.lines_loaded(), 4);
        // If we ask for more data, it will report Ok(0) bytes read: EOF.
        assert_eq!(buffer.load_next_n_lines(2).unwrap(), 0);
    }

    #[test]
    fn is_exhausted() {
        let mut buffer = text_buffer("foo\nbar\n");
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        assert_eq!(buffer.remaining_text(), "foo\n");
        buffer.consume(4);
        // The buffer itself is empty, but input has not reached EOF yet.
        assert!(!buffer.is_exhausted());
        // Load another line
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        // Now input is at EOF, but the buffer contains text.
        assert!(!buffer.is_exhausted());
        // Consume the bytes in the buffer
        buffer.consume(4);
        // Now the buffer is empty. Looking ahead, we can tell that the input is empty,
        // but we have to try to load another line to actually encounter EOF.
        assert!(!buffer.is_exhausted());
        assert_eq!(buffer.load_next_line().unwrap(), 0);
        // Now the buffer is empty and the input has hit EOF.
        assert!(buffer.is_exhausted());
    }

    #[test]
    fn invalid_utf8_returns_err() {
        // Invalid UTF-8 data
        let data = &[0xf1, 0xf2, 0xc2, 0x80];
        let mut buffer = TextBuffer::new(data);
        assert!(buffer.load_next_line().is_err());
    }

    #[test]
    fn rollback() {
        // In order to handle any sort of transactional parsing in the readers, we need to have the
        // ability to unconsume
        let mut buffer = text_buffer("foo\nbar\n");
        assert_eq!(buffer.load_next_line().unwrap(), 4);

        buffer.checkpoint();
        match buffer.checkpoint {
            Some(check) => {
                assert_eq!(check.offset, 0);
                match check.line {
                    ValidUtf8Span(start, end) => {
                        assert_eq!(start, 0);
                        assert_eq!(end, 4);
                    }
                }
            }
            None => panic!("no checkpoint generated."),
        }

        assert_eq!(buffer.remaining_text(), "foo\n");
        buffer.consume(4); // We've moved beyond "foo"
        assert_eq!(buffer.line_offset, 4);

        buffer.rollback(); // Roll back to the start.
        assert_eq!(buffer.line_offset, 0);
        assert_eq!(buffer.remaining_text(), "foo\n");

        // Check again, but this time with a readline at the end.
        buffer.checkpoint();
        assert_eq!(buffer.remaining_text(), "foo\n");
        buffer.consume(4); // We've moved beyond "foo"

        assert_eq!(buffer.line_offset, 4);
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        assert_eq!(buffer.remaining_text(), "bar\n");
    }
}
