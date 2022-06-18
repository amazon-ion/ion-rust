use std::io;
use std::io::BufRead;

/// A text buffer that pulls more bytes from the input source as needed.
///
/// A parser reading from a text stream should use the [load_next_line] method to pull text into
/// the buffer from the input source. The text currently in the buffer can be accessed via the
/// [remaining_text] method. When a portion of that text has been processed, the user can discard it
/// with the [consume] method. If the buffer does not contain enough data to represent a full value,
/// more data can be pulled into the buffer with [load_next_line]; this additional text will be
/// visible in the next call to [remaining_text].
pub(crate) struct TextBuffer<R: BufRead> {
    // The input source to read from (an io::Cursor, BufReader, File, etc)
    input: R,
    // The line we're in the process of parsing.
    line: String,
    // How much of the current line we've already parsed.
    line_offset: usize,
    // The 1-based index of the line currently being read.
    // When the LineBuffer is first constructed and no lines
    // have been read from input, this value is 0.
    line_number: usize,
    // Whether `input` above has reached EOF.
    is_exhausted: bool,
}

impl<R: BufRead> TextBuffer<R> {
    /// Constructs a new LineBuffer that will pull lines of text from the provided input.
    pub fn new(input: R) -> Self {
        Self {
            input,
            line: String::with_capacity(128),
            line_offset: 0,
            line_number: 0,
            is_exhausted: false,
        }
    }

    /// Returns the trailing portion of the buffer that has not yet been marked as read via the
    /// [consume] method.
    pub fn remaining_text(&self) -> &str {
        &self.line[self.line_offset..]
    }

    /// Returns the number of lines that have been loaded from input. The number returned may be:
    /// * Greater than the number of lines that have been marked read via [consume].
    /// * Less than the number of lines that have been requested via [load_next_line] and
    ///   [load_next_n_lines] if the input stream was exhausted.
    pub fn lines_loaded(&self) -> usize {
        self.line_number
    }

    /// Returns [true] if the buffer is empty and the end of the input source has been reached;
    /// otherwise, returns false.
    pub fn is_exhausted(&self) -> bool {
        self.remaining_text().is_empty() && self.is_exhausted
    }

    /// Discards [number_of_bytes] bytes from the remaining line.
    /// If [number_of_bytes] would cause the remaining bytes to be invalid UTF8,
    /// this method will panic.
    /// If [number_of_bytes] is greater than the number of bytes remaining in the current line,
    /// this method will panic.
    pub fn consume(&mut self, number_of_bytes: usize) {
        let remaining_line = self.remaining_text();
        assert!(
            number_of_bytes <= remaining_line.len(),
            "Cannot consume() more bytes than are left in the current line."
        );
        assert!(
            remaining_line.is_char_boundary(number_of_bytes),
            "Cannot consume() a number of bytes that will leave invalid UTF8 in the current line."
        );
        self.line_offset += number_of_bytes;
    }

    /// Reads the next line of text from input, appending it to the end of the buffer.
    /// If the input is exhausted (i.e. is at EOF), returns Ok(0).
    pub fn load_next_line(&mut self) -> io::Result<usize> {
        self.load_next_n_lines(1)
    }

    /// Reads the next [number_of_lines] lines of text from input, appending each one to the end of
    /// the buffer. If fewer than [number_of_lines] remains in the input, the buffer will load as
    /// many as possible. If the input is exhausted (i.e. is at EOF), returns Ok(0).
    pub fn load_next_n_lines(&mut self, number_of_lines: usize) -> io::Result<usize> {
        self.restack_remaining_text();
        let mut total_bytes_read = 0;
        for _ in 0..number_of_lines {
            let bytes_read = self.input.read_line(&mut self.line)?;
            if bytes_read == 0 {
                self.is_exhausted = true;
                return Ok(total_bytes_read);
            }
            // The last line of `self.input` can have bytes that don't end in '\n'
            if self.line.ends_with('\n') {
                self.line_number += 1;
            }
            total_bytes_read += bytes_read;
        }
        Ok(total_bytes_read)
    }

    /// Provides direct access to the [TextBuffer]'s backing [String]. This can be used to edit the
    /// input text before it is processed. Note that lines added or removed when using this method
    /// will not be reflected in subsequent calls to [lines_loaded].
    pub fn inner(&mut self) -> &mut String {
        &mut self.line
    }

    /// Removes the part of the current line that has already been consumed and moves any remaining
    /// text back to the beginning of the buffer.
    fn restack_remaining_text(&mut self) {
        if self.line_offset == 0 {
            // Nothing to do.
            return;
        }
        let remaining_bytes = self.remaining_text().len();
        unsafe {
            // The `as_bytes_mut()` method below is unsafe.
            // https://doc.rust-lang.org/std/primitive.str.html#method.as_bytes_mut
            // A [str] is a byte array that is guaranteed to contain valid utf-8. Getting a mutable
            // reference to the contents of the array means that a user could modify it in such a
            // way that it was no longer valid utf-8. In this case, the invariants enforced by the
            // `consume` method guarantee that this will behave safely.
            // Copy the remaining text from the end of the String to the beginning of the String.
            self.line.as_bytes_mut().copy_within(self.line_offset.., 0);
            // Now that the remaining bytes are back at the beginning of the buffer, there's
            // some garbage where the old data used to be. When we go to truncate the line to its
            // new, shorter length, `truncate` will check to make sure that the buffer's contents
            // are still valid utf8. It does this by looking at the next byte after the end to see
            // if it's the beginning of a character. Since our buffer has garbage data, it's possible
            // that test will fail and it will cause a panic. To prevent this, we simply set the
            // next byte after truncated end of the buffer to zero.
            self.line.as_bytes_mut()[remaining_bytes] = 0;
            // Truncate the String to drop any data.
            self.line.truncate(remaining_bytes)
        }
        self.line_offset = 0;
    }
}

#[cfg(test)]
pub(crate) mod text_buffer_tests {
    use super::*;
    use std::{io, str};

    fn text_buffer(text: &str) -> TextBuffer<io::Cursor<&str>> {
        let input = io::Cursor::new(text);
        TextBuffer::new(input)
    }

    #[test]
    fn test_restack() {
        // This test accesses TextBuffer internals, which isn't typical for a unit tests.
        // However, the restack() function uses `unsafe` code and so warrants additional scrutiny.
        let mut buffer = text_buffer("foo\nbar\nbaz\nquux\n");
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        assert_eq!(buffer.remaining_text(), "foo\n");
        assert_eq!(buffer.line_offset, 0);
        buffer.consume(2);
        assert_eq!(buffer.remaining_text(), "o\n");
        assert_eq!(buffer.line_offset, 2);
        buffer.restack_remaining_text();
        assert_eq!(buffer.line_offset, 0);
        assert_eq!(buffer.remaining_text(), "o\n");
    }

    #[test]
    fn test_empty_restack() {
        // This test accesses TextBuffer internals, which isn't typical for a unit tests.
        // However, the restack() function uses `unsafe` code and so warrants additional scrutiny.
        let mut buffer = text_buffer("foo\nbar\nbaz\nquux\n");
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        assert_eq!(buffer.remaining_text(), "foo\n");
        assert_eq!(buffer.line_offset, 0);
        buffer.consume(4);
        assert_eq!(buffer.remaining_text(), "");
        assert_eq!(buffer.line_offset, 4);
        buffer.restack_remaining_text();
        assert_eq!(buffer.line_offset, 0);
        assert_eq!(buffer.remaining_text(), "");
    }

    #[test]
    fn test_consume() {
        let mut buffer = text_buffer("foo bar baz quux");
        buffer.load_next_line().unwrap();
        assert_eq!(buffer.remaining_text(), "foo bar baz quux");
        buffer.consume(4);
        assert_eq!(buffer.remaining_text(), "bar baz quux");
        buffer.consume(5);
        assert_eq!(buffer.remaining_text(), "az quux");
        buffer.consume(6);
        assert_eq!(buffer.remaining_text(), "x");
    }

    #[test]
    #[should_panic]
    fn test_consume_err_illegal_utf8_offset() {
        let mut buffer = text_buffer("😎");
        buffer.load_next_line().unwrap();
        // This jumps into the middle of the emoji.
        // If it were to succeed, the next call to remaining_text() would panic.
        buffer.consume(1);
    }

    #[test]
    #[should_panic]
    fn test_consume_err_too_many_bytes() {
        let mut buffer = text_buffer("foo");
        buffer.load_next_line().unwrap();
        // There are only 3 bytes in the buffer.
        // We cannot consume more bytes than are available.
        buffer.consume(75);
    }

    #[test]
    fn test_load_next_line() {
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
    fn test_load_next_n_lines() {
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
    fn test_is_exhausted() {
        let mut buffer = text_buffer("foo\nbar\n");
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        assert_eq!(buffer.remaining_text(), "foo\n");
        buffer.consume(4);
        // The buffer itself is empty, but input has not reached EOF yet.
        assert_eq!(buffer.is_exhausted(), false);
        // Load another line
        assert_eq!(buffer.load_next_line().unwrap(), 4);
        // Now input is at EOF, but the buffer contains text.
        assert_eq!(buffer.is_exhausted(), false);
        // Consume the bytes in the buffer
        buffer.consume(4);
        // Now the buffer is empty. Looking ahead, we can tell that the input is empty,
        // but we have to try to load another line to actually encounter EOF.
        assert_eq!(buffer.is_exhausted(), false);
        assert_eq!(buffer.load_next_line().unwrap(), 0);
        // Now the buffer is empty and the input has hit EOF.
        assert_eq!(buffer.is_exhausted(), true);
    }

    #[test]
    fn invalid_utf8_returns_err() {
        // Invalid UTF-8 data
        let data = &[0xf1, 0xf2, 0xc2, 0x80];
        let mut buffer = TextBuffer::new(io::Cursor::new(data));
        assert!(buffer.load_next_line().is_err());
    }
}
