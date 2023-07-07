use std::fmt::{Display, Error};

/// Position represents the location within an Ion stream where an error has been
/// identified. For all formats `byte_offset` will contain the number of bytes into the stream
/// that have been processed prior to encountering the error. When working with the text format,
/// `line_column` will be updated to contain the line and column as well.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Position {
    pub(crate) byte_offset: usize,
    pub(crate) line_column: Option<(usize, usize)>,
}

impl Position {
    /// Creates a new Position with the provided offset in bytes.
    /// Line and Column offsets can be added using [`Self::with_line_and_column()`].
    pub fn with_offset(offset: usize) -> Self {
        Position {
            byte_offset: offset,
            line_column: None,
        }
    }

    /// Add line and column information to the current Position.
    pub fn with_line_and_column(&self, line: usize, column: usize) -> Self {
        Position {
            line_column: Some((line, column)),
            ..*self
        }
    }

    /// Returns the offset from the start of the Ion stream in bytes.
    pub fn byte_offset(&self) -> usize {
        self.byte_offset
    }

    /// If available returns the text position as line and column offsets.
    pub fn line_and_column(&self) -> Option<(usize, usize)> {
        self.line_column
    }

    /// If available returns the line component of the text position.
    pub fn line(&self) -> Option<usize> {
        self.line_column.map(|(line, _column)| line)
    }

    /// If available returns the column component of the text position.
    pub fn column(&self) -> Option<usize> {
        self.line_column.map(|(_line, column)| column)
    }

    /// Returns true if the current Position contains line and column offsets.
    pub fn has_line_and_column(&self) -> bool {
        self.line_column.is_some()
    }
}

impl Display for Position {
    // Formats the position based on whether we have a LineAndColumn or not.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), Error> {
        match &self.line_column {
            None => write!(f, "{}", self.byte_offset),
            Some((line, column)) => {
                write!(f, "{} ({}:{})", self.byte_offset, line, column)
            }
        }
    }
}

impl From<usize> for Position {
    fn from(offset: usize) -> Self {
        Position::with_offset(offset)
    }
}
