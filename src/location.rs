/// Represents the source location (row, column) of this element in the original Ion text.
///
/// The source location metadata is primarily intended for error reporting and debugging purposes,
/// helping applications provide meaningful feedback to users about the source of issues.
///
/// # Returns
/// * `Some((row, column))` - Position where this element was found in the source text
/// * `None` - Location information is not available
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SourceLocation {
    location: Option<(usize, usize)>,
}

impl SourceLocation {
    pub fn new(row: usize, column: usize) -> SourceLocation {
        Self {
            location: Some((row, column)),
        }
    }

    pub fn empty() -> SourceLocation {
        Self { location: None }
    }

    pub fn is_empty(&self) -> bool {
        self.location.is_none()
    }

    pub fn location(&self) -> Option<(usize, usize)> {
        self.location
    }

    pub fn row(&self) -> usize {
        self.location.unwrap_or((0, 0)).0
    }

    pub fn column(&self) -> usize {
        self.location.unwrap_or((0, 0)).1
    }
}
