//! This module defines `IonParseError`, a custom error type, and `IonParseResult`, a type alias for an
//! [`PResult`] that parses `TextBuffer`s and produces `IonParseError`s if something goes wrong.

use crate::lazy::text::buffer::TextBuffer;
use crate::position::Position;
use crate::result::{DecodingError, IncompleteError};
use crate::{IonError, IonResult};
use std::borrow::Cow;
use std::fmt::Debug;
use winnow::error::{AddContext, ErrMode, ErrorKind, Needed, ParserError};
use winnow::stream::Stream;
use winnow::PResult;

/// A type alias for a [`PResult`] whose input is a [`TextBuffer`] and whose error type is an
/// `IonParseError`. All of the Ion parsers in the `TextBuffer` type return `IonParseResult`.
///
/// If the parser is successful, it will return `Ok(output_value)`. If it encounters a problem,
/// it will return a `winnow::error::ErrMode<IonParseError>`.
///
/// [`ErrMode`] is a generic enum with three possible variants:
/// 1. `Incomplete(_)` indicates that there wasn't enough input data to determine whether the
///    parser should match or not.
/// 2. `Backtrack(ion_parse_error)` indicates that the parser did not match the input text; the reader should try another.
/// 3. `Cut(ion_parse_error)` indicates that the parser matched the text but encountered
///    a problem when trying to materialize it into the `output_value`. In such cases, returning a
///    `Cut` signals that this was the correct parser to handle the input but it could not
///    be processed successfully for some reason. For example, a parser trying to match a number of
///    hours and minutes might match the text `11:71`, but fail when it tries to turn `71` into a
///    number of minutes because it's `>=60`. We know this was the right parser, but it wasn't
///    able to process it. (This is slightly contrived; it would be possible to write a parser
///    that rejected `71` as a number of minutes based on syntax alone.)
pub(crate) type IonParseResult<'a, O> = PResult<O, IonParseError<'a>>;

/// As above, but for parsers that simply identify (i.e. 'match') a slice of the input as a
/// particular item.
pub(crate) type IonMatchResult<'a> = IonParseResult<'a, TextBuffer<'a>>;

/// Returned to explain why the current parser could not successfully read the provided input.
/// The included `IonParseErrorKind` gives more granular detail, and indicates whether the reader
/// should continue trying other parsers if any alternatives remain.
#[derive(Debug, Clone)]
pub struct IonParseError<'data> {
    /// The input that could not be parsed successfully.
    input: TextBuffer<'data>,
    /// A human-friendly name for what the parser was working on when the error occurred
    context: &'static str,
    /// An explanation of what went wrong.
    kind: IonParseErrorKind,
}

impl<'data> IonParseError<'data> {
    /// Allows the context (a label for the task that was in progress) to be set on a manually
    /// constructed error. Mirrors winnow's [`Parser::context`](winnow::Parser::context) method.
    pub(crate) fn context(mut self, context: &'static str) -> Self {
        self.context = context;
        self
    }

    /// Converts this `IonParseError` into an `ErrMode::Cut<IonParseError>`.
    pub(crate) fn cut_err(self) -> ErrMode<Self> {
        ErrMode::Cut(self)
    }

    /// Converts this `IonParseError` into an `IonParseResult` containing an `Err(ErrMode::Cut<IonParseError>)`.
    pub(crate) fn cut<T>(self) -> IonParseResult<'data, T> {
        Err(ErrMode::Cut(self))
    }

    pub(crate) fn backtrack_err(self) -> ErrMode<Self> {
        ErrMode::Backtrack(self)
    }

    pub(crate) fn backtrack<T>(self) -> IonParseResult<'data, T> {
        Err(ErrMode::Backtrack(self))
    }
}

/// This should be overwritten by all parsers. If a parser does not overwrite it, this
/// will produce a coherent (albeit vague) error message.
const DEFAULT_CONTEXT: &str = "reading Ion data";

/// Adds error constructor methods to the `TextBuffer` type.
impl<'data> TextBuffer<'data> {
    #[inline(never)]
    pub(crate) fn incomplete_err_mode(
        &self,
        context: &'static str,
    ) -> ErrMode<IonParseError<'data>> {
        if self.is_final_data() {
            self.invalid("stream is incomplete; ran out of data")
                .context(context)
                .cut_err()
        } else {
            ErrMode::Incomplete(Needed::Unknown)
        }
    }

    pub fn incomplete<T>(&self, context: &'static str) -> IonParseResult<'data, T> {
        Err(self.incomplete_err_mode(context))
    }

    pub fn unrecognized(&self) -> IonParseError<'data> {
        IonParseError {
            input: *self,
            context: DEFAULT_CONTEXT,
            kind: IonParseErrorKind::Unrecognized(UnrecognizedInputError::new()),
        }
    }

    pub fn invalid(&self, description: impl Into<Cow<'static, str>>) -> IonParseError<'data> {
        IonParseError {
            input: *self,
            context: DEFAULT_CONTEXT,
            kind: IonParseErrorKind::Invalid(InvalidInputError::new(description)),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IonParseErrorKind {
    /// The parser ran out of input in the middle of an expression.
    Incomplete,
    /// The parser did not recognize the head of the provided input. It may be recognized by another
    /// parser if there are more to try.
    Unrecognized(UnrecognizedInputError),
    /// The parser detected that it was the correct parser to handle the provided input,
    /// but the input was malformed in some way. For example, if the list parser were reading this
    /// stream:
    /// ```ion
    ///     ["foo" "bar"]
    /// ```
    /// it would know from the leading `[` that this is a list and the list parser is therefore the
    /// correct parser to handle it. However, there was a comma missing after `"foo"`. The list
    /// parser can say definitively that the input not valid Ion data.
    Invalid(InvalidInputError),
}

#[derive(Clone, Debug, PartialEq)]
pub struct UnrecognizedInputError {
    /// The winnow-provided parser kind that rejected the input.
    winnow_error_kind: Option<ErrorKind>,
}

impl UnrecognizedInputError {
    fn new() -> Self {
        Self {
            winnow_error_kind: None,
        }
    }

    fn with_winnow_error_kind(winnow_error_kind: ErrorKind) -> Self {
        Self {
            winnow_error_kind: Some(winnow_error_kind),
        }
    }
}

/// Describes a problem that occurred while trying to parse a given input `TextBuffer`.
///
/// When returned as part of an `IonParseResult`, an `IonParseError` is always wrapped in
/// an [`ErrMode`] (see `IonParseResult`'s documentation for details). If the `ErrMode` is
/// a non-fatal `Error`, the `IonParseError`'s `description` will be `None`. If the `winnow::ErrMode` is
/// a fatal `Failure`, the `description` will be `Some(String)`. In this way, using an
/// `IonParseError` only incurs heap allocation costs when parsing is coming to an end.
#[derive(Debug, PartialEq, Clone)]
pub struct InvalidInputError {
    // A human-friendly description of the error.
    description: Cow<'static, str>,
}

impl InvalidInputError {
    /// Constructs a new `IonParseError` from the provided `input` text.
    pub(crate) fn new(description: impl Into<Cow<'static, str>>) -> Self {
        InvalidInputError {
            description: description.into(),
        }
    }
}

impl<'data> AddContext<TextBuffer<'data>> for IonParseError<'data> {
    fn add_context(
        mut self,
        _input: &TextBuffer<'data>,
        _token_start: &<TextBuffer<'data> as Stream>::Checkpoint,
        context: &'static str,
    ) -> Self {
        self.context = context;
        self
    }
}

// We cannot provide an analogous impl for `Incomplete` because it is missing necessary data.
impl From<IonParseError<'_>> for IonError {
    fn from(ion_parse_error: IonParseError<'_>) -> Self {
        use IonParseErrorKind::*;
        let mut message: String = match ion_parse_error.kind {
            Incomplete => {
                return IonError::Incomplete(IncompleteError::new(
                    ion_parse_error.context,
                    ion_parse_error.input.offset(),
                ));
            }
            Invalid(e) => e.description.into(),
            Unrecognized(..) => "found unrecognized syntax".into(),
        };

        message.push_str("\n    while ");
        message.push_str(ion_parse_error.context.as_ref());
        use std::fmt::Write;
        let input = ion_parse_error.input;

        // Make displayable strings showing the contents of the first 32 characters
        // of the buffer. If the buffer is smaller than 32 bytes, fewer characters will be shown
        // and a leading or trailing '...' will be displayed as appropriate.
        const NUM_CHARS_TO_SHOW: usize = 32;
        let buffer_head = match input.as_text() {
            // The buffer contains UTF-8 bytes, so we'll display it as text
            Ok(text) => {
                let mut head_chars = text.chars();
                let mut head = (&mut head_chars)
                    .take(NUM_CHARS_TO_SHOW)
                    .collect::<String>()
                    // XXX: Newlines wreck the formatting, so escape them in output.
                    //      We may wish to do this for other whitespace too.
                    .replace("\n", "\\n");
                if head_chars.next().is_some() {
                    head.push_str("...");
                }

                head
            }
            // The buffer contains non-text bytes, so we'll show its contents as formatted hex
            // pairs instead.
            Err(_) => {
                let head = format!(
                    "{:X?}",
                    &input.bytes()[..NUM_CHARS_TO_SHOW.min(input.len())]
                );
                head
            }
        };
        // The offset and buffer head will often be helpful to the programmer. The buffer tail
        // and buffer length will be helpful to library maintainers receiving copy/pasted
        // error messages to debug.
        write!(
            message,
            r#"
        offset={}
        input={}
        buffer len={}
        "#,
            input.offset(),
            buffer_head,
            input.len(),
        )
        .unwrap();
        let position = Position::with_offset(input.offset()).with_length(input.len());
        let decoding_error = DecodingError::new(message).with_position(position);
        IonError::Decoding(decoding_error)
    }
}

/// Allows `IonParseError` to be used as the error type in various `winnow` parsers.
impl<'data> ParserError<TextBuffer<'data>> for IonParseError<'data> {
    fn from_error_kind(input: &TextBuffer<'data>, error_kind: ErrorKind) -> Self {
        IonParseError {
            input: *input,
            context: DEFAULT_CONTEXT,
            kind: IonParseErrorKind::Unrecognized(UnrecognizedInputError::with_winnow_error_kind(
                error_kind,
            )),
        }
    }

    fn append(
        self,
        _input: &TextBuffer<'data>,
        _checkpoint: &<TextBuffer<'data> as Stream>::Checkpoint,
        _kind: ErrorKind,
    ) -> Self {
        // When an error stack is being built, this method is called to give the error
        // type an opportunity to aggregate the errors into a collection or a more descriptive
        // message. We don't currently use this feature as it can be expensive in the common case.
        // We may find a use for adding it behind a debugging-oriented feature gate.
        self
    }
}

/// Converts the output of a text Ion parser (any of `IonParseResult`, `IonParseError`,
/// or `winnow::ErrMode<IonParseError>`) into a general-purpose `IonResult`.
// This is necessary because `winnow`'s `ErrMode::Incomplete` variant doesn't store an IonParseError
// like its other variants, so the input and context aren't available. This method adds them back
// in as a kludge. Winnow v0.7.0 should address this; see:
// <https://github.com/winnow-rs/winnow/discussions/693>
pub(crate) trait WithContext<'data, T> {
    fn with_context(self, label: &'static str, input: TextBuffer<'data>) -> IonResult<T>;
}

impl<'data, T> WithContext<'data, T> for ErrMode<IonParseError<'data>> {
    fn with_context(self, label: &'static str, input: TextBuffer<'data>) -> IonResult<T> {
        use ErrMode::*;
        let ion_parse_error = match self {
            // We only apply the label and input in the `Incomplete` case. Other cases already have
            // these fields populated, potentially by more precise information.
            Incomplete(_) => IonParseError {
                input,
                context: label,
                kind: IonParseErrorKind::Incomplete,
            },
            Backtrack(e) | Cut(e) => e,
        };

        let ion_error = IonError::from(ion_parse_error);
        Err(ion_error)
    }
}

// Turns an IonParseError into an IonResult
impl<'data, T> WithContext<'data, T> for IonParseError<'data> {
    fn with_context(mut self, label: &'static str, input: TextBuffer<'data>) -> IonResult<T> {
        if self.kind == IonParseErrorKind::Incomplete {
            self.input = input;
            self.context = label;
        }
        Err(IonError::from(self))
    }
}

impl<'data, T> WithContext<'data, T> for IonParseResult<'data, T> {
    fn with_context(self, label: &'static str, input: TextBuffer<'data>) -> IonResult<T> {
        match self {
            // No change needed in the ok case
            Ok(matched) => Ok(matched),
            Err(e) => e.with_context(label, input),
        }
    }
}
