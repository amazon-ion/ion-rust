//! This module defines `IonParseError`, a custom error type, and `IonParseResult`, a type alias for an
//! [`PResult`] that parses `TextBuffer`s and produces `IonParseError`s if something goes wrong.

use crate::lazy::text::buffer::TextBuffer;
use crate::position::Position;
use crate::result::{DecodingError, IonFailure};
use crate::{IonError, IonResult};
use std::borrow::Cow;
use std::fmt::{Debug, Display};
use winnow::error::{ErrMode, ErrorKind, ParseError, ParserError};
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

#[derive(Debug, PartialEq)]
pub enum IonParseError<'data> {
    // When nom reports that the data was incomplete, it doesn't provide additional context.
    Incomplete,
    // When we encounter illegal text Ion, we'll have more information to share with the user.
    Invalid(InvalidInputError<'data>),
}

/// Describes a problem that occurred while trying to parse a given input `TextBuffer`.
///
/// When returned as part of an `IonParseResult`, an `IonParseError` is always wrapped in
/// an [`ErrMode`] (see `IonParseResult`'s documentation for details). If the `ErrMode` is
/// a non-fatal `Error`, the `IonParseError`'s `description` will be `None`. If the `winnow::ErrMode` is
/// a fatal `Failure`, the `description` will be `Some(String)`. In this way, using an
/// `IonParseError` only incurs heap allocation costs when parsing is coming to an end.
#[derive(Debug, PartialEq)]
pub struct InvalidInputError<'data> {
    // The input that being parsed when the error arose
    input: TextBuffer<'data>,
    // A human-friendly name for what the parser was working on when the error occurred
    label: Option<Cow<'static, str>>,
    // The nature of the error--what went wrong?
    description: Option<Cow<'static, str>>,
    // The nom ErrorKind, which indicates which nom-provided parser encountered the error we're
    // bubbling up.
    nom_error_kind: Option<ErrorKind>,
}

impl<'data> InvalidInputError<'data> {
    /// Constructs a new `IonParseError` from the provided `input` text.
    pub(crate) fn new(input: TextBuffer<'data>) -> Self {
        InvalidInputError {
            input,
            label: None,
            description: None,
            nom_error_kind: None,
        }
    }

    /// Constructs a new `IonParseError` from the provided `input` text and `description`.
    pub(crate) fn with_label<D: Into<Cow<'static, str>>>(mut self, label: D) -> Self {
        self.label = Some(label.into());
        self
    }

    /// Constructs a new `IonParseError` from the provided `input` text and `description`.
    pub(crate) fn with_description<D: Into<Cow<'static, str>>>(mut self, description: D) -> Self {
        self.description = Some(description.into());
        self
    }

    /// Constructs a new `IonParseError` from the provided `input` text and `description`.
    pub(crate) fn with_nom_error_kind(mut self, nom_error_kind: ErrorKind) -> Self {
        self.nom_error_kind = Some(nom_error_kind);
        self
    }

    /// Returns a reference to the `description` text, if any.
    pub fn description(&self) -> Option<&str> {
        self.description.as_deref()
    }

    pub fn label(&self) -> Option<&str> {
        self.label.as_deref()
    }

    // TODO: Decide how to expose 'input'.
}

impl<'data> From<InvalidInputError<'data>> for IonParseError<'data> {
    fn from(value: InvalidInputError<'data>) -> Self {
        IonParseError::Invalid(value)
    }
}

// We cannot provide an analogous impl for `Incomplete` because it is missing necessary data.
impl From<InvalidInputError<'_>> for IonError {
    fn from(invalid_input_error: InvalidInputError<'_>) -> Self {
        let mut message = String::from(
            invalid_input_error
                .description()
                .unwrap_or("invalid Ion syntax encountered"),
        );
        if let Some(label) = invalid_input_error.label {
            message.push_str("\n    while ");
            message.push_str(label.as_ref());
        }
        use std::fmt::Write;
        let input = invalid_input_error.input;

        // Make displayable strings showing the contents of the first and last 32 characters
        // of the buffer. If the buffer is smaller than 32 bytes, fewer characters will be shown.
        const NUM_CHARS_TO_SHOW: usize = 32;
        let (buffer_head, buffer_tail) = match input.as_text() {
            // The buffer contains UTF-8 bytes, so we'll display it as text
            Ok(text) => {
                let mut head_chars = text.chars();
                let mut head = (&mut head_chars)
                    .take(NUM_CHARS_TO_SHOW)
                    .collect::<String>();
                if head_chars.next().is_some() {
                    head.push_str("...");
                }
                let mut tail_chars = text.chars().rev();
                let tail_backwards = (&mut tail_chars)
                    .take(NUM_CHARS_TO_SHOW)
                    .collect::<Vec<char>>();
                let mut tail = String::new();
                if tail_chars.next().is_some() {
                    tail.push_str("...");
                }
                tail.push_str(tail_backwards.iter().rev().collect::<String>().as_str());

                (head, tail)
            }
            // The buffer contains non-text bytes, so we'll show its contents as formatted hex
            // pairs instead.
            Err(_) => {
                let head = format!(
                    "{:X?}",
                    &invalid_input_error.input.bytes()[..NUM_CHARS_TO_SHOW.min(input.len())]
                );
                let tail_bytes_to_take = input.bytes().len().min(NUM_CHARS_TO_SHOW);
                let buffer_tail = &input.bytes()[input.len() - tail_bytes_to_take..];
                let tail = format!("{:X?}", buffer_tail);
                (head, tail)
            }
        };
        // The offset and buffer head will often be helpful to the programmer. The buffer tail
        // and buffer length will be helpful to library maintainers receiving copy/pasted
        // error messages to debug.
        write!(
            message,
            r#"
        offset={}
        buffer head=<{}>
        buffer tail=<{}>
        buffer len={}
        "#,
            invalid_input_error.input.offset(),
            buffer_head,
            buffer_tail,
            input.len(),
        )
        .unwrap();
        let position = Position::with_offset(invalid_input_error.input.offset())
            .with_length(invalid_input_error.input.len());
        let decoding_error = DecodingError::new(message).with_position(position);
        IonError::Decoding(decoding_error)
    }
}

impl<'data> From<ErrMode<IonParseError<'data>>> for IonParseError<'data> {
    fn from(value: ErrMode<IonParseError<'data>>) -> Self {
        use winnow::error::ErrMode::*;
        match value {
            Incomplete(_) => IonParseError::Incomplete,
            Backtrack(e) => e,
            Cut(e) => e,
        }
    }
}

/// Allows an `IonParseError` to be constructed from a `(&str, ErrorKind)` tuple, which is the
/// data provided by core `nom` parsers if they do not match the input.
impl<'data> From<(TextBuffer<'data>, ErrorKind)> for IonParseError<'data> {
    fn from((input, error_kind): (TextBuffer<'data>, ErrorKind)) -> Self {
        InvalidInputError::new(input)
            .with_nom_error_kind(error_kind)
            .into()
    }
}

/// Allows an [`ErrMode`] to be converted into an [IonParseError] by calling `.into()`.
impl<'data> From<ParseError<TextBuffer<'data>, IonParseError<'data>>> for IonParseError<'data> {
    fn from(parse_error: ParseError<TextBuffer<'data>, IonParseError<'data>>) -> Self {
        parse_error.into_inner()
    }
}

/// Allows `IonParseError` to be used as the error type in various `nom` functions.
impl<'data> ParserError<TextBuffer<'data>> for IonParseError<'data> {
    fn from_error_kind(input: &TextBuffer<'data>, error_kind: ErrorKind) -> Self {
        InvalidInputError::new(*input)
            .with_nom_error_kind(error_kind)
            .into()
    }

    fn append(
        self,
        input: &TextBuffer<'data>,
        _checkpoint: &<TextBuffer<'data> as Stream>::Checkpoint,
        _kind: ErrorKind,
    ) -> Self {
        // When an error stack is being built, this method is called to give the error
        // type an opportunity to aggregate the errors into a collection or a more descriptive
        // message. For now, we simply allow the most recent error to take precedence.
        IonParseError::Invalid(InvalidInputError::new(*input))
    }
}

/// `Result<Option<T>, _>` has a method called `transpose` that converts it into an `Option<Result<T, _>>`,
/// allowing it to be easily used in places like iterators that expect that return type.
/// This trait defines a similar extension method for `Result<(TextBuffer, Option<T>)>`.
pub(crate) trait ToIteratorOutput<'data, T> {
    fn transpose(self) -> Option<IonResult<T>>;
}

impl<'data, T> ToIteratorOutput<'data, T> for IonResult<(TextBuffer<'data>, Option<T>)> {
    fn transpose(self) -> Option<IonResult<T>> {
        match self {
            Ok((_remaining, Some(value))) => Some(Ok(value)),
            Ok((_remaining, None)) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

/// Converts the output of a text Ion parser (any of `IonParseResult`, `IonParseError`,
/// or `winnow::Err<IonParseError>`) into a general-purpose `IonResult`. If the implementing type
/// does not have its own `label` and `input`, the specified values will be used.
pub(crate) trait AddContext<'data, T> {
    fn with_context<'a>(
        self,
        label: impl Into<Cow<'static, str>>,
        input: TextBuffer<'data>,
    ) -> IonResult<T>
    where
        'data: 'a;
}

impl<'data, T> AddContext<'data, T> for ErrMode<IonParseError<'data>> {
    fn with_context<'a>(
        self,
        label: impl Into<Cow<'static, str>>,
        input: TextBuffer<'data>,
    ) -> IonResult<T>
    where
        'data: 'a,
    {
        let ipe = IonParseError::from(self);
        ipe.with_context(label, input)
    }
}

// Turns an IonParseError into an IonResult
impl<'data, T> AddContext<'data, T> for IonParseError<'data> {
    fn with_context<'a>(
        self,
        label: impl Into<Cow<'static, str>>,
        input: TextBuffer<'data>,
    ) -> IonResult<T>
    where
        'data: 'a,
    {
        match self {
            IonParseError::Incomplete => IonResult::incomplete(
                format!(
                    "{}; buffer utf-8: {}",
                    label.into(),
                    input.as_text().unwrap_or("<invalid utf-8>")
                ),
                input.offset(),
            ),
            IonParseError::Invalid(invalid_input_error) => Err(IonError::from(invalid_input_error)),
        }
    }
}

impl<'data, T> AddContext<'data, T> for IonParseResult<'data, T> {
    fn with_context<'a>(
        self,
        label: impl Into<Cow<'static, str>>,
        input: TextBuffer<'data>,
    ) -> IonResult<T>
    where
        'data: 'a,
    {
        match self {
            // No change needed in the ok case
            Ok(matched) => Ok(matched),
            Err(e) => e.with_context(label, input),
        }
    }
}

/// Constructs a `winnow::error::ErrMode::Cut` that contains an `IonParseError` describing the problem
/// that was encountered.
pub(crate) fn fatal_parse_error<D: Into<Cow<'static, str>>, O>(
    input: TextBuffer<'_>,
    description: D,
) -> IonParseResult<'_, O> {
    Err(ErrMode::Cut(
        InvalidInputError::new(input)
            .with_description(description)
            .into(),
    ))
}

/// An extension trait that allows a [Result] of any kind to be mapped to an
/// `IonParseResult` concisely.
pub(crate) trait OrFatalParseError<T> {
    fn or_fatal_parse_error<L: Display>(
        self,
        input: TextBuffer<'_>,
        label: L,
    ) -> IonParseResult<'_, T>;
}

/// See the documentation for [OrFatalParseError].
impl<T, E> OrFatalParseError<T> for Result<T, E>
where
    E: Debug,
{
    fn or_fatal_parse_error<L: Display>(
        self,
        input: TextBuffer<'_>,
        label: L,
    ) -> IonParseResult<'_, T> {
        match self {
            Ok(value) => Ok(value),
            Err(error) => fatal_parse_error(input, format!("{label}: {error:?}")),
        }
    }
}
