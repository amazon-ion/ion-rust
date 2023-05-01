//! The [`nom` parser combinator crate](https://docs.rs/nom/latest/nom/) intentionally provides
//! bare-bones error reporting by default. Each error contains only a `&str` representing the input
//! that could not be matched and an [`ErrorKind`] enum variant indicating which `nom` parser produced
//! the error. This stack-allocated type is very cheap to create, which is important because a
//! typical parse will require creating large numbers of short-lived error values.
//!
//! This module defines [`IonParseError`], a custom error type that can capture more information than is
//! supported by [`nom::error::Error`], as well as traits and functions for upgrading an `Error` into
//! an [`IonParseError`]. The module also defines [`IonParseResult`], a type alias for a [`IResult`]
//! that parses `&str`s and produces [`IonParseError`]s if something goes wrong.
//!
//! Two new extension traits are also provided to facilitate combining core `nom` parsers that
//! return an `IResult` (for example: `one_of`, `opt`, or `alt`) with higher-level parsers that
//! return an `IonParseResult` (for example: `parse_timestamp` or `parse_decimal`).
//!
//! 1. [`UpgradeIResult`] adds an `.upgrade()` method to every `IResult` that cheaply converts it into
//! an `IonParseResult`.
//! 2. [`UpgradeParser`] adds an `.upgrade()` method to every implementation of [`Parser`] that
//! causes it to return an `IonParseResult` instead of an `IResult`.

use nom::error::{Error as NomError, ErrorKind, ParseError};
use nom::{Err, IResult, Parser};
use std::fmt::Debug;

/// A type alias for a [`IResult`] whose input is a `&str` and whose error type is an
/// [`IonParseError`]. All of the Ion parsers in the `text::parsers` module return an
/// [`IonParseResult`].
///
/// If the parser is successful, it will return `Ok(output_value)`. If it encounters a problem,
/// it will return a `nom::Err<IonParseError>`. [nom::Err] is a generic enum with three possible
/// variants:
/// 1. `Incomplete(_)` indicates that there wasn't enough input data to determine whether the
///    parser should match or not.
/// 2. `Error(ion_parse_error)` indicates that the parser did not match the input text.
/// 3. `Failure(ion_parse_error)` indicates that the parser matched the text but encountered
///    a problem when trying to materialize it into the `output_value`. In such cases, returning a
///    `Failure` signals that this was the correct parser to handle the input but it could not
///    be processed successfully for some reason. For example, a parser trying to match a number of
///    hours and minutes might match the text `11:71`, but fail when it tries to turn `71` into a
///    number of minutes because it's `>=60`. We know this was the right parser, but it wasn't
///    able to process it. (This is slightly contrived; it would be possible to write a parser
///    that rejected `71` as a number of minutes based on syntax alone.)
pub(crate) type IonParseResult<'a, O> = IResult<&'a str, O, IonParseError<'a>>;
// Functions that return IonParseResult parse text  -^   ^     ^
//                    ...return a value of type `O` -----+     |
// ...or a nom::Err<IonParseError> if something goes wrong ----+

/// An extension trait that allows an [IResult] to be converted to an [IonParseResult].
///
/// If you write a parser by combining core `nom` parsers, the new parser will return [IResult].
/// If you'd like your parser to return an [IonParseResult] instead to improve its interoperability
/// with other parsers that return `IonParseResult`, you can call `upgrade()` on your parser's
/// output before returning it.
///
/// ```ignore // Doc tests cannot use internal APIs
/// use nom::bytes::streaming::tag;
/// use nom::sequence::terminated;
/// use nom::Parser; // trait provides the method `or`
/// use self::UpgradeIResult;
///
/// // Matches a prefix at the head of `input` that looks like an Ion boolean value followed
/// // by a space.
/// fn recognize_boolean(input: &str) -> IonParseResult<&str> {
///     // This syntax is idiomatic, but a bit tough for the uninitiated to interpret.
///     // A more verbose/explicit version of the same function is provided below.
///     terminated(tag("true").or(tag("false")), tag(" "))(input).upgrade()
/// }
///
/// use nom::IResult;
///
/// // The same function as above, but spelled out a bit more explicitly
/// fn verbose_recognize_boolean(input: &str) -> IonParseResult<&str> {
///     // Combine several core `nom` parsers to make a new parser with the desired logic
///     let parser = terminated(          // <-- Takes two parsers; if both succeed, returns the output of the first
///         tag("true").or(tag("false")), // <-- Parser 1 matches the text `true` or the text `false`
///         tag(" ")                      // <-- Parser 2 matches a single space
///     );
///
///     // Use our new parser to parse the provided text
///     let i_result: IResult<&str, &str, nom::error::Error<&str>> = parser(input);
///
///     // Upgrade the IResult our parser produced to make an IonParseResult
///     let ion_parse_result: IonParseResult<&str> = i_result.upgrade();
///
///     // Return the IonParseResult
///     ion_parse_result
/// }
/// ```
/// This is defined as an extension trait (rather than a [std::convert::From] implementation)
/// because both `IResult` and `IonParseResult` are just type aliases for different configurations
/// of [std::result::Result]. In order to implement `From`, your crate must own the concrete
/// type for which it is being implemented.
pub(crate) trait UpgradeIResult<'a, O> {
    /// Consumes the [IResult] and returns an [IonParseResult]. This is guaranteed not to require
    /// heap allocations.
    fn upgrade(self) -> IonParseResult<'a, O>;
}

/// This implementation makes it possible to call `.upgrade()` on an IResult, converting it into an
/// IonParseResult.
impl<'a, O> UpgradeIResult<'a, O> for IResult<&'a str, O> {
    fn upgrade(self) -> IonParseResult<'a, O> {
        match self {
            Ok(matched) => Ok(matched),
            Err(Err::Incomplete(e)) => Err(Err::Incomplete(e)),
            // Convert the `nom::Error` into an `IonParseError` using its `From` implementation.
            Err(Err::Error(e)) => Err(Err::Error(e.into())),
            Err(Err::Failure(e)) => Err(Err::Failure(e.into())),
        }
    }
}

/// Describes a problem that occurred while trying to parse a given input `&str`.
///
/// When returned as part of an [IonParseResult], an `IonParseError` is always wrapped in
/// a [nom::Err] (see [IonParseResult]'s documentation for details). If the `nom::Err` is
/// a non-fatal `Error`, the `IonParseError`'s `description` will be `None`. If the `nom::Err` is
/// a fatal `Failure`, the `description` will be `Some(String)`. In this way, using an
/// `IonParseError` only incurs heap allocation costs when parsing is coming to an end.
#[derive(Debug, PartialEq)]
pub(crate) struct IonParseError<'a> {
    input: &'a str,
    description: Option<String>,
}

impl<'a> IonParseError<'a> {
    /// Constructs a new `IonParseError` from the provided `input` text.
    pub fn new(input: &'a str) -> Self {
        IonParseError {
            input,
            description: None,
        }
    }

    /// Constructs a new `IonParseError` from the provided `input` text and `description`.
    pub fn with_description<D: Into<String>>(input: &'a str, description: D) -> Self {
        IonParseError {
            input,
            description: Some(description.into()),
        }
    }

    /// Returns a reference to the `description` text, if any.
    pub fn description(&self) -> Option<&str> {
        self.description.as_deref()
    }

    /// Consumes the `IonParseError` and returns a new one with a lifetime tied to the provided
    /// `input`.
    ///
    /// This is useful in situations where the input text had to be sanitized before parsing could
    /// be attempted. An IonParseError tied to the (locally constructed) sanitized text
    /// cannot be returned. In such cases, the IonParseError can be replaced by one that is tied
    /// to the original input text and which retains the original description.
    pub fn replace_input(self, input: &str) -> IonParseError {
        IonParseError {
            input,
            description: self.description,
        }
    }
}

/// Allows an `IonParseError` to be constructed from a `(&str, ErrorKind)` tuple, which is the
/// data provided by core `nom` parsers if they do not match the input.
impl<'a> From<(&'a str, ErrorKind)> for IonParseError<'a> {
    fn from((input, _error_kind): (&'a str, ErrorKind)) -> Self {
        IonParseError::new(input)
    }
}

/// Allows a [nom::error::Error] to be converted into an [IonParseError] by calling `.into()`.
impl<'a> From<nom::error::Error<&'a str>> for IonParseError<'a> {
    fn from(nom_error: NomError<&'a str>) -> Self {
        IonParseError::new(nom_error.input)
    }
}

/// Allows `IonParseError` to be used as the error type in various `nom` functions.
impl<'a> ParseError<&'a str> for IonParseError<'a> {
    fn from_error_kind(input: &'a str, _error_kind: ErrorKind) -> Self {
        IonParseError::new(input)
    }

    fn append(_input: &'a str, _kind: ErrorKind, other: Self) -> Self {
        // When an error stack is being built, this method is called to give the error
        // type an opportunity to aggregate the errors into a collection or a more descriptive
        // message. For now, we simply allow the most recent error to take precedence.
        other
    }
}

/// Constructs a `nom::Err::Failure` that contains an `IonParseError` describing the problem
/// that was encountered.
pub(crate) fn fatal_parse_error<D: Into<String>, O>(
    input: &str,
    description: D,
) -> IonParseResult<O> {
    Err(nom::Err::Failure(IonParseError::with_description(
        input,
        description,
    )))
}

/// An extension trait that allows a [std::result::Result] of any kind to be mapped to an
/// `IonParseResult` concisely.
pub(crate) trait OrFatalParseError<T> {
    fn or_fatal_parse_error<'a>(self, input: &'a str, label: &str) -> IonParseResult<'a, T>;
}

/// See the documentation for [OrFatalParseError].
impl<T, E> OrFatalParseError<T> for Result<T, E>
where
    E: Debug,
{
    fn or_fatal_parse_error<'a>(self, input: &'a str, label: &str) -> IonParseResult<'a, T> {
        match self {
            Ok(value) => Ok(("", value)),
            Err(error) => fatal_parse_error(input, format!("{label}: {error:?}")),
        }
    }
}

/// An extension trait that allows any parser that returns a [nom::IResult] to be converted into
/// a parser that returns an [IonParseResult] instead.
///
/// ```ignore // Doc tests cannot use internal APIs
/// use nom::bytes::streaming::tag;
/// use nom::sequence::tuple;
/// use nom::Parser; // trait provides the method `or`
/// use self::UpgradeIResult;
///
/// // Parser that matches a list start, an Ion value, and a list end
/// fn parse_list_with_one_value(input: &str) -> IonParseResult<TextValue> {
///     // Broken example:
///     //
///     //     tuple(               // <-- Expects all parameter parsers to use the same Error type
///     //         tag("["),        // <-- returns `IResult`
///     //         top_level_value, // <-- returns `IonParseResult`
///     //         tag("]")         // <-- returns `IResult`
///     //      )(input)            // <- ERROR!
///     //
///     // You can't mix `IResult` parsers like `tag("[")` and `tag("]")` with
///     // `IonParseResult` parsers like `top_level_value` inside of many nom
///     // parsers like `tuple`. Solution:
///
///     tuple(
///         tag("[").upgrade(), // <-- now this returns `IonParseResult`
///         top_level_value,    // <-- returns `IonParseResult`
///         tag("]").upgrade()  // <-- now this returns `IonParseResult
///     )(input)                // <- OK!
/// }
/// ```
/// This conversion is essentially free; `upgrade()` produces a stack-allocated [`UpgradedParser`]
/// whose only field is the wrapped parser; this means that its size and layout are identical
/// to the original parser. The only cost is the trivial expense of converting the parser's
/// output from an `IResult` to an [`IonParseResult`].
pub(crate) trait UpgradeParser<O> {
    fn upgrade(self) -> UpgradedParser<Self>;
}

/// Wraps a parser that returns an [IResult], causing it to return an [IonParseResult] instead.
pub(crate) struct UpgradedParser<P: ?Sized> {
    base_parser: P,
}

/// Allows any type that implements `nom`'s [nom::Parser] trait to call [UpgradeParser::upgrade].
impl<'a, P, O> UpgradeParser<O> for P
where
    P: Parser<&'a str, O, NomError<&'a str>>,
{
    fn upgrade(self) -> UpgradedParser<Self> {
        UpgradedParser { base_parser: self }
    }
}

/// Implements `nom`'s `[nom::Parser] trait for [UpgradedParser], allowing instances of that type
/// to be passed to `nom` functions.
impl<'a, P, O> Parser<&'a str, O, IonParseError<'a>> for UpgradedParser<P>
where
    P: Parser<&'a str, O, NomError<&'a str>>,
{
    fn parse(&mut self, input: &'a str) -> IonParseResult<'a, O> {
        let result = self.base_parser.parse(input);
        UpgradeIResult::upgrade(result)
    }
}
