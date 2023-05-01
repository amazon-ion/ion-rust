use std::fmt::Display;

use crate::element::{Blob, Clob};
use crate::types::Str;
use nom::Err::{Error, Failure, Incomplete};

use crate::raw_reader::{BufferedRawReader, RawStreamItem};
use crate::raw_symbol_token::RawSymbolToken;
use crate::result::{
    decoding_error, illegal_operation, illegal_operation_raw, incomplete_text_error, IonError,
    IonResult, Position,
};
use crate::stream_reader::IonReader;
use crate::text::non_blocking::text_buffer::TextBuffer;
use crate::text::parent_container::ParentContainer;
use crate::text::parse_result::IonParseResult;
use crate::text::parsers::containers::{
    list_delimiter, list_value_or_end, s_expression_delimiter, s_expression_value_or_end,
    struct_delimiter, struct_field_name_or_end, struct_field_value,
};
use crate::text::parsers::top_level::{stream_item, RawTextStreamItem};
use crate::text::text_value::{AnnotatedTextValue, TextValue};
use crate::types::{Decimal, Int, Timestamp};
use crate::IonType;

const INITIAL_PARENTS_CAPACITY: usize = 16;

// Represents the current actions being carried out by the reader.
#[derive(PartialEq, Debug)]
enum ReaderState {
    // Ready to read any value, no existing errors, no partial parses.
    Ready,
    // A previous `step_out` call failed to complete, but may have progressed through some values.
    // We need to continue the step_out before doing anything else.
    SteppingOut {
        // The depth the reader is attempting to step-out to.
        target_depth: usize,
        // Whether the step_out process is searching for the parent container's delimiter. If true,
        // then when continuing, the function will jump to searching for the delimiter. Otherwise it
        // will continue exhausting the elements within the container.
        finding_parent: bool,
    },
}

impl ReaderState {
    // Returns true if the current ReaderState is Ready.
    fn is_ready(&self) -> bool {
        *self == Self::Ready
    }

    fn reset(&mut self) {
        *self = Self::Ready;
    }
}

pub struct RawTextReader<A: AsRef<[u8]> + Expandable> {
    buffer: TextBuffer<A>,
    // If the reader is not positioned over a value inside a struct, this is None.
    current_field_name: Option<RawSymbolToken>,
    // If the reader has not yet begun reading at the current level or is positioned over an IVM,
    // this is None.
    current_value: Option<AnnotatedTextValue>,
    // If the reader is positioned over an IVM instead of a value, this is:
    //     Some(major_version, minor_version)
    // Otherwise, it is None.
    current_ivm: Option<(u8, u8)>,
    // True if the current text buffer is exhausted.
    is_eof: bool,
    // True if the caller has indicated that all data has been read for the 'stream'.
    is_eos: bool,
    parents: Vec<ParentContainer>,
    // Current state of the reader. This state, combined with `need_continue` will signal if an
    // action needs to be completed (need_continue = true) or if we are attempting for the first
    // time (need_continue = false).
    state: ReaderState,
    // The "call depth" of the current nested step_out.
    step_out_nest: usize,
    // Tracking whether or not we need to continue a previously failed state.
    need_continue: bool,
}

/// Represents the final outcome of a [RawTextReader]'s attempt to parse the next value in the stream.
///
/// `IonParseResult<'a>` is not suitable for this purpose; its lifetime, `'a`, causes
/// the result to hold a reference to the [RawTextReader]'s buffer even after parsing has finished,
/// making it difficult to perform the necessary bookkeeping that follows finding the next value.
///
/// This type is intentionally limited in what it stores to avoid having a lifetime.
#[derive(Eq, PartialEq, Debug)]
pub(crate) enum RootParseResult<O> {
    Ok(O),
    Eof,
    NoMatch,
    Incomplete(usize, usize),
    Failure(String),
}

impl From<Vec<u8>> for RawTextReader<Vec<u8>> {
    fn from(source: Vec<u8>) -> Self {
        RawTextReader::new(source)
    }
}

/// Provides a mechanism for identifying input types that allow adding more data.
/// This allows for some input-type oriented behaviors, like initializing the end of stream status
/// to true if we know more data can not be added.
pub trait Expandable {
    fn expandable(&self) -> bool;
}

impl<T: AsRef<[u8]> + ?Sized> Expandable for &T {
    fn expandable(&self) -> bool {
        false
    }
}

impl Expandable for Vec<u8> {
    fn expandable(&self) -> bool {
        true
    }
}

impl<A: AsRef<[u8]> + Expandable> RawTextReader<A> {
    pub fn new(input: A) -> RawTextReader<A> {
        let expandable = input.expandable();
        RawTextReader {
            buffer: TextBuffer::new(input),
            current_field_name: None,
            current_value: None,
            current_ivm: None,
            is_eof: false,
            is_eos: !expandable,
            parents: Vec::with_capacity(INITIAL_PARENTS_CAPACITY),
            state: ReaderState::Ready,
            step_out_nest: 0,
            need_continue: false,
        }
    }

    fn load_next_value(&mut self) -> IonResult<()> {
        // If the reader's current value is the beginning of a container and the user calls `next()`,
        // we need to skip the entire container. We can do this by stepping into and then out of
        // that container; `step_out()` has logic that will exhaust the remaining values.
        let need_to_skip_container = !self.is_null()
            && self
                .current_value
                .as_ref()
                .map(|v| v.value().ion_type().is_container())
                .unwrap_or(false);

        if need_to_skip_container {
            self.step_in()?;
            self.step_out()?;
        }

        // Unset variables holding onto information about the previous position.
        self.current_ivm = None;
        self.current_value = None;
        self.current_field_name = None;

        if self.parents.is_empty() {
            // The `parents` stack is empty. We're at the top level.

            // If the reader has already found EOF (the end of the top level), there's no need to
            // try to read more data. Return Ok(None).
            if self.is_eof {
                self.current_value = None;
                return Ok(());
            }

            let next_stream_item = self.parse_next_nom(stream_item);
            return self.process_stream_item(next_stream_item);
        }

        // Otherwise, the `parents` stack is not empty. We're inside a container.

        // The `ParentLevel` type is only a couple of stack-allocated bytes. It's very cheap to clone.
        let parent = *self.parents.last().unwrap();
        // If the reader had already found the end of this container, return Ok(None).
        if parent.is_exhausted() {
            self.current_value = None;
            return Ok(());
        }
        // Otherwise, try to read the next value. The syntax we expect will depend on the
        // IonType of the parent container.
        let value = match parent.ion_type() {
            IonType::List => self.next_list_value(),
            IonType::SExp => self.next_s_expression_value(),
            IonType::Struct => {
                self.buffer.checkpoint();
                if let Some(field_name) = self.next_struct_field_name()? {
                    // ...remember it and return the field value that follows.
                    self.current_field_name = Some(field_name);
                    let field_value_result = match self.next_struct_field_value() {
                        Err(e) => {
                            self.current_field_name = None;
                            self.buffer.rollback();
                            return Err(e);
                        }
                        Ok(v) => v,
                    };
                    Ok(Some(field_value_result))
                } else {
                    Ok(None)
                }
            }
            other => unreachable!(
                "The reader's `parents` stack contained a scalar value: {:?}",
                other
            ),
        };

        match value {
            Ok(None) => {
                // If the parser returns Ok(None), we've just encountered the end of the container for
                // the first time. Set `is_exhausted` so we won't try to parse more until `step_out()` is
                // called.
                // We previously used a copy of the last `ParentLevel` in the stack to simplify reading.
                // To modify it, we'll need to get a mutable reference to the original.
                self.parents.last_mut().unwrap().set_exhausted(true);
                self.current_value = None;
            }
            Ok(Some(value)) => {
                // We successfully read a value. Set it as the current value.
                self.current_value = Some(value);
            }
            Err(e) => return Err(e),
        };

        Ok(())
    }

    // This function implements the logic of `step_out`, but is extracted in order to make tracking
    // of the step_out depth, which is handled by the actual `step_out` function, easier.
    //
    // See `step_out` for more info about how we handle errors when stepping out.
    fn step_out_impl(&mut self) -> IonResult<()> {
        let (target_depth, find_parent) = match self.state {
            ReaderState::Ready => (self.depth() - 1, false),
            ReaderState::SteppingOut {
                target_depth,
                finding_parent,
            } => (target_depth, finding_parent),
        };

        // `find_parent` indicates that we previously failed to step_out and still need to find the
        // delimiter, or end, for our parent container. We check it here, to see if we need to
        // still exhaust the elements of our current container.
        if !find_parent {
            if self.parents.is_empty() {
                return illegal_operation(
                    "Cannot call `step_out()` when the reader is at the top level.",
                );
            }

            // The container we're stepping out of.
            let parent = self.parents.last().unwrap();

            // If we're not at the end of the current container, advance the cursor until we are.
            // Unlike the binary reader, which can skip-scan, the text reader must visit every value
            // between its current position and the end of the container.
            if !parent.is_exhausted() {
                while let RawStreamItem::Value(_) | RawStreamItem::Null(_) = self.next()? {}
            }

            // Remove the parent container from the stack and clear the current value.
            let _ = self.parents.pop();
            self.current_value = None;

            if self.parents.is_empty() {
                // We're at the top level; nothing left to do.
                return Ok(());
            }
            // We have reached a point where the original parent is no longer known, so if an error
            // occurs while finishing up our step_out, we need to know where to start from.
            self.state = ReaderState::SteppingOut {
                target_depth,
                finding_parent: true,
            };
        }

        // We've stepped out, but the reader isn't at the top level. We're still inside another
        // container. Make sure the container was followed by either the appropriate delimiter
        // or the end of its parent.
        let container_type = self.parents.last().unwrap().ion_type();
        match container_type {
            IonType::List => {
                self.parse_expected("list delimiter or end", list_delimiter)?;
            }
            IonType::SExp => {
                self.parse_expected("s-expression delimiter or end", s_expression_delimiter)?;
            }
            IonType::Struct => {
                self.parse_expected("struct delimiter or end", struct_delimiter)?;
            }
            scalar => unreachable!("stepping out of a scalar type: {:?}", scalar),
        };

        self.state = ReaderState::SteppingOut {
            target_depth,
            finding_parent: false,
        };

        Ok(())
    }

    /// Continues any previously incomplete parsing attempt.
    fn continue_state(&mut self) -> IonResult<()> {
        if self.need_continue && self.step_out_nest == 0 {
            self.need_continue = false;

            match self.state {
                // Previously Attempted to step_out, and failed.
                ReaderState::SteppingOut { .. } => self.step_out(),
                ReaderState::Ready => Ok(()),
            }
        } else {
            Ok(())
        }
    }

    fn process_stream_item(
        &mut self,
        read_result: RootParseResult<RawTextStreamItem>,
    ) -> IonResult<()> {
        match read_result {
            RootParseResult::Ok(RawTextStreamItem::IonVersionMarker(1, 0)) => {
                // We found an IVM; we currently only support Ion 1.0.
                self.current_ivm = Some((1, 0));
                Ok(())
            }
            RootParseResult::Ok(RawTextStreamItem::IonVersionMarker(major, minor)) => {
                decoding_error(format!(
                    "Unsupported Ion version: v{major}.{minor}. Only 1.0 is supported."
                ))
            }
            RootParseResult::Ok(RawTextStreamItem::AnnotatedTextValue(value)) => {
                // We read a value successfully; set it as our current value.
                self.current_value = Some(value);
                Ok(())
            }
            RootParseResult::Incomplete(line, column) => incomplete_text_error(
                "text",
                Position::with_offset(self.buffer.bytes_consumed())
                    .with_text_position(line, column),
            ),
            RootParseResult::Eof => {
                // We are only concerned with EOF behaviors when we are at the end of the stream,
                // AND at the end of the buffer.
                if self.is_eos {
                    // The top level is the only depth at which EOF is legal. If we encounter an EOF,
                    // double check that the buffer doesn't actually have a value in it. See the
                    // comments in [parse_value_at_eof] for a detailed explanation of this.
                    let item = self.parse_value_at_eof();
                    if item == RootParseResult::Eof {
                        // This is a genuine EOF; make a note of it and clear the current value.
                        self.is_eof = true;
                        self.current_value = None;
                        return Ok(());
                    }
                    self.process_stream_item(item)
                } else {
                    // If we are not at the end of the stream, we need to get more data.
                    incomplete_text_error("text", self.buffer.get_position())
                }
            }
            RootParseResult::NoMatch => {
                // The parser didn't recognize the text in the input buffer.
                // Return an error that contains the text we were attempting to parse.
                let error_message = format!(
                    "unrecognized input near line {}: '{}'",
                    self.buffer.lines_loaded(),
                    self.buffer.remaining_text(),
                );
                decoding_error(error_message)
            }
            RootParseResult::Failure(error_message) => {
                // A fatal error occurred while reading the next value.
                // This could be an I/O error, malformed utf-8 data, or an invalid value.
                decoding_error(error_message)
            }
        }
    }

    /// Assumes that the reader is inside a list and attempts to parse the next value.
    /// If the next token in the stream is an end-of-list delimiter (`]`), returns Ok(None).
    fn next_list_value(&mut self) -> IonResult<Option<AnnotatedTextValue>> {
        self.parse_expected("a list", list_value_or_end)
    }

    /// Assumes that the reader is inside an s-expression and attempts to parse the next value.
    /// If the next token in the stream is an end-of-s-expression delimiter (`)`), returns Ok(None).
    fn next_s_expression_value(&mut self) -> IonResult<Option<AnnotatedTextValue>> {
        self.parse_expected("an s-expression", s_expression_value_or_end)
    }

    /// Assumes that the reader is inside an struct and attempts to parse the next field name.
    /// If the next token in the stream is an end-of-struct delimiter (`}`), returns Ok(None).
    fn next_struct_field_name(&mut self) -> IonResult<Option<RawSymbolToken>> {
        // If there isn't another value, this returns Ok(None).
        self.parse_expected("a struct field name", struct_field_name_or_end)
    }

    /// Assumes that the reader is inside a struct AND that a field has already been successfully
    /// parsed from input using [`next_struct_field_name`](Self::next_struct_field_name) and
    /// attempts to parse the next value.
    /// In this input position, only a value (or whitespace/comments) are legal. Anything else
    /// (including EOF) will result in a decoding error.
    fn next_struct_field_value(&mut self) -> IonResult<AnnotatedTextValue> {
        // Only called after a call to [next_struct_field_name] that returns Some(field_name).
        // It is not legal for a field name to be followed by a '}' or EOF.
        // If there isn't another value, returns an Err.
        self.parse_expected("a struct field value", struct_field_value)
    }

    /// Attempts to parse the next entity from the stream using the provided parser.
    /// Returns a decoding error if EOF is encountered while parsing.
    /// If the parser encounters an error, it will be returned as-is.
    fn parse_expected<P, O>(&mut self, entity_name: &str, parser: P) -> IonResult<O>
    where
        P: Fn(&str) -> IonParseResult<O>,
    {
        match self.parse_next(parser) {
            Ok(Some(value)) => Ok(value),
            Ok(None) => {
                if !self.is_eos {
                    incomplete_text_error("text", self.buffer.get_position())
                } else {
                    decoding_error(format!(
                        "unexpected end of input while reading {} on line {}: '{}'",
                        entity_name,
                        self.buffer.lines_loaded(),
                        self.buffer.remaining_text()
                    ))
                }
            }
            Err(err @ IonError::Incomplete { .. }) => Err(err),
            Err(e) => decoding_error(format!(
                "Parsing error occurred while parsing {} near line {}:\n'{}'\n{}",
                entity_name,
                self.buffer.lines_loaded(),
                self.buffer.remaining_text(),
                e
            )),
        }
    }

    fn parse_next<P, O>(&mut self, parser: P) -> IonResult<Option<O>>
    where
        P: Fn(&str) -> IonParseResult<O>,
    {
        match self.parse_next_nom(parser) {
            RootParseResult::Ok(item) => Ok(Some(item)),
            RootParseResult::Incomplete(line, column) => incomplete_text_error(
                "text",
                Position::with_offset(self.buffer.bytes_consumed())
                    .with_text_position(line, column),
            ),
            RootParseResult::Eof => Ok(None),
            RootParseResult::NoMatch => {
                // If we are not at the end of the stream we could be missing a match due to partial
                // data.
                if self.is_eos {
                    // Return an error that contains the text currently in the buffer (i.e. what we
                    // were attempting to parse.)
                    let error_message = format!(
                        "unrecognized input near line {}: '{}'",
                        self.buffer.lines_loaded(),
                        self.buffer.remaining_text(),
                    );
                    decoding_error(error_message)
                } else {
                    incomplete_text_error("text", self.buffer.get_position())
                }
            }
            RootParseResult::Failure(error_message) => decoding_error(error_message),
        }
    }

    /// Attempts to parse the next entity from the stream using the provided parser.
    /// If there isn't enough data in the buffer for the parser to match its input conclusively,
    /// more data will be loaded into the buffer and the parser will be called again.
    /// If EOF is encountered, returns `Ok(None)`.
    fn parse_next_nom<P, O>(&mut self, parser: P) -> RootParseResult<O>
    where
        P: Fn(&str) -> IonParseResult<O>,
    {
        use super::text_buffer::TextError;

        let RawTextReader {
            ref mut is_eof,
            ref mut buffer,
            ..
        } = *self;

        if *is_eof {
            return RootParseResult::Eof;
        }

        loop {
            // Note the number of bytes currently in the text buffer
            let length_before_parse = buffer.remaining_text().len();
            // Invoke the top_level_value() parser; this will attempt to recognize the next value
            // in the stream and return a &str slice containing the remaining, not-yet-parsed text.
            match parser(buffer.remaining_text()) {
                // If `top_level_value` returns 'Incomplete', there wasn't enough text in the buffer
                // to match the next value. No syntax errors have been encountered (yet?), but we
                // need to load more text into the buffer before we try to parse it again.
                Err(Incomplete(_needed)) => {
                    // Ask the buffer to load another line of text.
                    // TODO: Currently this loads a single line at a time for easier testing.
                    //       We may wish to bump it to a higher number of lines at a time (8?)
                    //       for efficiency once we're confident in the correctness.
                    match buffer.load_next_line() {
                        Ok(0) => {
                            // If load_next_line() returns Ok(0), we've reached the end of our input.
                            *is_eof = true;
                            // The buffer had an `Incomplete` value in it; now that we know we're at EOF,
                            // we can determine whether the buffer's contents should actually be
                            // considered complete.
                            return RootParseResult::Eof;
                        }
                        Ok(_bytes_loaded) => {
                            // Retry the parser on the extended buffer in the next loop iteration
                            continue;
                        }
                        Err(TextError::Incomplete { line, column }) => {
                            // If load_next_line() returns TextError::Incomplete, then that means
                            // it has incomplete UTF-8 data in the buffer, suggesting the user is
                            // not done providing the ion data.
                            return RootParseResult::Incomplete(line, column);
                        }
                        Err(e) => {
                            let error_message = format!("I/O error, could not read more data: {e}");
                            return RootParseResult::Failure(error_message);
                        }
                    }
                }
                Ok((remaining_text, value)) => {
                    // Our parser successfully matched a value.
                    // Note the length of the text that remains after parsing.
                    let length_after_parse = remaining_text.len();
                    // The difference in length tells us how many bytes were part of the
                    // text representation of the value that we found.
                    let bytes_consumed = length_before_parse - length_after_parse;
                    buffer.consume(bytes_consumed);
                    return RootParseResult::Ok(value);
                }
                Err(Error(_e)) => return RootParseResult::<O>::NoMatch,
                Err(Failure(e)) => {
                    let error_message = format!(
                        "unrecognized input near line {}: {}: '{}'",
                        buffer.lines_loaded(),
                        e.description().unwrap_or("<no description>"),
                        buffer.remaining_text(),
                    );
                    return RootParseResult::Failure(error_message);
                }
            };
        }
    }

    // Parses the contents of the text buffer again with the knowledge that we're at the end of the
    // input stream. This allows us to resolve a number of ambiguous cases.
    // For a detailed description of the problem that this addresses, please see:
    // https://github.com/amazon-ion/ion-rust/issues/318
    // This method should only be called when the reader is at the top level. An EOF at any other
    // depth is an error.
    fn parse_value_at_eof(&mut self) -> RootParseResult<RawTextStreamItem> {
        // An arbitrary, cheap-to-parse Ion value that we append to the buffer when its contents at
        // EOF are ambiguous.
        const SENTINEL_ION_TEXT: &str = "\n0\n";
        // We unfortunately need to copy here in order to append the SENTINEL_ION_TEXT, since we
        // aren't guaranteed a vector-backed reader.
        let mut remaining_text = self.buffer.remaining_text().to_owned();
        // Make a note of the text's length; we're about to modify it.
        let original_length = remaining_text.len();

        // Append our sentinel value to the end of the input buffer.
        remaining_text.push_str(SENTINEL_ION_TEXT);

        // If the buffer contained a value, the newline will indicate that the contents of the
        // buffer were complete. For example:
        // * the integer `7` becomes `7\n`; it wasn't the first digit in a truncated `755`.
        // * the boolean `false` becomes `false\n`; it wasn't actually half of the
        //   identifier `falseTeeth`.
        //
        // If the buffer contained a value that's written in segments, the extra `0` will indicate
        // that no more segments are coming. For example:
        // * `foo::bar` becomes `foo::bar\n0\n`; the parser can see that 'bar' is a value, not
        //    another annotation in the sequence.
        // * `'''long-form string'''` becomes `'''long-form string'''\n0\n`; the parser can see that
        //   there aren't any more long-form string segments in the sequence.
        //
        // Attempt to parse the updated buffer.
        let value = match stream_item(&remaining_text) {
            Ok(("\n", RawTextStreamItem::AnnotatedTextValue(value)))
                if value.annotations().is_empty()
                    && *value.value() == TextValue::Int(Int::I64(0)) =>
            {
                // We found the unannotated zero that we appended to the end of the buffer.
                // The "\n" in this pattern is the unparsed text left in the buffer,
                // which indicates that our 0 was parsed.
                RootParseResult::Eof
            }
            Ok((_remaining_text, value)) => {
                // If we match, and try to consume the remaining buffer in its entirety before we
                // know the data has been fully loaded we need to treat it as an incomplete error
                // so that we do not inadvertently succeed on a partial parse.
                if original_length == self.buffer.remaining_text().len() && !self.is_eos {
                    return RootParseResult::Incomplete(
                        self.buffer.lines_loaded(),
                        self.buffer.line_offset(),
                    );
                }
                // We found something else. The zero is still in the buffer; we can leave it there.
                // The reader's `is_eof` flag has been set, so the text buffer will never be used
                // again. Return the value we found.
                RootParseResult::Ok(value)
            }
            Err(Incomplete(_needed)) => {
                RootParseResult::Incomplete(self.buffer.lines_loaded(), self.buffer.line_offset())
            }
            Err(Error(ion_parse_error)) => {
                RootParseResult::Failure(format!(
                    "Parsing error occurred near line {}: '{}': '{:?}'",
                    self.buffer.lines_loaded(),
                    &self.buffer.remaining_text()[..original_length], /* Don't show the extra `\n0\n` */
                    ion_parse_error
                ))
            }
            Err(Failure(ion_parse_error)) => {
                RootParseResult::Failure(format!(
                    "A fatal error occurred while reading near line {}: '{}': '{:?}'",
                    self.buffer.lines_loaded(),
                    &self.buffer.remaining_text()[..original_length], /* Don't show the extra `\n0\n` */
                    ion_parse_error
                ))
            }
        };

        value
    }

    /// Constructs an [IonError::IllegalOperation] which explains that the reader was asked to
    /// perform an action that is only allowed when it is positioned over the item type described
    /// by the parameter `expected`.
    fn expected<E: Display>(&self, expected: E) -> IonError {
        illegal_operation_raw(format!(
            "type mismatch: expected a(n) {} but positioned over a(n) {}",
            expected,
            self.current()
        ))
    }
}

impl BufferedRawReader for RawTextReader<Vec<u8>> {
    fn append_bytes(&mut self, bytes: &[u8]) -> IonResult<()> {
        match self.buffer.append_bytes(bytes) {
            Err(e) => decoding_error(e.to_string()),
            Ok(()) => {
                self.is_eof = false;
                Ok(())
            }
        }
    }

    fn read_from<R: std::io::Read>(&mut self, source: R, length: usize) -> IonResult<usize> {
        let res = self.buffer.read_from(source, length);
        if res.is_ok() {
            self.is_eof = false;
        }
        res
    }

    // Mark the data stream as being complete. This tells the reader that all data has been read
    // into the reader.
    fn stream_complete(&mut self) {
        self.is_eos = true;
    }

    // Returns true if the stream has been marked as completely loaded via `stream_complete`.
    fn is_stream_complete(&self) -> bool {
        self.is_eos
    }
}

// Returned by the `annotations()` method below if there is no current value.
const EMPTY_SLICE_RAW_SYMBOL_TOKEN: &[RawSymbolToken] = &[];

// TODO: This implementation of the text reader eagerly materializes each value that it encounters
//       in the stream and stores it in the reader as `current_value`. Each time a user requests
//       a value via `read_i64`, `read_bool`, etc, a clone of `current_value` is returned (assuming
//       its type is in alignment with the request).
//       A better implementation would identify the input slice containing the next value without
//       materializing it and then attempt to materialize it when the user calls `read_TYPE`. This
//       would take less memory and would only materialize values that the user requests.
//       See: https://github.com/amazon-ion/ion-rust/issues/322
impl<A: AsRef<[u8]> + Expandable> IonReader for RawTextReader<A> {
    type Item = RawStreamItem;
    type Symbol = RawSymbolToken;

    fn ion_version(&self) -> (u8, u8) {
        (1, 0)
    }

    fn next(&mut self) -> IonResult<RawStreamItem> {
        // Failures due to incomplete data can occur any time the reader needs to advance, which
        // can occur in a call to `next()` or `step_out()`. (Note that in some cases the
        // implementations of `next()` and `step_out()` may invoke each other transitively.)
        self.continue_state()?;

        // Parse the next value from the stream, storing it in `self.current_value`.
        self.load_next_value()?;

        // If we're positioned on an IVM, return the (major, minor) version tuple
        if let Some((major, minor)) = self.current_ivm {
            return Ok(RawStreamItem::VersionMarker(major, minor));
        }

        // If we're positioned on a value, return its IonType and whether it's null.
        if let Some(value) = self.current_value.as_ref() {
            Ok(RawStreamItem::nullable_value(
                value.ion_type(),
                value.is_null(),
            ))
        } else {
            Ok(RawStreamItem::Nothing)
        }
    }

    fn current(&self) -> RawStreamItem {
        if let Some(ref value) = self.current_value {
            RawStreamItem::nullable_value(value.ion_type(), value.is_null())
        } else if let Some(ivm) = self.current_ivm {
            RawStreamItem::VersionMarker(ivm.0, ivm.1)
        } else {
            RawStreamItem::Nothing
        }
    }

    fn ion_type(&self) -> Option<IonType> {
        if let Some(ref value) = self.current_value {
            return Some(value.ion_type());
        }
        None
    }

    fn is_null(&self) -> bool {
        if let Some(ref value) = self.current_value {
            return value.is_null();
        }
        false
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'a> {
        let iterator = self
            .current_value
            .as_ref()
            .map(|value| value.annotations())
            .unwrap_or(EMPTY_SLICE_RAW_SYMBOL_TOKEN)
            .iter()
            .cloned()
            // The annotations are already in memory and are already resolved to text, so
            // this step cannot fail. Map each token to Ok(token).
            .map(Ok);
        Box::new(iterator)
    }

    fn has_annotations(&self) -> bool {
        self.current_value
            .as_ref()
            .map(|value| !value.annotations().is_empty())
            .unwrap_or(false)
    }

    fn number_of_annotations(&self) -> usize {
        self.current_value
            .as_ref()
            .map(|value| value.annotations().len())
            .unwrap_or(0)
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        match self.current_field_name.as_ref() {
            Some(name) => Ok(name.clone()),
            None => illegal_operation(
                "field_name() can only be called when the reader is positioned inside a struct",
            ),
        }
    }

    fn read_null(&mut self) -> IonResult<IonType> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Null(ion_type)) => Ok(*ion_type),
            _ => Err(self.expected("null value")),
        }
    }

    fn read_bool(&mut self) -> IonResult<bool> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Bool(value)) => Ok(*value),
            _ => Err(self.expected("bool value")),
        }
    }

    fn read_int(&mut self) -> IonResult<Int> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Int(value)) => Ok(value.clone()),
            _ => Err(self.expected("int value")),
        }
    }

    fn read_i64(&mut self) -> IonResult<i64> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Int(Int::I64(value))) => Ok(*value),
            Some(TextValue::Int(Int::BigInt(value))) => {
                decoding_error(format!("Integer {value} is too large to fit in an i64."))
            }
            _ => Err(self.expected("int value")),
        }
    }

    fn read_f32(&mut self) -> IonResult<f32> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Float(value)) => Ok(*value as f32),
            _ => Err(self.expected("float value")),
        }
    }

    fn read_f64(&mut self) -> IonResult<f64> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Float(value)) => Ok(*value),
            _ => Err(self.expected("float value")),
        }
    }

    fn read_decimal(&mut self) -> IonResult<Decimal> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Decimal(ref value)) => Ok(value.clone()),
            _ => Err(self.expected("decimal value")),
        }
    }

    fn read_string(&mut self) -> IonResult<Str> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::String(ref value)) => Ok(Str::from(value.as_str())),
            _ => Err(self.expected("string value")),
        }
    }

    fn read_str(&mut self) -> IonResult<&str> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::String(ref value)) => Ok(value.as_str()),
            _ => Err(self.expected("string value")),
        }
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Symbol(ref value)) => Ok(value.clone()),
            _ => Err(self.expected("symbol value")),
        }
    }

    fn read_blob(&mut self) -> IonResult<Blob> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Blob(ref value)) => Ok(Blob::from(value.as_slice())),
            _ => Err(self.expected("blob value")),
        }
    }

    fn read_clob(&mut self) -> IonResult<Clob> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Clob(ref value)) => Ok(Clob::from(value.as_slice())),
            _ => Err(self.expected("clob value")),
        }
    }

    fn read_timestamp(&mut self) -> IonResult<Timestamp> {
        match self.current_value.as_ref().map(|current| current.value()) {
            Some(TextValue::Timestamp(ref value)) => Ok(value.clone()),
            _ => Err(self.expected("timestamp value")),
        }
    }

    fn step_in(&mut self) -> IonResult<()> {
        match &self.current_value {
            Some(value) if value.ion_type().is_container() => {
                self.parents
                    .push(ParentContainer::new(value.value().ion_type()));
                self.current_value = None;
                Ok(())
            }
            Some(value) => {
                illegal_operation(format!("Cannot step_in() to a {:?}", value.ion_type()))
            }
            None => illegal_operation(format!(
                "{} {}",
                "Cannot `step_in`: the reader is not positioned on a value.",
                "Try calling `next()` to advance first."
            )),
        }
    }

    fn step_out(&mut self) -> IonResult<()> {
        let (target_depth, find_parent) = match self.state {
            ReaderState::Ready => (self.depth().saturating_sub(1), false),
            ReaderState::SteppingOut {
                target_depth,
                finding_parent,
            } => (target_depth, finding_parent),
        };
        self.state = ReaderState::SteppingOut {
            target_depth,
            finding_parent: find_parent,
        };

        // If an incomplete error occurs during a step_out, we will re-enter step_out and:
        //    Using the state information from the previous attempt, we will either continue
        //    exhausting the container, or continue looking for the parent container's delimiter,
        //    or end.
        //
        //    Once the failed step_out is done, we need to "bubble up" and step_out of any of
        //    the parent containers that the failed step_out was nested in. Since we have lost
        //    the call stack that we would normally lean on, we keep track of the depth we want
        //    to step out to and the nesting of step_out calls. We handle all step_outs like
        //    normal, until we have completed the exhaustion and delimiter steps for the
        //    container. Then, if the current step_out call is nested, we return. Otherwise, we
        //    loop back and continue executing step_outs for the parent container(s) until we have
        //    reached the target depth.
        loop {
            self.step_out_nest += 1;
            let result = self.step_out_impl();
            self.step_out_nest -= 1;

            if let Err(IonError::Incomplete { .. }) = result {
                self.need_continue = true;
            }
            result?;

            // If we are a nested call, we're done for now.
            if self.step_out_nest != 0 {
                break;
            } else if target_depth == self.depth() {
                // We've reached our desired depth, so we can reset our state, and target
                // depth.
                self.state = ReaderState::Ready;
                break;
            }
        }
        Ok(())
    }

    fn parent_type(&self) -> Option<IonType> {
        self.parents.last().map(|parent| parent.ion_type())
    }

    fn depth(&self) -> usize {
        self.parents.len()
    }
}

#[cfg(test)]
mod reader_tests {
    use rstest::*;

    use super::*;
    use crate::raw_reader::RawStreamItem;
    use crate::raw_symbol_token::{local_sid_token, text_token, RawSymbolToken};
    use crate::result::{IonResult, Position};
    use crate::stream_reader::IonReader;
    use crate::text::non_blocking::raw_text_reader::RawTextReader;
    use crate::text::text_value::{IntoRawAnnotations, TextValue};
    use crate::types::{Decimal, Timestamp};
    use crate::IonType;
    use crate::RawStreamItem::Nothing;

    fn next_type<T: AsRef<[u8]> + Expandable>(
        reader: &mut RawTextReader<T>,
        ion_type: IonType,
        is_null: bool,
    ) {
        assert_eq!(
            reader.next().unwrap(),
            RawStreamItem::nullable_value(ion_type, is_null)
        );
    }

    fn annotations_eq<I: IntoRawAnnotations>(reader: &mut RawTextReader<&str>, expected: I) {
        let expected: Vec<RawSymbolToken> = expected.into_annotations();
        let actual: Vec<RawSymbolToken> = reader
            .annotations()
            .map(|a| a.expect("annotation with unknown text"))
            .collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_basic_incomplete() -> IonResult<()> {
        let ion_data = r#"
        [1, 2, 3
        "#;
        let mut reader = RawTextReader::new(ion_data.as_bytes().to_owned());
        next_type(&mut reader, IonType::List, false);
        reader.step_in()?;
        next_type(&mut reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 1);
        next_type(&mut reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 2);
        match reader.next() {
            // the failure occurs after reading the \n after 3, so it is identified on line 3.
            Err(IonError::Incomplete {
                position:
                    Position {
                        line_column: Some((line, column)),
                        ..
                    },
                ..
            }) => {
                assert_eq!(line, 2);
                assert_eq!(column, 0);
            }
            Err(e) => panic!("unexpected error when parsing partial data: {e}"),
            Ok(item) => panic!("unexpected successful parsing of partial data: {item:?}"),
        }
        reader
            .append_bytes("]".as_bytes())
            .expect("Unable to append bytes");
        next_type(&mut reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 3);
        Ok(())
    }

    #[test]
    fn test_utf8_incomplete() -> IonResult<()> {
        let source: &[u8] = &[
            0x22, 0x57, 0x65, 0x20, 0x4c, 0x6f, 0x76, 0x65, 0x20, 0x49, 0x6f, 0x6e, 0x21, 0xe2,
            0x9a, 0x9b, 0xef, 0xb8, 0x8f, 0x22,
        ];

        // This will initialize our reader with the full source but end just short of
        // the end of the utf-8 sequence \xe29a9befb88f.
        let mut reader = RawTextReader::new(source[0..18].to_owned());

        match reader.next() {
            Err(IonError::Incomplete {
                position:
                    Position {
                        line_column: Some((line, column)),
                        ..
                    },
                ..
            }) => {
                assert_eq!(line, 0); // Line is still 0 since we haven't actually seen a '\n' yet.
                assert_eq!(column, 14); // failure at start of multi-byte sequence.
            }
            Err(e) => panic!("unexpected error after partial utf-8 data: {e}"),
            Ok(item) => panic!("unexpected successful parsing of partial utf-8 data: {item:?}"),
        }
        reader.append_bytes(&source[18..])?;
        next_type(&mut reader, IonType::String, false);
        Ok(())
    }

    #[test]
    fn test_skipping_containers() -> IonResult<()> {
        let ion_data = r#"
            0 [1, 2, 3] (4 5) 6
        "#;
        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 0);

        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 1);
        reader.step_out()?;
        // This should have skipped over the `2, 3` at the end of the list.
        next_type(reader, IonType::SExp, false);
        // Don't step into the s-expression. Instead, skip over it.
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 6);
        Ok(())
    }

    #[test]
    fn test_read_nested_containers() -> IonResult<()> {
        let ion_data = r#"
            {
                foo: [
                    1,
                    [2, 3],
                    4
                ],
                bar: {
                    a: 5,
                    b: (true true true)
                }
            }
            11
        "#;
        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        // The reader is now at the '2' nested inside of 'foo'
        reader.step_out()?;
        reader.step_out()?;
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        next_type(reader, IonType::SExp, false);
        reader.step_in()?;
        next_type(reader, IonType::Bool, false);
        next_type(reader, IonType::Bool, false);
        // The reader is now at the second 'true' in the s-expression nested in 'bar'/'b'
        reader.step_out()?;
        reader.step_out()?;
        reader.step_out()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 11);
        Ok(())
    }

    #[test]
    fn test_read_container_with_mixed_scalars_and_containers() -> IonResult<()> {
        let ion_data = r#"
            {
                foo: 4,
                bar: {
                    a: 5,
                    b: (true true true)
                }
            }
            42
        "#;

        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.field_name()?, text_token("foo"));
        next_type(reader, IonType::Struct, false);
        assert_eq!(reader.field_name()?, text_token("bar"));
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 5);
        reader.step_out()?;
        assert_eq!(reader.next()?, RawStreamItem::Nothing);
        reader.step_out()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 42);
        Ok(())
    }

    #[rstest]
    #[case(" null ", TextValue::Null(IonType::Null))]
    #[case(" null.string ", TextValue::Null(IonType::String))]
    #[case(" true ", TextValue::Bool(true))]
    #[case(" false ", TextValue::Bool(false))]
    #[case(" 738 ", TextValue::Int(Int::I64(738)))]
    #[case(" 2.5e0 ", TextValue::Float(2.5))]
    #[case(" 2.5 ", TextValue::Decimal(Decimal::new(25, -1)))]
    #[case(" 2007-07-12T ", TextValue::Timestamp(Timestamp::with_ymd(2007, 7, 12).build().unwrap()))]
    #[case(" foo ", TextValue::Symbol(text_token("foo")))]
    #[case(" \"hi!\" ", TextValue::String("hi!".to_owned()))]
    #[case(" {{ZW5jb2RlZA==}} ", TextValue::Blob(Vec::from("encoded".as_bytes())))]
    #[case(" {{\"hello\"}} ", TextValue::Clob(Vec::from("hello".as_bytes())))]
    fn test_read_single_top_level_values(#[case] text: &str, #[case] expected_value: TextValue) {
        let reader = &mut RawTextReader::new(text);
        next_type(
            reader,
            expected_value.ion_type(),
            matches!(expected_value, TextValue::Null(_)),
        );
        // TODO: Redo (or remove?) this test. There's not an API that exposes the
        //       AnnotatedTextValue any more. We're directly accessing `current_value` as a hack.
        let actual_value = reader.current_value.clone();
        assert_eq!(actual_value.unwrap(), expected_value.without_annotations());
    }

    #[test]
    fn test_text_read_multiple_top_level_values() -> IonResult<()> {
        let ion_data = r#"
            null
            true
            5
            5e0
            5.5
            2021-09-25T
            '$ion_1_0' // A quoted symbol, not an IVM
            $ion_1_0   // An IVM, not a symbol
            foo
            "hello"
            {foo: bar}
            ["foo", "bar"]
            ('''foo''')
        "#;

        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Null, true);

        next_type(reader, IonType::Bool, false);
        assert!(reader.read_bool()?);

        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 5);

        next_type(reader, IonType::Float, false);
        assert_eq!(reader.read_f64()?, 5.0f64);

        next_type(reader, IonType::Decimal, false);
        assert_eq!(reader.read_decimal()?, Decimal::new(55i32, -1i64));

        next_type(reader, IonType::Timestamp, false);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2021, 9, 25).build().unwrap()
        );

        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("$ion_1_0"));

        // A mid-stream Ion Version Marker
        assert_eq!(reader.next()?, RawStreamItem::VersionMarker(1, 0));

        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("foo"));

        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, "hello".to_string());

        // ===== CONTAINERS =====

        // Reading a struct: {foo: bar}
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("bar"));
        assert_eq!(reader.field_name()?, text_token("foo"));

        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Reading a list: ["foo", "bar"]
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, String::from("foo"));
        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, String::from("bar"));
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Reading an s-expression: ('''foo''')
        next_type(reader, IonType::SExp, false);
        reader.step_in()?;
        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, String::from("foo"));
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // There are no more top level values.snow
        assert_eq!(reader.next()?, Nothing);

        // Asking for more still results in `None`
        assert_eq!(reader.next()?, Nothing);

        Ok(())
    }

    #[test]
    fn test_read_multiple_top_level_values_with_comments() -> IonResult<()> {
        let ion_data = r#"
            /*
                Arrokoth is a trans-Neptunian object in the Kuiper belt.
                It is a contact binary composed of two plenetesimals joined
                along their major axes.
            */
            "(486958) 2014 MU69" // Original designation
            2014-06-26T // Date of discovery
            km::36 // width
        "#;

        let reader = &mut RawTextReader::new(ion_data);

        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, String::from("(486958) 2014 MU69"));

        next_type(reader, IonType::Timestamp, false);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2014, 6, 26).build()?
        );
        // TODO: Check for 'km' annotation after change to OwnedSymbolToken
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 36);
        Ok(())
    }

    #[test]
    fn test_text_read_multiple_annotated_top_level_values() -> IonResult<()> {
        let ion_data = r#"
            mercury::null
            venus::'earth'::true
            $17::mars::5
            jupiter::5e0
            'saturn'::5.5
            $100::$200::$300::2021-09-25T
            'uranus'::foo
            neptune::"hello"
            $55::{foo: $21::bar}
            pluto::[1, $77::2, 3]
            haumea::makemake::eris::ceres::(++ -- &&&&&)
        "#;
        // TODO: Check for annotations after OwnedSymbolToken

        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Null, true);
        annotations_eq(reader, ["mercury"]);

        next_type(reader, IonType::Bool, false);
        assert!(reader.read_bool()?);
        annotations_eq(reader, ["venus", "earth"]);

        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 5);
        annotations_eq(reader, &[local_sid_token(17), text_token("mars")]);

        next_type(reader, IonType::Float, false);
        assert_eq!(reader.read_f64()?, 5.0f64);
        annotations_eq(reader, ["jupiter"]);

        next_type(reader, IonType::Decimal, false);
        assert_eq!(reader.read_decimal()?, Decimal::new(55i32, -1i64));
        annotations_eq(reader, ["saturn"]);

        next_type(reader, IonType::Timestamp, false);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2021, 9, 25).build().unwrap()
        );
        annotations_eq(reader, [100, 200, 300]);

        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("foo"));
        annotations_eq(reader, ["uranus"]);

        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, "hello".to_string());
        annotations_eq(reader, ["neptune"]);

        // ===== CONTAINERS =====

        // Reading a struct: $55::{foo: $21::bar}
        next_type(reader, IonType::Struct, false);
        annotations_eq(reader, 55);
        reader.step_in()?;
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.field_name()?, text_token("foo"));
        annotations_eq(reader, 21);
        assert_eq!(reader.read_symbol()?, text_token("bar"));
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Reading a list: pluto::[1, $77::2, 3]
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.number_of_annotations(), 0);
        assert_eq!(reader.read_i64()?, 1);
        next_type(reader, IonType::Int, false);
        annotations_eq(reader, [77]);
        assert_eq!(reader.read_i64()?, 2);
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.number_of_annotations(), 0);
        assert_eq!(reader.read_i64()?, 3);
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Reading an s-expression: haumea::makemake::eris::ceres::(++ -- &&&&&)
        next_type(reader, IonType::SExp, false);
        annotations_eq(reader, ["haumea", "makemake", "eris", "ceres"]);
        reader.step_in()?;
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("++"));
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("--"));
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("&&&&&"));
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // There are no more top level values.
        assert_eq!(reader.next()?, Nothing);

        // Asking for more still results in `None`
        assert_eq!(reader.next()?, Nothing);

        Ok(())
    }

    #[test]
    fn structs_trailing_comma() -> IonResult<()> {
        let pretty_ion = br#"
            // Structs with last field with/without trailing comma
            (
                {a:1, b:2,}     // with trailing comma
                {a:1, b:2 }     // without trailing comma
            )
        "#;
        let mut reader = RawTextReader::new(&pretty_ion[..]);
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::SExp));
        reader.step_in()?;
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Struct));

        reader.step_in()?;
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?, RawSymbolToken::Text("a".to_string()));
        assert_eq!(reader.read_i64()?, 1);
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?, RawSymbolToken::Text("b".to_string()));
        assert_eq!(reader.read_i64()?, 2);
        reader.step_out()?;

        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Struct));
        reader.step_out()?;
        Ok(())
    }

    #[test]
    fn annotation_false() -> IonResult<()> {
        // The reader will reject the unquoted boolean keyword 'false' when used as an annotation
        let pretty_ion = br#"
            false::23
        "#;
        let mut reader = RawTextReader::new(&pretty_ion[..]);
        let result = reader.next();
        println!("{result:?}");
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn annotation_nan() -> IonResult<()> {
        // The reader will reject the unquoted float keyword 'nan' when used as an annotation
        let pretty_ion = br#"
            nan::23
        "#;
        let mut reader = RawTextReader::new(&pretty_ion[..]);
        let result = reader.next();
        println!("{result:?}");
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    // Ensure that field names and values are bundled transactionally so that we do not move past
    // the field name, in the event of a failed field value parse. This is limited to scalar values
    // and reading the start of a container ends the transaction.
    fn rollback_field_name() -> IonResult<()> {
        // We'll initialize the buffer with the first 9 characters, which will cause an incomplete
        // text error due to the ambiguous parse.
        //             | Init.  |  |
        let source = r#"{field: 10}"#;

        let mut reader = RawTextReader::new(source[..10].as_bytes().to_owned());
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Struct));

        reader.step_in()?;
        assert_eq!(reader.depth(), 1);

        match reader.next() {
            Err(IonError::Incomplete { .. }) => {
                assert!(reader.field_name().is_err());
                reader.read_from(&mut source[10..].as_bytes(), 3)?;
                reader.stream_complete();
                reader.next()?;
            }
            other => panic!("unexpected return from next: {other:?}"),
        }

        assert_eq!(reader.ion_type().unwrap(), IonType::Int);
        assert_eq!(reader.field_name()?.text(), Some("field"));

        Ok(())
    }

    #[test]
    // Test the happy path of reaching an IncompleteText error while stepping out of a container.
    // The happy part, is that we're just going to re-call `step_out` after feeding more data into
    // the buffer.
    fn resume_step_out() -> IonResult<()> {
        // The spacing on this is important, since we need to know where (approximately) the
        // incomplete error occurs. We provide the first 47 characters, which is everything in the
        // string up to, and including, the 'w' in 'somewhere'.
        //
        //              |    Initial Data Provided to the reader       | Added after Incomplete |
        //              [..............................................][.......................]
        let source = r#"{field:{another_field:{foo:"We should fail somewhere in this string.."}}}"#;

        let mut reader = RawTextReader::new(source[..47].as_bytes().to_owned());
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Struct));

        reader.step_in()?;
        assert_eq!(reader.depth(), 1);

        reader.next()?;

        reader.step_in()?;
        assert_eq!(reader.depth(), 2);

        match reader.step_out() {
            Err(IonError::Incomplete { .. }) => {
                assert_eq!(reader.depth(), 3); // we should fail at depth 3, within the foo field.
                reader.read_from(&mut source[47..].as_bytes(), 512)?;

                // Resume our initial step_out, this should bring us back to depth 1.
                reader.step_out()?;
                assert_eq!(reader.depth(), 1);
            }
            other => panic!("Expected to get an incomplete error: {other:?}"),
        }
        // Step out to the root of the document.
        reader.step_out()?;
        assert_eq!(0, reader.depth()); // we should be at the root level.
        Ok(())
    }

    // Test stepping out of an inner struct which has trailing fields and ensure all fields are
    // exhausted.
    #[test]
    fn resume_step_out_exhaustion() -> IonResult<()> {
        // The spacing on this is important, since we need to know where (approximately) the
        // incomplete error occurs. We provide the first 47 characters, which is everything in the
        // string up to, and including, the 'w' in 'somewhere'.
        //
        //              |    Initial Data Provided to the reader       | Added after Incomplete |
        //              [..............................................][.......................]
        let source = r#"{field:{another_field:{foo:"We should fail somewhere in this string..", number: 3}}, other_field: 21}"#;

        let mut reader = RawTextReader::new(source[..47].as_bytes().to_owned());

        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Struct));

        // Stepping into the top level struct..
        reader.step_in()?;
        assert_eq!(reader.depth(), 1);

        reader.next()?;
        assert_eq!(reader.field_name()?.text(), Some("field"));

        // Stepping into the `field` struct.
        reader.step_in()?;
        assert_eq!(reader.depth(), 2);

        reader.next()?;
        assert_eq!(reader.field_name()?.text(), Some("another_field"));

        // Step out of `field`.. after this we should be at `other_Field`.
        match reader.step_out() {
            Err(IonError::Incomplete { .. }) => {
                assert_eq!(reader.depth(), 3); // we should fail at depth 3, within the foo field.
                reader.read_from(&mut source[47..].as_bytes(), 512)?;
                reader.stream_complete();

                // Resume our initial step_out, this should bring us back to depth 1.
                reader.step_out()?;
                assert_eq!(reader.depth(), 1);
            }
            other => panic!("Expected to get an incomplete error: {other:?}"),
        }
        // We've stepped out of the inner structs, and we should be at the last field in the outter
        // most container.
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?.text(), Some("other_field"));
        assert_eq!(reader.read_i64()?, 21);

        // Step out to the root of the document.
        reader.step_out()?;
        assert_eq!(0, reader.depth()); // we should be at the root level.
        Ok(())
    }

    #[test]
    fn resume_step_out_exhaustion2() -> IonResult<()> {
        // For this source, we're going to initialize the reader with a partial source, from the
        // first byte to the start of the line with "quux". The last character of the buffer will
        // be the end-of-line, from the "baz" definition (offset 62).
        let source = r#"{
            foo: 1,
            bar: 2,
            baz: 3,
            quux: 4,
        }"#;

        // We first read up to the start of the line "quux" is on.
        let mut reader = RawTextReader::new(source[..62].as_bytes().to_owned());

        // Advance the reader, so that we can step_in to the struct.
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Struct));
        reader.step_in()?; // Step into the top level struct.

        // Read 'foo'..
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?.text(), Some("foo"));
        assert_eq!(reader.read_i64()?, 1);

        // Read "bar"
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?.text(), Some("bar"));
        assert_eq!(reader.read_i64()?, 2);

        // We have provided up to the "quux" definition in our buffer, and have read up to and
        // including the "bar" definition. Now we step_out, which should cause an incomplete error.
        match reader.step_out() {
            Err(IonError::Incomplete { .. }) => {
                // After receiving the incomplete error, the reader should not let us doing
                // anything other than completing the step_out. If we call next here, we should
                // still get an IncompleteText error.
                assert!(matches!(reader.next(), Err(IonError::Incomplete { .. })));

                // After the incomplete error, we'll provide the rest of the buffer which should
                // let us complete our step_out.
                reader.read_from(&mut source[62..].as_bytes(), 512)?;
                // Since we've provided the entirety of the source, we'll mark the stream complete.
                reader.stream_complete();
                // Stepping out should succeed, and leave us back at the top level.
                reader.step_out()?;
                assert_eq!(reader.depth(), 0);
            }
            other => panic!("Expected to get an incomplete error: {other:?}"),
        }
        // We have stepped out, and should now be at the end of the stream.
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Nothing);

        Ok(())
    }

    #[test]
    fn resume_failed_step_out_with_next() -> IonResult<()> {
        // This test is the same as resume_Step_out_exhaustion2, but we're going to make sure that
        // calling other functions (like next) after a failed step_out, continues the step_out and
        // avances like we'd expect.
        let source = r#"{
            foo: 1,
            bar: 2,
            baz: 3,
            quux: 4,
        }"#;

        // We first read up to the start of the line "quux" is on.
        let mut reader = RawTextReader::new(source[..62].as_bytes().to_owned());

        // Advance the reader, so that we can step_in to the struct.
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Struct));
        reader.step_in()?; // Step into the top level struct.

        // Read 'foo'..
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?.text(), Some("foo"));
        assert_eq!(reader.read_i64()?, 1);

        // Read "bar"
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?.text(), Some("bar"));
        assert_eq!(reader.read_i64()?, 2);

        // We have provided up to the "quux" definition in our buffer, and have read up to and
        // including the "bar" definition. Now we step_out, which should cause an incomplete error.
        match reader.step_out() {
            Err(IonError::Incomplete { .. }) => {
                // After receiving the incomplete error, the reader should not let us do anything
                // that doesn't result in completing the failed step_out. If we call next now, we
                // should get another IncompleteText error.
                assert!(matches!(reader.next(), Err(IonError::Incomplete { .. })));

                // After the incomplete error, we'll provide the rest of the buffer which should
                // let us complete our step_out.
                reader.read_from(&mut source[62..].as_bytes(), 512)?;
                // Since we've provided the entirety of the source, we'll mark the stream complete.
                reader.stream_complete();
                // Calling next will continue the step_out, and follow up by moving to the next
                // value.
                reader.next()?;
                assert_eq!(reader.depth(), 0);
            }
            other => panic!("Expected to get an incomplete error: {other:?}"),
        }
        // At this point, we should have successfully stepped out, and advanced with the `next`,
        // reaching the end of the document.
        //let result = reader.next()?;
        assert_eq!(reader.current(), RawStreamItem::Nothing);

        Ok(())
    }

    #[test]
    fn resume_step_out_from_failed_next() -> IonResult<()> {
        // This test is the same as resume_step_out_exhaustion2, but is a bit more simple. Rather
        // than stepping out, we're going to get to the struct, and then call `next`. This should
        // bring us to the end of the document, but we'll fail part way through and the user will
        // expect to have to call `next` again.
        let source = r#"{
            foo: 1,
            bar: 2,
            baz: 3,
            quux: 4,
        }"#;

        // We first read up to the start of the line "quux" is on.
        let mut reader = RawTextReader::new(source[..62].as_bytes().to_owned());

        // Advance the reader, so that we can step_in to the struct.
        let mut result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Struct));

        match reader.next() {
            Err(IonError::Incomplete { .. }) => {
                reader.read_from(&mut source[62..].as_bytes(), 512)?;
                reader.stream_complete();
                result = reader.next()?;
            }
            other => panic!("unexpected result from next: {other:?}"),
        }

        // At this point, we should have successfully stepped out, and advanced with the `next`,
        // reaching the end of the document.
        //let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Nothing);

        Ok(())
    }

    #[test]
    fn failed_step_out_no_values() -> IonResult<()> {
        // This test is just to ensure that once we fail, and need to continue a step_out, the
        // reader doesn't provide any functionality to read values, whether they are previous
        // values, or parsing new.
        let source = r#"{
            foo: 1,
            bar: 2,
            baz: 3,
            quux: 4,
        }"#;

        // We first read up to the start of the line "quux" is on.
        let mut reader = RawTextReader::new(source[..62].as_bytes().to_owned());

        // Advance the reader, so that we can step_in to the struct.
        let result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Struct));
        reader.step_in()?; // Step in, so we can read a value first..

        let mut result = reader.next()?;
        assert_eq!(result, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?.text(), Some("foo"));

        match reader.step_out() {
            Err(IonError::Incomplete { .. }) => {
                // We received the incomplete, and now we want to make sure that no previously
                // parsed data is available, and that the reader won't try to start parsing more.
                match reader.read_i64() {
                    Err(IonError::IllegalOperation { .. }) => (),
                    other => panic!("unexpected result from read_i64: {other:?}"),
                }

                reader.read_from(&mut source[62..].as_bytes(), 512)?;
                reader.stream_complete();
                result = reader.next()?;
            }
            other => panic!("unexpected result from next: {other:?}"),
        }
        assert_eq!(result, RawStreamItem::Nothing);

        Ok(())
    }

    #[test]
    fn generate_incomplete_on_truncated_escape() -> IonResult<()> {
        let source = "\"123456\\u269b\"";
        //                       ^-- First read stops here. (offset 9)
        let mut reader = RawTextReader::new(source.as_bytes()[..10].to_owned());

        match reader.next() {
            Err(IonError::Incomplete {
                position:
                    Position {
                        line_column: Some((line, column)),
                        ..
                    },
                ..
            }) => {
                assert_eq!(line, 0); // Line is still 0 since we haven't actually seen a '\n' yet.
                assert_eq!(column, 0); // start of the string; the value being parsed.
            }
            Err(e) => panic!("unexpected error after partial escaped sequence: {e}"),
            Ok(item) => {
                panic!("unexpected successful parsing of partial escaped sequence data: {item:?}")
            }
        }
        reader.append_bytes(source[10..].as_bytes())?;
        next_type(&mut reader, IonType::String, false);
        Ok(())
    }
}
