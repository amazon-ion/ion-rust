use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::Range;

use nom::character::streaming::satisfy;

use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{LazyDecoder, LazyRawSequence, LazyRawValue};
use crate::lazy::encoding::TextEncoding;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::AddContext;
use crate::lazy::text::parse_result::ToIteratorOutput;
use crate::lazy::text::value::LazyRawTextValue;
use crate::{IonResult, IonType};

#[derive(Copy, Clone)]
pub struct LazyRawTextSequence<'data> {
    pub(crate) value: LazyRawTextValue<'data>,
}

impl<'data> LazyRawTextSequence<'data> {
    pub fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub fn iter(&self) -> RawTextSequenceIterator<'data> {
        // Make an iterator over the input bytes that follow the initial `[`
        RawTextSequenceIterator::new(b']', self.value.input.slice_to_end(1))
    }
}

impl<'data> LazyContainerPrivate<'data, TextEncoding> for LazyRawTextSequence<'data> {
    fn from_value(value: LazyRawTextValue<'data>) -> Self {
        LazyRawTextSequence { value }
    }
}

impl<'data> LazyRawSequence<'data, TextEncoding> for LazyRawTextSequence<'data> {
    type Iterator = RawTextSequenceIterator<'data>;

    fn annotations(&self) -> <TextEncoding as LazyDecoder<'data>>::AnnotationsIterator {
        todo!("lazy sequence annotations")
    }

    fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    fn iter(&self) -> Self::Iterator {
        LazyRawTextSequence::iter(self)
    }

    fn as_value(&self) -> LazyRawTextValue<'data> {
        self.value
    }
}

impl<'a, 'data> IntoIterator for &'a LazyRawTextSequence<'data> {
    type Item = IonResult<LazyRawTextValue<'data>>;
    type IntoIter = RawTextSequenceIterator<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> Debug for LazyRawTextSequence<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.value.encoded_value.ion_type() {
            IonType::SExp => {
                write!(f, "(")?;
                for value in self {
                    write!(
                        f,
                        "{:?} ",
                        value
                            .map_err(|_| fmt::Error)?
                            .read()
                            .map_err(|_| fmt::Error)?
                    )?;
                }
                write!(f, ")").unwrap();
            }
            IonType::List => {
                write!(f, "[")?;
                for value in self {
                    write!(
                        f,
                        "{:?},",
                        value
                            .map_err(|_| fmt::Error)?
                            .read()
                            .map_err(|_| fmt::Error)?
                    )?;
                }
                write!(f, "]").unwrap();
            }
            _ => unreachable!("LazyRawSequence is only created for list and sexp"),
        }

        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct RawTextSequenceIterator<'data> {
    end_delimiter: u8,
    input: TextBufferView<'data>,
    // If this iterator has returned an error, it should return `None` forever afterwards
    has_returned_error: bool,
}

impl<'data> RawTextSequenceIterator<'data> {
    pub(crate) fn new(
        end_delimiter: u8,
        input: TextBufferView<'data>,
    ) -> RawTextSequenceIterator<'data> {
        RawTextSequenceIterator {
            end_delimiter,
            input,
            has_returned_error: false,
        }
    }
}

impl<'data> RawTextSequenceIterator<'data> {
    pub(crate) fn find_span(&self) -> IonResult<Range<usize>> {
        // The input has already skipped past the opening delimiter.
        let start = self.input.offset() - 1;
        // We need to find the input slice containing the closing delimiter. It's either...
        let input_after_last = if let Some(value_result) = self.last() {
            let value = value_result?;
            // ...the input slice that follows the last sequence value...
            value.input.slice_to_end(value.encoded_value.total_length())
        } else {
            // ...or there aren't values, so it's just the input after the opening delimiter.
            self.input
        };
        let (input_after_ws, _ws) = input_after_last
            .match_optional_comments_and_whitespace()
            .with_context("seeking the end of a sequence", input_after_last)?;
        let (input_after_end, _end_delimiter) =
            satisfy(|c| c == self.end_delimiter as char)(input_after_ws).with_context(
                "seeking the closing delimiter of a sequence",
                input_after_ws,
            )?;
        let end = input_after_end.offset();
        Ok(start..end)
    }
}

impl<'data> Iterator for RawTextSequenceIterator<'data> {
    type Item = IonResult<LazyRawTextValue<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_list_value() {
            Ok((remaining, Some(value))) => {
                self.input = remaining;
                Some(Ok(value))
            }
            Ok((_remaining, None)) => None,
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next list value", self.input)
                    .transpose()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;

    use crate::lazy::text::raw::reader::LazyRawTextReader;
    use crate::IonResult;

    fn expect_sequence_range(ion_data: &str, expected: Range<usize>) -> IonResult<()> {
        let reader = &mut LazyRawTextReader::new(ion_data.as_bytes());
        let value = reader.next()?.expect_value()?;
        let actual_range = value.encoded_value.data_range();
        assert_eq!(
            actual_range, expected,
            "Sequence range ({:?}) did not match expected range ({:?})",
            actual_range, expected
        );
        Ok(())
    }

    #[test]
    fn list_range() -> IonResult<()> {
        // For each pair below, we'll confirm that the top-level list is found to
        // occupy the specified input span.
        let tests = &[
            // (Ion input, expected range of the sequence)
            ("[]", 0..2),
            ("  []  ", 2..4),
            ("[1, 2]", 0..6),
            ("[1, /* comment ]]] */ 2]", 0..24),
            // Nested
            ("[1, 2, [3, 4, 5], 6]", 0..20),
            // Doubly nested
            ("[1, 2, [3, [a, b, c], 5], 6]", 0..28),
        ];
        for test in tests {
            expect_sequence_range(test.0, test.1.clone())?;
        }
        Ok(())
    }
}
