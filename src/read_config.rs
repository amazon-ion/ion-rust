use crate::catalog::{Catalog, EmptyCatalog};
use crate::constants::MAX_READ_WRITE_DEPTH;
use crate::lazy::any_encoding::AnyEncoding;
use crate::lazy::encoding::{BinaryEncoding_1_0, TextEncoding_1_0};
use crate::result::IonFailure;
use crate::{Decoder, IonError, IonResult};
use ice_code::ice as cold_path;

/// The start of the description of every maximum read depth error.
const MAX_READ_DEPTH_EXCEEDED_PREFIX: &str = "container nesting exceeds the maximum read depth";

/// Describes a container whose children would be nested more deeply than
/// [`MAX_READ_WRITE_DEPTH`].
#[cold]
pub(crate) fn max_read_depth_exceeded_message() -> String {
    format!(
        "{MAX_READ_DEPTH_EXCEEDED_PREFIX} ({MAX_READ_WRITE_DEPTH}); it can be raised by setting \
         `ION_RS_MAX_READ_WRITE_DEPTH` when building `ion-rs`"
    )
}

/// Whether `error` reports a container whose children would be nested more deeply than
/// [`MAX_READ_WRITE_DEPTH`]. The description is matched by prefix because the conversion of a
/// text parse error to an `IonError` appends context and input after it.
#[cold]
pub(crate) fn is_max_read_depth_exceeded(error: &IonError) -> bool {
    matches!(
        error,
        IonError::Decoding(e) if e.description().starts_with(MAX_READ_DEPTH_EXCEEDED_PREFIX)
    )
}

/// Asserts that `result` is a maximum read depth error.
#[cfg(test)]
#[track_caller]
pub(crate) fn assert_max_read_depth_exceeded(result: IonResult<impl std::fmt::Debug>) {
    match result {
        Err(e) if is_max_read_depth_exceeded(&e) => {}
        other => panic!("expected a maximum read depth error, found {other:?}"),
    }
}

/// Returns the depth remaining for the children of a container that has `remaining_depth` levels
/// left, or an error if the container's children would exceed [`MAX_READ_WRITE_DEPTH`].
#[inline]
pub(crate) fn child_read_depth(remaining_depth: u16) -> IonResult<u16> {
    match remaining_depth.checked_sub(1) {
        Some(children) => Ok(children),
        None => cold_path!(IonResult::decoding_error(max_read_depth_exceeded_message())),
    }
}

/// Provides configuration details for reader construction.
pub struct ReadConfig<D: Decoder> {
    pub(crate) catalog: Box<dyn Catalog>,
    encoding: D,
}

impl<D: Decoder> ReadConfig<D> {
    fn new(encoding: D) -> Self {
        ReadConfig::new_with_catalog(encoding, EmptyCatalog)
    }

    pub(crate) fn new_with_catalog(encoding: D, catalog: impl Catalog + 'static) -> Self {
        ReadConfig {
            catalog: Box::new(catalog),
            encoding,
        }
    }

    pub fn encoding(&self) -> D {
        self.encoding
    }
}

impl From<TextEncoding_1_0> for ReadConfig<TextEncoding_1_0> {
    fn from(encoding: TextEncoding_1_0) -> Self {
        ReadConfig::new(encoding)
    }
}

impl From<BinaryEncoding_1_0> for ReadConfig<BinaryEncoding_1_0> {
    fn from(encoding: BinaryEncoding_1_0) -> Self {
        ReadConfig::new(encoding)
    }
}

impl From<AnyEncoding> for ReadConfig<AnyEncoding> {
    fn from(encoding: AnyEncoding) -> Self {
        ReadConfig::new(encoding)
    }
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Read};

    use rstest::rstest;

    use super::{
        assert_max_read_depth_exceeded, is_max_read_depth_exceeded, MAX_READ_DEPTH_EXCEEDED_PREFIX,
    };
    use crate::constants::MAX_READ_WRITE_DEPTH;
    use crate::lazy::any_encoding::IonVersion;
    use crate::lazy::binary::test_utilities::{binary_nested, binary_type_descriptor};
    use crate::lazy::encoding::TextEncoding_1_0;
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::raw_stream_item::RawStreamItem;
    use crate::lazy::streaming_raw_reader::StreamingRawReader;
    use crate::lazy::text::buffer::TextBuffer;
    use crate::lazy::text::parse_result::WithContext;
    use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
    use crate::{
        ion_list, ion_sexp, ion_struct, v1_0, Element, IonError, IonResult, IonStream, IonType,
    };

    const MAX: usize = MAX_READ_WRITE_DEPTH as usize;

    /// Nests `innermost` in `levels` containers of type `kind`, so `innermost` is at depth `levels`.
    fn nested(kind: IonType, levels: usize, innermost: Element) -> Element {
        (0..levels).fold(innermost, |child, _| match kind {
            IonType::List => ion_list![child].into(),
            IonType::SExp => ion_sexp!(child).into(),
            IonType::Struct => ion_struct! {"a": child}.into(),
            _ => unreachable!("not a container type: {kind}"),
        })
    }

    fn empty(kind: IonType) -> Element {
        match kind {
            IonType::List => ion_list![].into(),
            IonType::SExp => ion_sexp!().into(),
            IonType::Struct => ion_struct! {}.into(),
            _ => unreachable!("not a container type: {kind}"),
        }
    }

    fn encode(element: &Element, binary: bool) -> IonResult<Vec<u8>> {
        if binary {
            element.encode_as(v1_0::Binary)
        } else {
            Ok(element.to_string().into_bytes())
        }
    }

    #[rstest]
    fn reads_values_at_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
        #[values(false, true)] binary: bool,
        #[values(Element::from(1), Element::null(IonType::List))] innermost: Element,
    ) -> IonResult<()> {
        let element = nested(kind, MAX, innermost);
        assert_eq!(Element::read_one(encode(&element, binary)?)?, element);
        Ok(())
    }

    #[rstest]
    fn rejects_values_beyond_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
        #[values(false, true)] binary: bool,
        #[values(false, true)] empty_innermost: bool,
    ) {
        // An empty container at depth `MAX` would have children at depth `MAX + 1`.
        let (levels, innermost, innermost_binary) = if empty_innermost {
            (MAX, empty(kind), vec![binary_type_descriptor(kind)])
        } else {
            (MAX + 1, Element::from(1), vec![0x21, 0x01])
        };
        // The managed writer rejects values this deep, so binary input is encoded by hand.
        let data = if binary {
            binary_nested(kind, levels, innermost_binary)
        } else {
            nested(kind, levels, innermost).to_string().into_bytes()
        };
        assert_max_read_depth_exceeded(Element::read_one(data));
    }

    #[rstest]
    #[case::list("[", "]")]
    #[case::sexp("(", ")")]
    #[case::struct_("{a:", "}")]
    #[case::annotated_list("a::[", "]")]
    fn rejects_text_nested_far_beyond_the_maximum_depth(#[case] open: &str, #[case] close: &str) {
        let levels = 10_000;
        let text = format!("{}1{}", open.repeat(levels), close.repeat(levels));
        assert_max_read_depth_exceeded(Element::read_one(text));
    }

    /// Parses every top-level value in `text` with the raw text reader, which checks nesting
    /// while matching each value and does not materialize it.
    fn parse_text(text: &str) -> IonResult<()> {
        let context = EncodingContext::for_ion_version(IonVersion::v1_0);
        let mut reader = LazyRawTextReader_1_0::new(context.get_ref(), text.as_bytes(), true);
        while !matches!(reader.next()?, RawStreamItem::EndOfStream(_)) {}
        Ok(())
    }

    /// Nests `innermost` in `levels` containers that each begin with `open` and end with `close`.
    fn text_nested(open: &str, close: &str, levels: usize, innermost: &str) -> String {
        format!("{}{innermost}{}", open.repeat(levels), close.repeat(levels))
    }

    #[rstest]
    #[case::list("[", "]")]
    #[case::sexp("(", ")")]
    #[case::struct_("{a:", "}")]
    #[case::annotated_list("a::[", "]")]
    fn text_parser_accepts_values_at_the_maximum_depth(
        #[case] open: &str,
        #[case] close: &str,
    ) -> IonResult<()> {
        let value = text_nested(open, close, MAX, "1");
        parse_text(&value)?;
        // The depth of one top-level value does not carry over to the next.
        parse_text(&format!("{value} {value}"))
    }

    #[rstest]
    #[case::list("[", "]", "[]")]
    #[case::sexp("(", ")", "()")]
    #[case::struct_("{a:", "}", "{}")]
    #[case::annotated_list("a::[", "]", "a::[]")]
    fn text_parser_rejects_values_beyond_the_maximum_depth(
        #[case] open: &str,
        #[case] close: &str,
        #[case] empty: &str,
        #[values(false, true)] empty_innermost: bool,
    ) {
        // An empty container at depth `MAX` would have children at depth `MAX + 1`.
        let text = if empty_innermost {
            text_nested(open, close, MAX, empty)
        } else {
            text_nested(open, close, MAX + 1, "1")
        };
        assert_max_read_depth_exceeded(parse_text(&text));
    }

    /// Siblings are at the same depth, so the depth reached inside one does not carry over to the
    /// next.
    #[test]
    fn text_parser_accepts_sibling_containers_at_the_maximum_depth() -> IonResult<()> {
        let child = text_nested("[", "]", MAX - 1, "1");
        parse_text(&format!("[{child}, {child}, {child}]"))
    }

    /// The error names the innermost container that exceeds the limit once, rather than once per
    /// enclosing container.
    #[rstest]
    #[case::list("[", "]")]
    #[case::sexp("(", ")")]
    #[case::struct_("{a:", "}")]
    #[case::annotated_list("a::[", "]")]
    fn text_depth_error_reports_the_innermost_container(
        #[case] open: &str,
        #[case] close: &str,
        #[values(false, true)] materialize: bool,
    ) {
        let text = text_nested(open, close, MAX + 1, "1");
        let result = if materialize {
            Element::read_one(text.as_str()).map(|_| ())
        } else {
            parse_text(&text)
        };
        let e = match result {
            Err(IonError::Decoding(e))
                if e.description().starts_with(MAX_READ_DEPTH_EXCEEDED_PREFIX) =>
            {
                e
            }
            other => panic!("expected a maximum read depth error, found {other:?}"),
        };
        let innermost_opening = text.rfind(['[', '(', '{']);
        assert_eq!(e.position().map(|p| p.byte_offset()), innermost_opening);
        assert_eq!(e.to_string().matches("\n    while ").count(), 1, "{e}");
    }

    /// Matches `text` as one value with `context`, as a parse that began at that value.
    fn match_value(context: &EncodingContext, text: &str, is_final_data: bool) -> IonResult<()> {
        let start = TextBuffer::with_offset(context.get_ref(), 0, text.as_bytes(), is_final_data);
        let mut input = start;
        input
            .match_annotated_value::<TextEncoding_1_0>()
            .with_context("matching a test value", start)?;
        Ok(())
    }

    /// The matcher restores the depth however it leaves a container, so a value matched next with
    /// the same context starts at depth 0.
    #[rstest]
    #[case::value("[[[1]]]", true, "value")]
    #[case::incomplete("[[[1", false, "incomplete")]
    #[case::other_error("[[[1 2]]]", true, "other error")]
    #[case::depth_error(&text_nested("[", "]", MAX + 1, "1"), true, "depth error")]
    fn text_matcher_restores_the_depth(
        #[case] text: &str,
        #[case] is_final_data: bool,
        #[case] expected: &str,
    ) -> IonResult<()> {
        let context = EncodingContext::for_ion_version(IonVersion::v1_0);
        let outcome = match match_value(&context, text, is_final_data) {
            Ok(()) => "value",
            Err(IonError::Incomplete(_)) => "incomplete",
            Err(e) if is_max_read_depth_exceeded(&e) => "depth error",
            Err(_) => "other error",
        };
        assert_eq!(outcome, expected);
        assert_eq!(context.text_depth.get(), 0);
        match_value(&context, &text_nested("[", "]", MAX, "1"), true)
    }

    /// The text reader starts each top-level value at depth 0, whatever depth an earlier parse with
    /// its context left.
    #[test]
    fn text_reader_resets_the_depth_before_each_value() -> IonResult<()> {
        let context = EncodingContext::for_ion_version(IonVersion::v1_0);
        let value = text_nested("[", "]", MAX, "1");
        let text = format!("{value} {value}");
        let mut reader = LazyRawTextReader_1_0::new(context.get_ref(), text.as_bytes(), true);
        for _ in 0..2 {
            context.text_depth.set(MAX_READ_WRITE_DEPTH);
            assert!(matches!(reader.next()?, RawStreamItem::Value(_)));
        }
        assert!(matches!(reader.next()?, RawStreamItem::EndOfStream(_)));
        Ok(())
    }

    /// Reads every top-level value in `text` with the streaming raw text reader, which receives
    /// `text` in two chunks split at byte `split`.
    fn parse_text_in_chunks(text: &str, split: usize) -> IonResult<()> {
        let (head, tail) = text.split_at(split);
        let input = Cursor::new(head).chain(Cursor::new(tail));
        let context = EncodingContext::for_ion_version(IonVersion::v1_0);
        let mut reader = StreamingRawReader::new(v1_0::Text, IonStream::new(input));
        while !matches!(
            reader.next(context.get_ref())?,
            RawStreamItem::EndOfStream(_)
        ) {}
        Ok(())
    }

    #[rstest]
    fn streaming_text_reader_accepts_values_at_the_maximum_depth(
        #[values(1, MAX, MAX + 1, MAX + 2, 2 * MAX)] split: usize,
    ) -> IonResult<()> {
        parse_text_in_chunks(&text_nested("[", "]", MAX, "1"), split)
    }

    #[rstest]
    fn streaming_text_reader_rejects_values_beyond_the_maximum_depth(
        #[values(1, MAX, MAX + 1, MAX + 2, 2 * MAX)] split: usize,
    ) {
        let text = text_nested("[", "]", MAX + 1, "1");
        assert_max_read_depth_exceeded(parse_text_in_chunks(&text, split));
    }
}
