// `pub` (in a crate-private module) because it appears in the `TextStyle` trait, which bounds the
// public text writer types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WhitespaceConfig {
    // Top-level values are independent of other values in the stream, we may separate differently
    pub(crate) space_between_top_level_values: &'static str,
    // Non-top-level values are within a container
    pub(crate) space_between_nested_values: &'static str,
    // Indentation is repeated before nested values, corresponding to the level of nesting
    pub(crate) indentation: &'static str,

    // The fields below join a delimiter with the whitespace that always follows it, so the writer
    // emits each with a single write.

    // `,` followed by `space_between_nested_values`; follows each value in a list or struct
    pub(crate) comma_separator: &'static str,
    // `:` and the whitespace after it, e.g. after 'foo' in "{foo: bar}"
    pub(crate) field_name_separator: &'static str,
    // The container's opening delimiter followed by the whitespace before its first value; all
    // three use the same whitespace
    pub(crate) list_start: &'static str,
    pub(crate) sexp_start: &'static str,
    pub(crate) struct_start: &'static str,
}

// The layouts are `const` rather than `static` so that a style's whitespace folds into the code of
// the crate that instantiates the writer, which only sees a `static`'s address unless it is built
// with cross-crate LTO.
pub(crate) const COMPACT_WHITESPACE_CONFIG: WhitespaceConfig = WhitespaceConfig {
    // Single space between top level values
    space_between_top_level_values: " ",
    // Single space between values
    space_between_nested_values: " ",
    // No indentation
    indentation: "",
    comma_separator: ", ",
    // Single space between field names and values
    field_name_separator: ": ",
    // The first value in a container appears next to the opening delimiter
    list_start: "[",
    sexp_start: "(",
    struct_start: "{",
};

pub(crate) const LINES_WHITESPACE_CONFIG: WhitespaceConfig = WhitespaceConfig {
    // Each value appears on its own line
    space_between_top_level_values: "\n",
    // Otherwise use the compact/default layout from `COMPACT_WHITESPACE_CONFIG`
    ..COMPACT_WHITESPACE_CONFIG
};

pub(crate) const PRETTY_WHITESPACE_CONFIG: WhitespaceConfig = WhitespaceConfig {
    // Each top-level value starts on its own line
    space_between_top_level_values: "\n",
    // Each value appears on its own line
    space_between_nested_values: "\n",
    // Values get two spaces of indentation per level of depth
    indentation: "  ",
    comma_separator: ",\n",
    // Field names and values are separated by a single space
    field_name_separator: ": ",
    // The first value in a container appears on a line by itself
    list_start: "[\n",
    sexp_start: "(\n",
    struct_start: "{\n",
};

use crate::lazy::encoder::private::Sealed;
use crate::TextFormat;

/// What a text value or container writer knows about its position that decides its indentation.
// `pub` (in a crate-private module, so it cannot be implemented outside the crate) because it
// bounds `TextStyle::Indentation`.
pub trait IndentationState: Copy {
    /// The state at `depth`, with no annotations written. `in_struct` is `true` for a struct
    /// field's value, which follows its already-indented field name.
    fn new(depth: u32, in_struct: bool) -> Self;
    fn depth(self) -> u32;
    fn in_struct(self) -> bool;
    /// Whether the value's annotations, and so its indentation, have been written.
    fn has_annotations(self) -> bool;
    fn set_has_annotations(&mut self, has_annotations: bool);
}

/// The indentation state of a style whose layout may indent.
// The depth is a `u32`, so that this packs into 8 bytes and a value writer that holds it stays at
// 24 bytes. The managed writer limits nesting to `max_depth`, a `u16`.
#[derive(Clone, Copy, Debug)]
pub struct TrackedIndentation {
    depth: u32,
    in_struct: bool,
    has_annotations: bool,
}

impl IndentationState for TrackedIndentation {
    #[inline(always)]
    fn new(depth: u32, in_struct: bool) -> Self {
        TrackedIndentation {
            depth,
            in_struct,
            has_annotations: false,
        }
    }

    #[inline(always)]
    fn depth(self) -> u32 {
        self.depth
    }

    #[inline(always)]
    fn in_struct(self) -> bool {
        self.in_struct
    }

    #[inline(always)]
    fn has_annotations(self) -> bool {
        self.has_annotations
    }

    #[inline(always)]
    fn set_has_annotations(&mut self, has_annotations: bool) {
        self.has_annotations = has_annotations;
    }
}

/// The indentation state of a style whose layout never indents: it stores nothing.
#[derive(Clone, Copy, Debug)]
pub struct NoIndentation;

impl IndentationState for NoIndentation {
    #[inline(always)]
    fn new(_depth: u32, _in_struct: bool) -> Self {
        NoIndentation
    }

    #[inline(always)]
    fn depth(self) -> u32 {
        0
    }

    #[inline(always)]
    fn in_struct(self) -> bool {
        false
    }

    #[inline(always)]
    fn has_annotations(self) -> bool {
        false
    }

    #[inline(always)]
    fn set_has_annotations(&mut self, _has_annotations: bool) {}
}

/// The whitespace layout of the text writer. A zero-sized style fixes the layout at compile time,
/// so each format gets its own copy of the writer with its whitespace inlined; [`RuntimeStyle`]
/// reads the layout from a config chosen at run time.
pub trait TextStyle: Copy + Sealed {
    /// The state value and container writers keep to indent. It is zero-sized for a layout that
    /// never indents, so those writers store and copy no indentation state.
    #[doc(hidden)]
    type Indentation: IndentationState;

    /// The layout this style writes.
    #[doc(hidden)]
    fn whitespace(self) -> &'static WhitespaceConfig;

    /// The style of a writer configured for `format`. A zero-sized style has a fixed layout, so it
    /// ignores `format`.
    #[doc(hidden)]
    fn from_format(format: TextFormat) -> Self;
}

/// A layout chosen at run time.
#[derive(Clone, Copy, Debug)]
pub struct RuntimeStyle(pub(crate) &'static WhitespaceConfig);

impl Sealed for RuntimeStyle {}

impl TextStyle for RuntimeStyle {
    type Indentation = TrackedIndentation;

    #[inline]
    fn whitespace(self) -> &'static WhitespaceConfig {
        self.0
    }

    #[inline]
    fn from_format(format: TextFormat) -> Self {
        RuntimeStyle(format.into())
    }
}

/// Implements `Sealed` and `TextStyle` for a zero-sized style that writes the layout of `$format`
/// with the given indentation state. This is the only place that pairs a style with its format.
macro_rules! impl_static_text_style {
    ($style:ident, $format:path, $indentation:ident) => {
        impl $style {
            /// The text format whose layout this style writes.
            pub(crate) const FORMAT: TextFormat = $format;
            // A `const`, like the layouts themselves, so that it folds into the instantiating
            // crate's code.
            const LAYOUT: &'static WhitespaceConfig = layout_of(Self::FORMAT);
        }

        impl Sealed for $style {}

        impl TextStyle for $style {
            type Indentation = $indentation;

            #[inline(always)]
            fn whitespace(self) -> &'static WhitespaceConfig {
                Self::LAYOUT
            }

            #[inline(always)]
            fn from_format(_format: TextFormat) -> Self {
                $style
            }
        }
    };
}

/// Ion 1.0 text in the [`TextFormat::Compact`] layout, fixed at compile time.
///
/// [`Writer::new`](crate::Writer::new) and [`Writer::idle`](crate::Writer::idle) accept this
/// marker, or the [`StyledWriteConfig`](crate::v1_0::StyledWriteConfig) that its `with_max_depth`
/// returns, and build a
/// `Writer<v1_0::Text, Output, v1_0::CompactText>`, whose code is specialized to the compact
/// layout. It writes the same text as a writer built from
/// `v1_0::Text.with_format(TextFormat::Compact)`, a `TextWriter<Output>` that reads its layout at
/// run time. `encode_as` and `encode_to` take only run-time-styled configurations.
///
/// ```
///# use ion_rs::IonResult;
///# #[cfg(feature = "experimental-reader-writer")]
///# fn main() -> IonResult<()> {
/// use ion_rs::{v1_0, Element, IonError, Writer};
///
/// let mut writer = Writer::new(v1_0::CompactText, Vec::new())?;
/// writer.write(1)?.write([2, 3])?;
/// assert_eq!(writer.close()?, b"1 [2, 3, ] ");
///
/// // A configuration of the marker's style can limit the nesting depth.
/// let config = v1_0::CompactText.with_max_depth(1);
/// let mut writer = Writer::new(config, Vec::new())?;
/// writer.write([1])?;
/// assert!(matches!(
///     writer.write(Element::read_one("[[1]]")?),
///     Err(IonError::Encoding(_))
/// ));
///# Ok(())
///# }
///# #[cfg(not(feature = "experimental-reader-writer"))]
///# fn main() -> IonResult<()> { Ok(()) }
/// ```
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CompactText;

impl_static_text_style!(CompactText, TextFormat::Compact, NoIndentation);

/// Ion 1.0 text in the [`TextFormat::Lines`] layout, fixed at compile time.
///
/// Like [`CompactText`], for the lines layout: a writer built with this marker writes the same text
/// as one built from `v1_0::Text.with_format(TextFormat::Lines)`, with its code specialized to the
/// layout.
///
/// ```
///# use ion_rs::IonResult;
///# #[cfg(feature = "experimental-reader-writer")]
///# fn main() -> IonResult<()> {
/// use ion_rs::{v1_0, Element, Writer};
///
/// let mut writer = Writer::new(v1_0::LinesText, Vec::new())?;
/// writer
///     .write(Element::read_one("{a: [1, 2]}")?)?
///     .write(Element::read_one("(c d)")?)?;
/// assert_eq!(writer.close()?, b"{a: [1, 2, ], }\n(c d )\n");
///# Ok(())
///# }
///# #[cfg(not(feature = "experimental-reader-writer"))]
///# fn main() -> IonResult<()> { Ok(()) }
/// ```
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LinesText;

impl_static_text_style!(LinesText, TextFormat::Lines, NoIndentation);

/// Ion 1.0 text in the [`TextFormat::Pretty`] layout, fixed at compile time.
///
/// Like [`CompactText`], for the pretty layout: a writer built with this marker writes the same
/// text as one built from `v1_0::Text.with_format(TextFormat::Pretty)`, with its code specialized
/// to the layout.
///
/// ```
///# use ion_rs::IonResult;
///# #[cfg(feature = "experimental-reader-writer")]
///# fn main() -> IonResult<()> {
/// use ion_rs::{v1_0, Element, Writer};
///
/// let mut writer = Writer::new(v1_0::PrettyText, Vec::new())?;
/// writer.write(Element::read_one("{a: [1, 2]}")?)?;
/// assert_eq!(writer.close()?, b"{\n  a: [\n    1,\n    2,\n  ],\n}\n");
///# Ok(())
///# }
///# #[cfg(not(feature = "experimental-reader-writer"))]
///# fn main() -> IonResult<()> { Ok(()) }
/// ```
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PrettyText;

impl_static_text_style!(PrettyText, TextFormat::Pretty, TrackedIndentation);

/// The layout of `format`. A `const fn`, so that a zero-sized style's layout can be a `const`.
#[inline]
const fn layout_of(format: TextFormat) -> &'static WhitespaceConfig {
    match format {
        TextFormat::Compact => &COMPACT_WHITESPACE_CONFIG,
        TextFormat::Lines => &LINES_WHITESPACE_CONFIG,
        TextFormat::Pretty => &PRETTY_WHITESPACE_CONFIG,
    }
}

impl From<TextFormat> for &'static WhitespaceConfig {
    #[inline]
    fn from(value: TextFormat) -> Self {
        layout_of(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case::compact(&COMPACT_WHITESPACE_CONFIG, "", " ")]
    #[case::lines(&LINES_WHITESPACE_CONFIG, "", " ")]
    #[case::pretty(&PRETTY_WHITESPACE_CONFIG, "\n", " ")]
    fn precombined_fields_are_consistent(
        #[case] config: &WhitespaceConfig,
        #[case] space_after_container_start: &str,
        #[case] space_after_field_name: &str,
    ) {
        assert_eq!(
            config.comma_separator,
            format!(",{}", config.space_between_nested_values)
        );
        assert_eq!(
            config.field_name_separator,
            format!(":{space_after_field_name}")
        );
        assert_eq!(config.list_start, format!("[{space_after_container_start}"));
        assert_eq!(config.sexp_start, format!("({space_after_container_start}"));
        assert_eq!(
            config.struct_start,
            format!("{{{space_after_container_start}")
        );
    }

    /// Every layout string fits in the two bytes that `write_layout` writes without a copy.
    #[rstest]
    #[case::compact(&COMPACT_WHITESPACE_CONFIG)]
    #[case::lines(&LINES_WHITESPACE_CONFIG)]
    #[case::pretty(&PRETTY_WHITESPACE_CONFIG)]
    fn layout_strings_are_at_most_two_bytes(#[case] config: &WhitespaceConfig) {
        let WhitespaceConfig {
            space_between_top_level_values,
            space_between_nested_values,
            indentation,
            comma_separator,
            field_name_separator,
            list_start,
            sexp_start,
            struct_start,
        } = *config;
        for (field, layout) in [
            (
                "space_between_top_level_values",
                space_between_top_level_values,
            ),
            ("space_between_nested_values", space_between_nested_values),
            ("indentation", indentation),
            ("comma_separator", comma_separator),
            ("field_name_separator", field_name_separator),
            ("list_start", list_start),
            ("sexp_start", sexp_start),
            ("struct_start", struct_start),
        ] {
            assert!(
                layout.len() <= 2,
                "`{field}` is {layout:?}, longer than the two bytes `write_layout` writes without a copy"
            );
        }
    }
}
