#[derive(Clone, Copy)]
pub(crate) struct WhitespaceConfig {
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

pub(crate) static COMPACT_WHITESPACE_CONFIG: WhitespaceConfig = WhitespaceConfig {
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

pub(crate) static LINES_WHITESPACE_CONFIG: WhitespaceConfig = WhitespaceConfig {
    // Each value appears on its own line
    space_between_top_level_values: "\n",
    // Otherwise use the compact/default layout from `COMPACT_WHITESPACE_CONFIG`
    ..COMPACT_WHITESPACE_CONFIG
};

pub(crate) static PRETTY_WHITESPACE_CONFIG: WhitespaceConfig = WhitespaceConfig {
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

use crate::TextFormat;

impl From<TextFormat> for &'static WhitespaceConfig {
    fn from(value: TextFormat) -> Self {
        match value {
            TextFormat::Compact => &COMPACT_WHITESPACE_CONFIG,
            TextFormat::Lines => &LINES_WHITESPACE_CONFIG,
            TextFormat::Pretty => &PRETTY_WHITESPACE_CONFIG,
        }
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
