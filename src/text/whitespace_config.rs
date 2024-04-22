#[derive(Clone, Copy)]
pub(crate) struct WhitespaceConfig {
    // Top-level values are independent of other values in the stream, we may separate differently
    pub(crate) space_between_top_level_values: &'static str,
    // Non-top-level values are within a container
    pub(crate) space_between_nested_values: &'static str,
    // Indentation is repeated before nested values, corresponding to the level of nesting
    pub(crate) indentation: &'static str,
    // e.g. after 'foo:' in "{foo: bar}"
    pub(crate) space_after_field_name: &'static str,
    // Between the container open and any value in it
    pub(crate) space_after_container_start: &'static str,
}

pub(crate) static COMPACT_WHITESPACE_CONFIG: WhitespaceConfig = WhitespaceConfig {
    // Single space between top level values
    space_between_top_level_values: " ",
    // Single space between values
    space_between_nested_values: " ",
    // No indentation
    indentation: "",
    // Single space between field names and values
    space_after_field_name: " ",
    // The first value in a container appears next to the opening delimiter
    space_after_container_start: "",
};

pub(crate) static LINES_WHITESPACE_CONFIG: WhitespaceConfig = WhitespaceConfig {
    // Each value appears on its own line
    space_between_top_level_values: "\n",
    // Otherwise use the compact/default layout from `DEFAULT_WS_CONFIG`
    ..COMPACT_WHITESPACE_CONFIG
};

pub(crate) static PRETTY_WHITESPACE_CONFIG: WhitespaceConfig = WhitespaceConfig {
    // Each top-level value starts on its own line
    space_between_top_level_values: "\n",
    // Each value appears on its own line
    space_between_nested_values: "\n",
    // Values get two spaces of indentation per level of depth
    indentation: "  ",
    // Field names and values are separated by a single space
    space_after_field_name: " ",
    // The first value in a container appears on a line by itself
    space_after_container_start: "\n",
};
