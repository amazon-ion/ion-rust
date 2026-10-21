/// Configuration options available to Ion 1.1 value writers.
///
/// The default configuration aligns closely with Ion 1.0's encoding. All symbols, field names, and
/// annotations are added to the symbol table and encoded as symbol IDs.
#[derive(Copy, Clone, Debug)]
// This config is copied into a new value writer for every nested value, so its layout is on the hot
// path. Each copy must be read back by loads that each fall within a single earlier store: a load
// that spans more than one in-flight store cannot be forwarded from the store buffer and stalls
// until the stores reach the cache, which slowed container-heavy encoding by ~2-12% on Graviton.
// `repr(C)` keeps the one-byte enum fields contiguous (one 4-byte store) ahead of the separately
// updated `remaining_depth`; the default layout places `remaining_depth` first, so a 4-byte load
// spans it and two of the enums.
#[repr(C)]
pub struct ValueWriterConfig {
    // How nested containers should be encoded.
    container_encoding: ContainerEncoding,
    // How symbol values should be encoded.
    symbol_value_encoding: SymbolValueEncoding,
    // How annotation sequences should be encoded
    annotations_encoding: AnnotationsEncoding,
    // If this writer emits a struct, the struct will encode its field names according to this setting.
    field_name_encoding: FieldNameEncoding,
    // The number of container levels that may still be opened, counting the value this writer
    // writes if it is a container: `0` means the value may not be a container. A plain `u16` rather
    // than an `Option`, whose tag and value would be stored separately and read back together.
    remaining_depth: u16,
}

impl Default for ValueWriterConfig {
    fn default() -> Self {
        Self::binary()
    }
}

/// Configuration options for encoding containers.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub enum ContainerEncoding {
    /// The container's length will be prepended to its contents. This requires more work for the
    /// writer, but allows the reader to traverse the stream more quickly via skip-scanning.
    #[default]
    LengthPrefixed,
    /// The start and end of the container will be encoded as opcodes. This requires less work for
    /// the writer, but the reader will not be able to skip over the container.
    Delimited,
}

// ===== Symbol text encoding policies =====
//
// The types below are very similar to one another. They have been kept distinct for two reasons:
//   1. It makes code setting these options a bit more obvious/self-documenting.
//   2. It leaves the door open to adding distinctive new options to each individually.

/// Configuration options for encoding a struct field name.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
#[non_exhaustive]
pub enum SymbolValueEncoding {
    /// Add all symbol values to the symbol table and encode them as symbol IDs.
    #[default]
    SymbolIds,
    /// Do not add symbol values to the symbol table; write their text inline.
    /// Symbol values specified as symbol IDs will not be mapped to text.
    InlineText,
    /// If a symbol value is already in the symbol table, encode it as a symbol ID.
    /// If it is not already in the symbol table, encode its text inline.
    NewSymbolsAsInlineText,
}

/// Configuration options for encoding an annotations sequence.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
#[non_exhaustive]
pub enum AnnotationsEncoding {
    /// Add all annotations to the symbol table and encode them as symbol IDs.
    #[default]
    SymbolIds,
    /// Do not add annotations to the symbol table; write their text inline.
    /// Annotations specified as symbol IDs will not be mapped to text.
    InlineText,
    /// If an annotation is already in the symbol table, encode it as a symbol ID.
    /// If it is not already in the symbol table, encode its text inline.
    NewSymbolsAsInlineText,
}

/// Configuration options for encoding a struct field name.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
#[non_exhaustive]
#[allow(clippy::enum_variant_names)]
pub enum FieldNameEncoding {
    /// Add all field names to the symbol table and encode them as symbol IDs.
    #[default]
    SymbolIds,
    /// Do not add field names to the symbol table; write their text inline.
    /// Field names specified as symbol IDs will not be mapped to text.
    InlineText,
    /// If a field name is already in the symbol table, encode it as a symbol ID.
    /// If it is not already in the symbol table, encode its text inline.
    NewSymbolsAsInlineText,
}

impl ValueWriterConfig {
    /// Constructs a `ValueWriterConfig` that writes all symbol tokens as inline text.
    pub const fn text() -> Self {
        ValueWriterConfig {
            container_encoding: ContainerEncoding::Delimited,
            symbol_value_encoding: SymbolValueEncoding::InlineText,
            annotations_encoding: AnnotationsEncoding::InlineText,
            field_name_encoding: FieldNameEncoding::InlineText,
            remaining_depth: u16::MAX,
        }
    }

    /// Constructs a `ValueWriterConfig` that writes all symbol tokens as symbol IDs.
    pub const fn binary() -> Self {
        ValueWriterConfig {
            container_encoding: ContainerEncoding::LengthPrefixed,
            symbol_value_encoding: SymbolValueEncoding::SymbolIds,
            annotations_encoding: AnnotationsEncoding::SymbolIds,
            field_name_encoding: FieldNameEncoding::SymbolIds,
            remaining_depth: u16::MAX,
        }
    }

    pub const fn container_encoding(&self) -> ContainerEncoding {
        self.container_encoding
    }

    pub const fn symbol_value_encoding(&self) -> SymbolValueEncoding {
        self.symbol_value_encoding
    }

    pub const fn field_name_encoding(&self) -> FieldNameEncoding {
        self.field_name_encoding
    }

    pub const fn annotations_encoding(&self) -> AnnotationsEncoding {
        self.annotations_encoding
    }

    /// Returns `true` if this value writer will write nested containers with a delimited encoding.
    pub const fn has_delimited_containers(&self) -> bool {
        matches!(self.container_encoding, ContainerEncoding::Delimited)
    }

    /// Configures this value writer will write nested containers using a delimited encoding. If it
    /// is `false`, nested containers will be length-prefixed.
    pub const fn with_delimited_containers(mut self) -> Self {
        self.container_encoding = ContainerEncoding::Delimited;
        self
    }

    /// If `delimited_containers` is `true`, this value writer will write nested containers using
    /// a delimited encoding. If it is `false`, nested containers will be length-prefixed.
    pub const fn with_container_encoding(mut self, container_encoding: ContainerEncoding) -> Self {
        self.container_encoding = container_encoding;
        self
    }

    /// Configures this value writer to write symbol values and annotations with their UTF-8 text
    /// inline.
    pub const fn with_symbol_value_encoding(
        mut self,
        symbol_value_encoding: SymbolValueEncoding,
    ) -> Self {
        self.symbol_value_encoding = symbol_value_encoding;
        self
    }

    /// Configures how this value writer will encode its annotations (if any).
    pub const fn with_annotations_encoding(
        mut self,
        annotations_encoding: AnnotationsEncoding,
    ) -> Self {
        self.annotations_encoding = annotations_encoding;
        self
    }

    /// If this value writer is used to write a struct, the struct be configured to encode its
    /// field names according to the specified t`field_name_encoding`.
    pub const fn with_field_name_encoding(
        mut self,
        field_name_encoding: FieldNameEncoding,
    ) -> Self {
        self.field_name_encoding = field_name_encoding;
        self
    }

    /// Allows `remaining_depth` levels of containers to be opened, counting the value this writer
    /// writes if it is a container: `0` means the value may not be a container.
    pub(crate) const fn with_remaining_depth(mut self, remaining_depth: u16) -> Self {
        self.remaining_depth = remaining_depth;
        self
    }

    /// Returns the configuration for the children of a container this writer is about to open, or
    /// `None` if they would exceed the maximum depth.
    #[inline]
    pub(crate) fn enter_container(mut self) -> Option<Self> {
        self.remaining_depth = self.remaining_depth.checked_sub(1)?;
        Some(self)
    }
}

#[cfg(test)]
mod tests {
    use super::ValueWriterConfig;
    use rstest::rstest;

    #[rstest]
    #[case::default_limit(u16::MAX, u16::MAX - 1)]
    #[case::one_level_left(1, 0)]
    fn enter_container_passes_the_remaining_depth_to_children(
        #[case] remaining_depth: u16,
        #[case] expected_for_children: u16,
    ) {
        let children = ValueWriterConfig::default()
            .with_remaining_depth(remaining_depth)
            .enter_container()
            .expect("the container should be allowed");
        assert_eq!(children.remaining_depth, expected_for_children);
    }

    #[test]
    fn enter_container_rejects_a_container_with_no_remaining_depth() {
        let config = ValueWriterConfig::default().with_remaining_depth(0);
        assert!(config.enter_container().is_none());
    }

    #[test]
    fn default_allows_u16_max_levels_of_containers() {
        assert_eq!(ValueWriterConfig::default().remaining_depth, u16::MAX);
    }
}
