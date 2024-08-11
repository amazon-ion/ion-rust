/// Configuration options available to Ion 1.1 value writers.
///
/// The default configuration aligns closely with Ion 1.0's encoding. All symbols, field names, and
/// annotations are added to the symbol table and encoded as symbol IDs.
#[derive(Copy, Clone, Debug, Default)]
pub struct ValueWriterConfig {
    // How nested containers should be encoded.
    container_encoding: ContainerEncoding,
    // How symbol values should be encoded.
    symbol_value_encoding: SymbolValueEncoding,
    // How annotation sequences should be encoded
    annotations_encoding: AnnotationsEncoding,
    // If this writer emits a struct, the struct will encode its field names according to this setting.
    field_name_encoding: FieldNameEncoding,
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
    WriteAsSymbolIds,
    /// Do not add symbol values to the symbol table; write their text inline.
    /// Symbol values specified as symbol IDs will not be mapped to text.
    WriteAsInlineText,
    /// If a symbol value is already in the symbol table, encode it as a symbol ID.
    /// If it is not already in the symbol table, encode its text inline.
    WriteNewSymbolsAsInlineText,
}

/// Configuration options for encoding an annotations sequence.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
#[non_exhaustive]
pub enum AnnotationsEncoding {
    /// Add all annotations to the symbol table and encode them as symbol IDs.
    #[default]
    WriteAsSymbolIds,
    /// Do not add annotations to the symbol table; write their text inline.
    /// Annotations specified as symbol IDs will not be mapped to text.
    WriteAsInlineText,
    /// If an annotation is already in the symbol table, encode it as a symbol ID.
    /// If it is not already in the symbol table, encode its text inline.
    WriteNewSymbolsAsInlineText,
}

/// Configuration options for encoding a struct field name.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
#[non_exhaustive]
pub enum FieldNameEncoding {
    /// Add all field names to the symbol table and encode them as symbol IDs.
    #[default]
    WriteAsSymbolIds,
    /// Do not add field names to the symbol table; write their text inline.
    /// Field names specified as symbol IDs will not be mapped to text.
    WriteAsInlineText,
    /// If a field name is already in the symbol table, encode it as a symbol ID.
    /// If it is not already in the symbol table, encode its text inline.
    WriteNewSymbolsAsInlineText,
}

impl ValueWriterConfig {
    /// Constructs a default `ValueWriterConfig`.
    pub fn new() -> Self {
        ValueWriterConfig::default()
    }

    pub fn container_encoding(&self) -> ContainerEncoding {
        self.container_encoding
    }

    pub fn symbol_value_encoding(&self) -> SymbolValueEncoding {
        self.symbol_value_encoding
    }

    pub fn field_name_encoding(&self) -> FieldNameEncoding {
        self.field_name_encoding
    }

    pub fn annotations_encoding(&self) -> AnnotationsEncoding {
        self.annotations_encoding
    }

    /// Returns `true` if this value writer will write nested containers with a delimited encoding.
    pub fn has_delimited_containers(&self) -> bool {
        self.container_encoding == ContainerEncoding::Delimited
    }

    /// Configures this value writer will write nested containers using a delimited encoding. If it
    /// is `false`, nested containers will be length-prefixed.
    pub fn with_delimited_containers(mut self) -> Self {
        self.container_encoding = ContainerEncoding::Delimited;
        self
    }

    /// If `delimited_containers` is `true`, this value writer will write nested containers using
    /// a delimited encoding. If it is `false`, nested containers will be length-prefixed.
    pub fn with_container_encoding(mut self, container_encoding: ContainerEncoding) -> Self {
        self.container_encoding = container_encoding;
        self
    }

    /// Configures this value writer to write symbol values and annotations with their UTF-8 text
    /// inline.
    pub fn with_symbol_value_encoding(
        mut self,
        symbol_value_encoding: SymbolValueEncoding,
    ) -> Self {
        self.symbol_value_encoding = symbol_value_encoding;
        self
    }

    /// Configures how this value writer will encode its annotations (if any).
    pub fn with_annotations_encoding(mut self, annotations_encoding: AnnotationsEncoding) -> Self {
        self.annotations_encoding = annotations_encoding;
        self
    }

    /// If this value writer is used to write a struct, the struct be configured to encode its
    /// field names according to the specified t`field_name_encoding`.
    pub fn with_field_name_encoding(mut self, field_name_encoding: FieldNameEncoding) -> Self {
        self.field_name_encoding = field_name_encoding;
        self
    }
}
