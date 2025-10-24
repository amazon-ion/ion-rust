use crate::IonResult;
use std::convert::TryFrom;

use crate::result::{IonError, IonFailure};
use crate::IonType;

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Directive {
    SetSymbols,
    AddSymbols,
    SetMacros,
    AddMacros,
    Use,
    Module,
    Import,
    Encoding,
    Invalid,
}

/// Represents the type information found in the header byte of each binary Ion value.
/// While this value can be readily mapped to a user-level [`IonType`], it is a distinct concept.
/// The IonOpcode enum captures system-level information that is not exposed to end users of the
/// library, including:
/// * Whether the cursor is positioned over whitespace that needs to be skipped.
/// * Whether the integer value being read is positive or negative.
/// * Whether the next type code is reserved.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
#[rustfmt::skip]
pub enum OpcodeType {
    // https://amazon-ion.github.io/ion-docs/books/ion-1-1/binary/e_expressions.html#encoding-expressions
    EExpWith1ByteAddress,           // 0x00-0x47 -
    EExpWithExtendedAddress,        // 0x48-0x4F -
    // https://amazon-ion.github.io/ion-docs/books/ion-1-1/binary/values/symbol.html#symbols-with-a-symbol-address
    SymbolAddress,                  // 0x50-0x57 -
    // https://amazon-ion.github.io/ion-docs/books/ion-1-1/binary/annotations.html
    AnnotationSymAddress,           // 0x58
    AnnotationInlineText,           // 0x59
    // https://amazon-ion.github.io/ion-docs/books/ion-1-1/binary/values/list.html#tagless-element-lists
    TaglessElementList,             // 0x5B
    // https://amazon-ion.github.io/ion-docs/books/ion-1-1/binary/values/sexp.html#tagless-element-s-expressions
    TaglessElementSExp,             // 0x5C
    // https://amazon-ion.github.io/ion-docs/books/ion-1-1/binary/values/int.html
    Integer,                        // 0x60-0x68 - Integer up to 8 bytes wide
    Float,                          // 0x6A-0x6D -
    Boolean,                        // 0x6E-0x6F -
                                    //
    Decimal,                        // 0x70-0x7F -
    TimestampShort,                 // 0x80-0x8C -
    // https://amazon-ion.github.io/ion-docs/books/ion-1-1/binary/values/null.html
    NullNull,                       // 0x8E      -
    TypedNull,                      // 0x8F      -

    String,                         // 0x90-0x9F -
    InlineSymbol,                   // 0xA0-0xAF -
    List,                           // 0xB0-0xBF -
    SExp,                           // 0xC0-0xCF -
    StructEmpty,                    // 0xD0      -
    Struct,                         // 0xD2-0xDF -
    IonVersionMarker,               // 0xE0      -
    Directive,                      // 0xE1-0xE8 -
    TemplatePlaceholder,            // 0xE9 -
    TemplatePlaceholderWithDefault, // 0xEA -
    TemplatePlaceholderTagless,     // 0xEB -
    Nop,                            // 0xEC-0xED -
    StructSwitchMode,               // 0xEE -
    DelimitedContainerClose,        // 0xEF -

    ListDelimited,                  // 0xF0 -
    SExpDelimited,                  // 0xF1 -
    StructDelimitedSID,             // 0xF2 -
    StructDelimitedFlexSym,         // 0xF3 -

    EExpressionWithLengthPrefix,    // 0xF4 -

    LargeInteger,                   // 0xF5 - Integer preceded by FlexUInt length
    // 0xF6 Long decimal
    TimestampLong,                  // 0xF7 - Long-form Timestamp
    // 0xF8 - Long string
    // 0xF9 - Symbol with FlexUInt length prefix and inline text
    // 0xFA - Long list
    // 0xFB - Long sexp
    // 0xFC - Long struct
    Blob,                        // 0xFE -
    Clob,                        // 0xFF -
    Invalid, // Represents an encoded value that does not match a defined opcode.
}

impl OpcodeType {
    pub fn is_delimited_start(self) -> bool {
        matches!(
            self,
            Self::ListDelimited
                | Self::SExpDelimited
                | Self::StructDelimitedSID
                | Self::StructDelimitedFlexSym
        )
    }

    pub fn is_delimited_end(self) -> bool {
        Self::DelimitedContainerClose == self
    }
}

impl TryFrom<OpcodeType> for IonType {
    type Error = IonError;

    /// Attempts to convert the system-level IonOpcode into the corresponding user-level IonType.
    fn try_from(opcode: OpcodeType) -> Result<Self, Self::Error> {
        use OpcodeType::*;
        let ion_type = match opcode {
            NullNull => IonType::Null,
            Nop => IonType::Null,
            _ => {
                return IonResult::decoding_error(format!(
                    "Attempted to make an IonType from an invalid opcode: {opcode:?}"
                ));
            }
        };
        Ok(ion_type)
    }
}

/// High-level categories of syntactic elements that an [`Opcode`](super::Opcode) may represent.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum OpcodeKind {
    /// A value
    Value(IonType),
    /// A data stream macro invocation (e-expression)
    EExp,
    /// An annotations sequence
    Annotations,
    /// e.g. An IVM, NOP, or delimited container END
    Control,
    /// e.g. `set_symbols`, `add_symbols`, `use`, `import`, etc
    Directive(Directive),
}
