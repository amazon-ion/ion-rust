use crate::IonResult;
use std::convert::TryFrom;

use crate::result::{IonError, IonFailure};
use crate::IonType;

/// Represents the type information found in the header byte of each binary Ion value.
/// While this value can be readily mapped to a user-level [`IonType`], it is a distinct concept.
/// The IonOpcode enum captures system-level information that is not exposed to end users of the
/// library, including:
/// * Whether the cursor is positioned over whitespace that needs to be skipped.
/// * Whether the integer value being read is positive or negative.
/// * Whether the next type code is reserved.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum OpcodeType {
    EExpressionWithAddress,    // 0x00-0x50 -
    EExpressionAddressFollows, // 0x50-0x5F -
    Integer,                   // 0x60-0x68 - Integer up to 8 bytes wide
    Float,                     // 0x6A-0x6D -
    Boolean,                   // 0x6E-0x6F -
    Decimal,                   // 0x70-0x7F -
    TimestampShort,            // 0x80-0x8F -
    String,                    // 0x90-0x9F -
    InlineSymbol,              // 0xA0-0xAF -
    List,                      // 0xB0-0xBF -
    SExpression,               // 0xC0-0xCF -
    StructEmpty,               // 0xD0      -
    // 0xD1 reserved
    Struct,           // 0xD2-0xDF -
    IonVersionMarker, // 0xE0      -

    SymbolAddress,        // 0xE1-0xE3 -
    AnnotationSymAddress, // 0xE4-0xE6 -
    AnnotationFlexSym,    // 0xE7-0xE9 -
    NullNull,             // 0xEA      -
    TypedNull,            // 0xEB      -
    Nop,                  // 0xEC-0xED -
    // Reserved
    SystemMacroInvoke,           // 0xEF      -
    DelimitedContainerClose,     // 0xF0
    ListDelimited,               // 0xF1
    SExpressionDelimited,        // 0xF2
    StructDelimited,             // 0xF3
    EExpressionWithLengthPrefix, // 0xF5
    LargeInteger,                // 0xF6 - Integer preceded by FlexUInt length
    Blob,                        // 0xFE -
    Clob,                        // 0xFF -
    // 0xF8 Long decimal
    TimestampLong, // 0xF8 - Long-form Timestamp
    // 0xF9 - Long string
    // 0xFA - FlexSym symbol
    // 0xFB - Long list
    // 0xFC - Long sexp
    // 0xFD - Long struct
    Invalid, // Represents an encoded value that does not match a defined opcode.
}

impl OpcodeType {
    pub fn is_delimited_start(self) -> bool {
        matches!(
            self,
            Self::ListDelimited | Self::SExpressionDelimited | Self::StructDelimited
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
