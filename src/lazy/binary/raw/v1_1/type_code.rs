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
    EExpressionWithAddress,    // 0x00-0x4F -
    EExpressionAddressFollows, // 0x40-0x4F -
    Integer,                   // 0x50-0x58 - Integer up to 8 bytes wide
    Float,                     // 0x5A-0x5D -
    Boolean,                   // 0x5E-0x5F -
    Decimal,                   // 0x60-0x6F -
    TimestampShort,            // 0x70-0x7F -
    String,                    // 0x80-0x80 -
    InlineSymbol,              // 0x90-0x9F -
    List,                      // 0xA0-0xAF -
    SExpression,               // 0xB0-0xBF -
    StructEmpty,               // 0xC0      -
    // reserved
    StructSymAddress, // 0xC2-0xCF -
    // reserved
    StructFlexSym,    // 0xD2-0xDF -
    IonVersionMarker, // 0xE0      -

    SymbolAddress,        // 0xE1-0xE3 -
    AnnotationSymAddress, // 0xE4-0xE6 -
    AnnotationFlexSym,    // 0xE7-0xE9 -
    NullNull,             // 0xEA      -
    TypedNull,            // 0xEB      -
    Nop,                  // 0xEC-0xED -
    // Reserved
    SystemMacroInvoke, // 0xEF      -
    // delimited container end
    // delimited list start
    // delimited s-expression start
    LargeInteger,  // 0xF5 - Integer preceeded by FlexUInt length
    Blob,          // 0xFE -
    Clob,          // 0xFF -
    TimestampLong, // 0xF7 - Long-form Timestamp
    Invalid,       // Represents an encoded value that does not match a defined opcode.
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
