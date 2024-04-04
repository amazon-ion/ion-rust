use crate::IonResult;
use std::convert::TryFrom;

use crate::result::{IonError, IonFailure};
use crate::IonType;

/// Represents the type information found in the header byte of each binary Ion value.
/// While this value can be readily mapped to a user-level [`IonType`], it is a distinct concept.
/// The IonTypeCode enum captures system-level information that is not exposed to end users of the
/// library, including:
/// * Whether the cursor is positioned over whitespace that needs to be skipped.
/// * Whether the integer value being read is positive or negative.
/// * Whether the next type code is reserved.
///
/// See the
/// [Typed Value Formats](https://amazon-ion.github.io/ion-docs/docs/binary.html#typed-value-formats)
/// section of the spec for more information.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum IonTypeCode {
    EExpression(bool), // 0x00-0x4F - With, or without, address in the opcode.
    Integer,           // 0x50-0x58 - Integer up to 8 bytes wide.
    Float,             // 0x5A-0x5D -
    Boolean,           // 0x5E-0x5F -
    Decimal,           // 0x60-0x6F -
    Timestamp,         // 0x70-0x7F -
    String,            // 0x80-0x80 -
    InlineSymbol,      // 0x90-0x9F -
    List,              // 0xA0-0xAF -
    SExpression,       // 0xB0-0xBF -
    StructEmpty,       // 0xC0      -
    // reserved
    StructSymAddress, // 0xD2-0xDF -
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
}

impl TryFrom<IonTypeCode> for IonType {
    type Error = IonError;

    /// Attempts to convert the system-level IonTypeCode into the corresponding user-level IonType.
    fn try_from(ion_type_code: IonTypeCode) -> Result<Self, Self::Error> {
        use IonTypeCode::*;
        let ion_type = match ion_type_code {
            NullNull => IonType::Null,
            Nop => IonType::Null,
            // NullOrNop => IonType::Null,
            // Boolean => IonType::Bool,
            // PositiveInteger | NegativeInteger => IonType::Int,
            // Float => IonType::Float,
            // Decimal => IonType::Decimal,
            // Timestamp => IonType::Timestamp,
            // Symbol => IonType::Symbol,
            // String => IonType::String,
            // Clob => IonType::Clob,
            // Blob => IonType::Blob,
            // List => IonType::List,
            // SExpression => IonType::SExp,
            // Struct => IonType::Struct,
            _ => {
                return IonResult::decoding_error(format!(
                    "Attempted to make an IonType from an invalid type code: {ion_type_code:?}"
                ));
            }
        };
        Ok(ion_type)
    }
}

impl TryFrom<u8> for IonTypeCode {
    type Error = IonError;

    /// Attempts to convert the provided byte into an IonTypeCode. Any value greater than 15
    /// will result in an Error.
    fn try_from(type_code: u8) -> Result<Self, Self::Error> {
        use IonTypeCode::*;
        let ion_type_code = match (type_code.overflowing_shr(8).0, type_code & 0x0F) {
            (0xE, 0xA) => NullNull,
            (0xE, 0xC..=0xD) => Nop,
            // 0 => NullOrNop,
            // 1 => Boolean,
            // 2 => PositiveInteger,
            // 3 => NegativeInteger,
            // 4 => Float,
            // 5 => Decimal,
            // 6 => Timestamp,
            // 7 => Symbol,
            // 8 => String,
            // 9 => Clob,
            // 10 => Blob,
            // 11 => List,
            // 12 => SExpression,
            // 13 => Struct,
            // 14 => AnnotationOrIvm,
            // 15 => Reserved,
            _ => {
                return IonResult::decoding_error(format!(
                    "{type_code:?} is not implemented, or an invalid type code."
                ));
            } // _ => {
              //     return IonResult::decoding_error(format!(
              //         "{type_code:?} is not a valid header type code."
              //     ));
              // }
        };
        Ok(ion_type_code)
    }
}

impl IonTypeCode {
    /// Constant function to convert an [`IonTypeCode`] into a `u8`.
    pub const fn to_u8(self) -> u8 {
        use IonTypeCode::*;
        match self {
            EExpression(true) => 0x0,
            // NullOrNop => 0,
            // Boolean => 1,
            // PositiveInteger => 2,
            // NegativeInteger => 3,
            // Float => 4,
            // Decimal => 5,
            // Timestamp => 6,
            // Symbol => 7,
            // String => 8,
            // Clob => 9,
            // Blob => 10,
            // List => 11,
            // SExpression => 12,
            // Struct => 13,
            // AnnotationOrIvm => 14,
            // Reserved => 15,
            _ => todo!(),
        }
    }
}
