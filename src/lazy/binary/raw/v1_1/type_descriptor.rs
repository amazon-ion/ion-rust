use crate::lazy::binary::encoded_value::EncodedHeader;
use crate::lazy::binary::raw::v1_1::type_code::OpcodeKind;
use crate::lazy::binary::raw::v1_1::LengthType::Unknown;
use crate::lazy::binary::raw::v1_1::OpcodeType;
use crate::IonType;

/// Contains all of the information that can be extracted from the one-octet Opcode
/// found at the beginning of each value, annotations wrapper, IVM, or NOP in a binary Ion stream.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Opcode {
    /// The specific syntactic element that this opcode represents.
    pub opcode_type: OpcodeType,
    /// The high-level category of syntactic elements to which the `OpcodeType` belongs.
    /// See [`OpcodeKind`] for the list of possible categories.
    pub kind: OpcodeKind,
    /// Whether the syntactic element that this opcode represents/precedes has a length encoded
    /// in the opcode itself, following the opcode, or must otherwise be inferred.
    pub length_type: LengthType,
    /// The raw input byte for this opcode.
    pub byte: u8,
}

/// A statically defined array of TypeDescriptor that allows a binary reader to map a given
/// byte (`u8`) to a `TypeDescriptor` without having to perform any masking or bitshift operations.
pub(crate) static ION_1_1_OPCODES: &[Opcode; 256] = &init_opcode_cache();
pub(crate) static ION_1_1_TYPED_NULL_TYPES: &[IonType; 12] = &[
    IonType::Bool,
    IonType::Int,
    IonType::Float,
    IonType::Decimal,
    IonType::Timestamp,
    IonType::String,
    IonType::Symbol,
    IonType::Blob,
    IonType::Clob,
    IonType::List,
    IonType::SExp,
    IonType::Struct,
];

const ION_1_1_TIMESTAMP_SHORT_SIZE: [u8; 13] = [1, 2, 2, 4, 5, 6, 7, 8, 5, 5, 7, 8, 9];

const DEFAULT_HEADER: Opcode = Opcode {
    kind: OpcodeKind::Control,
    opcode_type: OpcodeType::Nop,
    length_type: Unknown,
    byte: 0,
};

pub(crate) const fn init_opcode_cache() -> [Opcode; 256] {
    let mut jump_table = [DEFAULT_HEADER; 256];
    let mut index: usize = 0;
    while index < 256 {
        let byte = index as u8;
        jump_table[index] = Opcode::from_byte(byte);
        index += 1;
    }
    jump_table
}

impl Opcode {
    /// Attempts to parse the provided byte. If the opcode is unrecognized or the
    /// opcode + length code combination is illegal, an error will be returned.
    pub const fn from_byte(byte: u8) -> Opcode {
        let (high_nibble, low_nibble) = (byte >> 4, byte & 0x0F);
        use super::Directive;
        use crate::lazy::binary::raw::v1_1::type_code::OpcodeKind;
        use LengthType::*;
        use OpcodeType::*;

        // These are *additional* lengths beyond the opcode
        const IVM_LENGTH: u8 = 3;
        const UNTYPED_NULL_LENGTH: u8 = 0;
        const TYPED_NULL_LENGTH: u8 = 1;

        let (opcode_type, length_type, kind) = match (high_nibble, low_nibble) {
            (0x0..=0x3, _) => (EExpWith1ByteAddress, InOpcode(1), OpcodeKind::EExp),
            (0x4, 0x0..=0x7) => (EExpWith1ByteAddress, InOpcode(1), OpcodeKind::EExp),
            (0x4, 0x8..=0xF) => (EExpWithExtendedAddress, Unknown, OpcodeKind::EExp),
            (0x5, 0x0..=0x7) => (SymbolAddress, Unknown, OpcodeKind::Value(IonType::Symbol)),
            (0x5, 0x8) => (AnnotationSymAddress, Unknown, OpcodeKind::Annotations),
            (0x5, 0x9) => (AnnotationInlineText, Unknown, OpcodeKind::Annotations),
            (0x5, 0xB) => (
                TaglessElementList,
                Unknown,
                OpcodeKind::Value(IonType::List),
            ),
            (0x5, 0xA) => (
                TaglessElementSExp,
                Unknown,
                OpcodeKind::Value(IonType::SExp),
            ),
            (0x6, length @ 0x0..=0x8) => {
                (Integer, InOpcode(length), OpcodeKind::Value(IonType::Int))
            }
            (0x6, 0xA) => (Float, InOpcode(0), OpcodeKind::Value(IonType::Float)),
            (0x6, 0xB..=0xD) => (
                Float,
                InOpcode(1 << (low_nibble - 0xA)),
                OpcodeKind::Value(IonType::Float),
            ),
            (0x6, 0xE..=0xF) => (Boolean, InOpcode(0), OpcodeKind::Value(IonType::Bool)),
            (0x7, length) => (
                Decimal,
                InOpcode(length),
                OpcodeKind::Value(IonType::Decimal),
            ),
            (0x8, 0x0..=0xC) => (
                TimestampShort,
                InOpcode(ION_1_1_TIMESTAMP_SHORT_SIZE[low_nibble as usize]),
                OpcodeKind::Value(IonType::Timestamp),
            ),
            (0x8, 0xE) => (
                NullNull,
                InOpcode(UNTYPED_NULL_LENGTH),
                OpcodeKind::Value(IonType::Null),
            ),
            (0x8, 0xF) => (
                TypedNull,
                InOpcode(TYPED_NULL_LENGTH),
                OpcodeKind::Value(IonType::Null),
            ),
            (0x9, length) => (String, InOpcode(length), OpcodeKind::Value(IonType::String)),
            (0xA, length) => (
                InlineSymbol,
                InOpcode(length),
                OpcodeKind::Value(IonType::Symbol),
            ),
            (0xB, length) => (List, InOpcode(length), OpcodeKind::Value(IonType::List)),
            (0xC, length) => (SExp, InOpcode(length), OpcodeKind::Value(IonType::SExp)),
            (0xD, length) => (Struct, InOpcode(length), OpcodeKind::Value(IonType::Struct)),
            (0xE, 0x0) => (IonVersionMarker, InOpcode(IVM_LENGTH), OpcodeKind::Control),
            // TODO: Revisit directive representation
            (0xE, directive @ 0..=8) => (
                Directive,
                Unknown,
                OpcodeKind::Directive(match directive {
                    1 => Directive::SetSymbols,
                    2 => Directive::AddSymbols,
                    3 => Directive::SetMacros,
                    4 => Directive::AddMacros,
                    5 => Directive::Use,
                    6 => Directive::Module,
                    7 => Directive::Import,
                    8 => Directive::Encoding,
                    _ => Directive::Invalid,
                }),
            ),
            (0xE, 0x9) => (TemplatePlaceholder, InOpcode(0), OpcodeKind::Control),
            (0xE, 0xA) => (TemplatePlaceholderWithDefault, Unknown, OpcodeKind::Control),
            (0xE, 0xB) => (TemplatePlaceholderTagless, InOpcode(1), OpcodeKind::Control),
            (0xE, 0xC) => (Nop, InOpcode(0), OpcodeKind::Control),
            (0xE, 0xD) => (Nop, FlexUIntFollows, OpcodeKind::Control),
            (0xE, 0xE) => (StructSwitchMode, InOpcode(0), OpcodeKind::Control),
            (0xE, 0xF) => (DelimitedContainerClose, InOpcode(0), OpcodeKind::Control),
            (0xF, 0x0) => (ListDelimited, Unknown, OpcodeKind::Value(IonType::List)),
            (0xF, 0x1) => (SExpDelimited, Unknown, OpcodeKind::Value(IonType::SExp)),
            (0xF, 0x2) => (
                StructDelimitedSID,
                Unknown,
                OpcodeKind::Value(IonType::Struct),
            ),
            (0xF, 0x3) => (
                StructDelimitedFlexSym,
                Unknown,
                OpcodeKind::Value(IonType::Struct),
            ),
            (0xF, 0x4) => (
                EExpressionWithLengthPrefix,
                FlexUIntFollows,
                OpcodeKind::EExp,
            ),
            (0xF, 0x5) => (
                LargeInteger,
                FlexUIntFollows,
                OpcodeKind::Value(IonType::Int),
            ),
            (0xF, 0x6) => (
                Decimal,
                FlexUIntFollows,
                OpcodeKind::Value(IonType::Decimal),
            ),
            (0xF, 0x7) => (
                TimestampLong,
                FlexUIntFollows,
                OpcodeKind::Value(IonType::Timestamp),
            ),
            (0xF, 0x8) => (String, FlexUIntFollows, OpcodeKind::Value(IonType::String)), // 0xFF indicates >15 byte string.
            (0xF, 0x9) => (
                InlineSymbol,
                FlexUIntFollows,
                OpcodeKind::Value(IonType::Symbol),
            ),
            (0xF, 0xA) => (List, FlexUIntFollows, OpcodeKind::Value(IonType::List)),
            (0xF, 0xB) => (SExp, FlexUIntFollows, OpcodeKind::Value(IonType::SExp)),
            // TODO: Long structs are in 2 types, SID and FlexSym starting modes.
            (0xF, 0xC) => (Struct, FlexUIntFollows, OpcodeKind::Value(IonType::Struct)),
            (0xF, 0xE) => (Blob, FlexUIntFollows, OpcodeKind::Value(IonType::Blob)),
            (0xF, 0xF) => (Clob, FlexUIntFollows, OpcodeKind::Value(IonType::Clob)),

            _ => (Invalid, Unknown, OpcodeKind::Control),
        };
        Opcode {
            opcode_type,
            kind,
            length_type,
            byte,
        }
    }

    pub fn ion_type(&self) -> Option<IonType> {
        if let OpcodeKind::Value(ion_type) = self.kind {
            Some(ion_type)
        } else {
            None
        }
    }

    pub fn is_null(&self) -> bool {
        self.opcode_type == OpcodeType::NullNull || self.opcode_type == OpcodeType::TypedNull
    }

    pub fn is_nop(&self) -> bool {
        self.opcode_type == OpcodeType::Nop
    }

    pub fn is_e_expression(&self) -> bool {
        matches!(self.kind, OpcodeKind::EExp)
    }

    pub fn is_ivm_start(&self) -> bool {
        self.opcode_type == OpcodeType::IonVersionMarker
    }

    pub fn is_annotations_sequence(&self) -> bool {
        matches!(self.kind, OpcodeKind::Annotations)
    }

    pub fn low_nibble(&self) -> u8 {
        self.byte & 0x0F
    }

    pub fn is_delimited_start(&self) -> bool {
        self.opcode_type.is_delimited_start()
    }

    pub fn is_delimited_end(&self) -> bool {
        self.opcode_type.is_delimited_end()
    }

    #[inline]
    pub fn to_header(self) -> Option<Header> {
        let header = Header {
            ion_type: self.ion_type()?,
            ion_type_code: self.opcode_type,
            length_type: self.length_type,
            byte: self.byte,
        };
        Some(header)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LengthType {
    /// The length of this construct is determined by the opcode. The `u8` indicates the number of
    /// _following_ bytes that are part of this construct.
    InOpcode(u8),
    /// The length of this construct is encoded as a `FlexUInt` following the opcode.
    FlexUIntFollows,
    /// The length is delimited (e.g. containers) or requires additional information from context to
    /// determine (e.g. e-expressions).
    Unknown,
}

/// Represents a `TypeDescriptor` that appears before an Ion value (and not a NOP, IVM,
/// or annotations wrapper).
///
/// Notably, it stores an `IonType` instead of an `Option<IonType>`, allowing functions that expect
/// a value header to avoid matching/unwrapping.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Header {
    pub ion_type: IonType,
    // The only time the `ion_type_code` is required is to distinguish between positive
    // and negative integers.
    pub ion_type_code: OpcodeType,
    pub length_type: LengthType,
    pub byte: u8,
}

impl Header {
    pub fn byte(&self) -> u8 {
        self.byte
    }

    pub fn low_nibble(&self) -> u8 {
        self.byte & 0x0F
    }

    pub fn length_type(&self) -> LengthType {
        self.length_type
    }
}

impl EncodedHeader for Header {
    type TypeCode = OpcodeType;

    fn ion_type(&self) -> IonType {
        self.ion_type
    }

    fn type_code(&self) -> Self::TypeCode {
        self.ion_type_code
    }

    fn is_null(&self) -> bool {
        self.ion_type_code == OpcodeType::NullNull || self.ion_type_code == OpcodeType::TypedNull
    }
}
