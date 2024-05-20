use crate::lazy::binary::encoded_value::EncodedHeader;
use crate::lazy::binary::raw::v1_1::OpcodeType;
use crate::IonType;

/// Contains all of the information that can be extracted from the one-octet Opcode
/// found at the beginning of each value, annotations wrapper, IVM, or NOP in a binary Ion stream.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Opcode {
    pub opcode_type: OpcodeType,
    pub ion_type: Option<IonType>,
    pub length_code: u8,
}

/// A statically defined array of TypeDescriptor that allows a binary reader to map a given
/// byte (`u8`) to a `TypeDescriptor` without having to perform any masking or bitshift operations.
pub(crate) static ION_1_1_OPCODES: &[Opcode; 256] = &init_opcode_cache();

static ION_1_1_TIMESTAMP_SHORT_SIZE: [u8; 13] = [1, 2, 2, 4, 5, 6, 7, 8, 5, 5, 7, 8, 9];

const DEFAULT_HEADER: Opcode = Opcode {
    opcode_type: OpcodeType::Nop,
    ion_type: None,
    length_code: 0,
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
        use OpcodeType::*;

        let (opcode_type, length_code, ion_type) = match (high_nibble, low_nibble) {
            (0x5, 0x0..=0x8) => (Integer, low_nibble, Some(IonType::Int)),
            (0x5, 0xA..=0xD) => (Float, low_nibble, Some(IonType::Float)),
            (0x5, 0xE..=0xF) => (Boolean, low_nibble, Some(IonType::Bool)),
            (0x6, _) => (Decimal, low_nibble, Some(IonType::Decimal)),
            (0x7, 0x0..=0xC) => (TimestampShort, low_nibble, Some(IonType::Timestamp)),
            (0x8, _) => (String, low_nibble, Some(IonType::String)),
            (0x9, _) => (InlineSymbol, low_nibble, Some(IonType::Symbol)),
            (0xA, _) => (List, low_nibble, Some(IonType::List)),
            (0xB, _) => (SExpression, low_nibble, Some(IonType::SExp)),
            (0xE, 0x0) => (IonVersionMarker, low_nibble, None),
            (0xE, 0x1..=0x3) => (SymbolAddress, low_nibble, Some(IonType::Symbol)),
            (0xE, 0xA) => (NullNull, low_nibble, Some(IonType::Null)),
            (0xE, 0xC..=0xD) => (Nop, low_nibble, None),
            (0xF, 0x5) => (LargeInteger, low_nibble, Some(IonType::Int)),
            (0xF, 0x6) => (Decimal, 0xFF, Some(IonType::Decimal)),
            (0xF, 0x8) => (String, 0xFF, Some(IonType::String)), // 0xFF indicates >15 byte string.
            (0xF, 0x9) => (InlineSymbol, 0xFF, Some(IonType::Symbol)),
            (0xF, 0xA) => (List, 0xFF, Some(IonType::List)),
            (0xF, 0xB) => (SExpression, 0xFF, Some(IonType::SExp)),
            (0xF, 0xE) => (Blob, low_nibble, Some(IonType::Blob)),
            (0xF, 0xF) => (Clob, low_nibble, Some(IonType::Clob)),
            (0xF, 0x7) => (TimestampLong, low_nibble, Some(IonType::Timestamp)),
            _ => (Invalid, low_nibble, None),
        };
        Opcode {
            ion_type,
            opcode_type,
            length_code,
        }
    }

    pub fn is_null(&self) -> bool {
        self.opcode_type == OpcodeType::NullNull || self.opcode_type == OpcodeType::TypedNull
    }

    pub fn is_nop(&self) -> bool {
        self.opcode_type == OpcodeType::Nop
    }

    pub fn is_ivm_start(&self) -> bool {
        self.opcode_type == OpcodeType::IonVersionMarker
    }

    pub fn is_annotation_wrapper(&self) -> bool {
        false
    }

    #[inline]
    pub fn to_header(self) -> Option<Header> {
        let ion_type = self.ion_type?;
        let header = Header {
            ion_type,
            ion_type_code: self.opcode_type,
            length_code: self.length_code,
        };
        Some(header)
    }
}

pub enum LengthType {
    InOpcode(u8),
    FlexUIntFollows,
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
    pub length_code: u8,
}

impl Header {
    pub fn length_type(&self) -> LengthType {
        use LengthType::*;
        match (self.ion_type_code, self.length_code) {
            (OpcodeType::Boolean, 0xE..=0xF) => InOpcode(0),
            (OpcodeType::Float, 0xA) => InOpcode(0),
            (OpcodeType::Float, 0xB..=0xD) => InOpcode(1 << (self.length_code - 0xA)),
            (OpcodeType::Integer, n) => InOpcode(n),
            (OpcodeType::Nop, 0xC) => InOpcode(0),
            (OpcodeType::NullNull, 0xA) => InOpcode(0),
            (OpcodeType::String, 0..=15) => InOpcode(self.length_code),
            (OpcodeType::InlineSymbol, n) if n < 16 => InOpcode(n),
            (OpcodeType::SymbolAddress, n) if n < 4 => InOpcode(n),
            (OpcodeType::Decimal, 0..=15) => InOpcode(self.length_code),
            (OpcodeType::List, n) if n < 16 => InOpcode(n),
            (OpcodeType::SExpression, n) if n < 16 => InOpcode(n),
            (OpcodeType::TimestampShort, 0..=12) => {
                InOpcode(ION_1_1_TIMESTAMP_SHORT_SIZE[self.length_code as usize])
            }
            _ => FlexUIntFollows,
        }
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

    fn length_code(&self) -> u8 {
        self.length_code
    }

    fn is_null(&self) -> bool {
        self.ion_type_code == OpcodeType::NullNull || self.ion_type_code == OpcodeType::TypedNull
    }
}
