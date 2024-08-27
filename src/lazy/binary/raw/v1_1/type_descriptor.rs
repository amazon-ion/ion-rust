use crate::lazy::binary::encoded_value::EncodedHeader;
use crate::lazy::binary::raw::v1_1::OpcodeType;
use crate::IonType;

/// Contains all of the information that can be extracted from the one-octet Opcode
/// found at the beginning of each value, annotations wrapper, IVM, or NOP in a binary Ion stream.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Opcode {
    pub opcode_type: OpcodeType,
    pub ion_type: Option<IonType>,
    pub low_nibble: u8,
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

static ION_1_1_TIMESTAMP_SHORT_SIZE: [u8; 13] = [1, 2, 2, 4, 5, 6, 7, 8, 5, 5, 7, 8, 9];

const DEFAULT_HEADER: Opcode = Opcode {
    opcode_type: OpcodeType::Nop,
    ion_type: None,
    low_nibble: 0,
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
        use OpcodeType::*;

        let (opcode_type, length_code, ion_type) = match (high_nibble, low_nibble) {
            (0x0..=0x3, _) => (EExpressionWith4BitAddress, low_nibble, None),
            (0x4, _) => (EExpressionWith12BitAddress, low_nibble, None),
            (0x5, _) => (EExpressionWith20BitAddress, low_nibble, None),
            (0x6, 0x0..=0x8) => (Integer, low_nibble, Some(IonType::Int)),
            (0x6, 0xA..=0xD) => (Float, low_nibble, Some(IonType::Float)),
            (0x6, 0xE..=0xF) => (Boolean, low_nibble, Some(IonType::Bool)),
            (0x7, _) => (Decimal, low_nibble, Some(IonType::Decimal)),
            (0x8, 0x0..=0xC) => (TimestampShort, low_nibble, Some(IonType::Timestamp)),
            (0x9, _) => (String, low_nibble, Some(IonType::String)),
            (0xA, _) => (InlineSymbol, low_nibble, Some(IonType::Symbol)),
            (0xB, _) => (List, low_nibble, Some(IonType::List)),
            (0xC, _) => (SExpression, low_nibble, Some(IonType::SExp)),
            (0xD, _) => (Struct, low_nibble, Some(IonType::Struct)),
            (0xE, 0x0) => (IonVersionMarker, low_nibble, None),
            (0xE, 0x1..=0x3) => (SymbolAddress, low_nibble, Some(IonType::Symbol)),
            (0xE, 0x4..=0x6) => (AnnotationSymAddress, low_nibble, None),
            (0xE, 0x7..=0x9) => (AnnotationFlexSym, low_nibble, None),
            (0xE, 0xA) => (NullNull, low_nibble, Some(IonType::Null)),
            (0xE, 0xB) => (TypedNull, low_nibble, Some(IonType::Null)),
            (0xE, 0xC..=0xD) => (Nop, low_nibble, None),
            (0xF, 0x0) => (DelimitedContainerClose, low_nibble, None),
            (0xF, 0x1) => (ListDelimited, low_nibble, Some(IonType::List)),
            (0xF, 0x2) => (SExpressionDelimited, low_nibble, Some(IonType::SExp)),
            (0xF, 0x3) => (StructDelimited, low_nibble, Some(IonType::Struct)),
            (0xF, 0x5) => (EExpressionWithLengthPrefix, low_nibble, None),
            (0xF, 0x6) => (LargeInteger, low_nibble, Some(IonType::Int)),
            (0xF, 0x7) => (Decimal, 0xFF, Some(IonType::Decimal)),
            (0xF, 0x8) => (TimestampLong, low_nibble, Some(IonType::Timestamp)),
            (0xF, 0x9) => (String, 0xFF, Some(IonType::String)), // 0xFF indicates >15 byte string.
            (0xF, 0xA) => (InlineSymbol, 0xFF, Some(IonType::Symbol)),
            (0xF, 0xB) => (List, 0xFF, Some(IonType::List)),
            (0xF, 0xC) => (SExpression, 0xFF, Some(IonType::SExp)),
            (0xF, 0xD) => (Struct, 0xFF, Some(IonType::Struct)),
            (0xF, 0xE) => (Blob, low_nibble, Some(IonType::Blob)),
            (0xF, 0xF) => (Clob, low_nibble, Some(IonType::Clob)),
            _ => (Invalid, low_nibble, None),
        };
        Opcode {
            ion_type,
            opcode_type,
            low_nibble: length_code,
            byte,
        }
    }

    pub fn ion_type(&self) -> Option<IonType> {
        self.ion_type
    }

    pub fn is_null(&self) -> bool {
        self.opcode_type == OpcodeType::NullNull || self.opcode_type == OpcodeType::TypedNull
    }

    pub fn is_nop(&self) -> bool {
        self.opcode_type == OpcodeType::Nop
    }

    pub fn is_e_expression(&self) -> bool {
        use OpcodeType::*;
        matches!(
            self.opcode_type,
            EExpressionWith4BitAddress
                | EExpressionWith12BitAddress
                | EExpressionWith20BitAddress
                | EExpressionWithLengthPrefix
        )
    }

    pub fn is_ivm_start(&self) -> bool {
        self.opcode_type == OpcodeType::IonVersionMarker
    }

    pub fn is_annotations_sequence(&self) -> bool {
        use OpcodeType::*;
        matches!(self.opcode_type, AnnotationSymAddress | AnnotationFlexSym)
    }

    pub fn low_nibble(&self) -> u8 {
        self.low_nibble
    }

    pub fn is_delimited_start(&self) -> bool {
        self.opcode_type.is_delimited_start()
    }

    pub fn is_delimited_end(&self) -> bool {
        self.opcode_type.is_delimited_end()
    }

    #[inline]
    pub fn to_header(self) -> Option<Header> {
        let ion_type = self.ion_type?;
        let header = Header {
            ion_type,
            ion_type_code: self.opcode_type,
            low_nibble: self.low_nibble,
        };
        Some(header)
    }
}

pub enum LengthType {
    InOpcode(u8),
    FlexUIntFollows,
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
    pub low_nibble: u8,
}

impl Header {
    pub fn length_type(&self) -> LengthType {
        use LengthType::*;
        match (self.ion_type_code, self.low_nibble) {
            (OpcodeType::Boolean, 0xE..=0xF) => InOpcode(0),
            (OpcodeType::Float, 0xA) => InOpcode(0),
            (OpcodeType::Float, 0xB..=0xD) => InOpcode(1 << (self.low_nibble - 0xA)),
            (OpcodeType::Integer, n) => InOpcode(n),
            (OpcodeType::Nop, 0xC) => InOpcode(0),
            (OpcodeType::NullNull, 0xA) => InOpcode(0),
            (OpcodeType::String, 0..=15) => InOpcode(self.low_nibble),
            (OpcodeType::InlineSymbol, n) if n < 16 => InOpcode(n),
            (OpcodeType::SymbolAddress, n) if n < 4 => InOpcode(n),
            (OpcodeType::Decimal, 0..=15) => InOpcode(self.low_nibble),
            (OpcodeType::List, n) if n < 16 => InOpcode(n),
            (OpcodeType::SExpression, n) if n < 16 => InOpcode(n),
            (OpcodeType::TimestampShort, 0..=12) => {
                InOpcode(ION_1_1_TIMESTAMP_SHORT_SIZE[self.low_nibble as usize])
            }
            (OpcodeType::TypedNull, _) => InOpcode(1),
            (OpcodeType::Struct, n) if n < 16 => InOpcode(n),
            (OpcodeType::DelimitedContainerClose, 0) => InOpcode(0),
            (
                OpcodeType::ListDelimited
                | OpcodeType::SExpressionDelimited
                | OpcodeType::StructDelimited,
                _,
            ) => Unknown,
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

    fn low_nibble(&self) -> u8 {
        self.low_nibble
    }

    fn is_null(&self) -> bool {
        self.ion_type_code == OpcodeType::NullNull || self.ion_type_code == OpcodeType::TypedNull
    }
}
