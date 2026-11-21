use crate::element::Element;
use crate::lazy::encoder::writer::Writer;
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::write_config::WriteConfig;
use crate::{IonResult, IonType};

/// Transcribes text Ion to binary Ion
pub fn to_binary_ion(text_ion: &str) -> IonResult<Vec<u8>> {
    elements_to_binary_ion(&Element::read_all(text_ion)?)
}

/// Encodes `elements` as binary Ion.
pub fn elements_to_binary_ion<'a>(
    elements: impl IntoIterator<Item = &'a Element>,
) -> IonResult<Vec<u8>> {
    let buffer = Vec::new();
    let config = WriteConfig::<BinaryEncoding_1_0>::new();
    let mut writer = Writer::new(config, buffer)?;
    for element in elements {
        writer.write(element)?;
    }
    writer.close()
}

/// The Ion 1.0 binary type descriptor of an empty container of type `kind`.
pub(crate) fn binary_type_descriptor(kind: IonType) -> u8 {
    match kind {
        IonType::List => 0xB0,
        IonType::SExp => 0xC0,
        IonType::Struct => 0xD0,
        _ => unreachable!("not a container type: {kind}"),
    }
}

/// Encodes an Ion 1.0 binary value whose type descriptor is `type_code`, followed by `contents`.
/// The low four bits of `type_code` must be 0. The length of `contents` is stored in those bits if
/// it is less than 14, and as a VarUInt after the type descriptor otherwise. A struct whose
/// `contents` is one byte long also uses the VarUInt, because `0xD1` starts a sorted struct.
pub(crate) fn binary_value(type_code: u8, contents: Vec<u8>) -> Vec<u8> {
    let mut value = vec![type_code];
    if contents.len() < 14 && !(type_code == 0xD0 && contents.len() == 1) {
        value[0] |= contents.len() as u8;
    } else {
        value[0] |= 0x0E;
        let mut length = contents.len();
        let mut var_uint = vec![(length & 0x7F) as u8 | 0x80];
        length >>= 7;
        while length > 0 {
            var_uint.insert(0, (length & 0x7F) as u8);
            length >>= 7;
        }
        value.extend(var_uint);
    }
    value.extend(contents);
    value
}

/// Encodes `innermost`, an encoded binary value, in `levels` containers of type `kind` as an
/// Ion 1.0 binary stream. Each struct has one field, named `name` (`$4`).
pub(crate) fn binary_nested(kind: IonType, levels: usize, innermost: Vec<u8>) -> Vec<u8> {
    let field_name: &[u8] = if kind == IonType::Struct {
        &[0x84]
    } else {
        &[]
    };
    let body = (0..levels).fold(innermost, |child, _| {
        binary_value(binary_type_descriptor(kind), [field_name, &child].concat())
    });
    [&[0xE0, 0x01, 0x00, 0xEA][..], &body].concat()
}
