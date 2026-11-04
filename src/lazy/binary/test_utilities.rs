use crate::element::Element;
use crate::lazy::encoder::writer::Writer;
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::write_config::WriteConfig;
use crate::IonResult;

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
