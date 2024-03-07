use bumpalo::collections::Vec as BumpVec;
use ice_code::ice as cold_path;

use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::RawSymbolTokenRef::{SymbolId, Text};
use crate::{FlexInt, RawSymbolTokenRef};

/// An Ion 1.1 encoding primitive that can compactly represent a symbol ID or inline text.
#[derive(Debug)]
pub struct FlexSym {
    // No fields yet; these may be added when we get to read support.
}

impl FlexSym {
    /// A FlexSym-encoded logical zero: the byte `0x01u8`
    pub const ZERO: u8 = 0x01;

    /// Encode the provided `symbol` as a FlexSym and write it to the provided [`BumpVec`].
    pub fn encode_symbol(output: &mut BumpVec<u8>, symbol: impl AsRawSymbolTokenRef) {
        let symbol_token = symbol.as_raw_symbol_token_ref();
        // Write the field name
        match symbol_token {
            SymbolId(sid) if sid != 0 => {
                FlexInt::encode_i64(output, sid as i64);
            }
            Text(text) if !text.is_empty() => {
                let negated_num_bytes = -(text.len() as i64);
                FlexInt::encode_i64(output, negated_num_bytes);
                output.extend_from_slice_copy(text.as_bytes());
            }
            _ => cold_path! {
                Self::encode_special_case(output, symbol_token)
            },
        };
    }

    /// Encodes the empty string or symbol ID zero as a FlexSym. The caller is responsible for
    /// confirming that `symbol` is one of those two cases before calling.
    fn encode_special_case(output: &mut BumpVec<u8>, symbol: RawSymbolTokenRef) {
        let encoding: &[u8] = match symbol {
            SymbolId(_) => &[FlexSym::ZERO, 0xE1, 0x00],
            Text(_) => &[FlexSym::ZERO, 0x80],
        };
        output.extend_from_slice_copy(encoding);
    }
}
