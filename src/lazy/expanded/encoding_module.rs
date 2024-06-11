use crate::lazy::expanded::macro_table::MacroTable;
use crate::SymbolTable;

#[derive(Debug, Clone)]
pub struct EncodingModule {
    name: String,
    version: usize,
    macro_table: MacroTable,
    symbol_table: SymbolTable,
}
