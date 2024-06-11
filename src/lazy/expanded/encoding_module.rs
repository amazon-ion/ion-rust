use crate::lazy::expanded::macro_table::MacroTable;
use crate::SymbolTable;

#[derive(Debug, Clone)]
pub struct EncodingModule {
    name: String,
    macro_table: MacroTable,
    symbol_table: SymbolTable,
}

impl EncodingModule {
    pub fn new(name: String, macro_table: MacroTable, symbol_table: SymbolTable) -> Self {
        Self {
            name,
            macro_table,
            symbol_table,
        }
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn macro_table(&self) -> &MacroTable {
        &self.macro_table
    }
    pub fn macro_table_mut(&mut self) -> &mut MacroTable {
        &mut self.macro_table
    }
    pub fn symbol_table(&self) -> &SymbolTable {
        &self.symbol_table
    }
    pub fn symbol_table_mut(&mut self) -> &mut SymbolTable {
        &mut self.symbol_table
    }
    pub fn set_macro_table(&mut self, macro_table: MacroTable) {
        self.macro_table = macro_table;
    }
    pub fn set_symbol_table(&mut self, symbol_table: SymbolTable) {
        self.symbol_table = symbol_table;
    }
}
