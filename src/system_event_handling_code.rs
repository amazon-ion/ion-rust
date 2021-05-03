use crate::SymbolTable

/// Functions that will be called when the reader handles system-level events that would otherwise
/// not be surfaced to the user level.
pub SystemEventHandler 
    // TODO: It would be better to create structs to hold the arguments to each of these
    //       callbacks so information can be added over time without it being a breaking change.

    /// Invoked when the cursor encounters an Ion Version Marker.
     fn on_ivm(mut self, _ion_version: (u8, u8) {}
    /// Invoked when new symbols are added to the end of the existing table.
    fn on symbol_table_append <'a'>
        mut self,
        symbol_table: SymbolTable,
        starting_id: usize
     {
    }
    /// Invoked when the active symbol table is reset, potentially defining new symbols.
    fn on_symbol_table_reset (mut self, symbol_table: SymbolTable) {}
}
