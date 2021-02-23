use crate::SymbolTable;

/// Functions that will be called when the reader handles system-level events that would otherwise
/// not be surfaced to the user level.
pub trait SystemEventHandler {
    // TODO: It would be better to create structs to hold the arguments to each of these
    //       callbacks so information can be added over time without it being a breaking change.

    /// Invoked when the cursor encounters an Ion Version Marker.
    fn on_ivm(&mut self, _ion_version: (u8, u8)) {}
    /// Invoked when new symbols are added to the end of the existing table.
    fn on_symbol_table_append<'a>(
        &'a mut self,
        _symbol_table: &'a SymbolTable,
        _starting_id: usize,
    ) {
    }
    /// Invoked when the active symbol table is reset, potentially defining new symbols.
    fn on_symbol_table_reset<'a>(&'a mut self, _symbol_table: &'a SymbolTable) {}
}
