use crate::result::illegal_operation;
use crate::IonResult;

#[derive(Debug, Clone, PartialEq, Eq)]
/// Stores [`SharedSymbolTable`] with the table name, version and imports
/// For more information on [`SharedSymbolTable`], see:
/// <https://amazon-ion.github.io/ion-docs/docs/symbols.html#shared-symbol-tables>
pub struct SharedSymbolTable {
    name: String,
    version: usize,
    symbols: Vec<Option<String>>,
}

impl SharedSymbolTable {
    pub fn new(name: String, version: usize, imports: Vec<Option<String>>) -> IonResult<Self> {
        // As per Ion Specification, the name field should be a string with length at least one.
        // If the field has any other value, then materialization of this symbol table must fail.
        if name.is_empty() {
            return illegal_operation("shared symbol table with empty name is not allowed");
        }

        Ok(Self {
            name,
            version,
            symbols: imports,
        })
    }

    /// Returns the version of this [`SharedSymbolTable`]
    pub fn version(&self) -> usize {
        self.version
    }

    /// Returns the name of this [`SharedSymbolTable`]
    pub fn name(&self) -> &str {
        &self.name
    }
}
