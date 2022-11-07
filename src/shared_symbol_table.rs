use crate::result::illegal_operation;
use crate::IonResult;

#[derive(Debug, Clone, PartialEq, Eq)]
/// Stores [SharedSymbolTable] with the table name, version and imports
/// For more information on [SharedSymbolTable]: https://amzn.github.io/ion-docs/docs/symbols.html#shared-symbol-tables
pub struct SharedSymbolTable {
    name: String,
    version: usize,
    imports: Vec<Option<String>>,
}

impl SharedSymbolTable {
    pub fn new(
        name: String,
        version: Option<usize>,
        imports: Vec<Option<String>>,
    ) -> IonResult<Self> {
        // As per Ion Specification, the name field should be a string with length at least one.
        // If the field has any other value, then materialization of this symbol table must fail.
        if name.is_empty() {
            return illegal_operation("Can not define a shared symbol table with empty name");
        }
        let table_version = match version {
            None => {
                // The version field should be at least 1
                // If the version is missing or has any other value, it is treated as if it were 1
                1
            }
            Some(version_number) if version_number < 1 => {
                // The version field should be at least 1
                // If the version is missing or has any other value, it is treated as if it were 1
                1
            }
            Some(version_number) => version_number,
        };

        Ok(Self {
            name,
            version: table_version,
            imports,
        })
    }

    /// Returns the version of this [SharedSymbolTable]
    pub fn version(&self) -> usize {
        self.version
    }

    /// Returns the name of this [SharedSymbolTable]
    pub fn name(&self) -> &String {
        &self.name
    }
}
