use crate::result::{illegal_operation, illegal_operation_raw, IonResult};
use crate::shared_symbol_table::SharedSymbolTable;
use std::collections::{BTreeMap, HashMap};

/// A Catalog is a collection of Shared Symbol Tables.
/// For more information about the concept of a catalog,
/// see [the `symbols` section of the specification](https://amazon-ion.github.io/ion-docs/docs/symbols.html#the-catalog).
pub trait Catalog {
    /// Returns the Shared Symbol Table with given table name
    /// If a table with the given name doesn't exists or if the table name is an empty string
    /// then returns an error
    /// If a table with multiple versions exists for the given name then it will return the latest version of table
    fn get_table(&self, name: &str) -> IonResult<SharedSymbolTable>;
    /// Returns the Shared Symbol Table with given table name and version
    /// If a table with given name and version doesn't exists then it returns an error
    fn get_table_with_version(&self, name: &str, version: usize) -> IonResult<SharedSymbolTable>;
}

struct MapCatalog {
    tables_by_name: HashMap<String, BTreeMap<usize, SharedSymbolTable>>,
}

impl MapCatalog {
    pub fn new() -> Self {
        Self {
            tables_by_name: HashMap::new(),
        }
    }
}

impl Catalog for MapCatalog {
    fn get_table(&self, name: &str) -> IonResult<SharedSymbolTable> {
        if name.is_empty() {
            return illegal_operation("symbol table with empty name doesn't exists");
        }

        let versions: &BTreeMap<usize, SharedSymbolTable> =
            self.tables_by_name.get(name).ok_or_else(|| {
                illegal_operation_raw(format!("symbol table with name: {name} does not exist"))
            })?;

        let (_highest_version, table) = versions.iter().rev().next().ok_or_else(|| {
            illegal_operation_raw(format!("symbol table with name: {name} does not exist"))
        })?;
        Ok(table.to_owned())
    }

    fn get_table_with_version(&self, name: &str, version: usize) -> IonResult<SharedSymbolTable> {
        if name.is_empty() {
            return illegal_operation("symbol table with empty name doesn't exists");
        }

        let versions: &BTreeMap<usize, SharedSymbolTable> =
            self.tables_by_name.get(name).ok_or_else(|| {
                illegal_operation_raw(format!("symbol table with name: {name} does not exist"))
            })?;

        let table = versions.get(&version).ok_or_else(|| {
            illegal_operation_raw(format!("symbol table with name: {name} does not exist"))
        })?;
        Ok(table.to_owned())
    }
}

impl MapCatalog {
    /// Adds a Shared Symbol Table with name into the Catalog
    fn put_table(&mut self, table: SharedSymbolTable) {
        match self.tables_by_name.get_mut(table.name()) {
            None => {
                let mut versions: BTreeMap<usize, SharedSymbolTable> = BTreeMap::new();
                let table_name = table.name().to_owned();
                versions.insert(table.version(), table);
                self.tables_by_name.insert(table_name, versions);
            }
            Some(versions) => {
                versions.insert(table.version(), table);
            }
        };
    }
}

#[cfg(test)]
mod tests {
    use crate::catalog::{Catalog, MapCatalog};
    use crate::shared_symbol_table::SharedSymbolTable;
    use crate::IonResult;

    #[test]
    fn get_table_with_name_test() -> IonResult<()> {
        let sst = SharedSymbolTable::new(
            "T".to_string(),
            1,
            vec![Some("true".to_string()), Some("false".to_string())],
        )?;
        let mut catalog = MapCatalog::new();
        catalog.put_table(sst);

        // get table with name "T"
        assert!(catalog.get_table("T").is_ok());

        // verify that table with name "S" doesn't exist
        assert!(catalog.get_table("S").is_err());
        Ok(())
    }

    #[test]
    fn get_table_with_version_test() -> IonResult<()> {
        let sst = SharedSymbolTable::new(
            "T".to_string(),
            1,
            vec![Some("true".to_string()), Some("false".to_string())],
        )?;
        let mut catalog = MapCatalog::new();
        catalog.put_table(sst);

        // get table with name "T" and version 1
        assert!(catalog.get_table_with_version("T", 1).is_ok());

        // verify that table with name "T" and version 2 doesn't exist
        assert!(catalog.get_table_with_version("T", 2).is_err());
        Ok(())
    }
}
