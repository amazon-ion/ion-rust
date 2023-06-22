use crate::element::reader::ElementReader;
use crate::reader::Reader;
use crate::result::{illegal_operation, illegal_operation_raw};
use crate::types::IntAccess;
use crate::{Int, IonResult};

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

    /**
       Constructs a shared symbol table using Ion reader.
       Below is an example of a shared symbol table:
       $ion_shared_symbol_table::
       {
         name: "com.amazon.ols.symbols.offer",
         version: 1,
         imports: // For informational purposes only.
         [
           { name:"..." , version:1 },
           // ...
         ],
         symbols:
         [
           "fee", "fie", "foe", /* ... */ "hooligan"
         ]
       }
    */
    pub fn new_shared_symbol_table_using_reader(reader: &mut Reader) -> IonResult<Self> {
        return if let Some(sst_element) = reader.read_next_element()? {
            let sst_struct = sst_element
                .as_struct()
                .ok_or(illegal_operation_raw(format!(
                    "Expected struct found {}",
                    sst_element.ion_type()
                )))?
                .to_owned();
            let name =
                sst_struct
                    .get("name")
                    .and_then(|i| i.as_string())
                    .ok_or(illegal_operation_raw(
                        "Unable to process name of shared symbol table",
                    ))?;
            let mut version = sst_struct
                .get("version")
                .and_then(|i| i.as_int())
                .unwrap_or(&Int::from(1))
                .as_i64()
                .unwrap() as usize;
            if version < 1 {
                version = 1;
            }
            let symbols: Vec<Option<String>> = sst_struct
                .get("symbols")
                .and_then(|i| i.as_sequence())
                .map(|s| {
                    s.elements()
                        .map(|sym| sym.as_text().map(|text| text.to_string()))
                })
                .ok_or(illegal_operation_raw(
                    "Unable to process symbols of shared symbol table",
                ))?
                .collect();
            SharedSymbolTable::new(name.to_string(), version, symbols)
        } else {
            illegal_operation("Unable to read a shared symbol table struct")
        };
    }

    /// Returns the version of this [`SharedSymbolTable`]
    pub fn version(&self) -> usize {
        self.version
    }

    /// Returns the name of this [`SharedSymbolTable`]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the symbols defined in this [`SharedSymbolTable`]
    pub fn symbols(&self) -> &Vec<Option<String>> {
        &self.symbols
    }
}

#[cfg(test)]
mod shared_symbol_table_tests {
    use crate::reader::ReaderBuilder;
    use crate::shared_symbol_table::SharedSymbolTable;
    use crate::IonResult;

    #[test]
    fn shared_symbol_table_read_test() -> IonResult<()> {
        let ion_data = r#"
            $ion_shared_symbol_table::
            {
             name: "com.amazon.test.symbols",
             version: 1,
             // For informational purposes only.
             imports: [],
             symbols:
             [
               "fee", "fie", "foe"
             ]
            }
        "#;
        let mut reader = ReaderBuilder::new().build(ion_data.as_bytes())?;
        let sst = SharedSymbolTable::new_shared_symbol_table_using_reader(&mut reader)?;
        assert_eq!(sst.name(), "com.amazon.test.symbols");
        assert_eq!(sst.version(), 1);
        assert_eq!(sst.symbols().len(), 3);
        assert_eq!(sst.symbols()[0], Some("fee".to_string()));
        assert_eq!(sst.symbols()[1], Some("fie".to_string()));
        assert_eq!(sst.symbols()[2], Some("foe".to_string()));
        Ok(())
    }
}
