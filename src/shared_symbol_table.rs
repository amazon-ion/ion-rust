use crate::element::{Element, Sequence};
use crate::result::IonFailure;
use crate::IonResult;
use crate::{Int, IonError, Symbol};

#[derive(Debug, Clone, PartialEq, Eq)]
/// Stores [`SharedSymbolTable`] with the table name, version and imports
/// For more information on [`SharedSymbolTable`], see:
/// <https://amazon-ion.github.io/ion-docs/docs/symbols.html#shared-symbol-tables>
pub struct SharedSymbolTable {
    name: String,
    version: usize,
    symbols: Vec<Symbol>,
}

impl SharedSymbolTable {
    pub fn new(name: String, version: usize, imports: Vec<Symbol>) -> IonResult<Self> {
        // As per Ion Specification, the name field should be a string with length at least one.
        // If the field has any other value, then materialization of this symbol table must fail.
        if name.is_empty() {
            return IonResult::illegal_operation(
                "shared symbol table with empty name is not allowed",
            );
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

    /// Returns the symbols defined in this [`SharedSymbolTable`]
    pub fn symbols(&self) -> &[Symbol] {
        &self.symbols
    }
}

/// Constructs a [shared symbol table]( https://amazon-ion.github.io/ion-docs/docs/symbols.html#shared-symbol-tables) using Ion reader.
/// Below is an example of a shared symbol table:
///
/// ```ignore
/// $ion_shared_symbol_table::
/// {
///   name: "com.amazon.ols.symbols.offer",
///   version: 1,
///   imports: // For informational purposes only.
///   [
///     { name:"..." , version:1 },
///     // ...
///   ],
///   symbols:
///   [
///     "fee", "fie", "foe", /* ... */ "hooligan"
///   ]
/// }
/// ```

impl TryFrom<Element> for SharedSymbolTable {
    type Error = IonError;

    fn try_from(sst_element: Element) -> Result<Self, Self::Error> {
        let sst_struct = sst_element
            .as_struct()
            .ok_or(IonError::illegal_operation(format!(
                "expected a struct, but found a(n) {}",
                sst_element.ion_type()
            )))?
            .to_owned();
        let name_field = sst_struct
            .get("name")
            .ok_or_else(|| IonError::illegal_operation("missing a 'name' field"))?;
        let name = name_field.as_string().ok_or_else(|| {
            IonError::illegal_operation(format!(
                "expected the 'name' field to be a string, but found a(n) {}",
                name_field
            ))
        })?;
        let mut version = sst_struct
            .get("version")
            .and_then(|i| i.as_int())
            .unwrap_or(&Int::from(1))
            .expect_i64()? as usize;
        if version < 1 {
            version = 1;
        }
        let symbols: Vec<Symbol> = sst_struct
            .get("symbols")
            .and_then(|s| s.as_sequence())
            .unwrap_or(&Sequence::from(vec![])) // If the `symbols` field is missing or has any other type, it is treated as if it were an empty list.
            .elements()
            .map(|sym| {
                sym.as_string()
                    .map(Symbol::owned)
                    .unwrap_or(Symbol::unknown_text()) // adds undefined symbol IDs("gaps) for null or non symbol elements
            })
            .collect();
        SharedSymbolTable::new(name.to_string(), version, symbols)
    }
}

#[cfg(test)]
mod shared_symbol_table_tests {
    use crate::element::Element;
    use crate::shared_symbol_table::SharedSymbolTable;
    use crate::{IonResult, Symbol};

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
        let sst: SharedSymbolTable = Element::read_one(ion_data.as_bytes())?.try_into()?;
        assert_eq!(sst.name(), "com.amazon.test.symbols");
        assert_eq!(sst.version(), 1);
        assert_eq!(sst.symbols().len(), 3);
        assert_eq!(sst.symbols()[0], Symbol::owned("fee"));
        assert_eq!(sst.symbols()[1], Symbol::owned("fie"));
        assert_eq!(sst.symbols()[2], Symbol::owned("foe"));
        Ok(())
    }
}
