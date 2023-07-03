use crate::result::IonFailure;
use crate::{IonResult, IonType, RawSymbolTokenRef, SymbolTable};

use crate::lazy::binary::raw::lazy_raw_reader::LazyRawReader;
use crate::lazy::binary::raw::lazy_raw_struct::LazyRawStruct;
use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;

use crate::lazy::binary::system::lazy_struct::LazyStruct;
use crate::lazy::binary::system::lazy_value::LazyValue;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::system_stream_item::SystemStreamItem;

// Symbol IDs used for processing symbol table structs
const ION_SYMBOL_TABLE: RawSymbolTokenRef = RawSymbolTokenRef::SymbolId(3);
const IMPORTS: RawSymbolTokenRef = RawSymbolTokenRef::SymbolId(6);
const SYMBOLS: RawSymbolTokenRef = RawSymbolTokenRef::SymbolId(7);

/// A binary reader that only reads each value that it visits upon request (that is: lazily).
///
/// Unlike [`crate::lazy::binary::lazy_reader::LazyReader`], which only exposes values that are part
/// of the application data model, [`LazySystemReader`] also yields Ion version markers
/// (as [`SystemStreamItem::VersionMarker`]) and structs representing a symbol table (as
/// [`SystemStreamItem::SymbolTable`]).
///
/// Each time [`LazySystemReader::next_item`] is called, the reader will advance to the next top-level
/// value in the input stream. Once positioned on a top-level value, users may visit nested values by
/// calling [`LazyValue::read`] and working with the resulting [`crate::lazy::value_ref::ValueRef`],
/// which may contain either a scalar value or a lazy container that may itself be traversed.
///
/// The values that the reader yields ([`LazyValue`],
/// [`crate::lazy::binary::system::lazy_sequence::LazySequence`], and [`LazyStruct`]) are immutable
/// references to the data stream, and remain valid until [`LazySystemReader::next_item`] is
/// called again to advance the reader to the next top level value. This means that these references
/// can be stored, read, and re-read as long as the reader remains on the same top-level value.
/// ```
///# use ion_rs::IonResult;
///# fn main() -> IonResult<()> {
///
/// // Construct an Element and serialize it as binary Ion.
/// use ion_rs::element::Element;
/// use ion_rs::ion_list;
/// use ion_rs::lazy::binary::lazy_reader::LazyReader;
///
/// let element: Element = ion_list! [10, 20, 30].into();
/// let binary_ion = element.to_binary()?;
///
/// let mut lazy_reader = LazyReader::new(&binary_ion)?;
///
/// // Get the first value from the stream and confirm that it's a list.
/// let lazy_list = lazy_reader.expect_next()?.read()?.expect_list()?;
///
/// // Visit the values in the list
/// let mut sum = 0;
/// for lazy_value in &lazy_list {
///     // Read each lazy value in the lazy list as an int (i64) and
///     // add it to the running total
///     sum += lazy_value?.read()?.expect_i64()?;
/// }
///
/// assert_eq!(sum, 60);
///
/// // Note that we can re-read any of the lazy values. Here we'll step into the list again and
/// // read the first child value.
/// let first_int = lazy_list.iter().next().unwrap()?.read()?.expect_i64()?;
/// assert_eq!(first_int, 10);
///
///# Ok(())
///# }
/// ```
pub struct LazySystemReader<'data> {
    raw_reader: LazyRawReader<'data>,
    symbol_table: SymbolTable,
    pending_lst: PendingLst,
}

// If the reader encounters a symbol table in the stream, it will store all of the symbols that
// the table defines in this structure so that they may be applied when the reader next advances.
struct PendingLst {
    is_lst_append: bool,
    symbols: Vec<Option<String>>,
}

impl<'data> LazySystemReader<'data> {
    pub(crate) fn new(ion_data: &'data [u8]) -> LazySystemReader<'data> {
        let raw_reader = LazyRawReader::new(ion_data);
        LazySystemReader {
            raw_reader,
            symbol_table: SymbolTable::new(),
            pending_lst: PendingLst {
                is_lst_append: false,
                symbols: Vec::new(),
            },
        }
    }

    // Returns `true` if the provided [`LazyRawValue`] is a struct whose first annotation is
    // `$ion_symbol_table`.
    fn is_symbol_table_struct(lazy_value: &LazyRawValue) -> IonResult<bool> {
        if lazy_value.ion_type() != IonType::Struct {
            return Ok(false);
        }
        if let Some(symbol_ref) = lazy_value.annotations().next() {
            return Ok(symbol_ref? == ION_SYMBOL_TABLE);
        };
        Ok(false)
    }

    /// Returns the next top-level stream item (IVM, Symbol Table, Value, or Nothing) as a
    /// [`SystemStreamItem`].
    pub fn next_item<'top>(&'top mut self) -> IonResult<SystemStreamItem<'top, 'data>> {
        let LazySystemReader {
            raw_reader,
            symbol_table,
            pending_lst,
        } = self;
        Self::apply_pending_lst(symbol_table, pending_lst);
        let lazy_raw_value = match raw_reader.next()? {
            RawStreamItem::VersionMarker(major, minor) => {
                return Ok(SystemStreamItem::VersionMarker(major, minor));
            }
            RawStreamItem::Value(lazy_raw_value) => lazy_raw_value,
            RawStreamItem::EndOfStream => return Ok(SystemStreamItem::EndOfStream),
        };
        if Self::is_symbol_table_struct(&lazy_raw_value)? {
            Self::process_symbol_table(pending_lst, &lazy_raw_value)?;
            let lazy_struct = LazyStruct {
                raw_struct: LazyRawStruct {
                    value: lazy_raw_value,
                },
                symbol_table,
            };
            return Ok(SystemStreamItem::SymbolTable(lazy_struct));
        }
        let lazy_value = LazyValue::new(symbol_table, lazy_raw_value);
        Ok(SystemStreamItem::Value(lazy_value))
    }

    /// Returns the next value that is part of the application data model, bypassing all encoding
    /// artifacts (IVMs, symbol tables).
    // It would make more sense for this logic to live in the user-level `LazyReader` as a simple
    // loop over LazySystemReader::next. However, due to a limitation in the borrow checker[1], it's
    // not able to determine that calling LazySystemReader::next() multiple times in the same lexical
    // scope is safe. Rust's experimental borrow checker, Polonius, is able to understand it.
    // Until Polonius is available, the method will live here instead.
    // [1]: https://github.com/rust-lang/rust/issues/70255
    pub fn next_value<'top>(&'top mut self) -> IonResult<Option<LazyValue<'top, 'data>>> {
        let LazySystemReader {
            raw_reader,
            symbol_table,
            pending_lst,
        } = self;
        loop {
            Self::apply_pending_lst(symbol_table, pending_lst);
            let lazy_raw_value = match raw_reader.next()? {
                RawStreamItem::VersionMarker(_, _) => continue,
                RawStreamItem::Value(lazy_raw_value) => lazy_raw_value,
                RawStreamItem::EndOfStream => return Ok(None),
            };
            if Self::is_symbol_table_struct(&lazy_raw_value)? {
                // process the symbol table, but do not surface it
                Self::process_symbol_table(pending_lst, &lazy_raw_value)?;
            } else {
                return Ok(Some(LazyValue::new(symbol_table, lazy_raw_value)));
            }
        }
    }

    // If the last stream item the reader visited was a symbol table, its `PendingLst` will
    // contain new symbols that need to be added to the local symbol table.
    fn apply_pending_lst(symbol_table: &mut SymbolTable, pending_lst: &mut PendingLst) {
        // `is_empty()` will be true if the last item was not a symbol table OR if it was a symbol
        // table but did not define new symbols. In either case, there's nothing for us to do.
        if pending_lst.symbols.is_empty() {
            return;
        }
        // If the symbol table's `imports` field had a value of `$ion_symbol_table`, then we're
        // appending the symbols it defined to the end of our existing local symbol table.
        // Otherwise, we need to clear the existing table before appending the new symbols.
        if !pending_lst.is_lst_append {
            // We're setting the symbols list, not appending to it.
            symbol_table.reset();
        }
        // `drain()` empties the pending symbols list
        for symbol in pending_lst.symbols.drain(..) {
            symbol_table.intern_or_add_placeholder(symbol);
        }
        pending_lst.is_lst_append = false;
    }

    // Traverses a symbol table, processing the `symbols` and `imports` fields as needed to
    // populate the `PendingLst`.
    fn process_symbol_table(
        pending_lst: &mut PendingLst,
        symbol_table: &LazyRawValue,
    ) -> IonResult<()> {
        // We've already confirmed this is an annotated struct
        let symbol_table = symbol_table.read()?.expect_struct()?;
        // Assume it's not an LST append unless we found `imports: $ion_symbol_table`
        pending_lst.is_lst_append = false;
        // let mut fields = symbol_table.iter();
        let mut found_symbols_field = false;
        let mut found_imports_field = false;

        for field_result in &symbol_table {
            let field = field_result?;
            if field.name() == SYMBOLS {
                if found_symbols_field {
                    return IonResult::decoding_error(
                        "found symbol table with multiple 'symbols' fields",
                    );
                }
                found_symbols_field = true;
                Self::process_symbols(pending_lst, field.value())?;
            }
            if field.name() == IMPORTS {
                if found_imports_field {
                    return IonResult::decoding_error(
                        "found symbol table with multiple 'imports' fields",
                    );
                }
                found_imports_field = true;
                Self::process_imports(pending_lst, field.value())?;
            }
            // Ignore other fields
        }
        Ok(())
    }

    // Store any strings defined in the `symbols` field in the `PendingLst` for future application.
    fn process_symbols(pending_lst: &mut PendingLst, symbols: &LazyRawValue) -> IonResult<()> {
        if let RawValueRef::List(list) = symbols.read()? {
            for symbol_text in &list {
                if let RawValueRef::String(text) = symbol_text?.read()? {
                    pending_lst.symbols.push(Some(text.to_owned()))
                } else {
                    pending_lst.symbols.push(None)
                }
            }
        }
        // Nulls and non-list values are ignored.
        Ok(())
    }

    // Check for `imports: $ion_symbol_table`.
    fn process_imports(pending_lst: &mut PendingLst, imports: &LazyRawValue) -> IonResult<()> {
        match imports.read()? {
            RawValueRef::Symbol(symbol_ref) => {
                if symbol_ref == RawSymbolTokenRef::SymbolId(3) {
                    pending_lst.is_lst_append = true;
                }
                // Any other symbol is ignored
            }
            // TODO: Implement shared symbol table imports
            RawValueRef::List(_) => {
                return IonResult::decoding_error(
                    "This implementation does not yet support shared symbol table imports",
                );
            }
            _ => {
                // Nulls and other types are ignored
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::system_stream_item::SystemStreamItem;
    use crate::IonResult;

    #[test]
    fn try_it() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
        foo
        bar
        $ion_symbol_table
        baz
        name
        gary
        imports
        hello
        "#,
        )?;
        let mut system_reader = LazySystemReader::new(&ion_data);
        loop {
            match system_reader.next_item()? {
                SystemStreamItem::VersionMarker(major, minor) => {
                    println!("ivm => v{}.{}", major, minor)
                }
                SystemStreamItem::SymbolTable(ref s) => println!("symtab => {:?}", s),
                SystemStreamItem::Value(ref v) => println!("value => {:?}", v.read()?),
                SystemStreamItem::EndOfStream => break,
            }
        }
        Ok(())
    }

    #[test]
    fn sequence_iter() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
        (
          (foo baz baz)
          (1 2 3)
          (a b c)
        )
        "#,
        )?;
        let mut system_reader = LazySystemReader::new(&ion_data);
        loop {
            match system_reader.next_item()? {
                SystemStreamItem::Value(value) => {
                    for value in &value.read()?.expect_sexp()? {
                        println!("{:?}", value?.read()?);
                    }
                }
                SystemStreamItem::EndOfStream => break,
                _ => {}
            }
        }
        Ok(())
    }

    #[test]
    fn struct_iter() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
        {
          foo: 1,
          bar: true,
          baz: null.symbol,
          quux: "hello"
        }
        "#,
        )?;
        let mut system_reader = LazySystemReader::new(&ion_data);
        loop {
            match system_reader.next_item()? {
                SystemStreamItem::Value(value) => {
                    for field in &value.read()?.expect_struct()? {
                        let field = field?;
                        println!("{:?}: {:?},", field.name()?, field.value().read()?);
                    }
                }
                SystemStreamItem::EndOfStream => break,
                _ => {}
            }
        }
        Ok(())
    }
}
