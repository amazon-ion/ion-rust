#![allow(non_camel_case_types)]

use crate::lazy::any_encoding::AnyEncoding;
use crate::lazy::decoder::Decoder;
use crate::lazy::encoding::{BinaryEncoding_1_0, TextEncoding_1_0, TextEncoding_1_1};
use crate::lazy::expanded::{ExpandedValueRef, ExpandingReader, LazyExpandedValue};
use crate::lazy::streaming_raw_reader::{IonInput, StreamingRawReader};
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::value::LazyValue;
use crate::result::IonFailure;
use crate::{IonResult, IonType, RawSymbolRef, SymbolTable};

// Symbol IDs used for processing symbol table structs
const ION_SYMBOL_TABLE: RawSymbolRef = RawSymbolRef::SymbolId(3);
const IMPORTS: RawSymbolRef = RawSymbolRef::SymbolId(6);
const SYMBOLS: RawSymbolRef = RawSymbolRef::SymbolId(7);

/// A binary reader that only reads each value that it visits upon request (that is: lazily).
///
/// Unlike [`crate::lazy::reader::IonReader`], which only exposes values that are part
/// of the application data model, [`SystemReader`] also yields Ion version markers
/// (as [`SystemStreamItem::VersionMarker`]) and structs representing a symbol table (as
/// [`SystemStreamItem::SymbolTable`]).
///
/// Each time [`SystemReader::next_item`] is called, the reader will advance to the next top-level
/// value in the input stream. Once positioned on a top-level value, users may visit nested values by
/// calling [`LazyValue::read`] and working with the resulting [`crate::lazy::value_ref::ValueRef`],
/// which may contain either a scalar value or a lazy container that may itself be traversed.
///
/// The values that the reader yields ([`LazyValue`],
/// [`LazyList`](crate::LazyList), [`LazySExp`](crate::LazySExp) and [`LazyStruct`](crate::LazyStruct)), are immutable references to the data stream,
/// and remain valid until [`SystemReader::next_item`] is called again to advance the reader to
/// the next top level value. This means that these references can be stored, read, and re-read as
/// long as the reader remains on the same top-level value.
/// ```
///# use ion_rs::IonResult;
///# #[cfg(feature="experimental-reader-writer")]
///# fn main() -> IonResult<()> {
///
/// // Construct an Element and serialize it as binary Ion.
/// use ion_rs::{Element, ion_list};
/// use ion_rs::v1_0::{Binary, BinaryReader};
///
/// let element: Element = ion_list! [10, 20, 30].into();
/// let binary_ion = element.encode_as(Binary)?;
///
/// let mut lazy_reader = BinaryReader::new(binary_ion)?;
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
///# #[cfg(not(feature = "experimental-reader-writer"))]
///# fn main() -> IonResult<()> { Ok(()) }
/// ```
pub struct SystemReader<Encoding: Decoder, Input: IonInput> {
    pub(crate) expanding_reader: ExpandingReader<Encoding, Input>,
}

pub type SystemBinaryReader_1_0<Input> = SystemReader<BinaryEncoding_1_0, Input>;
pub type SystemTextReader_1_0<Input> = SystemReader<TextEncoding_1_0, Input>;
pub type SystemTextReader_1_1<Input> = SystemReader<TextEncoding_1_1, Input>;

pub type SystemAnyReader<Input> = SystemReader<AnyEncoding, Input>;

// If the reader encounters a symbol table in the stream, it will store all of the symbols that
// the table defines in this structure so that they may be applied when the reader next advances.
#[derive(Default)]
pub(crate) struct PendingLst {
    pub(crate) has_changes: bool,
    pub(crate) is_lst_append: bool,
    pub(crate) symbols: Vec<Option<String>>,
}

impl PendingLst {
    pub fn new() -> Self {
        Self {
            has_changes: false,
            is_lst_append: false,
            symbols: Vec::new(),
        }
    }
}

impl<Input: IonInput> SystemAnyReader<Input> {
    pub fn new(ion_data: Input) -> SystemAnyReader<Input> {
        let raw_reader = StreamingRawReader::new(AnyEncoding, ion_data);
        let expanding_reader = ExpandingReader::new(raw_reader);
        SystemReader { expanding_reader }
    }
}

impl<Input: IonInput> SystemBinaryReader_1_0<Input> {
    pub fn new(ion_data: Input) -> SystemBinaryReader_1_0<Input> {
        let raw_reader = StreamingRawReader::new(BinaryEncoding_1_0, ion_data);
        let expanding_reader = ExpandingReader::new(raw_reader);
        SystemReader { expanding_reader }
    }
}

impl<Input: IonInput> SystemTextReader_1_1<Input> {
    pub fn new(ion_data: Input) -> SystemTextReader_1_1<Input> {
        let raw_reader = StreamingRawReader::new(TextEncoding_1_1, ion_data);
        let expanding_reader = ExpandingReader::new(raw_reader);
        SystemReader { expanding_reader }
    }
}

impl<Encoding: Decoder, Input: IonInput> SystemReader<Encoding, Input> {
    // Returns `true` if the provided [`LazyRawValue`] is a struct whose first annotation is
    // `$ion_symbol_table`.
    pub fn is_symbol_table_struct(
        lazy_value: &'_ LazyExpandedValue<'_, Encoding>,
    ) -> IonResult<bool> {
        if lazy_value.ion_type() != IonType::Struct {
            return Ok(false);
        }
        if let Some(symbol_ref) = lazy_value.annotations().next() {
            return Ok(symbol_ref?.matches_sid_or_text(3, "$ion_symbol_table"));
        };
        Ok(false)
    }

    /// Returns the next top-level stream item (IVM, Symbol Table, Value, or Nothing) as a
    /// [`SystemStreamItem`].
    pub fn next_item(&mut self) -> IonResult<SystemStreamItem<'_, Encoding>> {
        self.expanding_reader.next_item()
    }

    /// Returns the next value that is part of the application data model, bypassing all encoding
    /// artifacts (IVMs, symbol tables).
    pub fn next_value(&mut self) -> IonResult<Option<LazyValue<Encoding>>> {
        self.expanding_reader.next_value()
    }

    // If the last stream item the reader visited was a symbol table, its `PendingLst` will
    // contain new symbols that need to be added to the local symbol table.
    fn apply_pending_lst(symbol_table: &mut SymbolTable, pending_lst: &mut PendingLst) {
        // If the symbol table's `imports` field had a value of `$ion_symbol_table`, then we're
        // appending the symbols it defined to the end of our existing local symbol table.
        // Otherwise, we need to clear the existing table before appending the new symbols.
        if pending_lst.is_lst_append {
            if pending_lst.symbols.is_empty() {
                return;
            }
        } else {
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
    pub(crate) fn process_symbol_table(
        pending_lst: &mut PendingLst,
        symbol_table: &LazyExpandedValue<'_, Encoding>,
    ) -> IonResult<()> {
        // We've already confirmed this is an annotated struct
        let symbol_table = symbol_table.read()?.expect_struct()?;

        let mut found_symbols_field = false;
        let mut found_imports_field = false;

        for field_result in symbol_table.iter() {
            let field = field_result?;
            if field.name().read_raw()?.matches_sid_or_text(7, "symbols") {
                if found_symbols_field {
                    return IonResult::decoding_error(
                        "found symbol table with multiple 'symbols' fields",
                    );
                }
                found_symbols_field = true;
                Self::process_symbols(pending_lst, field.value())?;
            }
            if field.name().read_raw()?.matches_sid_or_text(6, "imports") {
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
    fn process_symbols(
        pending_lst: &mut PendingLst,
        symbols: LazyExpandedValue<'_, Encoding>,
    ) -> IonResult<()> {
        if let ExpandedValueRef::List(list) = symbols.read()? {
            for symbol_text_result in list.iter() {
                if let ExpandedValueRef::String(str_ref) = symbol_text_result?.read()? {
                    pending_lst.symbols.push(Some(str_ref.text().to_owned()))
                } else {
                    pending_lst.symbols.push(None)
                }
            }
        }
        // Nulls and non-list values are ignored.
        Ok(())
    }

    // Check for `imports: $ion_symbol_table`.
    fn process_imports(
        pending_lst: &mut PendingLst,
        imports: LazyExpandedValue<'_, Encoding>,
    ) -> IonResult<()> {
        match imports.read()? {
            ExpandedValueRef::Symbol(symbol_ref) => {
                if symbol_ref.matches_sid_or_text(3, "$ion_symbol_table") {
                    pending_lst.is_lst_append = true;
                }
                // Any other symbol is ignored
            }
            // TODO: Implement shared symbol table imports
            ExpandedValueRef::List(_) => {
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
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::decoder::RawVersionMarker;
    use crate::lazy::system_stream_item::SystemStreamItem;
    use crate::IonResult;

    use super::*;

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
        let mut system_reader = SystemBinaryReader_1_0::new(ion_data);
        loop {
            match system_reader.next_item()? {
                SystemStreamItem::VersionMarker(marker) => {
                    println!("ivm => v{}.{}", marker.major(), marker.minor())
                }
                SystemStreamItem::SymbolTable(ref s) => println!("symtab => {:?}", s),
                SystemStreamItem::Value(ref v) => println!("value => {:?}", v.read()?),
                SystemStreamItem::EndOfStream(_) => break,
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
        let mut system_reader = SystemBinaryReader_1_0::new(ion_data);
        loop {
            match system_reader.next_item()? {
                SystemStreamItem::Value(value) => {
                    for value in &value.read()?.expect_sexp()? {
                        println!("{:?}", value?.read()?);
                    }
                }
                SystemStreamItem::EndOfStream(_) => break,
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
        let mut system_reader = SystemBinaryReader_1_0::new(ion_data);
        loop {
            match system_reader.next_item()? {
                SystemStreamItem::Value(value) => {
                    for field in &value.read()?.expect_struct()? {
                        let field = field?;
                        println!("{:?}: {:?},", field.name()?, field.value().read()?);
                    }
                }
                SystemStreamItem::EndOfStream(_) => break,
                _ => {}
            }
        }
        Ok(())
    }
}
