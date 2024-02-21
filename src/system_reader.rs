use delegate::delegate;
use std::ops::Range;

use crate::binary::non_blocking::raw_binary_reader::RawBinaryReader;
use crate::catalog::{Catalog, EmptyCatalog};
use crate::constants::v1_0::{system_symbol_ids, SYSTEM_SYMBOLS};
use crate::ion_reader::IonReader;
use crate::raw_reader::{Expandable, RawReader, RawStreamItem};
use crate::raw_symbol_token::RawSymbolToken;
use crate::result::{IonError, IonFailure, IonResult};
use crate::symbol_table::SymbolTable;
use crate::system_reader::LstPosition::*;
use crate::IonType;
use crate::{Blob, Clob, Decimal, Int, Str, Symbol, Timestamp};

/// Tracks where the [SystemReader] is in the process of reading a local symbol table.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum LstPosition {
    /// The enum variants below indicate that the reader is...

    /// Not positioned at or inside of an LST. Examples include when the reader is
    /// positioned over:
    /// * The start of the stream (i.e. nothing)
    /// * An IVM
    /// * A user value
    NotReadingAnLst,

    /// Positioned on an $ion_symbol_table but have not yet stepped in
    AtLstStart,

    /// Inside an LST but between fields at depth 1. This occurs when:
    /// * the reader has stepped into the LST but has not yet read a field
    /// * after the reader has stepped out of a field in the LST and is back at depth 1
    BetweenLstFields,

    /// Inside an $ion_symbol_table and positioned at the `imports` field but have not yet stepped in
    AtLstImports,

    /// Inside the `imports` field
    ProcessingLstImports,

    /// Positioned on an LST import but have not yet stepped in
    AtLstImportStart,

    /// Inside an LST import but between fields at depth 2. This occurs when:
    /// * the reader has stepped into the LST import but has not yet read a field
    /// * after the reader has stepped out of a field in the LST import and is back at depth 2
    BetweenLstImportFields,

    /// Positioned on the name field of an import
    AtImportName,

    /// Positioned on the version field of an import
    AtImportVersion,

    /// Positioned on the max_id field of an import
    AtImportMaxId,

    /// Inside an $ion_symbol_table and positioned at the `symbols` field but have not yet stepped in
    AtLstSymbols,

    /// Inside the `symbols` field
    ProcessingLstSymbols,

    /// Inside an $ion_symbol_table and positioned at a field whose behavior is not defined by the
    /// spec.
    AtLstOpenContent,

    /// Inside an $ion_symbol_table but processing "open" content--data defined by the user but not
    /// required or recognized by the spec.
    ProcessingLstOpenContent,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
/// Raw stream elements that a SystemReader may encounter.
pub enum SystemStreamItem {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    /// A non-null Ion value that is part of an encoded local symbol table.
    /// This includes:
    /// * Top-level structs annotated with $ion_symbol_table::
    /// * Any fields nested inside such structs, but especially `imports` and `symbols`
    SymbolTableValue(IonType),
    /// A null Ion value that is part of an encoded local symbol table.
    SymbolTableNull(IonType),
    /// A non-null Ion value and its corresponding Ion data type.
    Value(IonType),
    /// A null Ion value and its corresponding Ion data type.
    Null(IonType),
    /// Indicates that the reader is not positioned over anything. This can happen:
    /// * before the reader has begun processing the stream.
    /// * after the reader has stepped into a container, but before the reader has called next()
    /// * after the reader has stepped out of a container, but before the reader has called next()
    /// * after the reader has read the last item in a container
    Nothing,
}

// Stores information that has been read from a local symbol table that is currently being
// processed.
struct LstData {
    // The reader's position within the LST.
    state: LstPosition,
    // Whether this LST's symbols should be appended to the current symbol table.
    // If this is false, the current symbol table will be cleared before the new symbols are
    // added to the table. `is_append` is only set to true if the LST's `imports` field has
    // the symbol `$ion_symbol_table` as its value.
    is_append: bool,
    // All of the new symbols being defined in this LST. These pending symbols are buffered in a Vec
    // because the `symbols` field of the LST can appear before the `imports` field but the `imports`
    // field MUST be processed first.
    symbols: Vec<Option<String>>,
    // All of the symbols imported from a shared symbol table. These fields MUST be processed before
    // the LST append symbols.
    imported_symbols: Vec<Option<String>>,
    // Current import related information that will be used when processing shared symbol table from catalog
    current_import_name: Option<String>,
    current_import_version: Option<usize>,
    current_import_max_id: Option<usize>,
    // Whether we've already encountered a `symbols` field.
    has_found_symbols: bool,
    has_found_imports: bool,
}

impl LstData {
    fn new() -> LstData {
        LstData {
            is_append: false,
            symbols: vec![],
            imported_symbols: vec![],
            current_import_name: None,
            state: NotReadingAnLst,
            has_found_symbols: false,
            has_found_imports: false,
            current_import_version: None,
            current_import_max_id: None,
        }
    }
}

/// A streaming Ion reader that:
/// * maintains a symbol table
/// * processes local symbol tables as they are encountered
/// * can resolve symbol IDs into their associated text
/// * does NOT filter out encoding data like IVMs and symbol tables
///
/// SystemReader itself is format-agnostic; all format-specific logic is handled by the
/// wrapped [RawReader] implementation.
///
/// If the user skips over some or all of a local symbol table in the stream (via either `next()`
/// or `step_out()`), the SystemReader will automatically process the rest of the local symbol
/// table before advancing. This allows users to visit Ion values used to encode local symbol tables
/// without also being responsible for interpreting them (as they would with an implementation of
/// the [RawReader] trait.)
pub struct SystemReader<R: RawReader> {
    raw_reader: R,
    // The current symbol table
    symbol_table: SymbolTable,
    // Information about the local symbol table we're currently reading, if any
    lst: LstData,
    current_item: SystemStreamItem,
    catalog: Box<dyn Catalog>,
}

impl<R: RawReader> SystemReader<R> {
    pub fn new(raw_reader: R) -> SystemReader<R> {
        SystemReader {
            raw_reader,
            symbol_table: SymbolTable::new(),
            lst: LstData::new(),
            current_item: SystemStreamItem::Nothing,
            catalog: Box::<EmptyCatalog>::default(),
        }
    }

    pub fn with_catalog(raw_reader: R, catalog: Box<dyn Catalog>) -> SystemReader<R> {
        SystemReader {
            raw_reader,
            symbol_table: SymbolTable::new(),
            lst: LstData::new(),
            current_item: SystemStreamItem::Nothing,
            catalog,
        }
    }

    // Returns true if the raw reader is positioned over a top-level struct whose first annotation
    // is $ion_symbol_table.
    fn current_value_is_symbol_table(&self) -> IonResult<bool> {
        let on_top_level_struct =
            self.raw_reader.current() == RawStreamItem::Value(IonType::Struct) && self.depth() == 0;
        if !on_top_level_struct {
            return Ok(false);
        }
        if let Some(first_annotation_result) = self.raw_annotations().next() {
            let first_annotation = first_annotation_result?;
            return Ok(first_annotation.matches(
                system_symbol_ids::ION_SYMBOL_TABLE,
                SYSTEM_SYMBOLS[system_symbol_ids::ION_SYMBOL_TABLE].unwrap(),
            ));
        }
        Ok(false)
    }

    // When next() is called, process any LST-related data in the reader's current position before
    // advancing to the next value. This may involve stepping into and processing container values.
    fn before_next(&mut self) -> IonResult<()> {
        match self.lst.state {
            AtLstStart => {
                // If the reader is positioned over the beginning of an LST when next() is called,
                // we need to process the entire LST instead of just skipping to the next value.
                self.step_in()?;
                self.finish_reading_current_lst()?;
            }
            BetweenLstFields => {
                // If the reader is at depth=1 inside an LST but not positioned over a value,
                // do nothing and allow the call to next() to advance the cursor.
            }
            AtLstImports | AtLstSymbols | AtLstOpenContent => {
                // If the reader is positioned over an LST field at depth=1 when next() is called,
                // we need to process the value of that field instead of just skipping
                // to the next field.

                // If the field value is a scalar, it will have already been processed the last time
                // that the reader advanced. (See the 'after_next()` method.) If it's a
                // list, however, we need to process it now. (Other container types in LST fields
                // are ignored.)
                if self
                    .raw_reader
                    .ion_type()
                    .map(|t| t == IonType::List)
                    .unwrap_or(false)
                {
                    self.step_in()?;
                    self.finish_reading_current_level()?;
                }
            }
            AtLstImportStart => {
                // If the reader is positioned over the beginning of an LST import when next() is called,
                // we need to process the entire LST import instead of just skipping to the next value.
                self.step_in()?;
                self.finish_reading_current_level()?;
            }
            AtImportName => {
                // We're inside a shared symbol table import processing `name`, otherwise do nothing for open content.
                if let Some(IonType::String) = self.raw_reader.ion_type() {
                    self.lst.current_import_name = Some(self.raw_reader.read_str()?.to_string());
                }
                self.lst.state = BetweenLstImportFields;
            }
            AtImportVersion => {
                // We're inside a shared symbol table import processing either `version` otherwise do nothing for open content.
                if let Some(IonType::Int) = self.raw_reader.ion_type() {
                    self.lst.current_import_version = Some(self.raw_reader.read_i64()? as usize);
                }
                self.lst.state = BetweenLstImportFields;
            }
            AtImportMaxId => {
                // We're inside a shared symbol table import processing either `max_id` otherwise do nothing for open content.
                if let Some(IonType::Int) = self.raw_reader.ion_type() {
                    let max_id = self.raw_reader.read_i64()?;
                    if max_id < 0 {
                        return IonResult::decoding_error(
                            "symbol table import should have max_id greater than or equal to zero.",
                        );
                    }
                    self.lst.current_import_max_id = Some(max_id as usize);
                }
            }
            _ => {
                // Allow values at depths > 1 to be skipped.
            }
        }

        Ok(())
    }

    // After the raw reader is advanced by a call to `next()`, take stock of the reader's new
    // position. Return a SystemStreamItem indicating whether the reader is now positioned over
    // a user value or part of a local symbol table.
    fn after_next(&mut self, ion_type: IonType, is_null: bool) -> IonResult<SystemStreamItem> {
        // At this point, `self.lst.state` represents the reader's _previous_ position.
        // We have now advanced to the next value at the same depth and need to update
        // `self.lst.state` to reflect that.
        match self.lst.state {
            NotReadingAnLst | AtLstStart => {
                // If we're at the top level and the next element we encounter is a struct whose
                // first annotation is $ion_symbol_table, then set the state to `AtLstStart`
                if self.current_value_is_symbol_table()? {
                    self.lst.state = AtLstStart;
                } else {
                    // Otherwise, it's just a plain user value.
                    // This is the only branch in this method that returns a user value.
                    self.lst.state = NotReadingAnLst;
                    return if is_null {
                        Ok(SystemStreamItem::Null(ion_type))
                    } else {
                        Ok(SystemStreamItem::Value(ion_type))
                    };
                }
            }
            AtLstImports | AtLstSymbols | AtLstOpenContent | BetweenLstFields => {
                // The reader is inside the LST at depth=1. Figure out which field we're on and
                // update the state.
                match self.raw_reader.field_name() {
                    Ok(field_name_token) => {
                        if field_name_token.matches(system_symbol_ids::IMPORTS, "imports") {
                            if self.lst.has_found_imports {
                                return IonResult::decoding_error(
                                    "symbol table had multiple `imports` fields",
                                );
                            }
                            self.lst.has_found_imports = true;
                            self.move_to_lst_imports_field(ion_type)?;
                        } else if field_name_token.matches(system_symbol_ids::SYMBOLS, "symbols") {
                            if self.lst.has_found_symbols {
                                return IonResult::decoding_error(
                                    "symbol table had multiple `symbols` fields",
                                );
                            }
                            self.lst.has_found_symbols = true;
                            self.lst.state = AtLstSymbols;
                        } else {
                            // This field has no effect on our handling of the LST.
                            self.lst.state = AtLstOpenContent;
                        }
                    }
                    Err(IonError::IllegalOperation { .. }) => {
                        // TODO: Check this with self.raw_reader.current() == RawStreamItem::Nothing instead
                        // There's no field name; we're between fields.
                        self.lst.state = BetweenLstFields;
                    }
                    Err(error) => panic!(
                        "the RawReader returned an unexpected error from `field_name()`: {error:?}"
                    ),
                }
            }
            ProcessingLstImports => {
                // We're in the `imports` list processing a shared symbol table import.
                if let (IonType::Struct, false) = (ion_type, is_null) {
                    self.lst.state = AtLstImportStart;
                }
            }
            AtLstImportStart | BetweenLstImportFields => {
                match self.raw_reader.field_name() {
                    Ok(field_name_token) => {
                        let field_name = match field_name_token {
                            RawSymbolToken::SymbolId(sid) => self.symbol_table.text_for(sid),
                            RawSymbolToken::Text(ref text) => Some(text.as_str()),
                        };
                        if let Some(field_name) = field_name {
                            match field_name {
                                "name" => self.lst.state = AtImportName,
                                "version" => self.lst.state = AtImportVersion,
                                "max_id" => self.lst.state = AtImportMaxId,
                                _ => {}
                            }
                        }
                    }
                    Err(IonError::IllegalOperation { .. }) => {
                        // We're between the fields of LST import; do nothing.
                    }
                    Err(error) => panic!(
                        "the RawReader returned an unexpected error from `field_name()`: {error:?}"
                    ),
                }
            }
            ProcessingLstSymbols => {
                // We're in the `symbols` list.
                if let (IonType::String, false) = (ion_type, is_null) {
                    self.lst
                        .symbols
                        .push(Some(self.raw_reader.read_str()?.to_string()))
                } else {
                    // Non-string values and nulls are treated as symbols with unknown text.
                    self.lst.symbols.push(None);
                }
            }
            ProcessingLstOpenContent => {
                // We were in open content before and haven't stepped out yet. Do nothing.
            }
            _ => {
                // For all the other states that process an import; do nothing as they are already processed in before_next()
            }
        };

        if is_null {
            Ok(SystemStreamItem::SymbolTableNull(ion_type))
        } else {
            Ok(SystemStreamItem::SymbolTableValue(ion_type))
        }
    }

    // Called when the system reader advances to the `imports` field of an LST.
    fn move_to_lst_imports_field(&mut self, ion_type: IonType) -> IonResult<()> {
        self.lst.state = AtLstImports;
        match ion_type {
            IonType::Symbol => {
                // If the `imports` field value is the symbol '$ion_symbol_table', then this is an
                // LST append.
                if self
                    .raw_reader
                    .read_symbol()?
                    .matches(system_symbol_ids::ION_SYMBOL_TABLE, "$ion_symbol_table")
                {
                    self.lst.is_append = true;
                }
            }
            IonType::List => {
                // Once this is supported, this branch will do nothing because the list either
                // be processed when the user steps into/through it or when they try to skip over
                // it, not when it's first encountered. For now though, we fail because this
                // feature is not yet supported.
            }
            _ => {
                // Non-list, non-symbol values for the `imports` field are ignored.
            }
        };
        Ok(())
    }

    fn process_ivm(&mut self, major: u8, minor: u8) -> IonResult<SystemStreamItem> {
        if self.depth() > 0 {
            return IonResult::decoding_error("Encountered an IVM at a depth > 0");
        }

        self.lst.state = NotReadingAnLst;
        self.symbol_table.reset();
        Ok(SystemStreamItem::VersionMarker(major, minor))
    }

    // When the reader steps out of an LST, this method will add the new symbols we've been
    // buffering in `self.lst.symbols` to the current symbol table.
    fn add_lst_symbols_to_current_symbol_table(&mut self) {
        if !self.lst.is_append {
            // This is not an append. Clear the current symbol table.
            self.symbol_table.reset();
        }

        // This for loop consumes the `String` values, clearing `self.lst.imported_symbols`
        for value in self.lst.imported_symbols.drain(..) {
            self.symbol_table.add_symbol_or_placeholder(value);
        }
        // This for loop consumes the `String` values, clearing `self.lst.symbols`.
        for value in self.lst.symbols.drain(..) {
            if let Some(text) = value {
                // This symbol has defined text. Add it to the symbol table.
                self.symbol_table.intern(text);
            } else {
                // This symbol was a null or non-string value. Add a placeholder.
                self.symbol_table.add_placeholder();
            }
        }
    }

    // The SystemReader can skip any user-level value, but cannot skip Local Symbol Tables (LSTs) in
    // the stream. If the application tries to advance the reader beyond the LST using `next()` or
    // `step_out()`, the reader must first consume the rest of the LST so it can add any imported
    // or newly declared symbols to the current symbol table.
    // When this method returns, the reader will be positioned just after the LST and the current
    // symbol table will have been updated accordingly. The caller must then call `next()` to
    // advance to the next item in the stream.
    fn finish_reading_current_lst(&mut self) -> IonResult<()> {
        while self.depth() > 0 {
            self.finish_reading_current_level()?;
            self.step_out()?;
        }
        Ok(())
    }

    // Visit every value at or below the current level of nesting. For example, given this Ion data:
    //
    //    {
    //      foo: [1, 2, 3]
    //      bar: [(1), (2), (3)]
    //      //    ^-- The reader is positioned here, at the beginning of this s-expression.
    //      baz: true
    //    }
    //
    // If the reader were positioned at the first s-expression in the `bar`, this function would
    // advance the reader to the end of `bar`, visiting every nested value along the way.
    // When the function returned, the reader would need to call `step_out()` and `next()` to start
    // reading field `baz`.
    fn finish_reading_current_level(&mut self) -> IonResult<()> {
        use SystemStreamItem::*;
        let starting_depth = self.depth();
        // We need to visit every value in the LST (however deeply nested) so the current symbol
        // table will be updated with any new symbols that the LST imports/defines.
        loop {
            match self.next()? {
                VersionMarker(major, minor) => {
                    return IonResult::decoding_error(format!(
                        "Encountered an IVM for v{major}.{minor} inside an LST."
                    ))
                }
                Value(_) | Null(_) => {
                    // Any value inside an LST should be considered a `SymbolTableValue`; it
                    // shouldn't be possible to encounter a user-level `Value`.
                    unreachable!("Cannot encounter a user-level value inside an LST.")
                }
                SymbolTableValue(ion_type) => {
                    // We've encountered another value in the LST. If's a container, step into it.
                    if ion_type.is_container() {
                        self.step_in()?;
                    }
                    // The logic that handles interpreting each value in the LST lives inside
                    // the `process_raw_value` helper function. The act of calling `next()` and
                    // `step_in()` here is enough to trigger it.
                }
                SymbolTableNull(_ion_type) => {
                    // We've encountered a null value in the LST. Do nothing.
                }
                Nothing if self.depth() > starting_depth => {
                    // We've run out of values, but we're not back to the starting depth yet.
                    // Step out a level and let the loop call next() again.
                    self.step_out()?;
                }
                // We've run out of values and we're at the starting depth, so we're done.
                Nothing => return Ok(()),
            }
        }
    }

    pub fn raw_annotations(&self) -> impl Iterator<Item = IonResult<RawSymbolToken>> + '_ {
        self.raw_reader.annotations()
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        &self.symbol_table
    }

    pub fn read_raw_symbol(&mut self) -> IonResult<RawSymbolToken> {
        if self.lst.state == AtLstImports
            && self.raw_reader.ion_type() == Some(IonType::Symbol)
            && !self.raw_reader.is_null()
        {
            // The raw reader is at the `imports` field of an LST and its value is a symbol.
            return self.raw_reader.read_symbol();
        }
        // Otherwise, delegate to the raw reader
        if self.raw_reader.current() == RawStreamItem::Nothing {
            return IonResult::illegal_operation(
                "called `read_raw_symbol`, but reader is not over a value",
            );
        }
        self.raw_reader.read_symbol()
    }

    pub fn raw_field_name_token(&mut self) -> IonResult<RawSymbolToken> {
        self.raw_reader.field_name()
    }
}

impl<R: RawReader> IonReader for SystemReader<R> {
    type Item = SystemStreamItem;
    type Symbol = Symbol;

    /// Advances the system reader to the next raw stream element.
    // `next` resembles `Iterator::next()`
    #[allow(clippy::should_implement_trait)]
    fn next(&mut self) -> IonResult<Self::Item> {
        // If the reader is positioned at a container that makes up part of an LST, it cannot
        // simply skip it with next(); it must instead descend into that container to read each
        // value.
        self.before_next()?;
        let item = match self.raw_reader.next()? {
            RawStreamItem::VersionMarker(major, minor) => self.process_ivm(major, minor)?,
            RawStreamItem::Value(ion_type) => {
                // We need to consider the context to determine if this is a user-level value
                // or part of a system value.
                self.after_next(ion_type, false)?
            }
            RawStreamItem::Null(ion_type) => self.after_next(ion_type, true)?,
            RawStreamItem::Nothing => SystemStreamItem::Nothing,
        };
        self.current_item = item;
        Ok(item)
    }

    fn current(&self) -> Self::Item {
        self.current_item
    }

    fn step_in(&mut self) -> IonResult<()> {
        // Try to step in with the raw_reader. If the reader isn't positioned on container,
        // this will return an error.
        self.raw_reader.step_in()?;
        // Update the LST state to track what we've stepped into.
        match self.lst.state {
            NotReadingAnLst => {
                // We're diving deeper into user data; do nothing.
            }
            BetweenLstFields => {
                // raw_reader.step_in() above should have returned an error.
                unreachable!("The raw reader stepped in but the LST state was BetweenLstFields.");
            }
            AtLstStart => {
                // We've stepped into an LST struct but are not yet positioned on a field.
                self.lst.state = BetweenLstFields;
            }
            AtLstImports => {
                // We've stepped into the `imports` field of an LST.
                self.lst.state = ProcessingLstImports;
            }
            ProcessingLstImports => {}
            AtLstImportStart => {
                // We've stepped into an LST import struct but are not yet positioned on a field.
                self.lst.state = BetweenLstImportFields;
            }
            BetweenLstImportFields => {
                // raw_reader.step_in() above should have returned an error.
                unreachable!("The raw reader stepped in but the LST import state was BetweenLstImportFields.");
            }
            AtImportName | AtImportVersion | AtImportMaxId => {
                // We're diving deeper into the imports; do nothing.
            }
            AtLstSymbols => {
                // We've stepped into the `symbols` field of an LST.
                self.lst.state = ProcessingLstSymbols;
            }
            ProcessingLstSymbols => {
                // We're diving deeper into the symbols, which is weird but not illegal. Do nothing.
            }
            AtLstOpenContent => {
                // We've stepped into a container on a user-defined field that has not meaning
                // to the reader.
                self.lst.state = ProcessingLstOpenContent;
            }
            ProcessingLstOpenContent => {
                // This is user data with no meaning to the reader; do nothing.
            }
        }
        Ok(())
    }

    fn step_out(&mut self) -> IonResult<()> {
        // If stepping out is successful, we'll apply this new state before returning Ok(())
        let mut new_lst_state = self.lst.state;

        // Update the LST state to track where we are now that we're stepping out.
        match self.lst.state {
            NotReadingAnLst => {
                // Stepping out of user data can never change the LST state; do nothing.
            }
            AtLstStart => {
                // Symbol tables are always at the top level.
                return IonResult::illegal_operation(
                    "Cannot step out when the reader is at the top level.",
                );
            }
            BetweenLstFields | AtLstSymbols | AtLstImports | AtLstOpenContent => {
                // We're stepping out of the local symbol table altogether. Finish processing the
                // LST instead of skipping its remaining contents.
                self.finish_reading_current_level()?;
                self.add_lst_symbols_to_current_symbol_table();
                // Reset other LST-related state.
                self.lst.is_append = false;
                self.lst.has_found_symbols = false;
                self.lst.has_found_imports = false;
                new_lst_state = NotReadingAnLst;
            }
            ProcessingLstSymbols | ProcessingLstOpenContent => {
                // We're inside one of the LST fields. Finish processing the current level before
                // stepping out.
                self.finish_reading_current_level()?;
                // If the upcoming call to step_out() will cause us to leave the field altogether,
                // update our state to indicate that we're back at depth=1.
                if self.depth() == 2 {
                    new_lst_state = BetweenLstFields;
                }
            }
            AtLstImportStart | BetweenLstImportFields => {
                // We're inside one of the LST import. Finish processing the current level before
                // stepping out.
                self.finish_reading_current_level()?;
                // If the upcoming call to step_out() will cause us to leave the field altogether,
                // update our state to indicate that we're back at depth=1.
                if self.depth() == 3 {
                    new_lst_state = ProcessingLstImports;
                }
                // Finish processing LST shared symbol table import by retrieving shared symbol table from catalog.
                if self.lst.current_import_name.is_some()
                    && self.lst.current_import_version.is_some()
                {
                    let catalog = self.catalog.as_ref();
                    let version = self.lst.current_import_version.unwrap();
                    let import_name = self.lst.current_import_name.clone().unwrap();
                    // TODO: add a fallback mechanism that always returns a shared symbol table i.e. provides dummy table when it doesn't exist.
                    let sst = catalog
                        .get_table_with_version(&import_name, version)
                        .ok_or(IonError::decoding_error(format!(
                        "symbol table with name {import_name} doesn't exist for version {version}"
                    )))?;
                    for sym in sst.symbols() {
                        self.lst
                            .imported_symbols
                            .push(sym.text().map(|s| s.to_string()))
                    }
                    // Clear all the import information once it is processed.
                    self.lst.current_import_name = None;
                    self.lst.current_import_max_id = None;
                    self.lst.current_import_version = None;
                }
            }
            ProcessingLstImports => {
                // We're inside one of the LST fields. Finish processing the current level before
                // stepping out.
                self.finish_reading_current_level()?;
                // If the upcoming call to step_out() will cause us to leave the field altogether,
                // update our state to indicate that we're back at depth=1.
                if self.depth() == 2 {
                    new_lst_state = BetweenLstFields;
                }
            }
            AtImportName | AtImportMaxId | AtImportVersion => {
                // We're inside one of the LST fields. Finish processing the current level before
                // stepping out.
                self.finish_reading_current_level()?;
                // Finish processing LST shared symbol table import by retrieving shared symbol table from catalog.
                if self.lst.current_import_name.is_some()
                    && self.lst.current_import_version.is_some()
                {
                    let catalog = self.catalog.as_ref();
                    let import_name = self.lst.current_import_name.clone().unwrap();
                    // TODO: add a fallback mechanism that always returns a shared symbol table i.e. provides dummy table when it doesn't exist.
                    let sst = catalog
                        .get_table_with_version(
                            &import_name,
                            self.lst.current_import_version.unwrap(),
                        )
                        .ok_or(IonError::illegal_operation(format!(
                            "symbol table with name: {import_name} does not exist"
                        )))?;
                    for sym in sst.symbols() {
                        self.lst
                            .imported_symbols
                            .push(sym.text().map(|s| s.to_string()))
                    }
                    // Clear all the import information once it is processed.
                    self.lst.current_import_name = None;
                    self.lst.current_import_max_id = None;
                    self.lst.current_import_version = None;
                }
                if self.depth() == 3 {
                    new_lst_state = ProcessingLstImports;
                }
            }
        }

        self.raw_reader.step_out()?;
        self.lst.state = new_lst_state;
        Ok(())
    }

    fn field_name(&self) -> IonResult<Symbol> {
        match self.raw_reader.field_name() {
            Ok(RawSymbolToken::SymbolId(sid)) => {
                self.symbol_table.symbol_for(sid).cloned().ok_or_else(|| {
                    IonError::decoding_error(format!(
                        "encountered field ID with undefined text: ${sid}"
                    ))
                })
            }
            Ok(RawSymbolToken::Text(text)) => Ok(Symbol::owned(text)),
            Err(error) => Err(error),
        }
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Symbol>> + 'a> {
        let iter = self
            .raw_reader
            .annotations()
            .map(|raw_token| match raw_token {
                // If the annotation was a symbol ID, try to resolve it
                Ok(RawSymbolToken::SymbolId(sid)) => {
                    self.symbol_table.symbol_for(sid).cloned().ok_or_else(|| {
                        IonError::decoding_error(format!(
                            "Found annotation with undefined symbol ${sid}"
                        ))
                    })
                }
                // If the annotation was a text literal, turn it into a `Symbol`
                Ok(RawSymbolToken::Text(text)) => Ok(Symbol::owned(text)),
                // If the raw reader couldn't provide the annotation, propagate the error
                Err(error) => Err(error),
            });
        Box::new(iter)
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        let sid = match self.read_raw_symbol()? {
            RawSymbolToken::Text(text) => return Ok(Symbol::owned(text)),
            RawSymbolToken::SymbolId(sid) => sid,
        };
        if let Some(symbol) = self.symbol_table.symbol_for(sid) {
            // Make a cheap clone of the Arc<str> in the symbol table
            Ok(symbol.clone())
        } else if !self.symbol_table.sid_is_valid(sid) {
            IonResult::decoding_error(format!("Symbol ID ${sid} is out of range."))
        } else {
            IonResult::decoding_error(format!("Symbol ID ${sid} has unknown text."))
        }
    }

    // The SystemReader needs to expose many of the same functions as the Cursor, but only some of
    // those need to be re-defined to allow for system value processing. Any method listed here will
    // be delegated to self.raw_reader directly.
    delegate! {
        to self.raw_reader {
            fn is_null(&self) -> bool;
            fn ion_version(&self) -> (u8, u8);
            fn ion_type(&self) -> Option<IonType>;
            fn read_null(&mut self) -> IonResult<IonType>;
            fn read_bool(&mut self) -> IonResult<bool>;
            fn read_int(&mut self) -> IonResult<Int>;
            fn read_i64(&mut self) -> IonResult<i64>;
            fn read_f32(&mut self) -> IonResult<f32>;
            fn read_f64(&mut self) -> IonResult<f64>;
            fn read_decimal(&mut self) -> IonResult<Decimal>;
            fn read_str(&mut self) -> IonResult<&str>;
            fn read_string(&mut self) -> IonResult<Str>;
            fn read_blob(&mut self) -> IonResult<Blob>;
            fn read_clob(&mut self) -> IonResult<Clob>;
            fn read_timestamp(&mut self) -> IonResult<Timestamp>;
            fn depth(&self) -> usize;
            fn parent_type(&self) -> Option<IonType>;
        }
    }
}

/// Functionality that is only available if the data source we're reading from is in-memory, like
/// a `Vec<u8>` or `&[u8]`.
impl<T: AsRef<[u8]> + Expandable> SystemReader<RawBinaryReader<T>> {
    delegate! {
        to self.raw_reader {
            pub fn raw_bytes(&self) -> Option<&[u8]>;
            pub fn raw_field_id_bytes(&self) -> Option<&[u8]>;
            pub fn raw_header_bytes(&self) -> Option<&[u8]>;
            pub fn raw_value_bytes(&self) -> Option<&[u8]>;
            pub fn raw_annotations_bytes(&self) -> Option<&[u8]>;

            pub fn field_id_length(&self) -> Option<usize>;
            pub fn field_id_offset(&self) -> Option<usize>;
            pub fn field_id_range(&self) -> Option<Range<usize>>;

            pub fn annotations_length(&self) -> Option<usize>;
            pub fn annotations_offset(&self) -> Option<usize>;
            pub fn annotations_range(&self) -> Option<Range<usize>>;

            pub fn header_length(&self) -> usize;
            pub fn header_offset(&self) -> usize;
            pub fn header_range(&self) -> Range<usize>;

            pub fn value_length(&self) -> usize;
            pub fn value_offset(&self) -> usize;
            pub fn value_range(&self) -> Range<usize>;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::SystemStreamItem::*;
    use crate::blocking_reader::*;
    use crate::catalog::MapCatalog;
    use crate::shared_symbol_table::SharedSymbolTable;
    use std::sync::Arc;

    use super::*;

    fn system_reader_for(ion: &str) -> SystemReader<BlockingRawTextReader<&str>> {
        let raw_reader = BlockingRawTextReader::new(ion).expect("unable to initialize reader");
        SystemReader::new(raw_reader)
    }

    fn system_reader_with_catalog_for(
        ion: &str,
        catalog: Box<dyn Catalog>,
    ) -> SystemReader<BlockingRawTextReader<&str>> {
        let raw_reader = BlockingRawTextReader::new(ion).expect("unable to initialize reader");
        SystemReader::with_catalog(raw_reader, catalog)
    }

    fn binary_system_reader_with_catalog_for(
        ion: &[u8],
        catalog: Box<dyn Catalog>,
    ) -> SystemReader<BlockingRawBinaryReader<&[u8]>> {
        let raw_reader = BlockingRawBinaryReader::new(ion).expect("unable to initialize reader");
        SystemReader::with_catalog(raw_reader, catalog)
    }

    #[test]
    fn basic_symbol_table() -> IonResult<()> {
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_for(
            r#"
            $ion_symbol_table::{
                symbols: ["foo", "bar", "baz"],
            }
            $10 // "foo"
            $11 // "bar"
            $12 // "baz"
          "#,
        );
        // We step over the LST...
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        // ...but expect all of the symbols we encounter after it to be in the symbol table,
        // indicating that the SystemReader processed the LST even though we skipped it with `next()`
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "foo");
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "bar");
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "baz");
        Ok(())
    }

    #[test]
    fn shared_symbol_table() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["foo"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
            $ion_symbol_table::{
                imports: [ { name:"shared_table", version: 1 }],
            }
            $10 // "foo"
          "#,
            Box::new(map_catalog),
        );
        // We step over the LST...
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        // ...but expect all of the symbols we encounter after it to be in the symbol table,
        // indicating that the SystemReader processed the LST even though we skipped it with `next()`
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "foo");
        Ok(())
    }

    #[test]
    fn shared_symbol_table_import_with_max_id() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["foo"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
            $ion_symbol_table::{
                imports: [ { name:"shared_table", version: 1, max_id: 1 }],
            }
            $10 // "foo"
            $11
          "#,
            Box::new(map_catalog),
        );
        // We step over the LST...
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        // ...but expect all of the symbols we encounter after it to be in the symbol table,
        // indicating that the SystemReader processed the LST even though we skipped it with `next()`
        // since the max_id matches with the number of symbols in the `shared_table` no new unknown symbols be added to the table
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "foo");
        Ok(())
    }

    #[test]
    fn shared_symbol_table_step_in() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["foo"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
            $ion_symbol_table::{
                imports: [ { name:"shared_table", version: 1 }],
            }
            $10 // "foo"
          "#,
            Box::new(map_catalog),
        );
        // We process the LST by stepping into it...
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        reader.step_in()?;
        // Process the LST imports list
        assert_eq!(reader.next()?, SymbolTableValue(IonType::List));
        reader.step_in()?;
        // Process a shared symbol table import
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        reader.step_in()?;
        assert_eq!(reader.next()?, SymbolTableValue(IonType::String));
        assert_eq!(reader.read_string()?, "shared_table");
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Int));
        assert_eq!(reader.read_i64()?, 1);
        // We do not process the `version` fields to see if the SystemReader processed
        // the LST even though we skipped it with `step_out()`.
        reader.step_out()?;
        reader.step_out()?;
        reader.step_out()?;
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "foo");
        Ok(())
    }

    #[test]
    fn shared_symbol_table_partial_read() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["foo"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
            $ion_symbol_table::{
                imports: [ { name:"shared_table", version: 1, max_id: 1 }],
            }
            $10 // "foo"
          "#,
            Box::new(map_catalog),
        );
        // We process the LST by stepping into it...
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        reader.step_in()?;
        // Process the LST imports list
        assert_eq!(reader.next()?, SymbolTableValue(IonType::List));
        reader.step_in()?;
        // Process a shared symbol table import
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        reader.step_in()?;
        assert_eq!(reader.next()?, SymbolTableValue(IonType::String));
        assert_eq!(reader.read_string()?, "shared_table");
        reader.step_out()?;
        reader.step_out()?;
        reader.step_out()?;
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "foo");
        Ok(())
    }

    #[test]
    fn shared_and_local_symbols() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["foo"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
            $ion_symbol_table::{
                imports: [ { name:"shared_table", version: 1 } ],
                symbols: [ "local_symbol" ]
            }
            $10 // "foo"
            $11 // "local_symbol"
          "#,
            Box::new(map_catalog),
        );
        // We step over the LST...
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        // ...but expect all of the symbols we encounter after it to be in the symbol table,
        // indicating that the SystemReader processed the LST even though we skipped it with `next()`
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "foo");
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "local_symbol");
        Ok(())
    }

    #[test]
    fn multiple_shared_symbol_table_imports() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_1", 1, ["foo"])?);
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_2", 1, ["bar"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
            $ion_symbol_table::{
                imports: [ { name:"shared_table_1", version: 1 }, { name:"shared_table_2", version: 1 } ],
                symbols: [ "local_symbol" ]
            }
            $10 // "foo"
            $11 // "bar"
            $12 // "local_symbol"
          "#,
            Box::new(map_catalog),
        );
        // We step over the LST...
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        // ...but expect all of the symbols we encounter after it to be in the symbol table,
        // indicating that the SystemReader processed the LST even though we skipped it with `next()`
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "foo");
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "bar");
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "local_symbol");
        Ok(())
    }

    #[test]
    fn non_existing_shared_symbol_table_imports() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_1", 1, ["foo"])?);
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_2", 1, ["bar"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
            $ion_symbol_table::{
                imports: [ { name:"shared_table_3", version: 1, max_id: 3 }, { name:"shared_table_2", version: 1 }, { name:"shared_table_4", version: 1, max_id: 1 } ],
                symbols: [ "local_symbol" ]
            }
            $13 // "bar"
          "#,
            Box::new(map_catalog),
        );
        // We step over LST...
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        // ...but expect error as the reader would not be able to process a non existing shared symbol table
        assert!(reader.next().is_err());
        Ok(())
    }

    #[test]
    fn shared_symbol_table_import_binary() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        // add a table with system symbol `name` and a new symbol `foo`
        // reader should still add this system symbol `name` again($10), but whenever writing this symbol
        // smallest ID($4) will be used
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["name", "foo"])?);
        // The stream contains a shared symbol table import
        let mut reader = binary_system_reader_with_catalog_for(
            &[
                0xe0, 0x01, 0x00, 0xea, // Ion 1.0 Version Marker
                0xee, 0x9d, 0x81, 0x83, // '$ion_symbol_table'::
                0xde, 0x99, // 26 bytes struct
                0x86, // Field $6 `imports`
                0xbe, 0x96, // List
                0xde, 0x94, // 21 bytes struct
                0x84, // Field $4 `name`
                0x8c, 0x73, 0x68, 0x61, 0x72, 0x65, 0x64, 0x5f, 0x74, 0x61, 0x62, 0x6c,
                0x65, // "shared_table"
                0x85, // Field $5 `version`
                0x21, 0x01, // INT 1
                0x88, // $8 `max_id`
                0x21, 0x02, // INT 2
                0x71, 0x04, // $4 `name`
                0x71, 0x0a, // $10 `name`
                0x71, 0x0b, // $11 `foo`
            ],
            Box::new(map_catalog),
        );
        assert_eq!(reader.next()?, VersionMarker(1, 0));
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, Symbol::shared(Arc::from("name")));
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, Symbol::shared(Arc::from("name")));
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, Symbol::shared(Arc::from("foo")));
        Ok(())
    }

    #[test]
    fn symbol_table_append() -> IonResult<()> {
        // The stream contains multiple LST appends
        let mut reader = system_reader_for(
            r#"
            $ion_symbol_table::{
                imports: $ion_symbol_table,
                symbols: ["foo"],
            }
            $ion_symbol_table::{
                imports: $ion_symbol_table,
                symbols: ["bar"],
            }
            $ion_symbol_table::{
                imports: $ion_symbol_table,
                symbols: ["baz"],
            }
            $10 // "foo"
            $11 // "bar"
            $12 // "baz"
          "#,
        );
        // Expect 3 symbol tables in a row, stepping over each one
        for _ in 0..3 {
            assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        }
        // Confirm that the symbols defined in each append map to the expected text.
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "foo");
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "bar");
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "baz");
        Ok(())
    }

    #[test]
    fn symbol_table_reset() -> IonResult<()> {
        // The stream contains multiple symbol tables that are not appends. Verify that the
        // current symbol table is reset each time it encounters a non-append LST.
        let mut reader = system_reader_for(
            r#"
            $ion_symbol_table::{
                symbols: ["foo"],
            }
            $10 // "foo"
            $ion_1_0 // Reset the table on IVM
            $ion_symbol_table::{
                symbols: ["bar"],
            }
            $ion_symbol_table::{
                // Reset the table because this isn't an LST append
                symbols: ["baz"],
            }
            $10 // "baz"
          "#,
        );

        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        // Only system symbols initially
        assert_eq!(reader.symbol_table.len(), 10);

        // Advance to the symbol $10, loading the LST as we pass it
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.symbol_table.len(), 11);
        assert_eq!(reader.read_symbol()?, "foo");

        // Encounter an IVM, reset the table
        assert_eq!(reader.next()?, VersionMarker(1, 0));
        // The symbol we defined is gone
        assert_eq!(reader.symbol_table.len(), 10);

        // Step over the two symbol tables that follow
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));

        // Advance to the symbol $10 again, but this time it's 'baz'
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.symbol_table.len(), 11);
        assert_eq!(reader.read_symbol()?, "baz");

        Ok(())
    }

    #[test]
    fn manually_step_through_lst() -> IonResult<()> {
        // The stream contains an LST
        let mut reader = system_reader_for(
            r#"
            $ion_1_0
            $ion_symbol_table::{
                imports: $ion_symbol_table,
                symbols: ["foo", "bar", "baz"],
            }
            $10
            $11
            $12
          "#,
        );
        // IVM
        assert_eq!(reader.next()?, VersionMarker(1, 0));

        // Symbol table
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Struct));

        // Instead of stepping _over_ the LST as we've done in other tests, step into it.
        // We're going to visit/read every value inside the LST. Afterwards, we'll confirm
        // that the SystemReader correctly processed the LST under the hood as we stepped
        // through it ourselves.
        reader.step_in()?;

        // Advance to `imports`, confirm its value is the system symbol "$ion_symbol_table"
        assert_eq!(reader.next()?, SymbolTableValue(IonType::Symbol));
        assert_eq!(reader.field_name()?, "imports");
        assert_eq!(reader.read_symbol()?, "$ion_symbol_table".to_string());

        // Advance to `symbols`, visit each string in the list
        assert_eq!(reader.next()?, SymbolTableValue(IonType::List));
        assert_eq!(reader.field_name()?, "symbols");
        reader.step_in()?;
        assert_eq!(reader.next()?, SymbolTableValue(IonType::String));
        assert_eq!(reader.read_string()?, "foo");
        assert_eq!(reader.next()?, SymbolTableValue(IonType::String));
        assert_eq!(reader.read_string()?, "bar");
        assert_eq!(reader.next()?, SymbolTableValue(IonType::String));
        assert_eq!(reader.read_string()?, "baz");
        // No more strings
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // No more LST fields
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Read the user-level symbol values in the stream to confirm that the LST was processed
        // successfully by the SystemReader.
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "foo");
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "bar");
        assert_eq!(reader.next()?, Value(IonType::Symbol));
        assert_eq!(reader.read_symbol()?, "baz");

        Ok(())
    }
}
