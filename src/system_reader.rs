use crate::constants::v1_0::system_symbol_ids;
use crate::raw_reader::RawStreamItem;
use crate::raw_symbol_token::RawSymbolToken;
use crate::result::{decoding_error, illegal_operation, IonResult};
use crate::system_reader::LstPosition::*;
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::{IonType, RawBinaryReader, RawReader, SymbolTable};
use bigdecimal::BigDecimal;
use delegate::delegate;
use std::io;
use std::ops::Range;

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

#[derive(Debug, Eq, PartialEq)]
/// Raw stream elements that a SystemReader may encounter.
pub enum SystemStreamItem {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    /// An Ion value that is part of an encoded local symbol table.
    /// This includes:
    /// * Top-level structs annotated with $ion_symbol_table::
    /// * Any fields nested inside such structs, but especially `imports` and `symbols`
    SymbolTableData(IonType, bool),
    /// A user-level Ion value (e.g. an integer, timestamp, or struct).
    /// Includes the value's IonType and whether it is null.
    Value(IonType, bool),
}

// Stores information that has been read from a local symbol table that is currently being
// processed.
// TODO: Support shared symbol table imports.
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
    // At present, RawTextReader and RawBinaryReader cannot read the same value more than once.
    // When the SystemReader needs to read the current value as part of processing a local symbol
    // table, it must store a copy of that value in case the user requests it via `read_string()`,
    // `read_i64()`, etc. The fields below are used to store such copies.
    current_symbol: RawSymbolToken,
    current_string: String,
    current_int: i64,
}

impl LstData {
    fn new() -> LstData {
        LstData {
            is_append: false,
            symbols: vec![],
            state: LstPosition::NotReadingAnLst,
            current_symbol: RawSymbolToken::SymbolId(0),
            current_string: "".to_string(),
            current_int: 0,
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
/// wrapped RawReader implementation.
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
}

// FIXME: The `read_datetime` method is deprecated. However, this function body is generated by a
// macro, making it impossible to apply this #[allow(deprecated)] more narrowly. When `read_datetime`
// is removed, this annotation should be removed too.
#[allow(deprecated)]
impl<C: RawReader> SystemReader<C> {
    pub fn new(raw_reader: C) -> SystemReader<C> {
        SystemReader {
            raw_reader,
            symbol_table: SymbolTable::new(),
            lst: LstData::new(),
        }
    }

    // Returns true if the raw reader is positioned over a top-level struct whose first annotation
    // is $ion_symbol_table.
    fn current_value_is_symbol_table(&self) -> bool {
        self.raw_reader.ion_type() == Some(IonType::Struct)
            && self.depth() == 0
            && self
                .annotations()
                .next()
                .map(|a| a == Some("$ion_symbol_table"))
                .unwrap_or(false)
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
            _ => {
                // Allow values at depths > 1 to be skipped.
                // TODO: Process import structs that live at depth=2
                //       imports: [{name:_, version:_, max_id:_}, {name:_, version:_, max_id:_}]
            }
        }

        Ok(())
    }

    /// Advances the system reader to the next raw stream element.
    pub fn next(&mut self) -> IonResult<Option<SystemStreamItem>> {
        // If the reader is positioned at a container that makes up part of an LST, it cannot
        // simply skip it with next(); it must instead descend into that container to read each
        // value.
        self.before_next()?;
        return match self.raw_reader.next()? {
            Some(RawStreamItem::VersionMarker(major, minor)) => self.process_ivm(major, minor),
            Some(RawStreamItem::Value(ion_type, is_null)) => {
                // We need to consider the context to determine if this is a user-level value
                // or part of a system value.
                self.after_next(ion_type, is_null)
            }
            None => Ok(None),
        };
    }

    // After the raw reader is advanced by a call to `next()`, take stock of the reader's new
    // position. Return a SystemStreamItem indicating whether the reader is now positioned over
    // a user value or part of a local symbol table.
    fn after_next(
        &mut self,
        ion_type: IonType,
        is_null: bool,
    ) -> IonResult<Option<SystemStreamItem>> {
        // At this point, `self.lst.state` represents the reader's _previous_ position.
        // We have now advanced to the next value at the same depth and need to update
        // `self.lst.state` to reflect that.
        match self.lst.state {
            NotReadingAnLst | AtLstStart => {
                // If we're at the top level and the next element we encounter is a struct whose
                // first annotation is $ion_symbol_table, then set the state to `AtLstStart`
                if self.current_value_is_symbol_table() {
                    self.lst.state = AtLstStart;
                } else {
                    // Otherwise, it's just a plain user value.
                    // This is the only branch in this method that returns a user value.
                    self.lst.state = NotReadingAnLst;
                    return Ok(Some(SystemStreamItem::Value(ion_type, is_null)));
                }
            }
            AtLstImports | AtLstSymbols | AtLstOpenContent | BetweenLstFields => {
                // The reader is inside the LST at depth=1. Figure out which field we're on and
                // update the state.
                if let Some(field_name_token) = self.raw_reader.field_name() {
                    if field_name_token.matches(system_symbol_ids::IMPORTS, "imports") {
                        self.move_to_lst_imports_field(ion_type)?;
                    } else if field_name_token.matches(system_symbol_ids::SYMBOLS, "symbols") {
                        self.lst.state = AtLstSymbols;
                    } else {
                        // This field has no effect on our handling of the LST.
                        self.lst.state = AtLstOpenContent;
                    }
                } else {
                    // There's no field name; we're between fields.
                    self.lst.state = BetweenLstFields;
                }
            }
            ProcessingLstImports => {
                todo!("Support shared symbol table imports.");
            }
            ProcessingLstSymbols => {
                // We're in the `symbols` list.
                if let (IonType::String, false) = (ion_type, is_null) {
                    // If the current value is a non-null string, add its text to the symbol table.
                    self.load_current_string()?;
                    // We clone the current string because the user may ask for its value via
                    // read_string().
                    self.lst.symbols.push(Some(self.lst.current_string.clone()))
                } else {
                    // Non-string values and nulls are treated as symbols with unknown text.
                    self.lst.symbols.push(None);
                }
            }
            ProcessingLstOpenContent => {
                // We were in open content before and haven't stepped out yet. Do nothing.
            }
        };

        Ok(Some(SystemStreamItem::SymbolTableData(ion_type, is_null)))
    }

    // Called when the system reader advances to the `imports` field of an LST.
    fn move_to_lst_imports_field(&mut self, ion_type: IonType) -> IonResult<()> {
        self.lst.state = AtLstImports;
        match ion_type {
            IonType::Symbol => {
                // If the `imports` field value is the symbol '$ion_symbol_table', then this is an
                // LST append.
                self.load_current_symbol()?;
                if self
                    .lst
                    .current_symbol
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
                todo!("Support shared symbol table imports.");
            }
            _ => {
                // Non-list, non-symbol values for the `imports` field are ignored.
            }
        };
        Ok(())
    }

    // Reads the raw reader's current value expecting a symbol. Stores the value in
    // `self.lst.current_symbol` so it can be returned if the user requests it.
    fn load_current_symbol(&mut self) -> IonResult<()> {
        let token = self
            .raw_reader
            .read_symbol()?
            .expect("load_current_symbol() called at a value that was not a symbol.");
        self.lst.current_symbol = token;
        Ok(())
    }

    // Reads the raw reader's current value expecting a string. Stores the value in
    // `self.lst.current_string` so it can be returned if the user requests it.
    fn load_current_string(&mut self) -> IonResult<()> {
        self.lst.current_string.clear();
        let SystemReader {
            ref mut raw_reader,
            ref mut lst,
            ..
        } = *self;
        raw_reader
            .string_ref_map(|s| lst.current_string.push_str(s))
            .expect("load_current_string() called at a value that was not a string.");
        Ok(())
    }

    // Reads the raw reader's current value expecting an integer. Stores the value in
    // `self.lst.current_int` so it can be returned if the user requests it.
    fn load_current_int(&mut self) -> IonResult<()> {
        // Note: This method will only be called on integers found inside of local symbol tables.
        //       If an LST has an integer that's too big to fit in an i64, this will fail.
        self.raw_reader
            .read_i64()?
            .expect("load_current_int() called at a value that was not an integer.");
        Ok(())
    }

    pub fn step_in(&mut self) -> IonResult<()> {
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
            ProcessingLstImports => {
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

    pub fn step_out(&mut self) -> IonResult<()> {
        // If stepping out is successful, we'll apply this new state before returning Ok(())
        let mut new_lst_state = self.lst.state;

        // Update the LST state to track where we are now that we're stepping out.
        match self.lst.state {
            NotReadingAnLst => {
                // Stepping out of user data can never change the LST state; do nothing.
            }
            AtLstStart => {
                // Symbol tables are always at the top level.
                return illegal_operation("Cannot step out when the reader is at the top level.");
            }
            BetweenLstFields | AtLstSymbols | AtLstImports | AtLstOpenContent => {
                // We're stepping out of the local symbol table altogether. Finish processing the
                // LST instead of skipping its remaining contents.
                self.finish_reading_current_level()?;
                self.add_lst_symbols_to_current_symbol_table();
                self.lst.is_append = false;
                new_lst_state = NotReadingAnLst;
            }
            ProcessingLstImports | ProcessingLstSymbols | ProcessingLstOpenContent => {
                // We're inside one of the LST fields. Finish processing the current level before
                // stepping out.
                self.finish_reading_current_level()?;
                // If the upcoming call to step_out() will cause us to leave the field altogether,
                // update our state to indicate that we're back at depth=1.
                if self.depth() == 2 {
                    new_lst_state = BetweenLstFields;
                }
            }
        }

        self.raw_reader.step_out()?;
        self.lst.state = new_lst_state;
        Ok(())
    }

    // When the reader steps out of an LST, this method will add the new symbols we've been
    // buffering in `self.lst.symbols` to the current symbol table.
    fn add_lst_symbols_to_current_symbol_table(&mut self) {
        if !self.lst.is_append {
            // This is not an append. Clear the current symbol table.
            self.symbol_table.reset();
        }
        // TODO: support importing shared symbol tables
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
        let starting_depth = self.depth();
        // We need to visit every value in the LST (however deeply nested) so the current symbol
        // table will be updated with any new symbols that the LST imports/defines.
        loop {
            match self.next()? {
                Some(SystemStreamItem::VersionMarker(major, minor)) => {
                    return decoding_error(format!(
                        "Encountered an IVM for v{}.{} inside an LST.",
                        major, minor
                    ))
                }
                Some(SystemStreamItem::Value(_ion_type, _is_null)) => {
                    // Any value inside an LST should be considered a `SymbolTableValue`; it
                    // shouldn't be possible to encounter a user-level `Value`.
                    unreachable!("Cannot encounter a user-level value inside an LST.")
                }
                Some(SystemStreamItem::SymbolTableData(ion_type, is_null)) => {
                    // We've encountered another value in the LST. If's a container, step into it.
                    if !is_null && ion_type.is_container() {
                        self.step_in()?;
                    }
                    // The logic that handles interpreting each value in the LST lives inside
                    // the `process_raw_value` helper function. The act of calling `next()` and
                    // `step_in()` here is enough to trigger it.
                }
                None if self.depth() > starting_depth => {
                    // We've run out of values, but we're not back to the starting depth yet.
                    // Step out a level and let the loop call next() again.
                    self.step_out()?;
                }
                // We've run out of values and we're at the starting depth, so we're done.
                None => return Ok(()),
            }
        }
    }

    fn process_ivm(&mut self, major: u8, minor: u8) -> IonResult<Option<SystemStreamItem>> {
        if self.depth() > 0 {
            return decoding_error("Encountered an IVM at a depth > 0");
        }

        self.lst.state = NotReadingAnLst;
        self.symbol_table.reset();
        Ok(Some(SystemStreamItem::VersionMarker(major, minor)))
    }

    pub fn field_name(&self) -> Option<&str> {
        match self.raw_reader.field_name() {
            Some(RawSymbolToken::SymbolId(sid)) => self.symbol_table.text_for(*sid),
            Some(RawSymbolToken::Text(text)) => Some(text.as_str()),
            None => None,
        }
    }

    pub fn raw_annotations(&mut self) -> impl Iterator<Item = &RawSymbolToken> {
        self.raw_reader.annotations().iter()
    }

    pub fn annotations(&self) -> impl Iterator<Item = Option<&str>> {
        self.raw_reader
            .annotations()
            .iter()
            .map(move |raw_token| match raw_token {
                RawSymbolToken::SymbolId(sid) => self.symbol_table.text_for(*sid),
                RawSymbolToken::Text(text) => Some(text.as_str()),
            })
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        &self.symbol_table
    }

    pub fn read_symbol(&mut self) -> IonResult<Option<String>> {
        let sid = match self.read_raw_symbol()? {
            Some(RawSymbolToken::Text(text)) => return Ok(Some(text)),
            Some(RawSymbolToken::SymbolId(sid)) => sid,
            None => return Ok(None),
        };
        if let Some(text) = self.symbol_table.text_for(sid) {
            // TODO: SymbolTable should use Rc<str> so this is cheap
            Ok(Some(text.to_string()))
        } else {
            if !self.symbol_table.sid_is_valid(sid) {
                decoding_error(format!("Symbol ID ${} is out of range.", sid))
            } else {
                Ok(None)
            }
        }
    }

    pub fn read_raw_symbol(&mut self) -> IonResult<Option<RawSymbolToken>> {
        if self.lst.state == AtLstImports
            && self.raw_reader.ion_type() == Some(IonType::Symbol)
            && !self.raw_reader.is_null()
        {
            // The raw reader is at the `imports` field of an LST and its value is a symbol.
            // This means that it has eagerly loaded the symbol to see if it is $ion_symbol_table.
            // Return a copy of the materialized symbol value.
            return Ok(Some(self.lst.current_symbol.clone()));
        }
        // Otherwise, delegate to the raw reader
        self.raw_reader.read_symbol()
    }

    pub fn raw_field_name_token(&mut self) -> Option<&RawSymbolToken> {
        self.raw_reader.field_name()
    }

    // Returns true if the system reader already consumed the current string from input as part of
    // processing the current local symbol table.
    pub fn current_string_was_consumed(&self) -> bool {
        // The raw reader is inside the `symbols` field of an LST and its value is a string.
        // This means that the system reader has eagerly loaded the string to eventually store
        // its text in the current symbol table. Return a copy of the materialized string value.
        self.lst.state == ProcessingLstSymbols
            && self.raw_reader.ion_type() == Some(IonType::String)
            && !self.raw_reader.is_null()
    }

    pub fn read_string(&mut self) -> IonResult<Option<String>> {
        if self.current_string_was_consumed() {
            return Ok(Some(self.lst.current_string.clone()));
        }
        // Otherwise, delegate to the raw reader
        self.raw_reader.read_string()
    }

    pub fn string_ref_map<F, U>(&mut self, f: F) -> IonResult<Option<U>>
    where
        F: FnOnce(&str) -> U,
    {
        if self.current_string_was_consumed() {
            let text = self.lst.current_string.as_str();
            return Ok(Some(f(text)));
        }
        self.raw_reader.string_ref_map(f)
    }

    pub fn string_bytes_map<F, U>(&mut self, f: F) -> IonResult<Option<U>>
    where
        F: FnOnce(&[u8]) -> U,
    {
        if self.current_string_was_consumed() {
            let bytes = self.lst.current_string.as_bytes();
            return Ok(Some(f(bytes)));
        }
        self.raw_reader.string_bytes_map(f)
    }

    // The SystemReader needs to expose many of the same functions as the Cursor, but only some of
    // those need to be re-defined to allow for system value processing. Any method listed here will
    // be delegated to self.raw_reader directly.
    delegate! {
        to self.raw_reader {
            pub fn is_null(&self) -> bool;
            pub fn ion_version(&self) -> (u8, u8);
            pub fn ion_type(&self) -> Option<IonType>;
            pub fn read_null(&mut self) -> IonResult<Option<IonType>>;
            pub fn read_bool(&mut self) -> IonResult<Option<bool>>;
            pub fn read_i64(&mut self) -> IonResult<Option<i64>>;
            pub fn read_f32(&mut self) -> IonResult<Option<f32>>;
            pub fn read_f64(&mut self) -> IonResult<Option<f64>>;
            pub fn read_decimal(&mut self) -> IonResult<Option<Decimal>>;
            pub fn read_big_decimal(&mut self) -> IonResult<Option<BigDecimal>>;
            pub fn read_blob_bytes(&mut self) -> IonResult<Option<Vec<u8>>>;
            pub fn read_clob_bytes(&mut self) -> IonResult<Option<Vec<u8>>>;
            pub fn read_timestamp(&mut self) -> IonResult<Option<Timestamp>>;
            pub fn depth(&self) -> usize;
            pub fn clob_ref_map<F, U>(&mut self, f: F) -> IonResult<Option<U>> where F: FnOnce(&[u8]) -> U;
            pub fn blob_ref_map<F, U>(&mut self, f: F) -> IonResult<Option<U>> where F: FnOnce(&[u8]) -> U;
        }
    }
}

/// Functionality that is only available if the data source we're reading from is in-memory, like
/// a Vec<u8> or &[u8].
impl<T: AsRef<[u8]>> SystemReader<RawBinaryReader<io::Cursor<T>>> {
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
    use super::*;
    use crate::text::raw_text_reader::RawTextReader;

    fn system_reader_for(ion: &str) -> SystemReader<RawTextReader<&str>> {
        let raw_reader = RawTextReader::new(ion);
        SystemReader::new(raw_reader)
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
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::Struct, false))
        );
        // ...but expect all of the symbols we encounter after it to be in the symbol table,
        // indicating that the SystemReader processed the LST even though we skipped it with `next()`
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.read_symbol()?, Some("foo".to_string()));
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.read_symbol()?, Some("bar".to_string()));
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.read_symbol()?, Some("baz".to_string()));
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
            assert_eq!(
                reader.next()?,
                Some(SystemStreamItem::SymbolTableData(IonType::Struct, false))
            );
        }
        // Confirm that the symbols defined in each append map to the expected text.
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.read_symbol()?, Some("foo".to_string()));
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.read_symbol()?, Some("bar".to_string()));
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.read_symbol()?, Some("baz".to_string()));
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

        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::Struct, false))
        );
        // Only system symbols initially
        assert_eq!(reader.symbol_table.len(), 10);

        // Advance to the symbol $10, loading the LST as we pass it
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.symbol_table.len(), 11);
        assert_eq!(reader.read_symbol()?, Some("foo".to_string()));

        // Encounter an IVM, reset the table
        assert_eq!(reader.next()?, Some(SystemStreamItem::VersionMarker(1, 0)));
        // The symbol we defined is gone
        assert_eq!(reader.symbol_table.len(), 10);

        // Step over the two symbol tables that follow
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::Struct, false))
        );
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::Struct, false))
        );

        // Advance to the symbol $10 again, but this time it's 'baz'
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.symbol_table.len(), 11);
        assert_eq!(reader.read_symbol()?, Some("baz".to_string()));

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
        assert_eq!(reader.next()?, Some(SystemStreamItem::VersionMarker(1, 0)));

        // Symbol table
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::Struct, false))
        );

        // Instead of stepping _over_ the LST as we've done in other tests, step into it.
        // We're going to visit/read every value inside the LST. Afterwards, we'll confirm
        // that the SystemReader correctly processed the LST under the hood as we stepped
        // through it ourselves.
        reader.step_in()?;

        // Advance to `imports`, confirm its value is the system symbol "$ion_symbol_table"
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::Symbol, false))
        );
        assert_eq!(reader.field_name(), Some("imports"));
        assert_eq!(reader.read_symbol()?, Some("$ion_symbol_table".to_string()));

        // Advance to `symbols`, visit each string in the list
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::List, false))
        );
        assert_eq!(reader.field_name(), Some("symbols"));
        reader.step_in()?;
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::String, false))
        );
        assert_eq!(reader.read_string()?, Some("foo".to_string()));
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::String, false))
        );
        assert_eq!(reader.read_string()?, Some("bar".to_string()));
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::SymbolTableData(IonType::String, false))
        );
        assert_eq!(reader.read_string()?, Some("baz".to_string()));
        // No more strings
        assert_eq!(reader.next()?, None);
        reader.step_out()?;

        // No more LST fields
        assert_eq!(reader.next()?, None);
        reader.step_out()?;

        // Read the user-level symbol values in the stream to confirm that the LST was processed
        // successfully by the SystemReader.
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.read_symbol()?, Some("foo".to_string()));
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.read_symbol()?, Some("bar".to_string()));
        assert_eq!(
            reader.next()?,
            Some(SystemStreamItem::Value(IonType::Symbol, false))
        );
        assert_eq!(reader.read_symbol()?, Some("baz".to_string()));

        Ok(())
    }
}
