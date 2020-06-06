use crate::data_source::IonDataSource;
use crate::result::IonResult;
use crate::types::{IonType, SymbolId};
use bigdecimal::BigDecimal;
use chrono::{DateTime, FixedOffset};

/**
 * This trait captures the format-agnostic, system-level parser functionality needed to
 * navigate within an Ion stream and read the values encountered into native Rust data types.
 *
 * Cursor implementations are not expected to interpret symbol table declarations, resolve symbol
 * IDs into text, or otherwise interpret system-level constructs for use at a user level.
 *
 * Once a value has successfully been read from the stream using one of the read_* functions,
 * calling that function again may return an Err. This is left to the discretion of the implementor.
 */
pub trait Cursor<D: IonDataSource> {
    /// Returns the (major, minor) version of the Ion stream being read. If ion_version is called
    /// before an Ion Version Marker has been read, the version (1, 0) will be returned.
    fn ion_version(&self) -> (u8, u8);

    /// Attempts to advance the cursor to the next value in the stream at the current depth.
    /// If no value is encountered, returns None; otherwise, returns the Ion type of the next value.
    fn next(&mut self) -> IonResult<Option<StreamItem>>;

    /// Returns the Ion type of the value currently positioned under the cursor. If the cursor
    /// is not positioned over a value, returns None.
    fn ion_type(&self) -> Option<IonType>;

    /// Returns a slice containing all of the annotation symbol IDs for the current value.
    /// If there is no current value, returns an empty slice.
    fn annotation_ids(&self) -> &[SymbolId];

    /// If the current value is a field within a struct, returns the symbol ID of that
    /// field's name; otherwise, returns None.
    fn field_id(&self) -> Option<SymbolId>;

    /// If the current value is a null, returns the Ion type of the null; otherwise,
    /// returns None.
    fn read_null(&mut self) -> IonResult<Option<IonType>>;

    /// If the current value is a boolean, returns its value as a bool; otherwise, returns None.
    fn read_bool(&mut self) -> IonResult<Option<bool>>;

    /// If the current value is an integer, returns its value as an i64; otherwise, returns None.
    fn read_i64(&mut self) -> IonResult<Option<i64>>;

    /// If the current value is a float, returns its value as an f32; otherwise, returns None.
    fn read_f32(&mut self) -> IonResult<Option<f32>>;

    /// If the current value is a float, returns its value as an f64; otherwise, returns None.
    fn read_f64(&mut self) -> IonResult<Option<f64>>;

    /// If the current value is a decimal, returns its value as an BigDecimal; otherwise,
    /// returns None.
    fn read_big_decimal(&mut self) -> IonResult<Option<BigDecimal>>;

    /// If the current value is a string, returns its value as a String; otherwise, returns None.
    fn read_string(&mut self) -> IonResult<Option<String>>;

    /// If the current value is a symbol, returns its value as a SymbolId; otherwise, returns None.
    fn read_symbol_id(&mut self) -> IonResult<Option<SymbolId>>;

    /// If the current value is a blob, returns its value as a Vec<u8>; otherwise, returns None.
    fn read_blob_bytes(&mut self) -> IonResult<Option<Vec<u8>>>;

    /// If the current value is a clob, returns its value as a Vec<u8>; otherwise, returns None.
    fn read_clob_bytes(&mut self) -> IonResult<Option<Vec<u8>>>;

    /// If the current value is a timestamp, returns its value as a DateTime<FixedOffset>;
    /// otherwise, returns None.
    fn read_datetime(&mut self) -> IonResult<Option<DateTime<FixedOffset>>>;

    /// If the current value is a container (i.e. a struct, list, or s-expression), positions the
    /// cursor at the beginning of that container's sequence of child values. If the current value
    /// is not a container, returns Err.
    fn step_in(&mut self) -> IonResult<()>;

    /// Positions the cursor at the end of the container currently being traversed. Calling next()
    /// will position the cursor over the value that follows the container. If the cursor is not in
    /// a container (i.e. it is already at the top level), returns Err.
    fn step_out(&mut self) -> IonResult<()>;
}

#[derive(Debug, Eq, PartialEq)]
/// System-level stream components that a Cursor may encounter
pub enum StreamItem {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker,
    /// An $ion_symbol_table-annotated struct containing directives
    SymbolTableImport,
    /// A user-level Ion value (e.g. an integer, timestamp, or struct).
    /// Includes the value's IonType and whether it is null.
    Value(IonType, bool),
}
