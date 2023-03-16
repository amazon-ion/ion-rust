use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::IonResult;
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::types::IonType;
use crate::Integer;

/**
 * This trait captures the format-agnostic encoding functionality needed to write native Rust types
 * to a stream as Ion values.
 */
pub trait IonWriter {
    /// Returns the (major, minor) version of the Ion stream being written. If ion_version is called
    /// before an Ion Version Marker has been emitted, the version (1, 0) will be returned.
    fn ion_version(&self) -> (u8, u8);

    /// Writes an Ion version marker to the output stream.
    fn write_ion_version_marker(&mut self, major: u8, minor: u8) -> IonResult<()>;

    /// Returns `true` if this RawWriter supports writing field names, annotations, and
    /// symbol values directly as text; otherwise, returns `false`.
    ///
    /// If this method returns `false`, passing a [crate::RawSymbolToken::Text] to the
    /// [Self::set_annotations], [Self::set_field_name], or [Self::write_symbol] methods may result
    /// in a panic.
    fn supports_text_symbol_tokens(&self) -> bool;

    /// Sets a list of annotations that will be applied to the next value that is written.
    fn set_annotations<I, A>(&mut self, annotations: I)
    where
        A: AsRawSymbolTokenRef,
        I: IntoIterator<Item = A>;

    /// Writes an Ion `null` with the specified type to the output stream.
    /// To write an untyped `null` (which is equivalent to `null.null`), pass [IonType::Null].
    fn write_null(&mut self, ion_type: IonType) -> IonResult<()>;

    /// Writes an Ion `boolean` with the specified value to the output stream.
    fn write_bool(&mut self, value: bool) -> IonResult<()>;

    /// Writes an Ion `integer` with the specified value to the output stream.
    fn write_i64(&mut self, value: i64) -> IonResult<()>;

    /// Writes an Ion `integer` with the specified value to the output stream.
    fn write_integer(&mut self, value: &Integer) -> IonResult<()>;

    /// Writes an Ion `float` with the specified value to the output stream.
    fn write_f32(&mut self, value: f32) -> IonResult<()>;

    /// Writes an Ion `float` with the specified value to the output stream.
    fn write_f64(&mut self, value: f64) -> IonResult<()>;

    /// Writes an Ion `decimal` with the specified value to the output stream.
    fn write_decimal(&mut self, value: &Decimal) -> IonResult<()>;

    /// Writes an Ion `timestamp` with the specified value to the output stream.
    fn write_timestamp(&mut self, value: &Timestamp) -> IonResult<()>;

    /// Writes an Ion `symbol` with the specified value to the output stream.
    fn write_symbol<A: AsRawSymbolTokenRef>(&mut self, value: A) -> IonResult<()>;

    /// Writes an Ion `string` with the specified value to the output stream.
    fn write_string<A: AsRef<str>>(&mut self, value: A) -> IonResult<()>;

    /// Writes an Ion `clob` with the specified value to the output stream.
    fn write_clob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()>;

    /// Writes an Ion `blob` with the specified value to the output stream.
    fn write_blob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()>;

    /// Starts a new Ion container with the specified type.
    /// The only valid IonType values are:
    /// * [IonType::List]
    /// * [IonType::SExp]
    /// * [IonType::Struct]
    /// Passing any other IonType will result in an `Err`.
    fn step_in(&mut self, container_type: IonType) -> IonResult<()>;

    /// Sets the current field name to `name`. If the TextWriter is currently positioned inside
    /// of a struct, the field name will be written before the next value. Otherwise, it will be
    /// ignored.
    fn set_field_name<A: AsRawSymbolTokenRef>(&mut self, name: A);

    /// If the writer is positioned at the top level, returns `None`. Otherwise, returns
    /// `Some(_)` with the parent container's [IonType].
    fn parent_type(&self) -> Option<IonType>;

    /// Returns the number of containers that the writer has stepped into without subsequently
    /// stepping out.
    fn depth(&self) -> usize;

    /// Ends the current container. If the writer is not currently positioned within a container,
    /// calling this method will result in an `Err`.
    fn step_out(&mut self) -> IonResult<()>;

    /// Causes any buffered data to be written to the underlying io::Write implementation.
    /// This method can only be called when the writer is at the top level.
    fn flush(&mut self) -> IonResult<()>;
}
