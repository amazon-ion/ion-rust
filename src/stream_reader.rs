use crate::element::{Blob, Clob};
use crate::result::IonResult;
use crate::types::{Decimal, Int, IonType, Str, Timestamp};

/**
 * This trait captures the format-agnostic parser functionality needed to navigate within an Ion
 * stream and read the values encountered into native Rust data types.
 *
 * Once a value has successfully been read from the stream using one of the read_* functions,
 * calling that function again may return an Err. This is left to the discretion of the implementor.
 */
pub trait IonReader {
    /// The type returned by calls to [Self::next], indicating the next entity in the stream.
    /// Reader implementations representing different levels of abstraction will surface
    /// different sets of encoding artifacts. While an application-level Reader would only surface
    /// Ion values, a lower level Reader might surface symbol tables, Ion version markers, etc.
    type Item;

    /// The types used to represent field names, annotations, and symbol values at this Reader's
    /// level of abstraction.
    type Symbol;

    /// Returns the (major, minor) version of the Ion stream being read. If ion_version is called
    /// before an Ion Version Marker has been read, the version (1, 0) will be returned.
    fn ion_version(&self) -> (u8, u8);

    /// Attempts to advance the cursor to the next value in the stream at the current depth.
    /// If no value is encountered, returns None; otherwise, returns the Ion type of the next value.
    fn next(&mut self) -> IonResult<Self::Item>;

    /// Returns a value describing the stream entity over which the Reader is currently positioned.
    /// Depending on the Reader's level of abstraction, that entity may or may not be an Ion value.
    fn current(&self) -> Self::Item;

    /// If the current item is a value, returns that value's Ion type. Otherwise, returns None.
    fn ion_type(&self) -> Option<IonType>;

    /// Returns an iterator that will yield each of the annotations for the current value in order.
    /// If there is no current value, returns an empty iterator.
    // TODO: When GATs are stabilized, we can change this to a known associated type that's generic
    //       over the lifetime of &self.
    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'a>;

    /// If the reader is positioned over a value with one or more annotations, returns `true`.
    /// Otherwise, returns `false`.
    fn has_annotations(&self) -> bool {
        // Implementations are encouraged to override this when there's a cheaper way of
        // determining whether the current value has annotations.
        self.annotations().next().is_some()
    }

    /// Returns the number of annotations on the current value. If there is no current value,
    /// returns zero.
    fn number_of_annotations(&self) -> usize {
        // Implementations are encouraged to override this when there's a cheaper way of
        // calculating the number of annotations.
        self.annotations().count()
    }

    /// If the current item is a field within a struct, returns `Ok(_)` with a [Self::Symbol]
    /// representing the field's name; otherwise, returns an [crate::IonError::IllegalOperation].
    ///
    /// Implementations may also return an error for other reasons; for example, if [Self::Symbol]
    /// is a text data type but the field name is an undefined symbol ID, the reader may return
    /// a decoding error.
    fn field_name(&self) -> IonResult<Self::Symbol>;

    /// Returns `true` if the reader is currently positioned over an Ion null of any type.
    fn is_null(&self) -> bool;

    /// Attempts to read the current item as an Ion null and return its Ion type. If the current
    /// item is not a null or an IO error is encountered while reading, returns [crate::IonError].
    fn read_null(&mut self) -> IonResult<IonType>;

    /// Attempts to read the current item as an Ion boolean and return it as a bool. If the current
    /// item is not a boolean or an IO error is encountered while reading, returns [crate::IonError].
    fn read_bool(&mut self) -> IonResult<bool>;

    /// Attempts to read the current item as an Ion integer and return it as an i64. If the current
    /// item is not an integer, the integer is too large to be represented as an `i64`, or an IO
    /// error is encountered while reading, returns [crate::IonError].
    fn read_i64(&mut self) -> IonResult<i64>;

    /// Attempts to read the current item as an Ion integer and return it as an [`Int`](crate::types::Int). If the
    /// current item is not an integer or an IO error is encountered while reading, returns
    /// [crate::IonError].
    fn read_int(&mut self) -> IonResult<Int>;

    /// Attempts to read the current item as an Ion float and return it as an f32. If the current
    /// item is not a float or an IO error is encountered while reading, returns [crate::IonError].
    fn read_f32(&mut self) -> IonResult<f32>;

    /// Attempts to read the current item as an Ion float and return it as an f64. If the current
    /// item is not a float or an IO error is encountered while reading, returns [crate::IonError].
    fn read_f64(&mut self) -> IonResult<f64>;

    /// Attempts to read the current item as an Ion decimal and return it as a [crate::Decimal]. If the current
    /// item is not a decimal or an IO error is encountered while reading, returns [crate::IonError].
    fn read_decimal(&mut self) -> IonResult<Decimal>;

    /// Attempts to read the current item as an Ion string and return it as a [String]. If the current
    /// item is not a string or an IO error is encountered while reading, returns [crate::IonError].
    fn read_string(&mut self) -> IonResult<Str>;

    /// Attempts to read the current item as an Ion string and return it as a [&str]. If the
    /// current item is not a string or an IO error is encountered while reading, returns
    /// [crate::IonError].
    fn read_str(&mut self) -> IonResult<&str>;

    /// Attempts to read the current item as an Ion symbol and return it as a [Self::Symbol]. If the
    /// current item is not a symbol or an IO error is encountered while reading, returns [crate::IonError].
    fn read_symbol(&mut self) -> IonResult<Self::Symbol>;

    /// Attempts to read the current item as an Ion blob and return it as a `Vec<u8>`. If the
    /// current item is not a blob or an IO error is encountered while reading, returns [crate::IonError].
    fn read_blob(&mut self) -> IonResult<Blob>;

    /// Attempts to read the current item as an Ion clob and return it as a `Vec<u8>`. If the
    /// current item is not a clob or an IO error is encountered while reading, returns [crate::IonError].
    fn read_clob(&mut self) -> IonResult<Clob>;

    /// Attempts to read the current item as an Ion timestamp and return [crate::Timestamp]. If the current
    /// item is not a timestamp or an IO error is encountered while reading, returns [crate::IonError].
    fn read_timestamp(&mut self) -> IonResult<Timestamp>;

    /// If the current value is a container (i.e. a struct, list, or s-expression), positions the
    /// cursor at the beginning of that container's sequence of child values. The application must
    /// call [Self::next()] to advance to the first child value. If the current value is not a container,
    /// returns [crate::IonError].
    fn step_in(&mut self) -> IonResult<()>;

    /// Positions the cursor at the end of the container currently being traversed. Calling [Self::next()]
    /// will position the cursor over the item that follows the container. If the cursor is not in
    /// a container (i.e. it is already at the top level), returns [crate::IonError].
    fn step_out(&mut self) -> IonResult<()>;

    /// If the reader is positioned at the top level, returns `None`. Otherwise, returns
    /// `Some(_)` with the parent container's [crate::IonType].
    fn parent_type(&self) -> Option<IonType>;

    /// Returns a [usize] indicating the Reader's current level of nesting. That is: the number of
    /// times the Reader has stepped into a container without later stepping out. At the top level,
    /// this method returns `0`.
    fn depth(&self) -> usize;
}
