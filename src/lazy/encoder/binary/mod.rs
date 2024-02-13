pub mod v1_0;
pub mod v1_1;

/// Takes a series of `TYPE => METHOD` pairs, generating a function for each that calls the host
/// type's `encode_annotated` method to encode an annotations sequence and then delegates encoding
/// the value to the corresponding value writer method.
// This macro is used in the v1_0 and v1_1 binary writer implementations, which both define an
// `encode_annotated` method. That method is not codified (for example: in a trait); this relies
// solely on convention between the two.
macro_rules! annotate_and_delegate {
    // End of iteration
    () => {};
    // Recurses one argument pair at a time
    ($value_type:ty => $method:ident, $($rest:tt)*) => {
        fn $method(self, value: $value_type) -> IonResult<()> {
            self.encode_annotated(|value_writer| value_writer.$method(value))
        }
        annotate_and_delegate!($($rest)*);
    };
}
pub(crate) use annotate_and_delegate;
