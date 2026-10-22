//! Types for reporting various modes of success or failure.

use std::borrow::Cow;
use std::convert::From;
use std::fmt::{Debug, Error};
use std::{fmt, io};

use ice_code::ice as cold_path;
use thiserror::Error;

#[cfg(feature = "experimental-serde")]
use serde::{de, ser};

mod application_error;
mod conversion;
mod decoding_error;
mod encoding_error;
mod illegal_operation;
mod incomplete;
mod io_error;

pub use application_error::ApplicationError;
pub use conversion::ConversionOperationError;
pub use conversion::ConversionOperationResult;
pub use conversion::IonTypeExpectation;
pub use conversion::TypeExpectation;
pub use decoding_error::DecodingError;
pub use encoding_error::EncodingError;
pub use illegal_operation::IllegalOperation;
pub use incomplete::IncompleteError;
pub use io_error::IoError;

use crate::position::Position;
use crate::result::conversion::{ConversionError, ValueTypeExpectation};

/// A unified Result type representing the outcome of method calls that may fail.
pub type IonResult<T> = Result<T, IonError>;

/// Represents the different types of high-level failures that might occur when reading Ion data.
#[non_exhaustive]
#[derive(Clone, Debug, Error, PartialEq)]
pub enum IonError {
    /// Indicates that an IO error was encountered while reading or writing.
    #[error("{0}")]
    Io(#[from] IoError),

    /// Indicates that the input buffer did not contain enough data to perform the requested read
    /// operation. If the input source contains more data, the reader can append it to the buffer
    /// and try again.
    #[error("{0}")]
    Incomplete(#[from] IncompleteError),

    /// Indicates that the writer encountered a problem while serializing a given piece of data.
    #[error("{0}")]
    Encoding(#[from] EncodingError),

    /// Indicates that the data stream being read contained illegal or otherwise unreadable data.
    #[error("{0}")]
    Decoding(#[from] DecodingError),

    /// Returned when the user has performed an illegal operation (for example: calling stepOut()
    /// on the cursor at the top level.)
    #[error("{0}")]
    IllegalOperation(#[from] IllegalOperation),

    /// Returned when the user has attempted to convert a value to a type for which that value is
    /// not trivially convertable.
    #[error("{0}")]
    Conversion(#[from] ConversionError),

    /// Returned when application code (for example, a `WriteAsIon`
    /// implementation) raises its own error. See [`IonError::application`].
    // `transparent` (here and on `ApplicationError`) so that the application's error message
    // appears only once when reporters print the `source` chain.
    #[error(transparent)]
    Application(#[from] ApplicationError),
}

impl IonError {
    /// Converts an error raised by application code into an `IonError`, wrapping it in a new
    /// [`ApplicationError`] unless it is already an `IonError` or an `ApplicationError`.
    ///
    /// A wrapped error is recoverable with [`ApplicationError::downcast_ref`] if it was passed in
    /// as a concrete error type; see [`ApplicationError`] for the payloads that cannot be
    /// downcast.
    ///
    /// If `error` is itself an `IonError` (directly or in a `Box<dyn Error + Send + Sync>`), it is
    /// returned unchanged so that it keeps its original variant. An `ApplicationError` is returned
    /// as an `IonError::Application` without being wrapped again, so its payload stays
    /// downcastable. An `IonError` held inside any other type, such as an application error enum
    /// with an `Ion(IonError)` case or an `anyhow::Error`, is not unwrapped; extract or downcast it
    /// to `IonError` first rather than passing the whole value to this function.
    ///
    /// ```
    /// use ion_rs::{IonError, IonResult};
    ///
    /// #[derive(Debug, thiserror::Error)]
    /// #[error("account {0} is closed")]
    /// struct AccountClosed(u64);
    ///
    /// impl From<AccountClosed> for IonError {
    ///     fn from(error: AccountClosed) -> Self {
    ///         IonError::application(error)
    ///     }
    /// }
    ///
    /// fn ensure_open(id: u64, closed: bool) -> Result<(), AccountClosed> {
    ///     if closed {
    ///         return Err(AccountClosed(id));
    ///     }
    ///     Ok(())
    /// }
    ///
    /// fn write_account(id: u64, closed: bool) -> IonResult<()> {
    ///     ensure_open(id, closed)?;
    ///     // ... write the account ...
    ///     Ok(())
    /// }
    ///
    /// let error = write_account(42, true).unwrap_err();
    /// let IonError::Application(application_error) = &error else {
    ///     panic!("expected an application error");
    /// };
    /// let account_closed = application_error.downcast_ref::<AccountClosed>().unwrap();
    /// assert_eq!(account_closed.0, 42);
    /// assert_eq!(error.to_string(), "account 42 is closed");
    /// ```
    pub fn application(
        error: impl Into<Box<dyn std::error::Error + Send + Sync + 'static>>,
    ) -> Self {
        cold_path! {
            application_error => match error.into().downcast::<IonError>() {
                Ok(ion_error) => *ion_error,
                Err(error) => match error.downcast::<ApplicationError>() {
                    Ok(wrapped) => (*wrapped).into(),
                    Err(error) => ApplicationError::new(error).into(),
                },
            }
        }
    }
}

impl From<io::Error> for IonError {
    fn from(io_error: io::Error) -> Self {
        IoError::from(io_error).into()
    }
}

impl From<io::ErrorKind> for IonError {
    fn from(error_kind: io::ErrorKind) -> Self {
        // io::ErrorKind -> io::Error
        let io_error = io::Error::from(error_kind);
        // io::Error -> IoError -> IonError
        IoError::from(io_error).into()
    }
}

impl From<fmt::Error> for IonError {
    fn from(error: Error) -> Self {
        EncodingError::new(error.to_string()).into()
    }
}

impl From<IonError> for fmt::Error {
    fn from(_ion_error: IonError) -> Self {
        // This no-op transformation allows `?` to be used in `Debug` implementations wherever
        // an IonError could surface.
        fmt::Error
    }
}

impl<FromType, ToType> From<ConversionOperationError<FromType, ToType>> for IonError
where
    FromType: ValueTypeExpectation,
    ToType: TypeExpectation,
{
    fn from(err: ConversionOperationError<FromType, ToType>) -> Self {
        ConversionError::from(err).into()
    }
}

#[cfg(feature = "experimental-serde")]
impl de::Error for IonError {
    fn custom<T>(error: T) -> Self
    where
        T: std::fmt::Display,
    {
        DecodingError::new(error.to_string()).into()
    }
}

#[cfg(feature = "experimental-serde")]
impl ser::Error for IonError {
    fn custom<T>(error: T) -> Self
    where
        T: std::fmt::Display,
    {
        EncodingError::new(error.to_string()).into()
    }
}

// Crate-visible convenience methods for constructing error variants and wrapping them in the
// appropriate type: IonResult<T> or IonError. This is a trait so these methods can be added to
// `IonResult<T>`, which is just a type alias for `Result<T, IonError>`, whose implementation
// does not live in this crate.
pub(crate) trait IonFailure {
    // Note: this trait does not have an `io(...)` method because the only way we ever construct
    // an `IonError::Io` is by converting a `std::io::IoError` with the ? operator.
    // Because this trait is only crate-visible, methods can be added/changed as needed in
    // the future.
    fn incomplete(label: impl Into<Cow<'static, str>>, position: impl Into<Position>) -> Self;
    fn decoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self;
    fn encoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self;
    fn illegal_operation<S: Into<Cow<'static, str>>>(operation: S) -> Self;
}

impl IonFailure for IonError {
    fn incomplete(label: impl Into<Cow<'static, str>>, position: impl Into<Position>) -> Self {
        IncompleteError::new(label, position).into()
    }

    fn decoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self {
        DecodingError::new(description).into()
    }

    fn encoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self {
        EncodingError::new(description).into()
    }

    fn illegal_operation<S: Into<Cow<'static, str>>>(operation: S) -> Self {
        IllegalOperation::new(operation).into()
    }
}

impl<T> IonFailure for IonResult<T> {
    fn incomplete(label: impl Into<Cow<'static, str>>, position: impl Into<Position>) -> Self {
        Err(IonError::incomplete(label, position))
    }

    fn decoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self {
        Err(IonError::decoding_error(description))
    }

    fn encoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self {
        Err(IonError::encoding_error(description))
    }

    fn illegal_operation<S: Into<Cow<'static, str>>>(operation: S) -> Self {
        Err(IonError::illegal_operation(operation))
    }
}

#[cfg(test)]
mod tests {
    use super::{ApplicationError, IonError, IonFailure};
    use crate::position::Position;
    use rstest::rstest;
    use std::error::Error;
    use std::mem::{align_of, size_of};

    #[derive(Debug, thiserror::Error, PartialEq)]
    #[error("account {0} is closed")]
    struct AccountClosed(u64);

    fn application_error(error: &IonError) -> &ApplicationError {
        match error {
            IonError::Application(application_error) => application_error,
            other => panic!("expected IonError::Application, found {other:?}"),
        }
    }

    /// `IonError` is returned (inside `IonResult`) from nearly every read/write operation, so its
    /// size directly inflates the size of `Result<T, IonError>` on hot paths. The largest inline
    /// variant payloads (`DecodingError`, `IncompleteError`, `ConversionError`) are boxed down to a
    /// single pointer; the 32-byte bound is currently pinned by the still-inline `Cow<'static, str>`
    /// payloads of `EncodingError`/`IllegalOperation` (24 bytes + the enum discriminant). This
    /// guards against a regression that would reintroduce a large inline payload.
    #[test]
    fn ion_error_stays_small() {
        assert!(
            size_of::<IonError>() <= 32,
            "size_of::<IonError>() = {} (expected <= 32); a variant likely gained a large inline \
             payload — box it as done for position/type-name data",
            size_of::<IonError>()
        );
        assert!(
            align_of::<IonError>() <= 8,
            "align_of::<IonError>() = {} (expected <= 8)",
            align_of::<IonError>()
        );
    }

    // Boxing moved these errors' fields into private inner structs. These assert that the
    // user-visible `Display` text is unchanged (guards against, e.g., transposing the two
    // positional format arguments, which would still compile).
    #[test]
    fn display_text_is_stable() {
        let decoding = IonError::decoding_error("bad input");
        assert_eq!(decoding.to_string(), "bad input");

        let incomplete = IonError::incomplete("a value", Position::with_offset(42));
        assert_eq!(
            incomplete.to_string(),
            "ran out of input while reading a value at offset 42"
        );
    }

    #[test]
    fn ion_error_is_send_sync_static() {
        fn assert_send_sync_static<T: Send + Sync + 'static>() {}
        assert_send_sync_static::<IonError>();
    }

    #[test]
    fn application_error_downcasts_to_original() {
        let error = IonError::application(AccountClosed(42));
        let wrapped = application_error(&error).downcast_ref::<AccountClosed>();
        assert_eq!(wrapped, Some(&AccountClosed(42)));
        assert!(application_error(&error)
            .downcast_ref::<std::fmt::Error>()
            .is_none());
    }

    #[test]
    fn application_error_displays_original() {
        let error = IonError::application(AccountClosed(42));
        assert_eq!(error.to_string(), "account 42 is closed");
    }

    #[derive(Debug, thiserror::Error)]
    #[error("write failed")]
    struct WriteFailed(#[source] AccountClosed);

    /// The `Display` text of `error` and of each error in its `source` chain, as printed by error
    /// reporters such as `anyhow`'s `{:#}`.
    fn error_chain(error: &IonError) -> Vec<String> {
        std::iter::successors(Some(error as &dyn Error), |&e| e.source())
            .map(ToString::to_string)
            .collect()
    }

    #[rstest]
    #[case::without_source(IonError::application(AccountClosed(42)), &["account 42 is closed"])]
    #[case::with_source(
        IonError::application(WriteFailed(AccountClosed(42))),
        &["write failed", "account 42 is closed"]
    )]
    fn application_error_chain_does_not_repeat_messages(
        #[case] error: IonError,
        #[case] expected: &[&str],
    ) {
        assert_eq!(error_chain(&error), expected);
    }

    #[test]
    fn application_error_accepts_string_message() {
        let error = IonError::application("something went wrong");
        assert_eq!(error.to_string(), "something went wrong");
    }

    #[test]
    fn application_returns_ion_error_unchanged() {
        let original = IonError::encoding_error("bad value");
        let error = IonError::application(original.clone());
        assert_eq!(error, original);
    }

    #[test]
    fn application_returns_boxed_ion_error_unchanged() {
        let original = IonError::encoding_error("bad value");
        let boxed = Box::new(original.clone()) as Box<dyn Error + Send + Sync>;
        let error = IonError::application(boxed);
        assert_eq!(error, original);
    }

    #[test]
    fn application_does_not_rewrap_application_error() {
        let original = IonError::application(AccountClosed(42));
        let error = IonError::application(application_error(&original).clone());
        assert_eq!(error, original);
    }

    #[test]
    fn application_error_downcasts_boxed_original() {
        let boxed = Box::new(AccountClosed(42)) as Box<dyn Error + Send + Sync>;
        let error = IonError::application(boxed);
        let wrapped = application_error(&error).downcast_ref::<AccountClosed>();
        assert_eq!(wrapped, Some(&AccountClosed(42)));
    }

    #[test]
    fn application_error_equals_its_clone() {
        let error = IonError::application(AccountClosed(42));
        assert_eq!(error, error.clone());
    }

    #[test]
    fn separately_constructed_application_errors_are_not_equal() {
        let a = IonError::application(AccountClosed(42));
        let b = IonError::application(AccountClosed(42));
        assert_ne!(a, b);
    }
}
