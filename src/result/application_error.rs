use std::error::Error;
use std::fmt;
use std::sync::Arc;

/// An error raised by application code (for example, a `WriteAsIon`
/// implementation) rather than by Ion itself.
///
/// Construct one with [`IonError::application`](crate::IonError::application). The original
/// error is this error's [`source`](Error::source). [`downcast_ref`](Self::downcast_ref) recovers
/// it when it was passed in as a concrete error type (or as a `Box<dyn Error + Send + Sync>`
/// holding one). String messages are kept only as `Display` text, and type-erasing wrappers such
/// as `anyhow::Error` are stored as the wrapper's internal type; neither can be downcast to an
/// original type.
#[derive(Clone, Debug)]
pub struct ApplicationError {
    // `Arc` rather than `Box` so that `IonError` can remain `Clone`. The newtype hosts the
    // identity `PartialEq` below so that `IonError` can derive `PartialEq`.
    error: Arc<dyn Error + Send + Sync + 'static>,
}

impl ApplicationError {
    pub(crate) fn new(error: Box<dyn Error + Send + Sync + 'static>) -> Self {
        ApplicationError {
            error: Arc::from(error),
        }
    }

    /// Returns a reference to the wrapped error if it is of type `E`.
    pub fn downcast_ref<E: Error + 'static>(&self) -> Option<&E> {
        self.error.downcast_ref::<E>()
    }
}

impl fmt::Display for ApplicationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

// Not derived: `#[source]` on the `Arc` field would make the `Arc` itself the source, so the
// payload could not be downcast from the error chain.
impl Error for ApplicationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&*self.error)
    }
}

/// Two `ApplicationError`s are equal only if they wrap the same allocation (i.e. one is a clone of
/// the other); arbitrary error types cannot be compared for equality.
impl PartialEq for ApplicationError {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.error, &other.error)
    }
}
