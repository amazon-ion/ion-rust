use std::error::Error;
use std::sync::Arc;
use thiserror::Error;

/// An error raised by application code (for example, a `WriteAsIon`
/// implementation) rather than by Ion itself.
///
/// Construct one with [`IonError::application`](crate::IonError::application). This error is
/// transparent: its `Display` text and [`source`](Error::source) are those of the original error.
/// [`downcast_ref`](Self::downcast_ref) recovers the original error when it was passed in as a
/// concrete error type (or as a `Box<dyn Error + Send + Sync>` holding one). String messages are
/// kept only as `Display` text, and type-erasing wrappers such as `anyhow::Error` are stored as
/// the wrapper's internal type; neither can be downcast to an original type.
#[derive(Clone, Debug, Error)]
#[error(transparent)]
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

/// Two `ApplicationError`s are equal only if they wrap the same allocation (i.e. one is a clone of
/// the other); arbitrary error types cannot be compared for equality.
impl PartialEq for ApplicationError {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.error, &other.error)
    }
}
