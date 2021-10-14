use crate::IonType;

/// Represents a container that the text reader has stepped into.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ParentContainer {
    // The container type the reader has stepped into
    ion_type: IonType,
    // Whether the reader has encountered the end of the container yet
    is_exhausted: bool,
}

impl ParentContainer {
    pub fn new(ion_type: IonType) -> Self {
        assert!(
            ion_type.is_container(),
            "Cannot create a `ParentContainer` from a scalar: {}",
            ion_type
        );
        ParentContainer {
            ion_type,
            is_exhausted: false,
        }
    }

    /// Returns the IonType associated with this container. The IonType will always be `List`,
    /// `SExpression`, or `Struct`.
    pub fn ion_type(&self) -> IonType {
        self.ion_type
    }

    /// If the reader has reached the end of the container, this will return true.
    pub fn is_exhausted(&self) -> bool {
        self.is_exhausted
    }

    /// Sets the value that will be returned by `is_exhausted`. Will be called by the reader
    /// when it reaches the end marker (`]`, `)`, or `}`) of the current container.
    pub fn set_exhausted(&mut self, value: bool) {
        self.is_exhausted = value;
    }
}

#[cfg(test)]
mod parent_container_tests {
    use super::*;
    use crate::IonType;
    use rstest::*;

    #[rstest]
    #[case::list(IonType::List)]
    #[case::list(IonType::SExpression)]
    #[case::list(IonType::Struct)]
    #[should_panic]
    #[case::list(IonType::Integer)]
    #[should_panic]
    #[case::list(IonType::Null)]
    #[should_panic]
    #[case::list(IonType::Decimal)]
    fn create_parent_container_from_ion_type(#[case] ion_type: IonType) {
        ParentContainer::new(ion_type);
    }
}
