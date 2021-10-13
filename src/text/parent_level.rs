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

    pub fn ion_type(&self) -> IonType {
        self.ion_type
    }

    pub fn is_exhausted(&self) -> bool {
        self.is_exhausted
    }

    pub fn set_exhausted(&mut self, value: bool) {
        self.is_exhausted = value;
    }
}

#[cfg(test)]
mod parent_container_tests {
    use super::*;
    use crate::IonType;

    #[test]
    #[should_panic]
    fn create_parent_container_from_scalar() {
        ParentContainer::new(IonType::Timestamp);
    }
}
