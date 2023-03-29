use crate::element::builders::ListBuilder;
use crate::element::Element;
use crate::text::text_formatter::IonValueFormatter;
use std::fmt::{Display, Formatter};

/// An in-memory representation of an Ion list
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct List {
    pub(super) children: Vec<Element>,
}

impl List {
    pub(crate) fn new(children: Vec<Element>) -> Self {
        Self { children }
    }

    pub fn builder() -> ListBuilder {
        ListBuilder::new()
    }

    pub fn clone_builder(&self) -> ListBuilder {
        ListBuilder::with_initial_elements(&self.children)
    }
}

impl Display for List {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = IonValueFormatter { output: f };
        ivf.format_list(self).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}
