use crate::element::builders::SExpBuilder;
use crate::element::Element;
use crate::text::text_formatter::IonValueFormatter;
use std::fmt::{Display, Formatter};

/// An in-memory representation of an Ion s-expression
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SExp {
    pub(super) children: Vec<Element>,
}

impl SExp {
    pub(crate) fn new(children: Vec<Element>) -> Self {
        Self { children }
    }

    pub fn builder() -> SExpBuilder {
        SExpBuilder::new()
    }

    pub fn clone_builder(&self) -> SExpBuilder {
        SExpBuilder::with_initial_elements(&self.children)
    }
}

impl Display for SExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = IonValueFormatter { output: f };
        ivf.format_sexp(self).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}
