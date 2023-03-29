use crate::element::builders::SExpBuilder;
use crate::element::Element;
use crate::text::text_formatter::IonValueFormatter;
use std::fmt::{Display, Formatter};

/// An in-memory representation of an Ion s-expression
///
/// [`SExp`] implements [`IonSequence`], which defines most of its functionality.
/// ```
/// use ion_rs::element::{Element, IonSequence, List};
/// use ion_rs::ion_sexp;
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// let sexp = ion_sexp!(1 2 3);
/// assert_eq!(sexp.len(), 3);
/// assert_eq!(sexp.get(1), Some(&Element::integer(2)));
/// # Ok(())
/// # }
/// ```
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
