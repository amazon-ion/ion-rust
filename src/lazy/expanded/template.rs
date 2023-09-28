use bumpalo::collections::Vec as BumpVec;

use crate::lazy::expanded::EncodingContext;
use crate::{Element, Sequence};

pub type TdlMacroInvocation<'top> = &'top Element;

pub struct TemplateSequenceIterator<'top> {
    // The list element over which we're iterating
    sequence: &'top Sequence,
    index: usize,
    macro_stack: BumpVec<'top, TdlMacroInvocation<'top>>,
}

impl<'top> TemplateSequenceIterator<'top> {
    pub fn new(context: EncodingContext<'top>, sequence: &'top Sequence) -> Self {
        Self {
            sequence,
            index: 0,
            macro_stack: BumpVec::new_in(context.allocator),
        }
    }
}

impl<'top> Iterator for TemplateSequenceIterator<'top> {
    type Item = &'top Element;

    fn next(&mut self) -> Option<Self::Item> {
        match self.sequence.get(self.index) {
            Some(element) => {
                self.index += 1;
                Some(element)
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use bumpalo::Bump;

    use crate::lazy::expanded::macro_table::MacroTable;
    use crate::lazy::expanded::template::TemplateSequenceIterator;
    use crate::lazy::expanded::EncodingContext;
    use crate::{Element, IonResult, SymbolTable};

    #[test]
    fn template_list() -> IonResult<()> {
        let data = "[1, (values 2 3 4), 5]";
        let element = Element::read_one(data)?;
        let sequence = element.as_list().expect("list");
        let macro_table = MacroTable::new();
        let symtab = SymbolTable::new();
        let allocator = Bump::new();
        let context = EncodingContext {
            macro_table: &macro_table,
            symbol_table: &symtab,
            allocator: &allocator,
        };
        let iter = TemplateSequenceIterator::new(context, sequence);
        for value in iter {
            println!("{:?}", value);
        }
        Ok(())
    }
}
