use bumpalo::collections::Vec as BumpVec;
use std::fmt::Debug;

/// Backing storage for the [`MacroEvaluator`](crate::lazy::expanded::macro_evaluator::MacroEvaluator).
///
/// This is implemented both by `Vec` (which has a static lifetime) and [`BumpVec`](bumpalo::collections::Vec),
/// which uses storage tied to the encoding context's lifetime.
pub trait Stack<T>: Debug {
    fn push(&mut self, value: T);
    fn pop(&mut self) -> Option<T>;

    fn peek(&self) -> Option<&T>;
    fn peek_mut(&mut self) -> Option<&mut T>;

    fn clear(&mut self);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T: Debug> Stack<T> for Vec<T> {
    fn push(&mut self, value: T) {
        self.push(value)
    }

    fn pop(&mut self) -> Option<T> {
        self.pop()
    }

    fn peek(&self) -> Option<&T> {
        self.last()
    }

    fn peek_mut(&mut self) -> Option<&mut T> {
        self.last_mut()
    }

    fn clear(&mut self) {
        self.clear()
    }

    fn len(&self) -> usize {
        self.len()
    }
}

impl<'a, T: Debug> Stack<T> for BumpVec<'a, T> {
    fn push(&mut self, value: T) {
        self.push(value)
    }

    fn pop(&mut self) -> Option<T> {
        self.pop()
    }

    fn peek(&self) -> Option<&T> {
        self.last()
    }

    fn peek_mut(&mut self) -> Option<&mut T> {
        self.last_mut()
    }

    fn clear(&mut self) {
        self.clear()
    }

    fn len(&self) -> usize {
        self.len()
    }
}
