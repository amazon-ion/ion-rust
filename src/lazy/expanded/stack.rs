use std::fmt::Debug;

use bumpalo::collections::Vec as BumpVec;

/// Backing storage for the [`MacroEvaluator`](crate::lazy::expanded::macro_evaluator::MacroEvaluator)'s
/// macro expansion and argument stacks.
///
/// This is implemented both by `Vec` (which has a static lifetime) and [`BumpVec`](bumpalo::collections::Vec),
/// which uses storage tied to the encoding context's lifetime.
pub trait Stack {
    type Storage<'a, T: 'a + Debug>: StackStorage<T> + Debug;
}

pub trait StackStorage<T> {
    fn push(&mut self, value: T);
    fn pop(&mut self) -> Option<T>;
    fn peek(&self) -> Option<&T>;
    fn peek_mut(&mut self) -> Option<&mut T>;
    fn clear(&mut self);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn as_slice(&self) -> &[T];
}

pub struct VecStack;

impl Stack for VecStack {
    type Storage<'a, T: 'a + Debug> = Vec<T>;
}

impl<T: Debug> StackStorage<T> for Vec<T> {
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

    fn as_slice(&self) -> &[T] {
        self.as_slice()
    }
}

pub struct BumpVecStack;

impl Stack for BumpVecStack {
    type Storage<'a, T: 'a + Debug> = BumpVec<'a, T>;
}

impl<'a, T: Debug + 'a> StackStorage<T> for BumpVec<'a, T> {
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

    fn as_slice(&self) -> &[T] {
        self.as_slice()
    }
}
