use crate::lazy::decoder::{LazyDecoder, LazyRawValueExpr};
use bumpalo::collections::Vec as BumpVec;

pub struct RawValueExprCache<'top, D: LazyDecoder> {
    values: BumpVec<'top, LazyRawValueExpr<'top, D>>,
}
