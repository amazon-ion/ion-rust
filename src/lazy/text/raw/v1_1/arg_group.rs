use std::ops::Range;

use crate::lazy::decoder::{LazyRawValueExpr, RawValueExpr};
use crate::lazy::encoding::TextEncoding_1_1;
use crate::lazy::expanded::e_expression::ArgGroup;
use crate::lazy::expanded::macro_evaluator::{
    EExpressionArgGroup, MacroExpr, RawEExpression, ValueExpr,
};
use crate::lazy::expanded::template::{Parameter, ParameterEncoding};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::text::buffer::TextBufferView;
use crate::result::IonFailure;
use crate::{Decoder, HasRange, HasSpan, IonResult, LazyExpandedValue, Span};

#[derive(Copy, Clone, Debug)]
pub struct EExpArg<'top, D: Decoder> {
    parameter: &'top Parameter,
    expr: EExpArgExpr<'top, D>,
}

impl<'top, D: Decoder> EExpArg<'top, D> {
    pub fn new(parameter: &'top Parameter, expr: EExpArgExpr<'top, D>) -> Self {
        Self { parameter, expr }
    }

    pub fn encoding(&self) -> &'top Parameter {
        self.parameter
    }

    pub fn expr(&self) -> &EExpArgExpr<'top, D> {
        &self.expr
    }

    pub fn resolve(&self, context: EncodingContextRef<'top>) -> IonResult<ValueExpr<'top, D>> {
        let value_expr = match self.expr {
            EExpArgExpr::ValueLiteral(value) => {
                ValueExpr::ValueLiteral(LazyExpandedValue::from_literal(context, value))
            }
            EExpArgExpr::EExp(eexp) => {
                ValueExpr::MacroInvocation(MacroExpr::from_eexp(eexp.resolve(context)?))
            }
            EExpArgExpr::ArgGroup(group) => {
                ValueExpr::MacroInvocation(MacroExpr::from_eexp_arg_group(group.resolve(context)))
            }
        };
        Ok(value_expr)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum EExpArgExpr<'top, D: Decoder> {
    ValueLiteral(<D as Decoder>::Value<'top>),
    EExp(<D as Decoder>::EExp<'top>),
    ArgGroup(<<D as Decoder>::EExp<'top> as RawEExpression<'top, D>>::ArgGroup),
}

impl<'top, D: Decoder> EExpArgExpr<'top, D> {
    pub fn expect_value(&self) -> IonResult<<D as Decoder>::Value<'top>> {
        let EExpArgExpr::ValueLiteral(value) = self else {
            return IonResult::decoding_error(format!("expected a value literal, found {self:?}"));
        };
        Ok(*value)
    }

    pub fn expect_eexp(&self) -> IonResult<<D as Decoder>::EExp<'top>> {
        let EExpArgExpr::EExp(eexp) = self else {
            return IonResult::decoding_error(format!("expected an e-expression, found {self:?}"));
        };
        Ok(*eexp)
    }

    pub fn expect_arg_group(
        &self,
    ) -> IonResult<<<D as Decoder>::EExp<'top> as RawEExpression<'top, D>>::ArgGroup> {
        let EExpArgExpr::ArgGroup(group) = self else {
            return IonResult::decoding_error(format!("expected an arg group, found {self:?}"));
        };
        Ok(*group)
    }
}

impl<'top, D: Decoder> From<LazyRawValueExpr<'top, D>> for EExpArgExpr<'top, D> {
    fn from(value: LazyRawValueExpr<'top, D>) -> Self {
        match value {
            RawValueExpr::ValueLiteral(v) => EExpArgExpr::ValueLiteral(v),
            RawValueExpr::EExp(e) => EExpArgExpr::EExp(e),
        }
    }
}

impl<'top, D: Decoder> HasRange for EExpArgExpr<'top, D> {
    fn range(&self) -> Range<usize> {
        match self {
            EExpArgExpr::ValueLiteral(v) => v.range(),
            EExpArgExpr::EExp(e) => e.range(),
            EExpArgExpr::ArgGroup(a) => a.range(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TextEExpArgGroup<'top> {
    input: TextBufferView<'top>,
    parameter: &'top Parameter,
    // Notice that the expressions inside an arg group cannot themselves be arg groups,
    // only value literals or e-expressions.
    expr_cache: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
}

impl<'top> TextEExpArgGroup<'top> {
    pub fn new(
        parameter: &'top Parameter,
        input: TextBufferView<'top>,
        child_expr_cache: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
    ) -> Self {
        Self {
            input,
            parameter,
            expr_cache: child_expr_cache,
        }
    }
}

impl<'top> HasRange for TextEExpArgGroup<'top> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> HasSpan<'top> for TextEExpArgGroup<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TextEExpArgGroupIterator<'top> {
    child_expr_cache: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
    index: usize,
}

impl<'top> Iterator for TextEExpArgGroupIterator<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, TextEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        let child_expr = self.child_expr_cache.get(self.index)?;
        self.index += 1;
        Some(Ok(*child_expr))
    }
}

impl<'top> IntoIterator for TextEExpArgGroup<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, TextEncoding_1_1>>;
    type IntoIter = TextEExpArgGroupIterator<'top>;

    fn into_iter(self) -> Self::IntoIter {
        TextEExpArgGroupIterator {
            child_expr_cache: self.expr_cache,
            index: 0,
        }
    }
}

impl<'top> EExpressionArgGroup<'top, TextEncoding_1_1> for TextEExpArgGroup<'top> {
    fn encoding(&self) -> ParameterEncoding {
        self.parameter.encoding()
    }

    fn resolve(self, context: EncodingContextRef<'top>) -> ArgGroup<'top, TextEncoding_1_1> {
        ArgGroup::new(self, context)
    }
}
//
// #[test]
// fn do_it() -> IonResult<()> {
//     use crate::v1_1::RawBinaryWriter;
//     let mut writer = RawBinaryWriter::new(Vec::new())?;
//     // TODO: tagless encodings
//     for _ in 0..1 {
//         let mut eexp = writer.eexp_writer(3)?;
//         eexp.write(1670446800245i64)?
//             .write(418)?
//             .write("6")?
//             .write("1")?
//             .write("18b4fa")?;
//         let mut nested_eexp = eexp.eexp_writer(1)?;
//         nested_eexp
//             .write("region 4")?
//             .write("2022-12-07T20:59:59.744000Z")?;
//         nested_eexp.close()?;
//         eexp.close()?;
//     }
//     let bytes = writer.close()?;
//     println!("{bytes:#04X?}");
//     Ok(())
// }
//
// #[test]
// fn x() -> IonResult<()> {
//     let template_definition_text = r#"
//             (macro event (timestamp thread_id thread_name client_num host_id parameters*)
//                 {
//                     'timestamp': timestamp,
//                     'threadId': thread_id,
//                     'threadName': (make_string "scheduler-thread-" thread_name),
//                     'loggerName': "com.example.organization.product.component.ClassName",
//                     'logLevel': (quote INFO),
//                     'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
//                     'parameters': [
//                         "SUCCESS",
//                         (make_string "example-client-" client_num),
//                         (make_string "aws-us-east-5f-" host_id),
//                         parameters
//                     ]
//                 }
//             )
//         "#;
//     #[rustfmt::skip]
//     let bbb = vec![
//         // Ion v1.1 Version Marker
//         0xE0, 0x01, 0x01, 0xEA,
//         0x03, // Macro ID 3
//         0b10, // [NOTE: `0b`] `parameters*` arg is an arg group
//         0x66, // 6-byte integer (`timestamp` param)
//         0x75, 0x5D, 0x63, 0xEE, 0x84, 0x01,
//         0x62, // 2-byte integer (`thread_id` param)
//         0xA2, 0x01,
//         0x91, // 1-byte string (`thread_name` param)
//         0x36,
//         0x91, // 1-byte string (`client_num` param)
//         0x31,
//         0x96, // 6-byte string (`host_id` param)
//         0x31, 0x38, 0x62, 0x34, 0x66, 0x61,
//         0x4D, // Arg group length prefix
//         0x98, // 8-byte string
//         0x72, 0x65, 0x67, 0x69,
//         0x6F, 0x6E, 0x20, 0x34,
//         0xF9, // Long-form, 27-byte string
//         0x37, 0x32, 0x30, 0x32,
//         0x32, 0x2D, 0x31, 0x32,
//         0x2D, 0x30, 0x37, 0x54,
//         0x32, 0x30, 0x3A, 0x35,
//         0x39, 0x3A, 0x35, 0x39,
//         0x2E, 0x37, 0x34, 0x34,
//         0x30, 0x30, 0x30, 0x5A,
//     ];
//     let mut reader = Reader::new(v1_1::Binary, &bbb)?;
//     reader.register_template(template_definition_text)?;
//     let sequence = reader.read_all_elements()?;
//     for value in sequence {
//         println!("{value}");
//     }
//     Ok(())
// }
