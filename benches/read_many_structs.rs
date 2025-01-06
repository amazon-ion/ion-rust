use criterion::{criterion_group, criterion_main};
use ion_rs::MacroTable;

#[cfg(not(feature = "experimental"))]
mod benchmark {
    use criterion::Criterion;

    pub fn criterion_benchmark(_c: &mut Criterion) {
        panic!("This benchmark requires the 'experimental' feature to work; try again with `--features experimental`");
    }
}

/// An Ion 1.1 test stream to benchmark. Each instance of this type contains data that was encoded
/// with different settings; for example, using more or fewer macros, or using length-prefixing.
#[allow(non_camel_case_types)]
pub struct TestData_1_1 {
    name: String,
    template_definition_text: String,
    text_data: String,
    binary_data: Vec<u8>,
}

/// Produces an Ion 1.1 stream with `num_values` top-level e-expressions. Each e-expression invokes
/// a template that makes more extensive use of macros to minimize the size of each invocation. This
/// makes the stream much more compact, but comes at the expense of evaluation overhead when the
/// stream is read. If only a subset of the fields are read from each value, this overhead will be
/// minimal.
fn maximally_compact_1_1_data(num_values: usize) -> TestData_1_1 {
    let template_definition_text: String = r#"
        (macro event (timestamp thread_id thread_name client_num host_id parameters*)
            {
                timestamp: (%timestamp),
                threadId: (%thread_id),
                threadName: (.make_string "scheduler-thread-" (%thread_name)),
                loggerName: "com.example.organization.product.component.ClassName",
                logLevel: INFO,
                format: "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
                parameters: [
                    "SUCCESS",
                    (.make_string "example-client-" (%client_num)),
                    (.make_string "aws-us-east-5f-" (%host_id)),
                    (%parameters)
                ]
            }
        )
    "#.to_owned();

    let text_1_1_data = r#"(:event 1670446800245 418 "6" "1" "abc123" (:: "region 4" "2022-12-07T20:59:59.744000Z"))"#.repeat(num_values);

    #[rustfmt::skip]
    let binary_1_1_data: Vec<u8> = [MacroTable::FIRST_USER_MACRO_ID as u8, // Macro ID
        0b10, // [NOTE: `0b`] `parameters*` arg is an arg group
        0x66, // 6-byte integer (`timestamp` param)
        0x75, 0x5D, 0x63, 0xEE, 0x84, 0x01,
        0x62, // 2-byte integer (`thread_id` param)
        0xA2, 0x01,
        0x91, // 1-byte string (`thread_name` param)
        0x36,
        0x91, // 1-byte string (`client_num` param)
        0x31,
        0x96, // 6-byte string (`host_id` param)
        0x61, 0x62, 0x63, 0x31, 0x32, 0x33,
        0x4D, // Arg group length prefix
        0x98, // 8-byte string
        0x72, 0x65, 0x67, 0x69,
        0x6F, 0x6E, 0x20, 0x34,
        0xF9, // Long-form, 27-byte string
        0x37, 0x32, 0x30, 0x32,
        0x32, 0x2D, 0x31, 0x32,
        0x2D, 0x30, 0x37, 0x54,
        0x32, 0x30, 0x3A, 0x35,
        0x39, 0x3A, 0x35, 0x39,
        0x2E, 0x37, 0x34, 0x34,
        0x30, 0x30, 0x30, 0x5A].repeat(num_values);
    TestData_1_1 {
        name: "maximally compact".to_owned(),
        template_definition_text,
        text_data: text_1_1_data,
        binary_data: binary_1_1_data,
    }
}

/// Produces an Ion 1.1 stream with `num_values` top-level e-expressions. Each e-expression invokes
/// a template that does not use additional macros. This makes the stream compact relative to its
/// Ion 1.0 equivalent, but not as compact as it is in the "maximally compact" configuration above.
/// The lighter use of macros means that there is less evaluation overhead at read time.
fn moderately_compact_1_1_data(num_values: usize) -> TestData_1_1 {
    let template_definition_text = r#"
        (macro event (timestamp thread_id thread_name client_num host_id parameters*)
            {
                timestamp: (%timestamp),
                threadId: (%thread_id),
                threadName: (%thread_name),
                loggerName: "com.example.organization.product.component.ClassName",
                logLevel: INFO,
                format: "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
                parameters: [
                    "SUCCESS",
                    (%client_num),
                    (%host_id),
                    (%parameters)
                ]
            }
        )
    "#;

    let text_1_1_data = r#"(:event 1670446800245 418 "scheduler-thread-6" "example-client-1" "aws-us-east-5f-abc123" (:: "region 4" "2022-12-07T20:59:59.744000Z"))"#.repeat(num_values);
    #[rustfmt::skip]
    let binary_1_1_data: Vec<u8> = [MacroTable::FIRST_USER_MACRO_ID as u8, // Macro ID
        0b10, // [NOTE: `0b` prefix] `parameters*` arg is an arg group
        0x66, // 6-byte integer (`timestamp` param)
        0x75, 0x5D, 0x63, 0xEE, 0x84, 0x01,
        0x62, // 2-byte integer (`thread_id` param)
        0xA2, 0x01,
        0xF9, // long-form string (`thread_name` param)
        0x25, // FlexUInt byte length 18
        // "scheduler-thread-6"
        0x73, 0x63, 0x68, 0x65, 0x64, 0x75, 0x6C, 0x65, 0x72, 0x2D, 0x74, 0x68, 0x72, 0x65, 0x61, 0x64, 0x2D, 0x36,
        0xF9, // 1-byte string (`client_num` param)
        0x21, // FlexUInt byte length 16
         // "example-client-1"
        0x65, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2D, 0x63, 0x6C, 0x69, 0x65, 0x6E, 0x74, 0x2D, 0x31,
        0xF9, // long-form string (`host_id` param)
        0x2B, // FlexUInt byte length 21
        // "aws-us-east-5f-abc123"
        0x61, 0x77, 0x73, 0x2D, 0x75, 0x73,
        0x2D, 0x65, 0x61, 0x73, 0x74, 0x2D,
        0x35, 0x66, 0x2D, 0x61, 0x62, 0x63, 0x31, 0x32, 0x33,
        0x4D, // Arg group length prefix
        0x98, // 8-byte string
        0x72, 0x65, 0x67, 0x69,
        0x6F, 0x6E, 0x20, 0x34,
        0xF9, // Long-form, 27-byte string
        0x37, 0x32, 0x30, 0x32,
        0x32, 0x2D, 0x31, 0x32,
        0x2D, 0x30, 0x37, 0x54,
        0x32, 0x30, 0x3A, 0x35,
        0x39, 0x3A, 0x35, 0x39,
        0x2E, 0x37, 0x34, 0x34,
        0x30, 0x30, 0x30, 0x5A].repeat(num_values);

    TestData_1_1 {
        name: "moderately compact".to_owned(),
        template_definition_text: template_definition_text.to_owned(),
        text_data: text_1_1_data,
        binary_data: binary_1_1_data,
    }
}

/// Like `moderately_compact_1_1_data` above, but each top-level e-expression in the stream is
/// length-prefixed. This allows the reader to step over e-expressions without fully parsing them,
/// making top-level skip-scanning highly efficient at the expense of 1-2 extra bytes per
/// e-expression.
fn length_prefixed_moderately_compact_1_1_data(num_values: usize) -> TestData_1_1 {
    let template_definition_text = r#"
        (macro event (timestamp thread_id thread_name client_num host_id parameters*)
            {
                timestamp: (%timestamp),
                threadId: (%thread_id),
                threadName: (%thread_name),
                loggerName: "com.example.organization.product.component.ClassName",
                logLevel: INFO,
                format: "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
                parameters: [
                    "SUCCESS",
                    (%client_num),
                    (%host_id),
                    (%parameters)
                ]
            }
        )
    "#;

    let text_1_1_data = r#"(:event 1670446800245 418 "scheduler-thread-6" "example-client-1" "aws-us-east-5f-abc123" (:: "region 4" "2022-12-07T20:59:59.744000Z"))"#.repeat(num_values);
    #[rustfmt::skip]
    let binary_1_1_data: Vec<u8> = [0xF5, // LP invocation
        ((MacroTable::FIRST_USER_MACRO_ID * 2) + 1) as u8, // Macro ID
        0xDF, // Length prefix: FlexUInt 111
        0b10, // [NOTE: `0b` prefix] `parameters*` arg is an arg group
        0x66, // 6-byte integer (`timestamp` param)
        0x75, 0x5D, 0x63, 0xEE, 0x84, 0x01,
        0x62, // 2-byte integer (`thread_id` param)
        0xA2, 0x01,
        0xF9, // long-form string (`thread_name` param)
        0x25, // FlexUInt byte length 18
        // "scheduler-thread-6"
        0x73, 0x63, 0x68, 0x65, 0x64, 0x75, 0x6C, 0x65, 0x72, 0x2D, 0x74, 0x68, 0x72, 0x65, 0x61, 0x64, 0x2D, 0x36,
        0xF9, // 1-byte string (`client_num` param)
        0x21, // FlexUInt byte length 16
        // "example-client-1"
        0x65, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2D, 0x63, 0x6C, 0x69, 0x65, 0x6E, 0x74, 0x2D, 0x31,
        0xF9, // long-form string (`host_id` param)
        0x2B, // FlexUInt byte length 21
        // "aws-us-east-5f-abc123"
        0x61, 0x77, 0x73, 0x2D, 0x75, 0x73,
        0x2D, 0x65, 0x61, 0x73, 0x74, 0x2D,
        0x35, 0x66, 0x2D, 0x61, 0x62, 0x63, 0x31, 0x32, 0x33,
        0x4D, // Arg group length prefix
        0x98, // 8-byte string
        0x72, 0x65, 0x67, 0x69,
        0x6F, 0x6E, 0x20, 0x34,
        0xF9, // Long-form, 27-byte string
        0x37, 0x32, 0x30, 0x32,
        0x32, 0x2D, 0x31, 0x32,
        0x2D, 0x30, 0x37, 0x54,
        0x32, 0x30, 0x3A, 0x35,
        0x39, 0x3A, 0x35, 0x39,
        0x2E, 0x37, 0x34, 0x34,
        0x30, 0x30, 0x30, 0x5A].repeat(num_values);

    TestData_1_1 {
        name: "moderately compact w/length-prefixed top level".to_owned(),
        template_definition_text: template_definition_text.to_owned(),
        text_data: text_1_1_data,
        binary_data: binary_1_1_data,
    }
}

#[cfg(feature = "experimental")]
mod benchmark {
    use criterion::{black_box, Criterion};

    use crate::{
        length_prefixed_moderately_compact_1_1_data, maximally_compact_1_1_data,
        moderately_compact_1_1_data, TestData_1_1,
    };
    use ion_rs::{
        v1_0, v1_1, ElementReader, Encoding, EncodingContext, IonData, IonVersion,
        LazyRawBinaryReader_1_1, RawEExpression, RawStreamItem, Reader, Sequence, TemplateCompiler,
        ValueExpr, WriteConfig,
    };
    use ion_rs::{Decoder, Element, IonResult, LazyStruct, LazyValue, ValueRef};

    /// The entrypoint for the benchmark.
    pub fn criterion_benchmark(c: &mut Criterion) {
        const NUM_VALUES: usize = 10_000;
        let seq_1_0 = benchmark_1_0(c, NUM_VALUES).unwrap();
        benchmark_1_1(c, &seq_1_0, maximally_compact_1_1_data(NUM_VALUES)).unwrap();
        benchmark_1_1(c, &seq_1_0, moderately_compact_1_1_data(NUM_VALUES)).unwrap();
        benchmark_1_1(
            c,
            &seq_1_0,
            length_prefixed_moderately_compact_1_1_data(NUM_VALUES),
        )
        .unwrap();
    }

    /// Reads this value and, if it's a container, any nested values. Returns the number of values read.
    fn count_value_and_children<D: Decoder>(lazy_value: &LazyValue<'_, D>) -> IonResult<usize> {
        use ValueRef::*;
        let child_count = match lazy_value.read()? {
            List(s) => count_sequence_children(s.iter())?,
            SExp(s) => count_sequence_children(s.iter())?,
            Struct(s) => count_struct_children(&s)?,
            scalar => {
                let _ = black_box(scalar);
                0
            }
        };
        Ok(1 + child_count)
    }

    /// Reads the child values of a list or s-expression. Returns the number of values read.
    fn count_sequence_children<'a, D: Decoder>(
        lazy_sequence: impl Iterator<Item = IonResult<LazyValue<'a, D>>>,
    ) -> IonResult<usize> {
        let mut count = 0;
        for value in lazy_sequence {
            count += count_value_and_children(&value?)?;
        }
        Ok(count)
    }

    /// Reads the field values of a struct. Returns the number of values read.
    fn count_struct_children<D: Decoder>(lazy_struct: &LazyStruct<'_, D>) -> IonResult<usize> {
        let mut count = 0;
        for field in lazy_struct {
            count += count_value_and_children(&field?.value())?;
        }
        Ok(count)
    }

    /// Constructs and benchmarks the 'baseline' Ion 1.0 data stream with `num_values` top-level values.
    /// Returns the materialized `Sequence` representation of the stream so other benchmarks can
    /// confirm that they are reading Ion-equivalent data.
    pub fn benchmark_1_0(c: &mut Criterion, num_values: usize) -> IonResult<Sequence> {
        let pretty_data_1_0 = r#"{
            'timestamp': 1670446800245,
            'threadId': 418,
            'threadName': "scheduler-thread-6",
            'loggerName': "com.example.organization.product.component.ClassName",
            'logLevel': INFO,
            'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
            'parameters': ["SUCCESS","example-client-1","aws-us-east-5f-abc123","region 4","2022-12-07T20:59:59.744000Z",],
        }"#.repeat(num_values);
        let text_1_0_data = rewrite_as(&pretty_data_1_0, v1_0::Text).unwrap();
        let binary_1_0_data = rewrite_as(&pretty_data_1_0, v1_0::Binary).unwrap();

        println!("Text Ion 1.0 data size: {} bytes", text_1_0_data.len());
        println!("Bin  Ion 1.0 data size: {} bytes", binary_1_0_data.len());

        // Load the Ion 1.0 values into a Sequence. We'll compare our Ion 1.1 streams' data to this
        // sequence to make sure that all of the tests are working on equivalent data.
        let seq_1_0 = Reader::new(v1_0::Text, text_1_0_data.as_slice())
            .unwrap()
            .read_all_elements()?;

        let mut text_1_0_group = c.benchmark_group("text 1.0");
        // Visit each top level value in the stream without reading it.
        text_1_0_group.bench_function("scan all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_0::Text, text_1_0_data.as_slice()).unwrap();
                while let Some(item) = reader.next().unwrap() {
                    black_box(item);
                }
            })
        });
        // Read every value in the stream, however deeply nested.
        text_1_0_group.bench_function("read all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_0::Text, text_1_0_data.as_slice()).unwrap();
                let mut num_values = 0usize;
                while let Some(item) = reader.next().unwrap() {
                    num_values += count_value_and_children(&item).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        // Read the 'format' field from each top-level struct in the stream.
        text_1_0_group.bench_function("read 'format' field", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_0::Text, text_1_0_data.as_slice()).unwrap();
                let mut num_values = 0usize;
                while let Some(value) = reader.next().unwrap() {
                    let s = value.read().unwrap().expect_struct().unwrap();
                    let parameters_list = s.find_expected("format").unwrap();
                    num_values += count_value_and_children(&parameters_list).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        text_1_0_group.finish();

        let mut binary_1_0_group = c.benchmark_group("binary 1.0");
        binary_1_0_group.bench_function("scan all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_0::Binary, binary_1_0_data.as_slice()).unwrap();
                while let Some(item) = reader.next().unwrap() {
                    black_box(item);
                }
            })
        });
        binary_1_0_group.bench_function("read all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_0::Binary, binary_1_0_data.as_slice()).unwrap();
                let mut num_values = 0usize;
                while let Some(item) = reader.next().unwrap() {
                    num_values += count_value_and_children(&item).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        binary_1_0_group.bench_function("read 'format' field", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_0::Binary, binary_1_0_data.as_slice()).unwrap();
                let mut num_values = 0usize;
                while let Some(value) = reader.next().unwrap() {
                    let s = value.read().unwrap().expect_struct().unwrap();
                    let parameters_list = s.find_expected("format").unwrap();
                    num_values += count_value_and_children(&parameters_list).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        binary_1_0_group.finish();

        Ok(seq_1_0)
    }

    /// Benchmarks reading the provided Ion 1.1-encoded test data using various access patterns.
    /// Before benchmarking begins, tests to make sure that the Ion 1.1 data is Ion-equivalent to
    /// the Ion 1.0-encoded sequence `seq_1_0`.
    pub fn benchmark_1_1(
        c: &mut Criterion,
        seq_1_0: &Sequence,
        test_data_1_1: TestData_1_1,
    ) -> IonResult<()> {
        let text_1_1_data = test_data_1_1.text_data.as_str();
        let binary_1_1_data = test_data_1_1.binary_data.as_slice();
        let name = test_data_1_1.name.as_str();

        let empty_context = EncodingContext::for_ion_version(IonVersion::v1_1);
        let compiled_macro = TemplateCompiler::compile_from_source(
            empty_context.get_ref(),
            &test_data_1_1.template_definition_text,
        )
        .unwrap();

        println!("=== v1.1: {name} ===");
        println!("Binary data size: {} bytes", binary_1_1_data.len());
        println!("Text   data size: {} bytes", text_1_1_data.len());

        // === Binary equivalence check ===
        let mut reader_1_1 = Reader::new(v1_1::Binary, binary_1_1_data).unwrap();
        reader_1_1.register_template(compiled_macro.clone())?;
        let seq_1_1 = reader_1_1.read_all_elements().unwrap();
        assert!(
            IonData::eq(seq_1_0, &seq_1_1),
            "{name} binary Ion 1.1 sequence was not equal to the original Ion 1.0 sequence: \n{:#?}\n  !=\n{:#?}",
            seq_1_0.elements().next().unwrap(),
            seq_1_1.elements().next().unwrap(),
        );

        // === Text equivalence check ===
        let mut reader_1_1 = Reader::new(v1_1::Text, text_1_1_data).unwrap();
        reader_1_1
            .register_template(compiled_macro.clone())
            .unwrap();
        let seq_1_1 = reader_1_1.read_all_elements().unwrap();
        assert!(
            IonData::eq(seq_1_0, &seq_1_1),
            "{name} text Ion 1.1 sequence was not equal to the original Ion 1.0 sequence"
        );

        // Reads each raw top-level e-expression in full without performing evaluation. This is an
        // optional "fast path" for macros that are known at compile time; a program can access their
        // component values without performing evaluation.
        // TODO: The macro table should have a reasonable interface for 'intercepting' e-expressions
        //       before they are evaluated when a type knows how to interpret them without evaluation.
        let mut binary_1_1_group = c.benchmark_group(format!("{name} binary 1.1"));
        binary_1_1_group.bench_function("read all from eexp", |b| {
            let mut context = EncodingContext::for_ion_version(IonVersion::v1_1);
            context
                .macro_table_mut()
                .add_template_macro(compiled_macro.clone())
                .unwrap();
            let context_ref = context.get_ref();
            b.iter(|| {
                // We don't have an API for doing this with the application-level reader yet, so
                // for now we use a manually configured context and a raw reader.
                let mut reader = LazyRawBinaryReader_1_1::new(context_ref, binary_1_1_data);
                let mut num_top_level_values: usize = 0;
                // Skip past the IVM
                reader.next().unwrap().expect_ivm().unwrap();
                // Expect every top-level item to be an e-expression.
                while let RawStreamItem::EExp(raw_eexp) = reader.next().unwrap() {
                    num_top_level_values += 1;
                    // Look up the e-expression's invoked macro ID in the encoding context.
                    let eexp = raw_eexp.resolve(context_ref).unwrap();
                    // Visit and read all of the e-expression's arguments.
                    for arg in eexp.arguments() {
                        match arg.unwrap() {
                            // If the argument is a value literal, read it.
                            ValueExpr::ValueLiteral(value) => {
                                black_box(value.read_resolved().unwrap());
                            }
                            // TODO: Support macro invocations (not just arg groups) as arguments in the benchmark
                            ValueExpr::MacroInvocation(macro_expr) => {
                                use ion_rs::MacroExprKind::*;
                                match macro_expr.kind() {
                                    // If the argument is a group, read all of its contained expressions.
                                    EExpArgGroup(group) => {
                                        for expr in group.expressions() {
                                            match expr.unwrap() {
                                                ValueExpr::ValueLiteral(value) => {
                                                    black_box(value.read_resolved().unwrap());
                                                }
                                                ValueExpr::MacroInvocation(_) => {
                                                    todo!("arg groups of macro invocations in benchmark")
                                                }
                                            }
                                        }
                                    }
                                    _ => todo!("other macro types as e-expr args in benchmark"),
                                }
                            }
                        };
                    }
                }
                assert_eq!(num_top_level_values, seq_1_1.len());
                black_box(num_top_level_values);
            })
        });
        binary_1_1_group.bench_function("scan all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Binary, binary_1_1_data).unwrap();
                reader.register_template(compiled_macro.clone()).unwrap();
                while let Some(item) = reader.next().unwrap() {
                    black_box(item);
                }
            })
        });
        binary_1_1_group.bench_function("read all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Binary, binary_1_1_data).unwrap();
                reader.register_template(compiled_macro.clone()).unwrap();
                let mut num_values = 0usize;
                while let Some(item) = reader.next().unwrap() {
                    num_values += count_value_and_children(&item).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        binary_1_1_group.bench_function("read 'format' field", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Binary, binary_1_1_data).unwrap();
                reader.register_template(compiled_macro.clone()).unwrap();
                let mut num_values = 0usize;
                while let Some(value) = reader.next().unwrap() {
                    let s = value.read().unwrap().expect_struct().unwrap();
                    let format_field_value = s.find_expected("format").unwrap();
                    num_values += count_value_and_children(&format_field_value).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        binary_1_1_group.finish();

        let mut text_1_1_group = c.benchmark_group(format!("{} text 1.1", &test_data_1_1.name));
        text_1_1_group.bench_function("scan all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Text, text_1_1_data.as_bytes()).unwrap();
                reader.register_template(compiled_macro.clone()).unwrap();
                while let Some(item) = reader.next().unwrap() {
                    black_box(item);
                }
            })
        });
        text_1_1_group.bench_function("read all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Text, text_1_1_data.as_bytes()).unwrap();
                reader.register_template(compiled_macro.clone()).unwrap();
                let mut num_values = 0usize;
                while let Some(item) = reader.next().unwrap() {
                    num_values += count_value_and_children(&item).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        text_1_1_group.bench_function("read 'format' field", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Text, text_1_1_data.as_bytes()).unwrap();
                reader.register_template(compiled_macro.clone()).unwrap();
                let mut num_values = 0usize;
                while let Some(value) = reader.next().unwrap() {
                    let s = value.read().unwrap().expect_struct().unwrap();
                    let parameters_list = s.find_expected("format").unwrap();
                    num_values += count_value_and_children(&parameters_list).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        text_1_1_group.finish();
        Ok(())
    }

    /// Transcodes the provided text Ion using the specified `WriteConfig`.
    fn rewrite_as<E: Encoding>(
        pretty_ion: &str,
        config: impl Into<WriteConfig<E>>,
    ) -> IonResult<Vec<u8>> {
        let values = Element::read_all(pretty_ion).unwrap();
        let mut buffer = Vec::new();
        values.encode_to(&mut buffer, config)?;
        Ok(buffer)
    }
}

criterion_group!(benches, benchmark::criterion_benchmark);
criterion_main!(benches);
