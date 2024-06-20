use criterion::{criterion_group, criterion_main};

#[cfg(not(feature = "experimental"))]
mod benchmark {
    use criterion::Criterion;

    pub fn criterion_benchmark(_c: &mut Criterion) {
        panic!("This benchmark requires the 'experimental' feature to work; try again with `--features experimental`");
    }
}

#[cfg(feature = "experimental")]
mod benchmark {
    use criterion::{black_box, Criterion};

    use ion_rs::{v1_0, v1_1, ElementReader, Encoding, IonData, Reader, WriteConfig};
    use ion_rs::{Decoder, Element, IonResult, LazyStruct, LazyValue, ValueRef};

    fn rewrite_as<E: Encoding>(
        pretty_ion: &str,
        config: impl Into<WriteConfig<E>>,
    ) -> IonResult<Vec<u8>> {
        let values = Element::read_all(pretty_ion).unwrap();
        let mut buffer = Vec::new();
        values.encode_to(&mut buffer, config)?;
        Ok(buffer)
    }

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

    fn count_sequence_children<'a, D: Decoder>(
        lazy_sequence: impl Iterator<Item = IonResult<LazyValue<'a, D>>>,
    ) -> IonResult<usize> {
        let mut count = 0;
        for value in lazy_sequence {
            count += count_value_and_children(&value?)?;
        }
        Ok(count)
    }

    fn count_struct_children<D: Decoder>(lazy_struct: &LazyStruct<'_, D>) -> IonResult<usize> {
        let mut count = 0;
        for field in lazy_struct {
            count += count_value_and_children(&field?.value())?;
        }
        Ok(count)
    }

    pub fn criterion_benchmark(c: &mut Criterion) -> IonResult<()> {
        const NUM_VALUES: usize = 10_000;
        let pretty_data_1_0 = r#"{
            'timestamp': 1670446800245,
            'threadId': 418,
            'threadName': "scheduler-thread-6",
            'loggerName': "com.example.organization.product.component.ClassName",
            'logLevel': INFO,
            'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
            'parameters': ["SUCCESS","example-client-1","aws-us-east-5f-18b4fa","region 4","2022-12-07T20:59:59.744000Z",],
        }"#.repeat(NUM_VALUES);
        let text_1_0_data = rewrite_as(&pretty_data_1_0, v1_0::Text).unwrap();
        let binary_1_0_data = rewrite_as(&pretty_data_1_0, v1_0::Binary).unwrap();
        let template_definition_text = r#"
            (macro event (timestamp thread_id thread_name client_num host_id parameters*)
                {
                    'timestamp': timestamp,
                    'threadId': thread_id,
                    'threadName': (make_string "scheduler-thread-" thread_name),
                    'loggerName': "com.example.organization.product.component.ClassName",
                    'logLevel': (quote INFO),
                    'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
                    'parameters': [
                        "SUCCESS",
                        (make_string "example-client-" client_num),
                        (make_string "aws-us-east-5f-" host_id),
                        parameters
                    ]
                }
            )
        "#;

        let text_1_1_data = r#"(:event 1670446800245 418 "6" "1" "18b4fa" (: "region 4" "2022-12-07T20:59:59.744000Z"))"#.repeat(NUM_VALUES);

        #[rustfmt::skip]
        let mut binary_1_1_data_body: Vec<u8> = vec![
            0x03, // Macro ID 3
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
            0x31, 0x38, 0x62, 0x34, 0x66, 0x61,
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
            0x30, 0x30, 0x30, 0x5A,
        ].repeat(NUM_VALUES);
        // Ion v1.1 Version Marker
        let mut binary_1_1_data = vec![0xE0u8, 0x01, 0x01, 0xEA];
        binary_1_1_data.append(&mut binary_1_1_data_body);
        // fn write_binary_1_1_data() -> IonResult<Vec<u8>> {
        //     let mut writer = RawBinaryWriter::new(Vec::new())?;
        //     // TODO: tagless encodings
        //     for _ in 0..NUM_VALUES {
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
        //     writer.close()
        // }
        //
        // let binary_1_1_data = write_binary_1_1_data()?;

        println!("Bin  Ion 1.0 data size: {} bytes", binary_1_0_data.len());
        println!("Bin  Ion 1.1 data size: {} bytes", binary_1_1_data.len());
        println!("Text Ion 1.0 data size: {} bytes", text_1_0_data.len());
        println!("Text Ion 1.1 data size: {} bytes", text_1_1_data.len());

        // As a sanity check, materialize the data from both the Ion 1.0 and 1.1 streams and make sure
        // that they are equivalent before we start measuring the time needed to read them.
        // Here we load the text_1_0 data.
        let seq_1_0 = Reader::new(v1_1::Text, text_1_0_data.as_slice())
            .unwrap()
            .read_all_elements()
            .unwrap();

        // === Binary equivalence check ===
        let mut reader_1_1 = Reader::new(v1_1::Binary, binary_1_1_data.as_slice()).unwrap();
        reader_1_1
            .register_template_src(template_definition_text)
            .unwrap();
        let seq_1_1 = reader_1_1.read_all_elements().unwrap();
        assert!(
            IonData::eq(&seq_1_0, &seq_1_1),
            "Binary Ion 1.1 sequence was not equal to the original Ion 1.0 sequence"
        );

        // === Text equivalence check ===
        let mut reader_1_1 = Reader::new(v1_1::Text, text_1_1_data.as_bytes()).unwrap();
        reader_1_1
            .register_template_src(template_definition_text)
            .unwrap();
        let seq_1_1 = reader_1_1.read_all_elements().unwrap();
        assert!(
            IonData::eq(&seq_1_0, &seq_1_1),
            "Text Ion 1.1 sequence was not equal to the original Ion 1.0 sequence"
        );

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

        let mut binary_1_1_group = c.benchmark_group("binary 1.1");
        binary_1_1_group.bench_function("scan all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Binary, binary_1_1_data.as_slice()).unwrap();
                reader
                    .register_template_src(template_definition_text)
                    .unwrap();
                while let Some(item) = reader.next().unwrap() {
                    black_box(item);
                }
            })
        });
        binary_1_1_group.bench_function("read all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Binary, binary_1_1_data.as_slice()).unwrap();
                reader
                    .register_template_src(template_definition_text)
                    .unwrap();
                let mut num_values = 0usize;
                while let Some(item) = reader.next().unwrap() {
                    num_values += count_value_and_children(&item).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        binary_1_1_group.bench_function("read 'format' field", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Binary, binary_1_1_data.as_slice()).unwrap();
                reader
                    .register_template_src(template_definition_text)
                    .unwrap();
                let mut num_values = 0usize;
                while let Some(value) = reader.next().unwrap() {
                    let s = value.read().unwrap().expect_struct().unwrap();
                    let parameters_list = s.find_expected("format").unwrap();
                    num_values += count_value_and_children(&parameters_list).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        binary_1_1_group.finish();

        let mut text_1_0_group = c.benchmark_group("text 1.0");
        text_1_0_group.bench_function("scan all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Text, text_1_0_data.as_slice()).unwrap();
                while let Some(item) = reader.next().unwrap() {
                    black_box(item);
                }
            })
        });
        text_1_0_group.bench_function("read all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Text, text_1_0_data.as_slice()).unwrap();
                let mut num_values = 0usize;
                while let Some(item) = reader.next().unwrap() {
                    num_values += count_value_and_children(&item).unwrap();
                }
                let _ = black_box(num_values);
            })
        });
        text_1_0_group.bench_function("read 'format' field", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Text, text_1_0_data.as_slice()).unwrap();
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

        let mut text_1_1_group = c.benchmark_group("text 1.1");
        text_1_1_group.bench_function("scan all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Text, text_1_1_data.as_bytes()).unwrap();
                reader
                    .register_template_src(template_definition_text)
                    .unwrap();
                while let Some(item) = reader.next().unwrap() {
                    black_box(item);
                }
            })
        });
        text_1_1_group.bench_function("read all", |b| {
            b.iter(|| {
                let mut reader = Reader::new(v1_1::Text, text_1_1_data.as_bytes()).unwrap();
                reader
                    .register_template_src(template_definition_text)
                    .unwrap();
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
                reader
                    .register_template_src(template_definition_text)
                    .unwrap();
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
}

criterion_group!(benches, benchmark::criterion_benchmark);
criterion_main!(benches);
