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

    use ion_rs::{v1_0, ElementReader, Encoding, Reader, WriteConfig};
    use ion_rs::{Decoder, Element, IonResult, LazyStruct, LazyValue, ValueRef};

    /// The entrypoint for the benchmark.
    pub fn criterion_benchmark(c: &mut Criterion) {
        const NUM_VALUES: usize = 10_000;
        benchmark_1_0(c, NUM_VALUES).unwrap();
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

    /// Constructs and benchmarks an Ion 1.0 data stream with `num_values` top-level values.
    pub fn benchmark_1_0(c: &mut Criterion, num_values: usize) -> IonResult<()> {
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

        // Before benchmarking, confirm that the generated stream can be read back in full.
        let _seq_1_0 = Reader::new(v1_0::Text, text_1_0_data.as_slice())
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
