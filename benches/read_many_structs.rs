use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ion_rs::lazy::decoder::LazyDecoder;
use ion_rs::lazy::encoding::TextEncoding_1_1;
use ion_rs::lazy::r#struct::LazyStruct;
use ion_rs::lazy::reader::{LazyApplicationReader, LazyTextReader_1_1};
use ion_rs::lazy::value::LazyValue;
use ion_rs::lazy::value_ref::ValueRef;
use ion_rs::{Element, Format, IonResult, TextKind};
use ion_rs::{ElementReader, IonData};

fn rewrite_as_compact_text(pretty_ion: &str) -> IonResult<String> {
    let values = Element::read_all(pretty_ion).unwrap();
    let mut buffer = Vec::new();
    Element::write_all_as(&values, Format::Text(TextKind::Compact), &mut buffer)?;
    Ok(String::from_utf8(buffer).unwrap())
}

pub fn criterion_benchmark(c: &mut Criterion) {
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
    let data_1_0 = rewrite_as_compact_text(&pretty_data_1_0).unwrap();
    let template_text = r#"
            (macro event (timestamp thread_id thread_name client_num host_id parameters)
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

    let data_1_1 = r#"(:event 1670446800245 418 "6" "1" "18b4fa" (:values "region 4" "2022-12-07T20:59:59.744000Z"))"#.repeat(NUM_VALUES);

    println!("Ion 1.0 data size: {} bytes", data_1_0.len());
    println!("Ion 1.1 data size: {} bytes", data_1_1.len());

    // As a sanity check, materialize the data from both the Ion 1.0 and 1.1 streams and make sure
    // that they are equivalent before we start measuring the time needed to read them.
    let seq_1_0 = LazyTextReader_1_1::new(data_1_0.as_bytes())
        .unwrap()
        .read_all_elements()
        .unwrap();
    let mut reader_1_1 = LazyTextReader_1_1::new(data_1_1.as_bytes()).unwrap();
    reader_1_1.register_template(template_text).unwrap();
    let seq_1_1 = reader_1_1.read_all_elements().unwrap();
    assert!(
        IonData::eq(&seq_1_0, &seq_1_1),
        "Ion 1.0 sequence was not equal to the Ion 1.1 sequence"
    );

    fn count_value_and_children<D: LazyDecoder>(lazy_value: &LazyValue<'_, D>) -> IonResult<usize> {
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

    fn count_sequence_children<'a, D: LazyDecoder>(
        lazy_sequence: impl Iterator<Item = IonResult<LazyValue<'a, D>>>,
    ) -> IonResult<usize> {
        let mut count = 0;
        for value in lazy_sequence {
            count += count_value_and_children(&value?)?;
        }
        Ok(count)
    }

    fn count_struct_children<D: LazyDecoder>(lazy_struct: &LazyStruct<'_, D>) -> IonResult<usize> {
        let mut count = 0;
        for field in lazy_struct {
            count += count_value_and_children(&field?.value())?;
        }
        Ok(count)
    }

    c.bench_function("text 1.0: scan all", |b| {
        b.iter(|| {
            let mut reader =
                LazyApplicationReader::<'_, TextEncoding_1_1>::new(data_1_0.as_bytes()).unwrap();
            while let Some(item) = reader.next().unwrap() {
                black_box(item);
            }
        })
    });
    c.bench_function("text 1.0: read all", |b| {
        b.iter(|| {
            let mut reader =
                LazyApplicationReader::<'_, TextEncoding_1_1>::new(data_1_0.as_bytes()).unwrap();
            let mut num_values = 0usize;
            while let Some(item) = reader.next().unwrap() {
                num_values += count_value_and_children(&item).unwrap();
            }
            let _ = black_box(num_values);
        })
    });
    c.bench_function("text 1.0: read 'format' field", |b| {
        b.iter(|| {
            let mut reader =
                LazyApplicationReader::<'_, TextEncoding_1_1>::new(data_1_0.as_bytes()).unwrap();
            let mut num_values = 0usize;
            while let Some(value) = reader.next().unwrap() {
                let s = value.read().unwrap().expect_struct().unwrap();
                let parameters_list = s.find_expected("format").unwrap();
                num_values += count_value_and_children(&parameters_list).unwrap();
            }
            let _ = black_box(num_values);
        })
    });
    c.bench_function("text 1.1: scan all", |b| {
        b.iter(|| {
            let mut reader = LazyTextReader_1_1::new(data_1_1.as_bytes()).unwrap();
            reader.register_template(template_text).unwrap();
            while let Some(item) = reader.next().unwrap() {
                black_box(item);
            }
        })
    });
    c.bench_function("text 1.1: read all", |b| {
        b.iter(|| {
            let mut reader = LazyTextReader_1_1::new(data_1_1.as_bytes()).unwrap();
            reader.register_template(template_text).unwrap();
            let mut num_values = 0usize;
            while let Some(item) = reader.next().unwrap() {
                num_values += count_value_and_children(&item).unwrap();
            }
            let _ = black_box(num_values);
        })
    });
    c.bench_function("text 1.1: read 'format' field", |b| {
        b.iter(|| {
            let mut reader =
                LazyApplicationReader::<'_, TextEncoding_1_1>::new(data_1_1.as_bytes()).unwrap();
            reader.register_template(template_text).unwrap();
            let mut num_values = 0usize;
            while let Some(value) = reader.next().unwrap() {
                let s = value.read().unwrap().expect_struct().unwrap();
                let parameters_list = s.find_expected("format").unwrap();
                num_values += count_value_and_children(&parameters_list).unwrap();
            }
            let _ = black_box(num_values);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
