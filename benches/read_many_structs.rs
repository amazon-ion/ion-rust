use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ion_rs::lazy::decoder::LazyDecoder;
use ion_rs::lazy::encoding::TextEncoding_1_1;
use ion_rs::lazy::r#struct::LazyStruct;
use ion_rs::lazy::reader::{LazyApplicationReader, LazyTextReader_1_0, LazyTextReader_1_1};
use ion_rs::lazy::value::LazyValue;
use ion_rs::lazy::value_ref::ValueRef;
use ion_rs::IonResult;
use nom::AsBytes;

pub fn criterion_benchmark(c: &mut Criterion) {
    const NUM_VALUES: usize = 10_000;
    let data_1_0 = concat!("{",
            "'timestamp': 1670446800245,",
            "'threadId': 418,",
            r#"'threadName': "scheduler-thread-6","#,
            r#"'loggerName': "com.example.organization.product.component.ClassName","#,
            "'logLevel': INFO,",
            r#"'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}","#,
            r#"'parameters': ["SUCCESS","example-client-1","aws-us-east-5f-18b4fa","region 4","2022-12-07T20:59:59.744000Z",],"#,
        "}"
    ).repeat(NUM_VALUES);
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
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
