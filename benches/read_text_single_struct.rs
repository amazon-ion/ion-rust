use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ion_rs::lazy::encoding::TextEncoding_1_1;
use ion_rs::lazy::reader::{LazyApplicationReader, LazyTextReader_1_0, LazyTextReader_1_1};
use nom::AsBytes;

pub fn criterion_benchmark(c: &mut Criterion) {
    const NUM_VALUES: usize = 10_000;
    let data_1_0 = r#"
        {
            'timestamp': 1670446800245,
            'threadId': 418,
            'threadName': "scheduler-thread-6",
            'loggerName': "com.example.organization.product.component.ClassName",
            'logLevel': INFO,
            'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
            'parameters': [
                "SUCCESS",
                "example-client-1",
                "aws-us-east-5f-18b4fa",
                "region 4",
                "2022-12-07T20:59:59.744000Z",
            ]
        }
    "#.repeat(NUM_VALUES);
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

    let data_1_1 = r#"
        (:event
            1670446800245
            418
            "6"
            "1"
            "18b4fa"
            (:values
                "region 4"
                "2022-12-07T20:59:59.744000Z"))
    "#
    .repeat(NUM_VALUES);

    println!("Ion 1.0 data size: {} bytes", data_1_0.len());
    println!("Ion 1.1 data size: {} bytes", data_1_1.len());

    c.bench_function("text 1.0", |b| {
        b.iter(|| {
            let mut reader =
                LazyApplicationReader::<'_, TextEncoding_1_1>::new(data_1_0.as_bytes()).unwrap();
            while let Some(item) = reader.next().unwrap() {
                black_box(item);
            }
        })
    });
    c.bench_function("text 1.1", |b| {
        b.iter(|| {
            let mut reader = LazyTextReader_1_1::new(data_1_1.as_bytes()).unwrap();
            reader.register_template(template_text).unwrap();
            while let Some(item) = reader.next().unwrap() {
                black_box(item);
            }
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
