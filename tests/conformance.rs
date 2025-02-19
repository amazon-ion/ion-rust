#![cfg(feature = "experimental-ion-1-1")]

use std::collections::HashMap;

use ion_rs::serde::to_string;
use serde::Serialize;

use crate::conformance_dsl::prelude::*;

#[cfg(feature = "experimental-reader-writer")]
mod conformance_dsl;

#[derive(PartialEq, Serialize)]
enum TestResult {
    Ok,
    Failed,
    Panic,
}

impl ToString for TestResult {
    fn to_string(&self) -> String {
        match self {
            Self::Ok => "Ok".to_string(),
            Self::Failed => "Failed".to_string(),
            Self::Panic => "Panic".to_string(),
        }
    }
}

#[derive(Serialize)]
struct TestReport {
    name: String,
    result: TestResult,
    error: Option<String>,
}

/// Implementable trait for providing different output formats for the test results report.
trait TestReporter {
    /// Set the current collection. This is generally a single source file containing one or more
    /// test documents. This function will be called before any test results are provided.
    fn current_collection(&mut self, source: &str, collection: &TestCollection);
    /// Add a result for the current collection.
    fn add_test_result(&mut self, result: TestReport);
    /// Called when all test results have been added for all test collections.
    fn finalize(&mut self);
}

/// A test reporter that renders the results of all tests to the terminal in a human readable way,
/// mimicking the output of cargo test.
#[derive(Default)]
struct PlainReporter {
    name_width: usize,
    current_source: String,
    failed_tests: Vec<(String, TestReport)>,
}

impl TestReporter for PlainReporter {
    fn current_collection(&mut self, source: &str, collection: &TestCollection) {
        println!("\nRunning tests: {}", source);
        self.current_source = source.to_owned();
        self.name_width = collection.iter().fold(0, |acc, d| {
            std::cmp::max(acc, d.name.as_ref().map_or(0, |n| n.len()))
        });
    }

    fn add_test_result(&mut self, report: TestReport) {
        println!(
            "  {:<width$}   ...  [{}]",
            report.name,
            report.result.to_string(),
            width = self.name_width
        );
        if report.result != TestResult::Ok {
            self.failed_tests
                .push((self.current_source.clone(), report));
        }
    }

    fn finalize(&mut self) {
        if self.failed_tests.len() > 0 {
            println!(
                "============================================================================"
            );
            for (source, result) in self.failed_tests.iter() {
                println!("Source: {}", source);
                println!("Test  : {}", result.name);
                let error = if result.result == TestResult::Panic {
                    format!("PANIC: {}", result.error.clone().unwrap())
                } else {
                    result.error.clone().unwrap()
                };
                println!("Error : {}", error);
                println!("----------------------------------------------");
            }
        }
    }
}

/// A test reporter that renders the results of all tests into an ion document containing the
/// pass/fail results as well as the failure reason for each test within each test source.
#[derive(Default)]
struct IonReporter {
    current_source: String,
    results: HashMap<String, Vec<TestReport>>,
}

impl TestReporter for IonReporter {
    fn current_collection(&mut self, source: &str, _collection: &TestCollection) {
        self.current_source = source.to_string();
        self.results.insert(self.current_source.clone(), vec![]);
    }

    fn add_test_result(&mut self, report: TestReport) {
        self.results
            .get_mut(&self.current_source)
            .unwrap()
            .push(report);
    }

    fn finalize(&mut self) {
        println!("{}", to_string(&self.results).unwrap());
    }
}

#[cfg(feature = "experimental-reader-writer")]
pub fn main() {
    let options = std::env::args()
        .skip(1)
        .take_while(|a| a.starts_with("-"))
        .collect::<Vec<String>>();
    let test_paths = std::env::args()
        .skip(1 + options.len())
        .collect::<Vec<String>>();
    let emit_ion = Some("-i") == options.get(0).map(|v| v.as_str());

    let mut reporter: Box<dyn TestReporter> = if emit_ion {
        Box::new(IonReporter::default())
    } else {
        Box::new(PlainReporter::default())
    };

    for test_path in test_paths {
        let collection = TestCollection::load(&test_path).expect("unable to load test file");
        // let name_len = collection.iter().fold(0, |acc, d| std::cmp::max(acc, d.name.as_ref().map_or(0, |n| n.len())));

        reporter.current_collection(&test_path, &collection);
        for doc in collection.iter() {
            let panic_buffer = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
            let old_hook = std::panic::take_hook();
            // Limit the span that we've hijack'd the panic hook, so that if something goes wrong
            // with the unit test outside of our conformance eval, we don't conflate the two.
            std::panic::set_hook({
                let mut panic_buffer = panic_buffer.clone();
                Box::new(move |info| {
                    let mut panic_buffer = panic_buffer.lock().unwrap();
                    // If we have a nice string-ish payload we can just take it.. otherwise we'll
                    // capture the debug fmt of the info itself.
                    if let Some(s) = info.payload().downcast_ref::<&str>() {
                        panic_buffer.push_str(s);
                    } else {
                        panic_buffer.push_str(&format!("{:?}", info));
                    }
                })
            });
            let panic_result = std::panic::catch_unwind(|| doc.run());
            std::panic::set_hook(old_hook);

            let test_result = if panic_result.is_ok() {
                let name = doc.name.as_deref().unwrap_or("<unnamed>").to_owned();
                match panic_result.unwrap() {
                    Err(e) => TestReport {
                        name,
                        result: TestResult::Failed,
                        error: Some(format!("{:?}", e)),
                    },
                    Ok(_) => TestReport {
                        name,
                        result: TestResult::Ok,
                        error: None,
                    },
                }
            } else {
                TestReport {
                    name: doc.name.as_deref().unwrap_or("<unnamed>").to_owned(),
                    result: TestResult::Panic,
                    error: Some((*panic_buffer.lock().unwrap()).to_string()),
                }
            };
            reporter.add_test_result(test_result);
        }
    }
    reporter.finalize();
}

#[cfg(not(feature = "experimental-reader-writer"))]
pub fn main() {
    println!("Needs feature experimental-reader-writer");
}
