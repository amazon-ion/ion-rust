
#[cfg(feature = "experimental-reader-writer")]
mod conformance_dsl;

#[cfg(feature = "experimental-reader-writer")]
pub fn main() {
    use crate::conformance_dsl::prelude::*;

    let test_paths = std::env::args().skip(1).collect::<Vec<String>>();
    let mut errors: Vec<(String, String, conformance_dsl::ConformanceError)> = vec!();

    // Formatting: Get max test name length.

    println!("Testing {} conformance collections.\n", test_paths.len());

    let mut failures = 0;

    for test_path in test_paths {
        println!("\nRunning tests: {} ========================", test_path);
        let collection = TestCollection::load(&test_path).expect("unable to load test file");
        let name_len = collection.iter().fold(0, |acc, d| std::cmp::max(acc, d.name.as_ref().map_or(0, |n| n.len())));

        for doc in collection.iter() {
            match doc.name.as_ref() {
                Some(n) => print!("   {:<width$}", n, width = name_len),
                None => print!("   {:<width$}", "<unnamed>", width = name_len),
            }

            print!("  ...  ");
            match doc.run() {
                Err(e) => {
                    println!("[FAILED]");
                    failures += 1;
                    errors.push((test_path.to_owned(), doc.name.as_deref().unwrap_or("<unnamed>").to_owned(), e.clone()));
                }
                Ok(_) => println!("[OK]"),
            }
        }
    }

    // println!("\nConformance Summary: {} Succeeded, {} Failed", collection.len() - failures, failures);

    for (test_path, test_name, err) in errors {
        println!("-------------------------");
        println!("File: {}", test_path);
        println!("Test: {}", test_name);
        println!("Error: {:?}", err);
    }

    if failures > 0 {
        panic!("Conformance test(s) failed");
    }
}

#[cfg(not(feature = "experimental-reader-writer"))]
pub fn main() {
    println!("Needs feature experimental-reader-writer");
}
