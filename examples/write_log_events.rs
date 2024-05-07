//! This program demonstrates implementing WriteAsIon using Ion 1.1's e-expressions for a more
//! compact encoding. It uses raw-level writer APIs that end users are unlikely to leverage.
//! Ion 1.1 is not yet finalized; the encoding produced by this example and the APIs it uses
//! are very likely to change.

use ion_rs::*;

fn main() -> IonResult<()> {
    #[cfg(not(feature = "experimental-lazy-reader"))]
    panic!("This example requires the 'experimental-lazy-reader' feature to work.");

    #[cfg(feature = "experimental-lazy-reader")]
    example::write_log_events()
}

#[cfg(feature = "experimental-lazy-reader")]
mod example {
    use chrono::{DateTime, FixedOffset};
    use ion_rs::lazy::encoder::binary::v1_0::writer::LazyRawBinaryWriter_1_0;
    use ion_rs::lazy::encoder::binary::v1_1::writer::LazyRawBinaryWriter_1_1;
    use ion_rs::lazy::encoder::value_writer::{SequenceWriter, StructWriter, ValueWriter};
    use ion_rs::lazy::encoder::write_as_ion::WriteAsIon;
    use ion_rs::*;
    use std::env::args;

    use rand::rngs::StdRng;
    use rand::seq::SliceRandom;
    use rand::{Rng, SeedableRng};
    use std::io::BufWriter;
    use std::ops::Range;
    use tempfile::NamedTempFile;

    pub fn write_log_events() -> IonResult<()> {
        // By default, this program deletes the encoded output before it ends. To keep the files
        // for further review, you can pass a `--keep-files`/`-k` flag.
        let args: Vec<String> = args().collect();
        let keep_files_flag = match args.get(1).map(|a| a.as_str()) {
            Some("--keep-files") | Some("-k") => true,
            _ => false,
        };

        // Create a set of Log4J-style statements that might appear in a typical program. These statements
        // have a fixed combination of (logger name, log level, format string) fields.
        let log_statements = log_statements();

        // Create a set of `NUM_EVENTS` log events. Each event comes from a log statement (described above)
        // and provides additional one-off information like a timestamp, thread ID, thread name, and
        // parameters to populate the format string.
        const NUM_EVENTS: usize = 1_000_000;
        const RNG_SEED: u64 = 1024;
        let events = generate_events(RNG_SEED, &log_statements, NUM_EVENTS);

        // Make some files in the OS' temp directory to hold our encoded output.
        let ion_1_0_file = NamedTempFile::new().expect("failed to create a temp file");
        let ion_1_1_file = NamedTempFile::new().expect("failed to create a temp file");

        println!(
            "Output files:\nIon 1.0: {}\nIon 1.1: {}",
            ion_1_0_file.path().to_string_lossy(),
            ion_1_1_file.path().to_string_lossy(),
        );

        // Encode the log events as Ion 1.0 data
        let buf_writer = BufWriter::new(ion_1_0_file.as_file());
        let mut ion_writer = LazyRawBinaryWriter_1_0::new(buf_writer)?;
        for event in &events {
            ion_writer.write(SerializeWithoutMacros(event))?;
        }
        ion_writer.flush()?;
        drop(ion_writer);

        // Encode the log events as Ion 1.1 data
        let buf_writer = BufWriter::new(ion_1_1_file.as_file());
        let mut ion_writer = LazyRawBinaryWriter_1_1::new(buf_writer)?;
        for event in &events {
            ion_writer.write(SerializeWithMacros(event))?;
        }
        ion_writer.flush()?;
        drop(ion_writer);

        let size_in_1_0 = ion_1_0_file
            .as_file()
            .metadata()
            .expect("failed to read Ion 1.0 file length")
            .len();
        let size_in_1_1 = ion_1_1_file
            .as_file()
            .metadata()
            .expect("failed to read Ion 1.1 file length")
            .len();

        let percentage_smaller = ((size_in_1_0 - size_in_1_1) as f64 / size_in_1_0 as f64) * 100.0;
        println!("1.0 size: {size_in_1_0}");
        println!("1.1 size: {size_in_1_1} ({percentage_smaller:.2}% smaller)");

        if keep_files_flag {
            ion_1_0_file.keep().expect("failed to persist Ion 1.0 file");
            ion_1_1_file.keep().expect("failed to persist Ion 1.1 file");
        }

        Ok(())
    }

    // ===== Data types representing elements of a log file =====

    // A log statement in the fictional codebase
    #[derive(Debug)]
    // This struct has several fields that get populated but which are not (yet) used: `logger_name`
    // `log_level`, and `format`. Currently, the encoded output for Ion 1.0 writes these as symbol
    // IDs and Ion 1.1 refers to them as part of a macro. In both cases, however, the encoding
    // context is not written out in the resulting Ion stream.
    // TODO: Include the symbol/macro table definitions in the resulting output stream.
    #[allow(dead_code)]
    struct LogStatement {
        index: usize,
        logger_name: String,
        log_level: String,
        format: String,
        parameter_types: Vec<ParameterType>,
    }

    impl LogStatement {
        pub fn new(
            index: usize,
            class_name: &str,
            log_level: &str,
            format: impl Into<String>,
            parameter_types: impl Into<Vec<ParameterType>>,
        ) -> Self {
            Self {
                index,
                logger_name: format!("{PACKAGE_NAME}.{class_name}"),
                log_level: log_level.to_string(),
                format: format.into(),
                parameter_types: parameter_types.into(),
            }
        }
    }

    // Each log statement expects a series of parameters to populate the format string. While the
    // log statement doesn't care about their type, we configure an expected type for each
    // parameter to generate log event text that makes sense.
    #[derive(PartialEq, Copy, Clone, Debug)]
    enum ParameterType {
        Int,
        String,
    }

    // A Log4J-ish log event
    #[derive(Debug)]
    struct LogEvent<'a> {
        timestamp: Timestamp,
        thread_id: usize,
        thread_name: String,
        statement: &'a LogStatement,
        parameters: Vec<Parameter>,
    }

    // Randomly selected int or string values that will be passed as parameters to our log events
    #[derive(Clone, Debug)]
    enum Parameter {
        Int(i64),
        String(String),
    }

    // ===== Serialization logic for the above types =====

    impl WriteAsIon for Parameter {
        fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
            match self {
                Parameter::Int(i) => i.write_as_ion(writer),
                Parameter::String(s) => s.as_str().write_as_ion(writer),
            }
        }
    }

    // Wrapper types to explicitly opt into or out of macro usage. These will not be necessary in
    // the future, as types will be able to define both a macro-ized serialization and a no-macros
    // serialization, allowing the writer to choose whichever is more appropriate.
    struct SerializeWithoutMacros<'a, 'b>(&'a LogEvent<'b>);
    struct SerializeWithMacros<'a, 'b>(&'a LogEvent<'b>);

    // When serializing without macros (usually in Ion 1.0), we write out a struct with each
    // field name/value pair. In the case of recurring strings, we take the liberty of writing
    // out symbol IDs instead of the full text; this silent type coercion from string to symbol
    // is technically data loss, but results in a much more compact encoding.
    impl<'a, 'b> WriteAsIon for SerializeWithoutMacros<'a, 'b> {
        fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
            let event = self.0;
            let mut struct_ = writer.struct_writer()?;
            struct_
                //            v--- Each field name is a symbol ID
                .write(10, &event.timestamp)?
                .write(11, event.thread_id)?
                .write(12, &event.thread_name)?
                //                 v--- The fixed strings from the log statement are also SIDs
                .write(13, RawSymbolTokenRef::SymbolId(17))? // logger name
                .write(14, RawSymbolTokenRef::SymbolId(18))? // log level
                .write(15, RawSymbolTokenRef::SymbolId(19))? // format
                .write(16, &event.parameters)?;
            struct_.close()
        }
    }

    // When leveraging macros, the thread name's recurring prefix can be elided from the output.
    // This wrapper type is used by the `SerializeWithMacros` type to change to serialization
    // behavior for the thread name.
    struct ThreadName<'a>(&'a str);

    impl<'a> WriteAsIon for ThreadName<'a> {
        fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
            // ID 12 chosen arbitrarily, but aligns with Ion 1.0 encoding above
            let mut eexp = writer.eexp_writer(12)?;
            eexp
                // Ignore the part of the thread name that starts with the recurring prefix.
                .write(&self.0[THREAD_NAME_PREFIX.len()..])?;
            eexp.close()
        }
    }

    impl<'a, 'b> WriteAsIon for SerializeWithMacros<'a, 'b> {
        fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
            let event = self.0;
            let mut eexp = writer.eexp_writer(event.statement.index)?;
            eexp.write(&event.timestamp)?
                .write(event.thread_id)?
                // Wrap the thread name in the `ThreadName` wrapper to change its serialization.
                .write(ThreadName(&event.thread_name))?
                .write(&event.parameters)?;
            eexp.close()
        }
    }

    // ===== Random generation of sample data =====

    const INT_PARAMETER_RANGE: Range<i64> = 0..5_000;
    fn generate_int_parameter(rng: &mut StdRng) -> Parameter {
        Parameter::Int(rng.gen_range(INT_PARAMETER_RANGE))
    }

    fn generate_string_parameter(rng: &mut StdRng) -> Parameter {
        const WORDS: &[&str] = &["users", "transactions", "accounts", "customers", "waffles"];
        Parameter::String(WORDS.choose(rng).unwrap().to_string())
    }

    fn log_statements() -> Vec<LogStatement> {
        use ParameterType::*;
        vec![
            LogStatement::new(
                0,
                "Foo",
                "DEBUG",
                "Database heartbeat received after {} ms",
                &[Int]
            ),
            LogStatement::new(
                1,
                "Bar",
                "INFO",
                "Retrieved {} results from the '{}' table in {} ms",
                &[Int, String, Int],
            ),
            LogStatement::new(
                2,
                "Baz",
                "WARN",
                "Query to the '{}' table took {} ms to execute, which is higher than the configured threshold",
                &[String, Int],
            ),
            LogStatement::new(
                3,
                "Quux",
                "ERROR",
                "Connection to database lost",
                &[]
            ),
        ]
    }

    const INITIAL_EPOCH_MILLIS: i64 = 1708617898 * 1_000; // Feb 22, 2024
    const THREAD_NAME_PREFIX: &str = "worker-thread-";
    const PACKAGE_NAME: &str = "com.example.organization.product.component";

    fn generate_events(
        seed: u64,
        log_statements: &[LogStatement],
        num_events: usize,
    ) -> Vec<LogEvent<'_>> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..num_events)
            .map(|i| generate_event(&mut rng, log_statements, i))
            .collect()
    }

    fn generate_event<'rng, 'statements>(
        rng: &'rng mut StdRng,
        log_statements: &'statements [LogStatement],
        event_index: usize,
    ) -> LogEvent<'statements> {
        // Each event is 1 second after the previous event
        let event_epoch_millis = INITIAL_EPOCH_MILLIS + (event_index as i64 * 1000);
        let datetime: DateTime<FixedOffset> = DateTime::from_timestamp_millis(event_epoch_millis)
            .unwrap()
            .into();
        let timestamp: Timestamp = datetime.into();

        let thread_id = rng.gen_range(1..=128);
        let thread_name = format!("{THREAD_NAME_PREFIX}{}", rng.gen_range(1..=8));
        let statement = log_statements.choose(rng).unwrap();

        let parameters: Vec<Parameter> = statement
            .parameter_types
            .iter()
            .map(|pt| match pt {
                ParameterType::Int => generate_int_parameter(rng),
                ParameterType::String => generate_string_parameter(rng),
            })
            .collect();

        LogEvent {
            timestamp,
            thread_id,
            thread_name,
            statement,
            parameters,
        }
    }
}
