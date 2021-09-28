use std::io;
use std::io::{BufRead, BufReader};

/// Types that implement this trait can be converted into an implementation of [io::BufRead],
/// allowing them to be passed to the [TextReader::new] constructor. This allows [TextReader::new]
/// to support reading Strings, &str slices, &[u8] slices, files, etc.
pub trait TextIonDataSource {
    type TextSource: BufRead;
    fn to_text_ion_data_source(self) -> Self::TextSource;
}

impl TextIonDataSource for String {
    type TextSource = io::Cursor<Self>;

    fn to_text_ion_data_source(self) -> Self::TextSource {
        io::Cursor::new(self)
    }
}

impl<'a> TextIonDataSource for &'a str {
    type TextSource = io::Cursor<Self>;

    fn to_text_ion_data_source(self) -> Self::TextSource {
        io::Cursor::new(self)
    }
}

impl<'a> TextIonDataSource for &'a &[u8] {
    type TextSource = io::Cursor<Self>;

    fn to_text_ion_data_source(self) -> Self::TextSource {
        io::Cursor::new(self)
    }
}

impl<T: io::Read> TextIonDataSource for BufReader<T> {
    type TextSource = Self;

    fn to_text_ion_data_source(self) -> Self::TextSource {
        self
    }
}
