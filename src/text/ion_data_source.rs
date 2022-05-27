use std::fs::File;
use std::io;
use std::io::{BufRead, BufReader, Read};

/// Types that implement this trait can be converted into an implementation of [io::BufRead],
/// allowing users to build a [Reader] from a variety of types that might not define I/O operations
/// on their own.
pub trait ToIonDataSource {
    type DataSource: BufRead;
    fn to_ion_data_source(self) -> Self::DataSource;
}

impl ToIonDataSource for String {
    type DataSource = io::Cursor<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        io::Cursor::new(self)
    }
}

impl<'a> ToIonDataSource for &'a str {
    type DataSource = io::Cursor<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        io::Cursor::new(self)
    }
}

impl<'a> ToIonDataSource for &'a [u8] {
    type DataSource = io::Cursor<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        io::Cursor::new(self)
    }
}

impl<'a> ToIonDataSource for Vec<u8> {
    type DataSource = io::Cursor<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        io::Cursor::new(self)
    }
}

impl<T: BufRead, U: BufRead> ToIonDataSource for io::Chain<T, U> {
    type DataSource = Self;

    fn to_ion_data_source(self) -> Self::DataSource {
        self
    }
}

impl<T: Read> ToIonDataSource for BufReader<T> {
    type DataSource = Self;

    fn to_ion_data_source(self) -> Self::DataSource {
        self
    }
}

impl ToIonDataSource for File {
    type DataSource = BufReader<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        BufReader::new(self)
    }
}
