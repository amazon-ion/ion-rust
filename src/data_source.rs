use std::fs::File;
use std::io;
use std::io::{BufRead, BufReader, Read, StdinLock};

/// Types that implement this trait can be converted into an implementation of [BufRead], allowing
/// users to deserialize Ion from a variety of types that might not define I/O operations on their own.
pub trait IonDataSource {
    type DataSource: BufRead;
    fn to_ion_data_source(self) -> Self::DataSource;
}

impl IonDataSource for String {
    type DataSource = io::Cursor<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        io::Cursor::new(self)
    }
}

impl<'a> IonDataSource for &'a str {
    type DataSource = io::Cursor<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        io::Cursor::new(self)
    }
}

impl<'a> IonDataSource for &'a [u8] {
    type DataSource = io::Cursor<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        io::Cursor::new(self)
    }
}

impl<'a, const N: usize> IonDataSource for &'a [u8; N] {
    type DataSource = io::Cursor<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        io::Cursor::new(self)
    }
}

impl IonDataSource for Vec<u8> {
    type DataSource = io::Cursor<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        io::Cursor::new(self)
    }
}

impl<T: BufRead, U: BufRead> IonDataSource for io::Chain<T, U> {
    type DataSource = Self;

    fn to_ion_data_source(self) -> Self::DataSource {
        self
    }
}

impl<T> IonDataSource for io::Cursor<T>
where
    T: AsRef<[u8]>,
{
    type DataSource = Self;

    fn to_ion_data_source(self) -> Self::DataSource {
        self
    }
}

impl<T: Read> IonDataSource for BufReader<T> {
    type DataSource = Self;

    fn to_ion_data_source(self) -> Self::DataSource {
        self
    }
}

impl IonDataSource for File {
    type DataSource = BufReader<Self>;

    fn to_ion_data_source(self) -> Self::DataSource {
        BufReader::new(self)
    }
}

// Allows Readers to consume Ion directly from STDIN
impl<'a> IonDataSource for StdinLock<'a> {
    type DataSource = Self;

    fn to_ion_data_source(self) -> Self::DataSource {
        self
    }
}
