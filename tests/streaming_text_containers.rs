#![cfg(feature = "experimental-reader-writer")]

use ion_rs::{v1_0, AnyEncoding, Element, ElementReader, IonData, IonError, IonStream, Reader};
use std::io::{self, Read};

struct Chunks<'a> {
    data: &'a [u8],
    chunk_size: usize,
    stop_at_end: bool,
}

impl Read for Chunks<'_> {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        if self.data.is_empty() && self.stop_at_end {
            return Err(io::ErrorKind::WouldBlock.into());
        }
        let count = output.len().min(self.data.len()).min(self.chunk_size);
        output[..count].copy_from_slice(&self.data[..count]);
        self.data = &self.data[count..];
        Ok(count)
    }
}

#[test]
fn containers_at_each_chunk_boundary() {
    for text in [
        r#"[{name:"reader",count:17,tags:[1,2,3],enabled:true}]"#,
        r#"{a:[1,2],b:(foo / bar),c:{nested:true}}"#,
        r#"["escaped \" ] } ) \\", 'quoted \' ] } )', '''long ' '' ] } )''']"#,
        "[1, // ] } )\r\n 2, /* ] } ) */ 3]",
        "[1, '''one''' /* ] */ '''two''', 3]",
        r#"[{{YWJj//8=}}, {{"clob ] } )"}}, 1]"#,
        r#"annotated::[{foo:"bar"}]"#,
    ] {
        let expected = Element::read_all(text).unwrap();
        for chunk_size in 1..=text.len() {
            let input = Chunks {
                data: text.as_bytes(),
                chunk_size,
                stop_at_end: false,
            };
            let actual = Reader::new(AnyEncoding, IonStream::new(input))
                .unwrap()
                .read_all_elements()
                .unwrap();
            assert_eq!(
                IonData::from(actual),
                IonData::from(expected.clone()),
                "chunk {chunk_size}: {text}"
            );
        }
    }
}

#[test]
fn completed_container_does_not_wait_for_another_read() {
    let text = format!("[{}0]", r#"{a:"quoted ]",b:[1,2]},"#.repeat(1000));
    for chunk_size in [1, 7, 1024, 4096] {
        let input = Chunks {
            data: text.as_bytes(),
            chunk_size,
            stop_at_end: true,
        };
        let mut reader = Reader::new(v1_0::Text, IonStream::new(input)).unwrap();
        let item = reader.expect_next().unwrap();
        assert_eq!(
            item.read().unwrap().expect_list().unwrap().iter().count(),
            1001
        );
    }
}

#[test]
fn multiple_containers_and_scalars_share_the_buffer() {
    let text = format!("[{}0] 17 ann::{{a:2}} [3,4]", "{a:1},".repeat(100));
    let expected = Element::read_all(&text).unwrap();
    for chunk_size in [1, 3, 32, 100, 4096] {
        let input = Chunks {
            data: text.as_bytes(),
            chunk_size,
            stop_at_end: false,
        };
        let actual = Reader::new(AnyEncoding, IonStream::new(input))
            .unwrap()
            .read_all_elements()
            .unwrap();
        assert_eq!(IonData::from(actual), IonData::from(expected.clone()));
    }
}

#[test]
fn incomplete_and_invalid_containers_remain_errors() {
    for text in [
        "[1,2",
        "{a:[1,2]",
        "[1,?",
        "[1,}",
        "[1,\"unterminated",
        "[1,/* comment",
    ] {
        for chunk_size in 1..=text.len() {
            let input = Chunks {
                data: text.as_bytes(),
                chunk_size,
                stop_at_end: false,
            };
            assert!(Reader::new(v1_0::Text, IonStream::new(input))
                .unwrap()
                .read_all_elements()
                .is_err());
        }
    }
}

#[test]
fn malformed_input_is_not_hidden_by_a_later_io_error() {
    let input = Chunks {
        data: b"[1,2,3,4,?",
        chunk_size: 3,
        stop_at_end: true,
    };
    let result = Reader::new(v1_0::Text, IonStream::new(input))
        .unwrap()
        .read_all_elements();
    assert!(matches!(result, Err(IonError::Decoding(_))));
}

#[test]
fn incomplete_input_preserves_io_errors() {
    let input = Chunks {
        data: b"[1,2,3,4,5",
        chunk_size: 3,
        stop_at_end: true,
    };
    let result = Reader::new(v1_0::Text, IonStream::new(input))
        .unwrap()
        .read_all_elements();
    assert!(matches!(result, Err(IonError::Io(_))));
}
