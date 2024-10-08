use crate::element::builders::SequenceBuilder;
use crate::element::iterators::SequenceIterator;
use crate::element::Element;
use crate::ion_data::{IonEq, IonOrd};
use crate::lazy::encoding::Encoding;
use crate::write_config::WriteConfig;
use crate::IonResult;
use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use std::io;

/// An iterable, addressable series of Ion [`Element`]s.
///
/// A `Sequence` is not itself an Ion value type, but can represent a series of Ion values appearing
/// in a [`List`](crate::List), a [`SExp`](crate::SExp), or at the top level.
#[derive(Clone, PartialEq, Eq)]
pub struct Sequence {
    elements: Vec<Element>,
}

impl Debug for Sequence {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Sequence<")?;
        let mut is_first = true;
        for element in self {
            if is_first {
                write!(f, "{element}")?;
                is_first = false;
            } else {
                write!(f, ", {element}")?;
            }
        }
        write!(f, ">")
    }
}

impl Sequence {
    pub fn new<E: Into<Element>, I: IntoIterator<Item = E>>(elements: I) -> Sequence {
        let elements = elements.into_iter().map(|e| e.into()).collect();
        Sequence { elements }
    }

    pub fn builder() -> SequenceBuilder {
        SequenceBuilder::new()
    }

    pub fn clone_builder(&self) -> SequenceBuilder {
        SequenceBuilder::with_initial_elements(&self.elements)
    }

    pub fn elements(&self) -> SequenceIterator<'_> {
        SequenceIterator::new(&self.elements)
    }

    pub fn get(&self, index: usize) -> Option<&Element> {
        self.elements.get(index)
    }

    pub fn len(&self) -> usize {
        self.elements.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> SequenceIterator<'_> {
        self.elements()
    }

    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::{Element, Sequence};
    /// use ion_rs::v1_0::Binary;
    ///
    /// let ion_data = r#"1 2 3 foo bar baz"#;
    /// let sequence_before: Sequence = Element::read_all(ion_data)?;
    ///
    /// // Encode the elements in this sequence as a binary Ion stream.
    /// let ion_bytes: Vec<u8> = sequence_before.encode_as(Binary)?;
    /// // Read the sequence back from the binary stream
    /// let sequence_after = Element::read_all(ion_bytes)?;
    ///
    /// // Confirm that the value we read back is identical to the one we serialized
    /// assert_eq!(sequence_before, sequence_after);
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn encode_as<E: Encoding, C: Into<WriteConfig<E>>>(
        &self,
        config: C,
    ) -> IonResult<E::Output> {
        config.into().encode_all(self.elements())
    }

    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::{Element, Sequence};
    /// use ion_rs::v1_0::Binary;
    ///
    /// let ion_data = r#"1 2 3 foo bar baz"#;
    /// let sequence_before: Sequence = Element::read_all(ion_data)?;
    ///
    /// // Encode the elements in this sequence to our buffer as a binary Ion stream. The bytes will
    /// // be written to the provided Vec<u8>, and the Vec<u8> will be returned when encoding is complete.
    /// let ion_bytes: Vec<u8> = sequence_before.encode_to(Vec::new(), Binary)?;
    /// // Read the sequence back from the binary stream
    /// let sequence_after = Element::read_all(ion_bytes)?;
    ///
    /// // Confirm that the value we read back is identical to the one we serialized
    /// assert_eq!(sequence_before, sequence_after);
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn encode_to<E: Encoding, C: Into<WriteConfig<E>>, W: io::Write>(
        &self,
        output: W,
        config: C,
    ) -> IonResult<W> {
        config.into().encode_all_to(output, self.elements())
    }
}

impl AsRef<Sequence> for Sequence {
    fn as_ref(&self) -> &Sequence {
        self
    }
}

impl AsRef<[Element]> for Sequence {
    fn as_ref(&self) -> &[Element] {
        self.elements.as_slice()
    }
}

// This is more efficient than Sequence::new(), which will iterate over and convert each value to
// an Element for better ergonomics.
impl From<Vec<Element>> for Sequence {
    fn from(elements: Vec<Element>) -> Self {
        Sequence { elements }
    }
}

impl<'a> IntoIterator for &'a Sequence {
    type Item = &'a Element;
    // TODO: Change once `impl Trait` type aliases are stable
    // type IntoIter = impl Iterator<Item = &'a Element>;
    type IntoIter = SequenceIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements()
    }
}

// TODO: This currently clones elements. We should change `Sequence` to wrap a VecDeque so we can
//       pop from the front.
impl IntoIterator for Sequence {
    type Item = Element;
    // TODO: Change once `impl Trait` type aliases are stable
    // type IntoIter = impl Iterator<Item = &'a Element>;
    type IntoIter = OwnedSequenceIterator;

    fn into_iter(self) -> Self::IntoIter {
        OwnedSequenceIterator {
            current: 0,
            sequence: self,
        }
    }
}

impl FromIterator<Element> for Sequence {
    fn from_iter<T: IntoIterator<Item = Element>>(iter: T) -> Self {
        Vec::from_iter(iter).into()
    }
}

impl IonEq for Sequence {
    fn ion_eq(&self, other: &Self) -> bool {
        self.elements.ion_eq(&other.elements)
    }
}

impl IonOrd for Sequence {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.elements.ion_cmp(&other.elements)
    }
}

pub struct OwnedSequenceIterator {
    current: usize,
    sequence: Sequence,
}

impl Iterator for OwnedSequenceIterator {
    type Item = Element;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(element) = self.sequence.get(self.current) {
            self.current += 1;
            Some(element.clone())
        } else {
            None
        }
    }
}
