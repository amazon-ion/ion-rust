use crate::element::Annotations;
use crate::IonType;
use std::cmp::Ordering;

/// Trait used for delegating [Eq] and [PartialEq] in [IonData].
/// Implementations of [IonOrd] must be consistent with [IonEq].
/// Since there is no total ordering in the Ion specification, do not write any code that depends on
/// a specific order being preserved. Only depend on the fact that a total ordering does exist.
pub(crate) trait IonOrd {
    // Intentionally not public—this trait is exposed via `impl Ord for IonData`.
    // Called ion_cmp to avoid shadowing with Ord::cmp
    fn ion_cmp(&self, other: &Self) -> Ordering;
}

impl<T: IonOrd> IonOrd for &T {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        T::ion_cmp(self, other)
    }
}

impl IonOrd for IonType {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl IonOrd for Annotations {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl IonOrd for bool {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}

impl IonOrd for f64 {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.total_cmp(other)
    }
}

impl<T: IonOrd> IonOrd for Vec<T> {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        let mut i0 = self.iter();
        let mut i1 = other.iter();
        loop {
            match [i0.next(), i1.next()] {
                [None, Some(_)] => return Ordering::Less,
                [None, None] => return Ordering::Equal,
                [Some(_), None] => return Ordering::Greater,
                [Some(a), Some(b)] => {
                    let ord = a.ion_cmp(b);
                    if ord != Ordering::Equal {
                        return ord;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod ord_tests {
    use super::*;
    use crate::element::{List, Sequence};
    use crate::{Element, IonData};
    use rstest::*;

    #[rstest]
    #[case::ion_type_is_first_precedence(
        r#" null true 1 2e1 3d1 2023-01-02T Symbol "String" {{"Clob"}} {{ Blob }} [] () {} "#
    )]
    #[case::annotations_are_sorted("A $0::A bar::A foo::A foo::$0::A foo::bar::A")]
    #[case::annotations_have_lower_precedence_than_type("foo::bar::null foo::true 3")]
    #[case::annotations_have_higher_precedence_than_value("3 foo::2 foo::bar::1")]
    #[case::nulls(
        r"
        null.null
        null.bool
        null.int
        null.float
        null.decimal
        null.timestamp
        null.symbol
        null.string
        null.clob
        null.blob
        null.list
        null.sexp
        null.struct
    "
    )]
    #[case::bools("null.bool false true")]
    #[case::ints("null.int -1 0 1")]
    #[case::floats("null.float -inf -1e0 -0e0 0e0 1e0 +inf nan")]
    #[case::decimals(
        r"
        null.decimal
        -0.0
        -0.00
        0.0
        0.00
        0.001
        0.0010
        1.0
        1.00
        10.00
        1d3
        10d2
        100d1
        1000d0
    "
    )]
    #[case::timestamps_sorted_by_point_in_time_and_precision(
        r"
        null.timestamp
        2020T
        2020-01T
        2020-01-01T
        2020-01-01T00:00Z
        2020-01-01T00:00:00Z
        2020-01-01T00:00:00.000Z
        2020-01-01T00:00:00.000000Z
        2020-01-01T00:00:00.001Z
        2020-01-01T00:00:00.001000Z
        2020-01-01T00:00:01Z
        2020-01-01T00:01Z
        2020-01-02T
        2020-02T
        2021T
    "
    )]
    #[case::timestamps_sorted_by_offset(
        r"
        2020-01-01T06:00:00-00:00
        2020-01-01T05:00:00-01:00
        2020-01-01T06:00:00+00:00
        2020-01-01T07:00:00+01:00
        2020-01-01T06:00:00.000-00:00
        2020-01-01T05:00:00.000-01:00
        2020-01-01T06:00:00.000+00:00
        2020-01-01T07:00:00.000+01:00
    "
    )]
    #[case::symbols(
        r"
        null.symbol
        $0
        ''
        'a'
        'aa'
        'aaa'
        'ab'
        'aba'
    "
    )]
    #[case::strings(
        r#"
        null.string
        ""
        "a"
        "aa"
        "aaa"
        "ab"
        "aba"
    "#
    )]
    #[case::clobs(
        r#"
        null.clob
        {{ "" }}
        {{ "a" }}
        {{ "aa" }}
        {{ "aaa" }}
        {{ "ab" }}
        {{ "aba" }}
    "#
    )]
    #[case::blobs(
        r#"
        null.blob
        {{ }}
        {{ AA== }} // 0x00
        {{ AAA= }} // 0x00 0x00
        {{ AAAA }} // 0x00 0x00 0x00
        {{ AAE= }} // 0x00 0x01
        {{ AAEA }} // 0x00 0x01 0x00
        {{ AQ== }} // 0x01
        {{ AQE= }} // 0x01 0x01
    "#
    )]
    #[case::lists(
        r"
        null.list
        []
        [a]
        [a, a]
        [a, a, a]
        [a, b]
        [a, b, a]
    "
    )]
    #[case::sexps(
        r"
        null.sexp
        ()
        (a)
        (a a)
        (a a a)
        (a b)
        (a b a)
    "
    )]
    #[case::structs(
        r"
        null.struct
        {}
        { $0: A }
        { $0: A, $0: A }
        { $0: A, $0: B }
        { a: A }
        { a: A, a: A }
        { a: A, b: A, a: A }
        { a: A, a: B }
        { a: A, b: A, a: B }
        { a: A, b: A }
        { a: B, b: A }
    "
    )]
    fn test_order(#[case] ion: &str) {
        let original = Element::read_all(ion)
            .unwrap()
            .into_iter()
            .map(IonData::from)
            .collect::<Vec<_>>();
        let mut copy = original.clone();
        copy.sort();

        if original != copy {
            let original_for_display: List =
                Sequence::new(original.iter().cloned().map(IonData::into_inner)).into();
            let copy_for_display: List =
                Sequence::new(copy.iter().cloned().map(IonData::into_inner)).into();
            // Prints using display (i.e. as Ion text)
            println!("original: {original_for_display}");
            println!("copy: {copy_for_display}");
            // Prints using debug
            assert_eq!(original, copy);
        }

        let mut original_iter = original.iter();
        let mut previous_element = original_iter.next().unwrap();
        while let Some(element) = original_iter.next() {
            if element == previous_element {
                assert_eq!(Ordering::Equal, element.cmp(previous_element));
            } else {
                assert_eq!(Ordering::Greater, element.cmp(previous_element), "\n{element} <:> {previous_element}\n Less: {previous_element:?}\n More: {element:?}");
                assert_eq!(
                    Ordering::Less,
                    previous_element.cmp(element),
                    "{element} {element:?} -- {previous_element} {previous_element:?}"
                )
            }
            previous_element = element;
        }
    }
}
