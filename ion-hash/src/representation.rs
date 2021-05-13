use ion_rs::value::AnyInt;

// FIXME: Some types (e.g. BigInt) can't spit out a representation as a
// reference, and thus need to allocate. Change this trait so that not all types
// have to pay the cost of allocation.
pub(crate) trait Representation {
    fn repr(&self) -> Option<Vec<u8>>;
}

impl Representation for Option<&AnyInt> {
    fn repr(&self) -> Option<Vec<u8>> {
        match self {
            Some(AnyInt::I64(v)) => match v {
                0 => None,
                _ => Some(
                    v.abs()
                        .to_be_bytes()
                        .iter()
                        .skip_while(|b| **b == 0)
                        .map(|b| b.clone())
                        .collect::<Vec<_>>(),
                ),
            },
            Some(AnyInt::BigInt(v)) => Some(v.magnitude().to_bytes_be()),
            None => None,
        }
    }
}

impl Representation for Option<&str> {
    fn repr(&self) -> Option<Vec<u8>> {
        match self {
            Some(s) => Some(s.as_bytes().into()),
            None => None,
        }
    }
}
