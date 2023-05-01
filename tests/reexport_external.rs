use std::convert::TryInto;

use ion_rs::external::bigdecimal::{BigDecimal, Zero};
use ion_rs::types::Decimal;

/// This test shows how the ion_rs integration with bigdecimal can be used
/// through a reexport. This means that consumers of ion_rs can use this
/// integration without having to specify the exact depdendency version.
///
/// See also: https://github.com/amazon-ion/ion-rust/issues/302.
#[test]
fn bigdecimal_is_reexported() {
    let ion_rs_type = Decimal::new(0, 0);
    let integration_type: BigDecimal = ion_rs_type.try_into().expect("not negative zero");

    assert_eq!((Zero::zero(), 0), integration_type.as_bigint_and_exponent())
}
