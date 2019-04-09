/// Represents the Ion data type of a given value. To learn more about each data type,
/// read [the Ion Data Model](http://amzn.github.io/ion-docs/docs/spec.html#the-ion-data-model)
/// section of the spec.
#[derive(Debug, PartialEq, Eq, PartialOrd, Copy, Clone)]
pub enum IonType {
    Null,
    Boolean,
    Integer,
    Float,
    Decimal,
    Timestamp,
    Symbol,
    String,
    Clob,
    Blob,
    List,
    SExpression,
    Struct,
}
