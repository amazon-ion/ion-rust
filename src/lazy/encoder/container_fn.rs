//! Container population traits that allow closures to be used in places where the borrow checker
//! would normally balk due to point-in-time limitations.
//! See: <https://blog.rust-lang.org/2022/10/28/gats-stabilization.html#implied-static-requirement-from-higher-ranked-trait-bounds>

use crate::lazy::encoder::value_writer::ValueWriter;
use crate::IonResult;

/// Generates a trait with a single method that takes one of [`ValueWriter`]'s associated types as
/// an argument. The trait extends `FnOnce(TheAssociatedType) -> IonResult<()>`, allowing it to be
/// invoked directly as a closure. The macro also generates a blanket implementation of the trait
/// for any closures that also implement `FnOnce(TheAssociatedType) -> IonResult<()>`.
///
/// For example:
///```text
///     container_fn_trait!(ListFn => ListWriter);
///```
///
/// generates a trait `ListFn` with a single method:
///```text
///     fn populate(self, writer: &mut V::ListWriter) -> IonResult<()>;
///```
///
/// Types that implement this trait can be invoked as though they were closures.
/// Closures with the signature `(&mut V::ListWriter) -> IonResult<()>` automatically implement
/// the trait.
///
/// This circular arrangement allows the compiler to accept closures that would otherwise
/// require explicit Higher-Rank Trait Bounds, a feature which currently has limitations.
macro_rules! container_fn_trait {
    // End of iteration
    () => {};
    // Recurses one argument pair at a time
    ($trait_name:ident => $assoc_type_name:ident, $($rest:tt)*) => {
        pub trait $trait_name<V: ValueWriter>: FnOnce(&mut V::$assoc_type_name) -> IonResult<()> {
            fn populate(self, writer: &mut V::$assoc_type_name) -> IonResult<()>;
        }

        impl<F, V: ValueWriter> $trait_name<V> for F
            where
                F: FnOnce(&mut V::$assoc_type_name) -> IonResult<()>,
        {
            fn populate(self, writer: &mut V::$assoc_type_name) -> IonResult<()> {
                self(writer)
            }
        }

        container_fn_trait!($($rest)*);
    };
}

container_fn_trait!(
    ListFn => ListWriter,
    SExpFn => SExpWriter,
    StructFn => StructWriter,
    MacroArgsFn => MacroArgsWriter,
);
