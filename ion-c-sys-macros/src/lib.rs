use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{parse_quote, FnArg, Ident, PatType, ReturnType};

/// This macro is intended to support the `IonCReaderHandle` type. When any
/// function returns an `IonCError`, the error should be populated with the
/// current reader position.
///
/// Without this macro, errors could be decorated like so:
///
/// ```no_test
/// fn foo() -> IonCResult<()> {
///     fn1().map_err(|err| include_current_position(self.reader, err))?
///     // ...
///     Ok(())
/// }
/// ```
///
/// However, functions can fail in many places, so decorating each of these with
/// `map_err` is tedious and error prone:
///
/// ```no_test
/// fn foo() -> IonCResult<()> {
///   fn1()?.map_err(..);
///   fn2()?.map_err(..);
/// }
/// ```
///
/// This macro rewrites the function such that any error gets the position
/// added. It does this by moving the existing implementation into a closure and
/// then calling `map_err` on the result.
///
/// ***Note***: to make the variety of possible functions work (which include mutable
/// borrows, lifetime elision), the closure uses the `move` keyword. There are
/// some gymnastics (adapted from ***[dtolnay/no-panic][no-panic]***) to make that work out.
///
/// [no-panic]: https://github.com/dtolnay/no-panic
#[proc_macro_attribute]
pub fn position_error(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut function = syn::parse_macro_input!(item as syn::ItemFn);

    // this is heavily adapted for dtolnay/panic - as this code evolves to deal
    // with rustc/ion-c-sys changes refer to to the above for any changes
    // here...
    let mut move_self = None;
    let mut arg_pat = Vec::new();
    let mut arg_val = Vec::new();
    for (i, input) in function.sig.inputs.iter_mut().enumerate() {
        let numbered = Ident::new(&format!("__arg{}", i), Span::call_site());
        match input {
            FnArg::Typed(PatType { pat, .. }) => {
                arg_pat.push(quote!(#pat));
                arg_val.push(quote!(#numbered));
                *pat = parse_quote!(mut #numbered);
            }
            FnArg::Receiver(_) => {
                move_self = Some(quote! {
                    if false {
                        loop {}
                        #[allow(unreachable_code)]
                        {
                            let __self = self;
                        }
                    }
                });
            }
        }
    }

    let ret = match &function.sig.output {
        ReturnType::Default => quote!(-> ()),
        output @ ReturnType::Type(..) => quote!(#output),
    };
    let stmts = function.block.stmts;
    function.block = Box::new(parse_quote!({
        let reader = self.reader;
        let __result = (move || #ret {
            #move_self
            #(
                let #arg_pat = #arg_val;
            )*
            #(#stmts)*
        })();
        __result.map_err(|err| include_current_position(&reader, err))
    }));

    TokenStream::from(quote!(#function))
}
