extern crate proc_macro;
extern crate proc_macro2;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn;
use syn::{parse_macro_input, Ident, ItemFn};

fn impl_kernel_test(ast: &syn::ItemFn) -> TokenStream {
    let name = &ast.sig.ident;
    let case_name = Ident::new(&format!("__test_{}", name), Span::call_site());

    let tokens = quote! {
        #[test_case]
        const #case_name: (&'static str, &'static str, fn()) = (module_path!(), stringify!(#name), #name);
        #ast
    };

    tokens.into()
}

#[proc_macro_attribute]
pub fn kernel_test(attr: TokenStream, item: TokenStream) -> TokenStream {
    let ast: syn::ItemFn = parse_macro_input!(item as ItemFn);
    impl_kernel_test(&ast)
}
