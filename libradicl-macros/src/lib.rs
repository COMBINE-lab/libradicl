use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Lit, Meta, MetaNameValue};

#[proc_macro_derive(UmiTagged, attributes(umi_tagged))]
pub fn derive_umi_tagged(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    let name = &input.ident;
    let generics = &input.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    
    // Parse the attribute to get the field name
    let field_name = get_umi_field_name(&input);
    
    let field_ident = syn::Ident::new(&field_name, proc_macro2::Span::call_site());
    
    let expanded = quote! {
        impl #impl_generics UmiTaggedRecord for #name #ty_generics #where_clause {
            fn umi(&self) -> u64 {
                self.#field_ident
            }
        }
    };
    
    TokenStream::from(expanded)
}

fn get_umi_field_name(input: &DeriveInput) -> String {
    for attr in &input.attrs {
        if attr.path().is_ident("umi_tagged") {
            if let Meta::List(meta_list) = &attr.meta {
                let tokens = &meta_list.tokens;
                let parsed: Result<MetaNameValue, _> = syn::parse2(tokens.clone());
                
                if let Ok(nv) = parsed {
                    if nv.path.is_ident("umi") {
                        if let syn::Expr::Lit(expr_lit) = &nv.value {
                            if let Lit::Str(lit_str) = &expr_lit.lit {
                                return lit_str.value();
                            }
                        }
                    }
                }
            }
        }
    }
    
    // Default to "umi" if no attribute is found
    "umi".to_string()
}

