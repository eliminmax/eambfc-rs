// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::ToTokens;
use syn::{parse_macro_input, parse_quote, Attribute, Block, Ident, ItemFn};

/// Add the appropriate attribute to a function to omit its body and add an appropriate `ignore`
/// message if the `disasmtests` feature is disabled, and mark it with the `test` attribute
/// ```no_run
/// #[disasm_test]
/// fn foo() {
///     ...
/// }
/// ```
///
/// expands to
///
/// ```no_run
/// #[cfg_attr(not(feature = "disasmtests"), ignore = "Disassembly tests are not enabled")]
/// #[test]
/// fn foo() {
///     #[cfg(feature = "disasmtests")]
///     {
///         ...
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn disasm_test(_: TokenStream, func: TokenStream) -> TokenStream {
    let ItemFn {
        mut attrs,
        vis,
        sig,
        block: body,
    } = parse_macro_input!(func);
    attrs.push(parse_quote!(#[
        cfg_attr(not(feature = "disasmtests"),
        ignore = "Disassembly tests are not enabled")
    ]));
    attrs.push(parse_quote!(#[test]));

    let inner = body.to_token_stream();

    let block: Box<Block> = Box::new(parse_quote! {
        {
            #[cfg(feature = "disasmtests")]
            #inner
        }
    });

    ItemFn {
        attrs,
        vis,
        sig,
        block,
    }
    .into_token_stream()
    .into()
}

/// Add attributes to an architecture test function that adds an appropriate ignore message if the
/// test must be skipped for one of the following reasons:
///
/// 1. The `"bintests"` feature is disabled
/// 2. The architecture is disabled
/// 3. The system is unable to run the output binaries for the architecture, and thus can't test
///    them
///
/// The first of those reasons to be matched will be used.
///
///
/// ```no_run
/// #[bin_test(foo_arch)]
/// fn test_foo_arch() {
///     ...
/// }
/// ```
///
/// expands to
///
/// ```no_run
/// #[allow(unused_attribute, reason = "multiple possible reasons to ignore")]
/// #[cfg_attr(not(feature = "bintests"), ignore = "Binary tests are not enabled")]
/// #[cfg_attr(
///     not(feature = "foo_arch"), ignore = "foo_arch support disabled"
/// )]
/// #[cfg_attr(
///     any(target_os = "windows", not(can_run_foo_arch)),
///     ignore = "can't run foo_arch Linux ELF binaries"
/// )]
/// #[test]
/// fn test_foo_arch() {
///     #[cfg(feature = "disasmtests")]
///     {
///         ...
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn bin_test(arch: TokenStream, func: TokenStream) -> TokenStream {
    let arch: Ident = parse_macro_input!(arch);
    let mut test_func: ItemFn = parse_macro_input!(func);

    let can_run_cfg = Ident::new(&format!("can_run_{arch}"), Span::call_site());
    let arch_feature = arch.to_string();

    let extra_attrs: Vec<Attribute> = parse_quote!(
        #[allow(unused_attribute, reason = "multiple possible reasons to ignore")]
        #[cfg_attr(not(feature = "bintests"), ignore = "Binary tests are not enabled")]
        #[cfg_attr(
            not(feature = #arch_feature), ignore = concat!(#arch_feature, " support disabled")
        )]
        #[cfg_attr(
            any(target_os = "windows", not(#can_run_cfg)),
            ignore = concat!("can't run ", stringify!(#arch_feature), " Linux ELF binaries")
        )]
        #[test]
    );
    test_func.attrs.extend(extra_attrs);
    test_func.into_token_stream().into()
}
