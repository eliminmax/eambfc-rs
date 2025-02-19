// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::ToTokens;
use syn::{parse_macro_input, parse_quote, Attribute, Block, Ident, ItemFn};

#[proc_macro_attribute]
/// For tests which should be `ignore`d on non-unix targets due to the use of unix-only traits like
/// `std::os::unix::process::Command`, the bodies still must be able to compile on non-unix
/// targets. In such cases, this macro can replace the `#[test]` and `#[ignore]` attributes:
///
/// ```no_run
/// #[unix_test("<unix-only thing here>")]
/// fn foo() {
///     ...
/// }
/// ```
///
/// is equivalent to
/// ```no_run
/// #[cfg_attr(not(unix), ignore = "test \"foo\" requires unix-only <unix-only thing here>")]
/// #[test]
/// fn foo() {
///     #[cfg(unix)]
///     {
///         ...
///     }
///     #[cfg(not(unix))]
///     panic!("Test can't run on non-unix targets")
/// }
/// ```
///
/// It inserts the `panic!` for non-unix targets so that it can compile for both tests that return
/// `()` and tests that return `Result<T, E>`, due to the type coercion from `!` to anything.
pub fn unix_test(attr_arg: TokenStream, func: TokenStream) -> TokenStream {
    let unix_only_thing = parse_macro_input!(attr_arg as syn::LitStr).value();
    let mut func = parse_macro_input!(func as ItemFn);
    let ignore_reason = format!(
        "test {} requires unix-only {unix_only_thing}",
        func.sig.ident
    );

    func.attrs.extend([
        parse_quote!(#[cfg_attr(not(unix), ignore = #ignore_reason)]),
        parse_quote!(#[test]),
    ]);
    let inner = func.block.to_token_stream();
    func.block = Box::new(parse_quote! {
        {
            #[cfg(unix)]
            #inner
            #[cfg(not(unix))]
            panic!("Test can't run on non-unix targets")
        }
    });

    func.into_token_stream().into()
}

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
/// #[cfg_attr(not(feature = "bintests"), ignore = "Binary tests are not enabled")]
/// #[cfg_attr(
///     all(feature = "bintests", not(feature = "foo_arch")),
///     ignore = "foo_arch support disabled"
/// )]
/// #[cfg_attr(
///     all(
///         feature = "bintests", feature = "foo_arch",
///         any(target_os = "windows", not(can_run_foo_arch))
///     ),
///     ignore = "can't run foo_arch Linux ELF binaries"
/// )]
/// #[test]
/// fn test_foo_arch() {
///     #[cfg(feature = "bintests")]
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
    let feature = arch.to_string();

    let msg_disabled = format!("{arch} support disabled");
    let msg_cant_run = format!("can't run {arch} Linux ELF binaries");

    let extra_attrs: Vec<Attribute> = parse_quote!(
        #[cfg_attr(not(feature = "bintests"), ignore = "binary tests are not enabled")]
        #[cfg_attr(all(feature = "bintests", not(feature = #feature)), ignore = #msg_disabled)]
        #[cfg_attr(
            all(
                feature = "bintests", feature = #feature,
                any(target_os = "windows", not(#can_run_cfg))
            ),
            ignore = #msg_cant_run
        )]
        #[test]
    );
    test_func.attrs.extend(extra_attrs);
    test_func.into_token_stream().into()
}

/// An attribute that combines `#[test]` with `#[cfg_attr(debug_assertions), should_panic = "msg"]
/// ```no_run
/// #[debug_assert_test("msg")]
/// fn foo () {
///     ...
/// }
/// ```
/// expands to
/// #[test]
/// #[cfg(debug_assertions, should_panic = "msg")]
/// fn foo () {
///     ...
/// }
#[proc_macro_attribute]
pub fn debug_assert_test(attr_arg: TokenStream, func: TokenStream) -> TokenStream {
    let msg = parse_macro_input!(attr_arg as syn::LitStr)
        .value()
        .to_string();
    let mut func = parse_macro_input!(func as ItemFn);
    func.attrs.extend([
        parse_quote!(#[test]),
        parse_quote!(#[cfg_attr(debug_assertions, should_panic = #msg)]),
    ]);

    func.into_token_stream().into()
}
