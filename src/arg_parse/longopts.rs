// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use super::RunConfig;
use crate::err::{BFCompileError, BFErrorID};
use crate::OutMode;
use libc::{c_char, c_int, getopt_long, option};
use std::ffi::{CStr, CString, OsString};
use std::os::unix::ffi::OsStringExt;
use std::ptr::{null, null_mut};

enum ArgRequirements {
    None = 0,
    Required = 1,
    #[expect(
        dead_code,
        reason = "Variant not needed, included for completeness's sake"
    )]
    Optional = 2,
}

unsafe extern "C" {
    /// Global value set within `libc` by the POSIX `getopt` and GNU `getopt_long` functions -
    /// pointer to the parameter that was provided to the current argument
    ///
    /// # SAFETY: not safe to access in multi-threaded contexts, and not safe to access if it's not
    ///   already set by a libc function.
    static mut optarg: *mut c_char;
    /// Global value set within `libc` by the POSIX `getopt` and GNU `getopt_long` functions -
    ///   the index within `argv` of the next element to process
    ///
    /// # SAFETY: not safe to access in multi-threaded contexts, and not safe to access if it's not
    ///   already set by a libc function.
    static mut optind: c_int;
    /// Global value set within `libc` by the POSIX `getopt` and GNU `getopt_long` functions -
    ///   the ASCII character option that was passed, or -1 if no option was passed.
    ///
    /// # SAFETY: not safe to access in multi-threaded contexts, and not safe to access if it's not
    ///   already set by a libc function.
    static mut optopt: c_int;
}

/// Construct a new `option` with a null `flag`, and the provided parameters for the other fields.
const fn new_opt(name: &'static CStr, has_arg: ArgRequirements, val: u8) -> option {
    option {
        name: name.as_ptr(),
        has_arg: has_arg as c_int,
        flag: null_mut(),
        val: val as c_int,
    }
}

/// Return an `option` for use with `getopt_long` as the final option in its
/// `const *option longopts` array parameter
const fn final_opt() -> option {
    option {
        name: null(),
        has_arg: 0,
        flag: null_mut(),
        val: 0,
    }
}

/// A wrapper around a `Vec<*mut c_char>`, where each contained pointer was created with
/// `CString::into_raw`. Constructing it any other way will result in undefined behavior when
/// dropping it. Derefs to the underlying `Vec`
struct CCompatibleArgs(Vec<*mut c_char>);

impl CCompatibleArgs {
    fn into_iter(mut self) -> impl Iterator<Item = *mut c_char> {
        std::mem::take(&mut self.0).into_iter()
    }
}

impl std::ops::Deref for CCompatibleArgs {
    type Target = Vec<*mut c_char>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for CCompatibleArgs {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Drop for CCompatibleArgs {
    fn drop(&mut self) {
        self.0
            .drain(..)
            // SAFETY: As long as pointers in CCompatibleArgs all came from CString::into_raw,
            // this is safe.
            .for_each(|ptr| unsafe { drop(CString::from_raw(ptr)) });
    }
}

/// use glibc's `getopt_long` to parse `args`.
///
/// # panics if any arg within `args` contains embedded null bytes
///
/// # SAFETY
///
/// While this function **does** handle most of the safety invariants needed for `getopt_long`
/// internally, there is no way to use `getopt_long` safely in a multi-threaded context, so this
/// function can only be called before spawning any threads.
pub(crate) unsafe fn parse_args_long(
    args: impl Iterator<Item = OsString>,
) -> Result<RunConfig, (BFCompileError, OutMode)> {
    const OPTSTRING: &CStr = c":hVqjOkcAa:e:t:s:";

    let mut pcfg = super::PartialRunConfig::default();
    let mut args: Vec<_> = args.collect();
    args.insert(0, OsString::from("placeholder"));

    let mut raw_args = CCompatibleArgs(
        args.into_iter()
            .map(|arg| {
                let mut arg = arg.into_vec();
                arg.push(0);
                CString::from_vec_with_nul(arg)
                    .expect("Args should not have null bytes embedded!")
                    .into_raw()
            })
            .collect(),
    );

    let longopts = [
        new_opt(c"help", ArgRequirements::None, b'h'),
        new_opt(c"version", ArgRequirements::None, b'V'),
        new_opt(c"quiet", ArgRequirements::None, b'q'),
        new_opt(c"json", ArgRequirements::None, b'j'),
        new_opt(c"optimize", ArgRequirements::None, b'O'),
        new_opt(c"keep-failed", ArgRequirements::None, b'k'),
        new_opt(c"continue", ArgRequirements::None, b'c'),
        new_opt(c"list-targets", ArgRequirements::None, b'A'),
        new_opt(c"target-arch", ArgRequirements::Required, b'a'),
        new_opt(c"tape-size", ArgRequirements::Required, b't'),
        new_opt(c"source-suffix", ArgRequirements::Required, b'e'),
        new_opt(c"output-suffix", ArgRequirements::Required, b's'),
        final_opt(),
    ];
    loop {
        // SAFETY:
        // * `getopt_long` must be passed an optstring that's either empty or compatible with the
        // GNU version of `getopt`. OPTSTRING is compatible with the GNU version of `getopt`.
        //
        // * argc must be the number of elements in argv, which is a mutable array of *const chars.
        // The use of raw_args for both ensures that it is.
        //
        // * longopts must be terminated by an `options` struct with all values set to zero, which
        // it is.
        //
        // `longindex` may be null, in which case the related functionality is disabled.
        let opt = unsafe {
            getopt_long(
                raw_args.len() as c_int,
                raw_args.as_mut_ptr(),
                OPTSTRING.as_ptr(),
                longopts.as_ptr(),
                null_mut(),
            )
        };
        if opt == -1 {
            break;
        }
        let opt = opt.to_le_bytes()[0];
        match opt {
            b'h' => return Ok(RunConfig::ShowHelp),
            b'V' => return Ok(RunConfig::ShowVersion),
            b'A' => return Ok(RunConfig::ListArches),
            b'a' | b'e' | b's' | b't' => {
                // SAFETY: optarg is a pointer to a null-terminated `c_char` sequence containing
                // the parameter passed to the argument - assuming it's not `memcpy`ed, it's a
                // pointer to somewhere within `raw_args`. This is safe as long as `raw_args` is
                // allocated, which it definitely is at this point in the function, and is safe to
                // pass to the `pcfg.*` functions so long as it does not overlap with any other
                // pointers that it might have at the same time - which it won't.
                let param = unsafe { CStr::from_ptr(optarg) }.to_bytes();
                match opt {
                    b'a' => pcfg.set_arch(param)?,
                    b'e' => pcfg.set_ext(param.to_owned())?,
                    b's' => pcfg.set_suffix(param.to_owned())?,
                    b't' => pcfg.set_tape_size(param.to_owned())?,
                    _ => unreachable!(),
                }
            }
            // value returned when an option that expects a parameter is missing one
            b':' => {
                return Err(pcfg.gen_err(
                    BFErrorID::MissingOperand,
                    format!(
                        "-{} requires an additional argument",
                        // SAFETY: optopt will be set to a c_char option missing its expected
                        // value, so it will be one of `b'a' as c_char`, `b'e' as c_char`,
                        // `b's' as c_char`, or `b't' as c_char` In a single-threaded context, it's
                        // safe.
                        unsafe { optopt as u8 }.escape_ascii()
                    ),
                ));
            }
            0 => {
                return Err(pcfg.gen_err(
                    BFErrorID::UnknownArg,
                    format!(
                        "\"{}\" is not a recognized argument.",
                        // SAFETY: `optind` set by call to `getopt_long`, and safe to access in
                        // single-threaded contexts, and the pointer came from a CString, so is
                        // valid to use as a CStr
                        unsafe { CStr::from_ptr(raw_args[optind as usize - 1]) }.to_string_lossy()
                    ),
                ));
            }
            b'?' => {
                return Err(pcfg.gen_err(
                    BFErrorID::UnknownArg,
                    format!(
                        "'-{}' is not a recognized argument",
                        // SAFETY: `optopt` set by call to `getopt_long`, and safe to access in
                        // single-threaded contexts
                        unsafe { optopt as c_char as u8 }.escape_ascii()
                    ),
                ));
            }
            _ => pcfg.parse_standalone_flag(opt)?,
        }
    }
    let files = unsafe { get_files(raw_args.into_iter()) };
    if !files.is_empty() {
        pcfg.source_files = Some(files);
    }
    Ok(RunConfig::StandardRun(pcfg.try_into()?))
}

/// Convert a null-terminated `Vec<*mut c_char>` into a Vec<OsString> containing parameters that
/// did not contain command-line flags.
///
/// # SAFETY:
/// * This function must be passed a `Vec<*mut c_char>` created from `CString::into_raw`.
///   Anything else will result in undefined behavior.
///
/// * This function must only be called after calling a function that sets the `optind` global in
///   libc (such as `libc::getopt_long`),
///
/// * This function is not safe to use in a multithreaded context, as it's impossible to safely
///   access `optind` in a multithreaded context
unsafe fn get_files(mut raw_args: impl Iterator<Item = *mut c_char>) -> Vec<OsString> {
    raw_args
        .by_ref()
        // SAFETY: Only one thread can access optind at a time
        .take(unsafe { optind } as usize)
        // SAFETY: Only pointers originating from CString::into_raw can be safely passed here
        .for_each(|ptr| unsafe { drop(CString::from_raw(ptr)) });
    raw_args
        .map(|ptr| {
            // SAFETY: Only pointers originating from CString::into_raw can be safely passed here
            OsString::from_vec(unsafe { CString::from_raw(ptr) }.into_bytes())
        })
        .collect()
}
