// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};
use std::borrow::Cow;
use std::ffi::OsStr;
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt;
#[cfg(target_os = "wasi")]
use std::os::wasi::ffi::OsStrExt;

/// if `filename` ends with `extension`, return `Ok(f)`, where `f` is `filename` without
/// `extension` at the end.
/// otherwise, returns an `Err` with a `.error_id()` of `BFCompileError::BadExtension`.
///
/// On non-unix platforms, it returns an `Err` with a `.err_id()` of `BFCompileError::NonUTF8` if
/// either `filename` or `extension` are not valid Unicode
pub(super) fn rm_ext<'a>(
    filename: &'a OsStr,
    extension: &OsStr,
    suffix: Option<&OsStr>,
) -> Result<Cow<'a, OsStr>, BFCompileError> {
    let outname: &'a OsStr;
    #[cfg(any(unix, target_os = "wasi"))]
    {
        let name_len: usize = filename.as_bytes().len();
        let ext_len: usize = extension.as_bytes().len();
        if filename.as_bytes().ends_with(extension.as_bytes()) {
            outname = OsStr::from_bytes(&filename.as_bytes()[..name_len - ext_len]);
        } else {
            return Err(BFCompileError::basic(
                BFErrorID::BadExtension,
                format!(
                    "{} does not end with expected extension",
                    filename.to_string_lossy()
                ),
            ));
        }
    }

    #[cfg(not(tarpaulin_include))]
    #[cfg(not(any(unix, target_os = "wasi")))]
    {
        const SUPPORT_MSG: &str = " - non-Unicode filenames are only supported on Unix targets";
        let filename = filename.to_str().ok_or(BFCompileError::basic(
            BFErrorID::NonUTF8,
            format!(
                "filename {} is not valid Unicode{SUPPORT_MSG}",
                filename.to_string_lossy()
            ),
        ))?;
        let extension = extension
            .to_str()
            .unwrap_or_else(|| unreachable!("extension validated when parsing args"));
        outname = OsStr::new(
            filename
                .strip_suffix(extension)
                .ok_or(BFCompileError::basic(
                    BFErrorID::BadExtension,
                    format!("{filename} does not end with expected extension"),
                ))?,
        );
    };
    if let Some(suf) = suffix {
        let mut outname = outname.to_os_string();
        outname.push(suf);
        Ok(outname.into())
    } else {
        Ok(outname.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rmext_success() {
        assert_eq!(
            rm_ext("foobar".as_ref(), "bar".as_ref(), None),
            Ok(OsStr::new("foo").into())
        );
        assert_eq!(
            rm_ext("foobar".as_ref(), "bar".as_ref(), Some("_quux".as_ref())),
            Ok(OsStr::new("foo_quux").into())
        );
    }

    #[test]
    fn rmext_fail() {
        assert!(rm_ext("ee.e".as_ref(), ".bf".as_ref(), None)
            .is_err_and(|e| e.error_id() == BFErrorID::BadExtension));
    }
}
