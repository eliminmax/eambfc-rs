// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};
use std::ffi::OsStr;
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt;

/// if `filename` ends with `extension`, return `Ok(f)`, where `f` is `filename` without
/// `extension` at the end.
/// otherwise, returns an `Err` with a `.error_id()` of `BFCompileError::BadExtension`.
///
/// On non-unix platforms, it returns an `Err` with a `.err_id()` of `BFCompileError::NonUTF8` if
/// either `filename` or `extension` are not valid Unicode
pub(super) fn rm_ext<'a>(
    filename: &'a OsStr,
    extension: &OsStr,
) -> Result<&'a OsStr, BFCompileError> {
    #[cfg(unix)]
    {
        let name_len: usize = filename.as_bytes().len();
        let ext_len: usize = extension.as_bytes().len();
        if filename.as_bytes().ends_with(extension.as_bytes()) {
            Ok(OsStr::from_bytes(
                &filename.as_bytes()[..name_len - ext_len],
            ))
        } else {
            Err(BFCompileError::basic(
                BFErrorID::BadExtension,
                format!(
                    "{} does not end with expected extension",
                    filename.to_string_lossy()
                ),
            ))
        }
    }
    #[cfg(not(tarpaulin_include))]
    #[cfg(not(unix))]
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
        Ok(OsStr::new(filename.strip_suffix(extension).ok_or(
            BFCompileError::basic(
                BFErrorID::BadExtension,
                format!("{filename} does not end with expected extension"),
            ),
        )?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rmext_success() {
        assert_eq!(
            rm_ext("foobar".as_ref(), "bar".as_ref()),
            Ok("foo".as_ref())
        );
    }

    #[test]
    fn rmext_fail() {
        assert!(rm_ext("ee.e".as_ref(), ".bf".as_ref())
            .is_err_and(|e| e.error_id() == BFErrorID::BadExtension));
    }
}
