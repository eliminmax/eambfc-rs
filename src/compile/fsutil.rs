// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

// if filename ends with extension, return Ok(f), where f is the filename without the extension
// otherwise, return Err(filename)
use crate::err::{BFCompileError, BFErrorID};
use std::ffi::{OsStr, OsString};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
pub(super) fn rm_ext(filename: &OsStr, extension: &OsStr) -> Result<OsString, BFCompileError> {
    let name_len: usize = filename.as_bytes().len();
    let ext_len: usize = extension.as_bytes().len();
    if filename.as_bytes().ends_with(extension.as_bytes()) {
        let mut noext = filename.to_os_string().into_vec();
        noext.truncate(name_len - ext_len);
        Ok(OsString::from_vec(noext))
    } else {
        // somehow doing this results in 100% code coverage, but having filename.to_string_lossy as
        // an argument to format doesn't. Can change if tarpaulin is fixed.
        let filename = filename.to_string_lossy();
        Err(BFCompileError::basic(
            BFErrorID::BadExtension,
            format!("{filename} does not end with expected extension"),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rmext_success() {
        assert_eq!(
            rm_ext("foobar".as_ref(), "bar".as_ref()),
            Ok(OsString::from("foo"))
        );
    }

    #[test]
    fn rmext_fail() {
        assert!(rm_ext("ee.e".as_ref(), ".bf".as_ref())
            .is_err_and(|e| e.kind == BFErrorID::BadExtension));
    }
}
