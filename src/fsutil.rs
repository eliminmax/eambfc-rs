// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

// if filename ends with extension, return Ok(f), where f is the filename without the extension
// otherwise, return Err(filename)
use super::err::{BFCompileError, BFErrorID};
use std::ffi::{OsStr, OsString};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
pub fn rm_ext(filename: &OsStr, extension: &OsStr) -> Result<OsString, BFCompileError> {
    let name_len: usize = filename.as_bytes().len();
    let ext_len: usize = extension.as_bytes().len();
    if filename
        .to_os_string()
        .into_vec()
        .ends_with(extension.as_bytes())
    {
        let mut noext = filename.to_os_string().into_vec();
        noext.truncate(name_len - ext_len);
        Ok(OsString::from_vec(noext))
    } else {
        Err(BFCompileError::basic(
            BFErrorID::BAD_EXTENSION,
            format!(
                "{} does not end with expected extension",
                filename.to_string_lossy()
            ),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rmext_success_ascii() {
        assert_eq!(
            rm_ext(OsStr::from_bytes(b"foobar"), OsStr::from_bytes(b"bar")),
            Ok(OsString::from("foo"))
        );
    }

    #[test]
    fn rmext_success_non_ascii() {
        assert_eq!(
            rm_ext(OsStr::from_bytes(b"\xee.e"), OsStr::from_bytes(b".e")),
            Ok(OsString::from_vec(vec![0xee]))
        );
    }

    #[test]
    fn rmext_fail_non_ascii() {
        assert!(
            rm_ext(OsStr::from_bytes(b"\xee.e"), OsStr::from_bytes(b".bf"))
                .is_err_and(|e| e.kind == BFErrorID::BAD_EXTENSION)
        );
    }
}
