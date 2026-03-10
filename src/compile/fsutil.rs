// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use crate::err::{BFCompileError, BFErrorID};
use std::ffi::OsStr;
use std::path::{Path, PathBuf};

/// if `filename` ends with `extension`, return `Ok(f)`, where `f` is `filename` without
/// `extension` at the end.
/// otherwise, returns an `Err` with a `.error_id()` of `BFCompileError::BadExtension`.
///
/// On non-unix platforms, it returns an `Err` with a `.err_id()` of `BFCompileError::NonUTF8` if
/// either `filename` or `extension` are not valid Unicode
pub(super) fn set_extension(
    filename: &Path,
    source_extension: &OsStr,
    output_extension: Option<&OsStr>,
) -> Result<PathBuf, BFCompileError> {
    if filename.extension() == Some(source_extension) {
        Ok(filename.with_extension(output_extension.unwrap_or_default()))
    } else {
        Err(BFCompileError::basic(
            BFErrorID::BadSourceExtension,
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
    fn rmext_success() {
        assert_eq!(
            set_extension("foo.bar".as_ref(), "bar".as_ref(), None),
            Ok(PathBuf::from("foo"))
        );
        assert_eq!(
            set_extension("foo.bar".as_ref(), "bar".as_ref(), Some("_quux".as_ref())),
            Ok(PathBuf::from("foo._quux"))
        );
    }

    #[test]
    fn rmext_fail() {
        assert!(
            set_extension("ee.e".as_ref(), "bf".as_ref(), None)
                .is_err_and(|e| e.error_id() == BFErrorID::BadSourceExtension)
        );
    }
}
