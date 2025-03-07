// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

macro_rules! help_opt {
    ($l: literal, $s: literal, $pad: literal, $msg: literal) => {{
        if cfg!(feature = "longopts") {
            concat!(" --", $l, ", ", $pad, "-", $s, ":   ", $msg)
        } else {
            concat!(" -", $s, ":   ", $msg)
        }
    }};
    ($l: literal, $s: literal, $a: literal, $spad: literal, $lpad: literal, $msg: literal) => {{
        if cfg!(feature = "longopts") {
            concat!(
                " --", $l, "=", $a, ", ", $lpad, "-", $s, " ", $spad, $a, ":   ", $msg
            )
        } else {
            concat!(" -", $s, " ", $spad, $a, ":   ", $msg)
        }
    }};
}

pub fn help_fmt(progname: &str) -> String {
    format!(
        include_str!("../text_assets/help_template.txt"),
        progname = progname,
        help = help_opt!("help", "h", "        ", "display this help text and exit"),
        version = help_opt!(
            "version",
            "V",
            "     ",
            "print version information and exit"
        ),
        json = help_opt!("json", "j", "        ", "print errors in JSON format*"),
        quiet = help_opt!("quiet", "q", "       ", "don't print any errors*"),
        optimize = help_opt!("optimize", "O", "    ", "enable optimization**"),
        cont = help_opt!(
            "continue",
            "c",
            "    ",
            "continue to the next file on failure"
        ),
        list_targets = help_opt!("list-targets", "A", "", "list supported targets and exit"),
        keep = help_opt!("keep-failed", "k", " ", "keep files that failed to compile"),
        tape_size = help_opt!(
            "tape-size",
            "t",
            "count",
            "",
            "     ",
            "use <count> 4-KiB blocks for the tape"
        ),
        extension = help_opt!(
            "source-extension",
            "e",
            "ext",
            "  ",
            "",
            "use 'ext' as the source extension"
        ),
        arch = help_opt!(
            "target-arch",
            "a",
            "arch",
            " ",
            "    ",
            "compile for the specified architecture"
        ),
        out_suffix = help_opt!(
            "output-suffix",
            "s",
            "suf",
            "  ",
            "   ",
            "append 'suf' to output file names"
        ),
        default_arch = env!("EAMBFC_DEFAULT_ARCH"),
    )
}
