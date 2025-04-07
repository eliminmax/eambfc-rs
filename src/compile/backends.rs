// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[cfg(feature = "arm64")]
mod arm64;
#[cfg(feature = "arm64")]
pub(crate) use arm64::Arm64Inter;

#[cfg(feature = "riscv64")]
mod riscv64;
#[cfg(feature = "riscv64")]
pub(crate) use riscv64::RiscV64Inter;

#[cfg(feature = "s390x")]
mod s390x;
#[cfg(feature = "s390x")]
pub(crate) use s390x::S390xInter;

#[cfg(feature = "x86_64")]
mod x86_64;
#[cfg(feature = "x86_64")]
pub(crate) use x86_64::X86_64Inter;

use super::arch_inter;
use super::elf_tools;

#[allow(dead_code, reason = "Not used by all backends")]
trait MinimumBits {
    fn fits_within_bits(self, bits: u32) -> bool;
}

macro_rules! impl_min_bits {
    ([unsigned] $t: ty) => {
        impl MinimumBits for $t {
            fn fits_within_bits(self, bits: u32) -> bool {
                self < <$t>::pow(2, bits)
            }
        }
    };
    ([signed] $t: ty) => {
        impl MinimumBits for $t {
            fn fits_within_bits(self, bits: u32) -> bool {
                self >= -<$t>::pow(2, bits - 1) && self < <$t>::pow(2, bits - 1)
            }
        }
    };
}

impl_min_bits!([signed] i8);
impl_min_bits!([signed] i16);
impl_min_bits!([signed] i32);
impl_min_bits!([signed] i64);
impl_min_bits!([unsigned] u8);
impl_min_bits!([unsigned] u16);
impl_min_bits!([unsigned] u32);
impl_min_bits!([unsigned] u64);

#[cfg(test)]
mod test_min_bits {
    use super::MinimumBits;

    #[test]
    fn test_unsigned() {
        macro_rules! test_for {
            ($t: ty) => {
                for i in 1..(<$t>::BITS - 1) {
                    let tst_val = <$t>::pow(2, i);
                    assert!(tst_val.fits_within_bits(i + 1));
                    assert!(!tst_val.fits_within_bits(i));
                    assert!((tst_val - 1).fits_within_bits(i));
                }
            };
        }
        test_for!(u8);
        test_for!(u16);
        test_for!(u32);
        test_for!(u64);
    }

    #[test]
    fn test_signed() {
        macro_rules! test_for {
            ($t: ty) => {
                for i in 1..(<$t>::BITS - 2) {
                    let tst_val = <$t>::pow(2, i);
                    assert!(tst_val.fits_within_bits(i + 2));
                    assert!(!tst_val.fits_within_bits(i + 1));
                    assert!((-tst_val).fits_within_bits(i + 1));
                    assert!(!(-tst_val).fits_within_bits(i));
                    assert!((tst_val - 1).fits_within_bits(i + 1));
                }
            };
        }
        test_for!(i8);
        test_for!(i16);
        test_for!(i32);
        test_for!(i64);
    }
}
/// Provides a safe way to use LLVM's disassembler for backends to use for unit testing, using the
/// `Disassembler` struct.
#[cfg(not(tarpaulin_include))]
#[cfg(all(test, feature = "disasmtests"))]
mod test_utils {

    use super::elf_tools::{ElfArch, ElfClass};
    use llvm_sys::disassembler;
    use std::ffi::CStr;
    use std::sync::OnceLock;

    /// a dummy value to ensure that the LLVM Disassemblers are initialized
    static LLVM_TARGET_INIT: OnceLock<()> = OnceLock::new();

    /// cross the ffi boundary to call functions to set up the LLVM disassembler interface
    fn init_llvm() {
        use llvm_sys::target;
        // SAFETY: the `llvm_sys::target` functions are all opaque initialization functions that
        // are entirely on the LLVM side of the FFI boundary. They are
        LLVM_TARGET_INIT.get_or_init(|| unsafe {
            assert!(
                llvm_sys::core::LLVMIsMultithreaded() != 0,
                "LLVM must be build with multithreading"
            );
            target::LLVM_InitializeAllTargetInfos();
            target::LLVM_InitializeAllTargetMCs();
            target::LLVM_InitializeAllDisassemblers();
        });
    }

    /// return a tuple containing the LLVM target triple and the LLVM CPU id to target.
    ///
    /// # NOTE: to find list of supported features for a target, run the following command
    /// ```sh
    /// llc -march="$arch" -mattr=help
    /// ```
    fn target_info(arch: ElfArch) -> (&'static CStr, Option<&'static CStr>) {
        match arch {
            #[cfg(feature = "arm64")]
            // use a generic CPU for the arm64 and x86_64 backends.
            ElfArch::Arm64 => (c"aarch64-linux-gnu", None),
            #[cfg(feature = "x86_64")]
            ElfArch::X86_64 => (c"x86_64-linux-gnu", None),
            #[cfg(feature = "riscv64")]
            // for riscv64, use the `C` "(Compressed Instructions)" extension
            ElfArch::RiscV(ElfClass::ELFClass64) => (c"riscv64-linux-gnu", Some(c"+c")),
            // for s390x, use the `high-word` to have access to the high-word facility needed for
            // some instructions used for larger values
            #[cfg(feature = "s390x")]
            ElfArch::S390x => (c"systemz-linux-gnu", Some(c"+high-word")),
        }
    }

    /// A safe abstraction over `llvm_sys::disassembler::LLVMDisasmContextRef`
    pub struct Disassembler(disassembler::LLVMDisasmContextRef);

    impl Disassembler {
        /// Create a new Disassembler for the target architecture. The Disassembler is configured
        /// with `LLVMDisassembler_Option_PrintImmHex`, so immediates will typically be expressed in
        /// hexadecimal. If `target` is `ElfArch::X86_64`, then
        /// `LLVMDisassembler_Option_AsmPrinterVariant` will also be passed, to use Intel syntax
        /// for the disassembly.
        pub fn new(target: ElfArch) -> Self {
            init_llvm();
            let (triple, features) = target_info(target);
            // SAFETY: LLVMCreateDisasmCPU takes the target triple, cpu, disassembly info block, tag
            // type, and 2 optional callback functions. The disassembly info block and callback
            // functions are explicitly documented as being allowed to be null, and the tag type is
            // set to zero as it's not used. If the `LLVMCreateDisasmCPU` call returns a null
            // pointer, it's unsafe to proceed, but the assert ensures that it will crash instead.
            // The `LLVMSetDisasmOptions` function must take a valid `LLVMDisasmContextRef`, but
            // otherwise do not have any safety concerns.
            unsafe {
                let p = disassembler::LLVMCreateDisasmCPUFeatures(
                    triple.as_ptr(),
                    c"generic".as_ptr(),
                    features.map_or_else(core::ptr::null, CStr::as_ptr),
                    core::ptr::null_mut(),
                    0,
                    None,
                    None,
                );
                assert!(
                    !p.is_null(),
                    "Failed to create disassembler: LLVM returned null pointer"
                );
                // for x86_64, use Intel syntax.
                // If this were after the PrintImmHex call or bitmasked in with it, it would
                // override it, resulting in decimal immediates, so it needs to be a separate call.
                #[cfg(feature = "x86_64")]
                if target == ElfArch::X86_64 {
                    assert_eq!(
                        1,
                        disassembler::LLVMSetDisasmOptions(
                            p,
                            disassembler::LLVMDisassembler_Option_AsmPrinterVariant,
                        ),
                        "failed to switch to Intel syntax"
                    );
                }
                // use hex for immediates
                assert_eq!(
                    1,
                    disassembler::LLVMSetDisasmOptions(
                        p,
                        disassembler::LLVMDisassembler_Option_PrintImmHex,
                    ),
                    "failed to configure disassembler to use hex immediates"
                );
                Self(p)
            }
        }

        /// disassemble `bytes` into a Vec of assembly instructions. Panics if bytes can't be
        /// disassembled fully.
        pub fn disassemble(&mut self, mut bytes: Vec<u8>) -> Vec<String> {
            let mut disasm: Vec<String> = Vec::with_capacity(64);

            while !bytes.is_empty() {
                let mut output: [std::ffi::c_char; 128] = [0; 128];
                let old_len = bytes.len();
                let len = u64::try_from(old_len).expect("length must fit within 64 bits");
                // SAFETY: The final parameter ensures that will only write up to 128 bytes to
                // `output`.
                // The second parameter (`len`) is size of the input, and LLVM won't read more than
                // that internally.
                unsafe {
                    let disassembly_size = disassembler::LLVMDisasmInstruction(
                        self.0,
                        bytes.as_mut_ptr(),
                        len,
                        0,
                        output.as_mut_ptr(),
                        128,
                    );
                    // Drain the disassembled bytes from the byte vector - their value is no longer
                    // known, and they are no longer needed, so they should be dropped before
                    // anything else can happen.
                    bytes.drain(..disassembly_size);
                };

                assert_ne!(old_len, bytes.len(), "Failed to decompile {bytes:02x?}");

                disasm.push(
                    String::from_utf8(
                        output
                            .into_iter()
                            .filter(|&c| c != 0)
                            .map(|c| c as u8)
                            .collect(),
                    )
                    .unwrap()
                    .split('\t')
                    .filter(|snippet| !snippet.is_empty())
                    .collect::<Vec<_>>()
                    .join(" "),
                );
            }
            disasm
        }
    }

    impl Drop for Disassembler {
        fn drop(&mut self) {
            // SAFETY: this is the documented cleanup procedure for `LLVMDisasmContextRef`. It'll
            // only be called once, when `self` is dropped, so there's no risk of use-after-free
            unsafe {
                disassembler::LLVMDisasmDispose(self.0);
            }
        }
    }
}
