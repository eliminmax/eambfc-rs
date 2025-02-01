// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[cfg(feature = "arm64")]
mod arm64;
#[cfg(feature = "arm64")]
pub(crate) use arm64::Arm64Inter;

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

#[cfg(not(tarpaulin_include))]
#[cfg(test)]
mod test_utils {

    use super::elf_tools::ElfArch;
    use llvm_sys::disassembler;
    use std::ffi::CStr;
    use std::sync::OnceLock;

    /// a dummy value to ensure that the LLVM Disassembler functions are
    static LLVM_TARGET_INIT: OnceLock<()> = OnceLock::new();

    /// cross the ffi boundry to call functions to set up the LLVM disassembler interface
    fn init_llvm() {
        use llvm_sys::target;
        // SAFETY: the `llvm_sys::target` functions are all opaque initialization functions that
        // are entirely on the LLVM side of the FFI boundry. They are
        LLVM_TARGET_INIT.get_or_init(|| unsafe {
            target::LLVM_InitializeAllTargetInfos();
            target::LLVM_InitializeAllTargetMCs();
            target::LLVM_InitializeAllDisassemblers();
        });
    }

    /// return a tuple containing the LLVM target triple and the LLVM CPU id to target.
    fn target_info(arch: ElfArch) -> (&'static CStr, &'static CStr) {
        match arch {
            #[cfg(feature = "arm64")]
            // use a generic CPU for the arm64 and x86_64 backends.
            ElfArch::Arm64 => (c"aarch64-linux-gnu", c"generic"),
            #[cfg(feature = "x86_64")]
            ElfArch::X86_64 => (c"x86_64-linux-gnu", c"x86-64"),
            // for s390x, use the z196 CPU to have access to the high-word facility needed for some
            // instructions used for larger values
            #[cfg(feature = "s390x")]
            ElfArch::S390x => (c"systemz-linux-gnu", c"z196"),
        }
    }

    /// A safe abstraction over `llvm_sys::disassembler::LLVMDisasmContextRef`
    pub struct Disassembler(disassembler::LLVMDisasmContextRef);

    impl Disassembler {
        /// Create a new Disassembler for the target architecture
        pub fn new(isa: ElfArch) -> Self {
            init_llvm();
            let (triple, cpu) = target_info(isa);
            unsafe {
                let p = disassembler::LLVMCreateDisasmCPU(
                    triple.as_ptr(),
                    cpu.as_ptr(),
                    core::ptr::null_mut(),
                    0,
                    None,
                    None,
                );
                assert!(!p.is_null());
                // for x86_64, use Intel syntax.
                // If this were after the PrintImmHex call or bitmasked in with it, it would
                // override it, resulting in decimal immediates, so it needs to be a separate call.
                #[cfg(feature = "x86_64")]
                if isa == ElfArch::X86_64 {
                    disassembler::LLVMSetDisasmOptions(
                        p,
                        disassembler::LLVMDisassembler_Option_AsmPrinterVariant,
                    );
                }
                // use hex for immediates
                disassembler::LLVMSetDisasmOptions(
                    p,
                    disassembler::LLVMDisassembler_Option_PrintImmHex,
                );
                Self(p)
            }
        }

        pub fn disassemble(&mut self, mut bytes: Vec<u8>) -> Vec<String> {
            let mut disasm: Vec<String> = Vec::with_capacity(64);

            while !bytes.is_empty() {
                let mut output: [std::ffi::c_char; 128] = [0; 128];
                let old_len = bytes.len();
                let len = u64::try_from(old_len).unwrap();
                let disassembly_size = unsafe {
                    disassembler::LLVMDisasmInstruction(
                        self.0,
                        bytes.as_mut_ptr(),
                        len,
                        0,
                        output.as_mut_ptr(),
                        128,
                    )
                };

                bytes.drain(..disassembly_size);
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
            unsafe {
                disassembler::LLVMDisasmDispose(self.0);
            }
        }
    }
}
