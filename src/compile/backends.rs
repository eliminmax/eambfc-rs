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
fn disassemble(code: &[u8], engine: &capstone::Capstone) -> Vec<String> {
    let disassembled = engine.disasm_all(code, 0).expect("Failed to disassemble");
    disassembled
        .iter()
        .map(|insn| {
            let mut ret = insn.mnemonic().unwrap().to_string();
            let op_str = insn.op_str().unwrap();
            if !op_str.is_empty() {
                ret.push(' ');
                ret.push_str(op_str);
            }
            ret
        })
        .collect()
}

#[cfg(not(tarpaulin_include))]
#[cfg(test)]
mod test_utils {

    use super::elf_tools::ElfArch;
    use llvm_sys::disassembler;
    use std::ffi::CStr;
    use std::sync::OnceLock;

    static LLVM_TARGET_INIT: OnceLock<()> = OnceLock::new();

    fn init_llvm() {
        use llvm_sys::target;
        LLVM_TARGET_INIT.get_or_init(|| unsafe {
            target::LLVM_InitializeAllAsmPrinters();
            target::LLVM_InitializeAllTargets();
            target::LLVM_InitializeAllTargetInfos();
            target::LLVM_InitializeAllTargetMCs();
            target::LLVM_InitializeAllDisassemblers();
        });
    }

    impl ElfArch {
        fn triple(&self) -> &'static CStr {
            match self {
                #[cfg(feature = "arm64")]
                ElfArch::Arm64 => c"aarch64-unknown-linux-gnu",
                #[cfg(feature = "s390x")]
                ElfArch::S390x => c"systemz-unknown-linux-gnu",
                #[cfg(feature = "x86_64")]
                ElfArch::X86_64 => c"x86_64-unknown-linux-gnu",
            }
        }

        pub(super) fn disassemble(&self, bytes: &[u8]) -> Vec<String> {
            Disassembler::new(*self).disassemble(bytes.to_vec())
        }
    }

    /// A safe abstraction over llvm_sys::disassembler::LLVMDisasmContextRef
    #[derive(Debug)]
    pub struct Disassembler(disassembler::LLVMDisasmContextRef);

    impl Disassembler {
        /// Create a new Disassembler for the target architecture
        pub fn new(isa: ElfArch) -> Self {
            init_llvm();
            unsafe {
                let p = disassembler::LLVMCreateDisasm(
                    isa.triple().as_ptr(),
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
                if old_len == bytes.len() {
                    panic!("Failed to decompile {:#x?}", bytes);
                }

                disasm.push(
                    String::from_utf8(
                        output
                            .into_iter()
                            .filter_map(|c| if c != 0 { Some(c as u8) } else { None })
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
