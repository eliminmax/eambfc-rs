// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

#[cfg(any(feature = "i386", feature = "x86_64"))]
mod x86_common;

/// `use_backend!($module, $feature, $inter)`: Export `$module::$inter` at a crate level if
/// `$feature` is enabled
macro_rules! use_backend {
    ($module: ident, $feature: literal, $inter: ident) => {
        #[cfg(feature = $feature)]
        mod $module;
        #[cfg(feature = $feature)]
        pub(crate) use $module::$inter;
    };
}

use_backend!(arm64, "arm64", Arm64Inter);
use_backend!(i386, "i386", I386Inter);
use_backend!(riscv64, "riscv64", RiscV64Inter);
use_backend!(s390x, "s390x", S390xInter);
use_backend!(x86_64, "x86_64", X86_64Inter);

/// Enum of supported backends
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Backend {
    #[cfg(feature = "arm64")]
    Arm64,
    #[cfg(feature = "i386")]
    I386,
    #[cfg(feature = "riscv64")]
    RiscV64,
    #[cfg(feature = "s390x")]
    S390x,
    #[cfg(feature = "x86_64")]
    X86_64,
}

#[cfg(not(have_all_targets))]
/// Enum of disabled backends
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum DisabledBackend {
    #[cfg(not(feature = "arm64"))]
    Arm64,
    #[cfg(not(feature = "i386"))]
    I386,
    #[cfg(not(feature = "riscv64"))]
    RiscV64,
    #[cfg(not(feature = "s390x"))]
    S390x,
    #[cfg(not(feature = "x86_64"))]
    X86_64,
}

#[cfg(not(have_all_targets))]
impl std::fmt::Display for DisabledBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self {
                #[cfg(not(feature = "arm64"))]
                DisabledBackend::Arm64 => "arm64",
                #[cfg(not(feature = "i386"))]
                DisabledBackend::I386 => "i386",
                #[cfg(not(feature = "riscv64"))]
                DisabledBackend::RiscV64 => "riscv64",
                #[cfg(not(feature = "s390x"))]
                DisabledBackend::S390x => "s390x",
                #[cfg(not(feature = "x86_64"))]
                DisabledBackend::X86_64 => "x86_64",
            }
        )
    }
}

impl std::fmt::Display for Backend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self {
                #[cfg(feature = "arm64")]
                Backend::Arm64 => "arm64",
                #[cfg(feature = "i386")]
                Backend::I386 => "i386",
                #[cfg(feature = "riscv64")]
                Backend::RiscV64 => "riscv64",
                #[cfg(feature = "s390x")]
                Backend::S390x => "s390x",
                #[cfg(feature = "x86_64")]
                Backend::X86_64 => "x86_64",
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum BackendParseErr {
    #[cfg(not(have_all_targets))]
    DisabledBackend(DisabledBackend),
    UnknownBackend,
}

impl std::str::FromStr for Backend {
    type Err = BackendParseErr;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        macro_rules! select_if_enabled {
            ($feature: literal, $backend: ident) => {{
                #[cfg(feature = $feature)]
                {
                    Ok(Backend::$backend)
                }
                #[cfg(not(feature = $feature))]
                {
                    Err(BackendParseErr(DisabledBackend::$backend))
                }
            }};
        }
        match s {
            "arm64" | "aarch64" => select_if_enabled!("arm64", Arm64),
            "i386" | "i486" | "i586" | "i686" | "x86" => select_if_enabled!("i386", I386),
            "riscv64" | "riscv" => select_if_enabled!("riscv64", RiscV64),
            "s390x" | "s390" | "z/architecture" => select_if_enabled!("s390x", S390x),
            "x86_64" | "x64" | "amd64" | "x86-64" => select_if_enabled!("x86_64", X86_64),
            _ => Err(BackendParseErr::UnknownBackend),
        }
    }
}

impl Default for Backend {
    fn default() -> Self {
        env!("EAMBFC_DEFAULT_ARCH")
            .parse()
            .expect("build.rs validates default arch")
    }
}

use super::arch_inter;

mod backend_utils;

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum ElfClass {
    #[cfg(have_32bit_targets)]
    ELFClass32 = 1,
    #[cfg(have_64bit_targets)]
    ELFClass64 = 2,
}

impl ElfClass {
    const fn ehdr_sz(self) -> u16 {
        match self {
            #[cfg(have_32bit_targets)]
            ElfClass::ELFClass32 => 52,
            #[cfg(have_64bit_targets)]
            ElfClass::ELFClass64 => 64,
        }
    }
    const fn phdr_sz(self) -> u16 {
        match self {
            #[cfg(have_32bit_targets)]
            ElfClass::ELFClass32 => 32,
            #[cfg(have_64bit_targets)]
            ElfClass::ELFClass64 => 56,
        }
    }
    pub(crate) const fn bits(self) -> u8 {
        match self {
            #[cfg(have_32bit_targets)]
            ElfClass::ELFClass32 => 32,
            #[cfg(have_64bit_targets)]
            ElfClass::ELFClass64 => 64,
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum ByteOrdering {
    #[cfg(have_le_targets)]
    LittleEndian = 1,
    #[cfg(have_be_targets)]
    BigEndian = 2,
}

impl Backend {
    /// Get the `e_machine` value for the architecture
    const fn e_machine(self) -> u16 {
        match self {
            #[cfg(feature = "arm64")]
            Self::Arm64 => 183,
            #[cfg(feature = "i386")]
            Self::I386 => 3,
            #[cfg(feature = "riscv64")]
            Self::RiscV64 => 243,
            #[cfg(feature = "s390x")]
            Self::S390x => 22,
            #[cfg(feature = "x86_64")]
            Self::X86_64 => 62,
        }
    }
    /// Get the `e_ident[EI_CLASS]` value for the architecture, as an `ElfClass`
    pub(crate) const fn ei_class(self) -> ElfClass {
        match self {
            #[cfg(feature = "arm64")]
            Self::Arm64 => ElfClass::ELFClass64,
            #[cfg(feature = "i386")]
            Self::I386 => ElfClass::ELFClass32,
            #[cfg(feature = "riscv64")]
            Self::RiscV64 => ElfClass::ELFClass64,
            #[cfg(feature = "s390x")]
            Self::S390x => ElfClass::ELFClass64,
            #[cfg(feature = "x86_64")]
            Self::X86_64 => ElfClass::ELFClass64,
        }
    }

    /// Get the `e_ident[EI_DATA]` for the architecture, as a `ByteOrdering`
    pub(super) const fn ei_data(self) -> ByteOrdering {
        match self {
            #[cfg(feature = "s390x")]
            Self::S390x => ByteOrdering::BigEndian,
            #[cfg(have_le_targets)]
            _ => ByteOrdering::LittleEndian,
        }
    }
}

impl From<Backend> for [u8; 16] {
    fn from(e_arch: Backend) -> [u8; 16] {
        #[rustfmt::skip]
        let arr: [u8; 16] = [
            // magic bytes
            0x7f, b'E', b'L', b'F',
            // 32 or 64 bit
            e_arch.ei_class() as u8,
            // byte ordering for architecture
            e_arch.ei_data() as u8,
            // Version of an ELF file - only valid value
            1,
            // SYSV ABI with unspecified version
            0, 0,
            // padding bytes
            0, 0, 0, 0, 0, 0, 0
        ];
        arr
    }
}

/// The information needed to construct an ELF Ehdr, not including information which is always the
/// same across all ELF executables generated by eambfc-rs
pub(super) struct BinInfo {
    /// The target backend - used to determine the pointer size, byte ordering, and `e_machine`
    /// value for the Ehdr
    pub arch: Backend,
    /// The program entry point
    pub entry: u64,
    /// The backend-specific Ehdr flags
    pub flags: u32,
}

/// The information needed to construct and ELF Phdr entry, not including information which is
/// always the same across both of the segments used across all ELF executables generated by
/// eambfc-rs
pub(super) struct SegmentInfo {
    /// Used to determine byte ordering and register size
    pub arch: Backend,
    /// Segment `p_flags` value
    pub flags: u32,
    /// Segment `p_vaddr` value
    pub vaddr: u64,
    /// Segment `p_memsz` value
    pub size: u64,
    /// If true, use `size` as the `p_filesz` value. Otherwise, use `0` as the `p_filesz` value.
    pub file_backed: bool,
    /// Segment `p_align` value
    pub align: u32,
}

/// Pass a `BinInfo` binding, followed by `LE` or `BE` for little-endian or big-endian backends
/// respectively, then `32` for 32-bit or `64` for 64-bit backends respectively.
///
/// It will use the appropriate struct member sizes and write the bytes for the appropriate byte
/// ordering for the given register size and byte ordering combo.
///
/// # Example
///
/// ```no_run
/// let item: BinInfo = { ... };
/// serialize_ehdr!(item, LE, 64)
/// ```
// While ugly, it gets the job done without repeating code for different backend register sizes or
// byte orderings.
macro_rules! serialize_ehdr {
    // Variants meant for actual use
    ($item: ident, LE, 64) => {{ serialize_ehdr!(<internal> $item, to_le_bytes, u64) }};
    ($item: ident, BE, 64) => {{ serialize_ehdr!(<internal> $item, to_be_bytes, u64) }};
    ($item: ident, LE, 32) => {{ serialize_ehdr!(<internal> $item, to_le_bytes, u32) }};
    ($item: ident, BE, 32) => {{ serialize_ehdr!(<internal> $item, to_be_bytes, u32) }};
    // Internal implementation of the serialization
    (<internal> $item: ident, $func: ident, $addr_type: ty) => {{
        let mut v = Vec::with_capacity($item.arch.ei_class().ehdr_sz().into());
        v.extend(<[u8; 16]>::from($item.arch));
        // e_type = ET_EXEC
        v.extend(u16::$func(2));
        // e_machine (provided by `$item`)
        v.extend($item.arch.e_machine().$func());
        // e_version = 1
        v.extend(u32::$func(1));
        // e_entry (provided by `$item`)
        v.extend(
            <$addr_type>::try_from($item.entry)
                .expect("Validated tape size")
                .$func(),
        );
        // e_phoff is always equal to e_ehsize, which depends on the architecture class
        v.extend(<$addr_type>::from($item.arch.ei_class().ehdr_sz()).$func());
        // e_shoff is always zero
        v.extend(<$addr_type>::$func(0));
        // e_flags (provided by `$item`)
        v.extend($item.flags.$func());
        // e_ehsize depends on the architecture class
        v.extend($item.arch.ei_class().ehdr_sz().$func());
        // e_phentsize depends on the architecture class
        v.extend($item.arch.ei_class().phdr_sz().$func());
        // e_phnum is always 2: 1 for the code segment and 1 for the tape segment
        v.extend(u16::$func(2));
        // e_shentsize is zero as there is no section header table
        v.extend(u16::$func(0));
        // e_shnum is zero as there is no section header table
        v.extend(u16::$func(0));
        // e_shstrndx is zero as there is no section header table
        v.extend(u16::$func(0));
        v
    }};
}

/// pass a `Phdr` binding, followed by `LE` or `BE` for little or big-endian backends respectively,
/// followed by `64` or `32` for 64-bit or 32-bit backends respectively.
///
/// It will use the appropriate struct member sizes and order for the provided size, and write the
/// bytes of the members in the provided byte ordering
macro_rules! serialize_phdr {
    // Variants meant for actual use
    ($item: ident, LE, $sz: tt) => {{ serialize_phdr!(<internal> $item, to_le_bytes, $sz) }};
    ($item: ident, BE, $sz: tt) => {{ serialize_phdr!(<internal> $item, to_be_bytes, $sz) }};

    // Items in 64-bit order
    (<internal> $item:ident, $func:ident, 64) => {{
        let mut v = Vec::with_capacity(56);
        // p_type is always `PT_LOAD`
        v.extend(u32::$func(1));
        // p_flags (provided by `$item`)
        v.extend($item.flags.$func());
        // p_offset is 0 either because there's no backing data in file or it's the whole file
        v.extend(u64::$func(0));
        // p_vaddr (provided by `$item`)
        v.extend($item.vaddr.$func());
        // p_paddr is always zero
        v.extend(u64::$func(0));
        // p_filesz
        v.extend(if $item.file_backed { $item.size } else { 0 }.$func());
        // p_memsz (provided by `$item`)
        v.extend($item.size.$func());
        // p_align (provided by `$item`) (need to extend to 64 bits)
        v.extend(u64::from($item.align).$func());
        v
    }};

    (<internal> $item:ident, $func:ident, 32) => {{
        let mut v = Vec::with_capacity(32);
        // p_type is always `PT_LOAD`
        v.extend(u32::$func(1));
        // p_offset is 0 either because there's no backing data in file or it's the whole file
        v.extend(u32::$func(0));
        // p_vaddr (provided by `$item`)
        v.extend(u32::try_from($item.vaddr).expect("Validated vaddr").$func());
        // p_paddr is always zero
        v.extend(u32::$func(0));
        let size: u32 = $item.size.try_into().expect("validated size");
        // p_filesz
        v.extend(if $item.file_backed { size } else { 0 }.$func());
        // p_memsz (provided by `$item`)
        v.extend(size.$func());
        // p_flags (provided by `$item`)
        v.extend($item.flags.$func());
        // p_align (provided by `$item`)
        v.extend($item.align.$func());
        v
    }};
}

impl From<BinInfo> for Vec<u8> {
    fn from(item: BinInfo) -> Self {
        match (item.arch.ei_class(), item.arch.ei_data()) {
            #[cfg(all(have_64bit_targets, have_le_targets))]
            (ElfClass::ELFClass64, ByteOrdering::LittleEndian) => serialize_ehdr!(item, LE, 64),
            #[cfg(all(have_32bit_targets, have_le_targets))]
            (ElfClass::ELFClass32, ByteOrdering::LittleEndian) => serialize_ehdr!(item, LE, 32),
            #[cfg(all(have_64bit_targets, have_be_targets))]
            (ElfClass::ELFClass64, ByteOrdering::BigEndian) => serialize_ehdr!(item, BE, 64),
            #[cfg(all(have_32bit_targets, have_be_targets))]
            (ElfClass::ELFClass32, ByteOrdering::BigEndian) => serialize_ehdr!(item, BE, 64),
        }
    }
}

// as endian-ness is not communicated in Phdr entries, it's added to the Phdr struct used within
// eambfc-rs for this.
impl From<SegmentInfo> for Vec<u8> {
    fn from(item: SegmentInfo) -> Self {
        match (item.arch.ei_class(), item.arch.ei_data()) {
            #[cfg(all(have_64bit_targets, have_le_targets))]
            (ElfClass::ELFClass64, ByteOrdering::LittleEndian) => serialize_phdr!(item, LE, 64),
            #[cfg(all(have_32bit_targets, have_le_targets))]
            (ElfClass::ELFClass32, ByteOrdering::LittleEndian) => serialize_phdr!(item, LE, 32),
            #[cfg(all(have_64bit_targets, have_be_targets))]
            (ElfClass::ELFClass64, ByteOrdering::BigEndian) => serialize_phdr!(item, BE, 64),
            #[cfg(all(have_32bit_targets, have_be_targets))]
            (ElfClass::ELFClass32, ByteOrdering::BigEndian) => serialize_phdr!(item, BE, 64),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Backend;
    #[test]
    fn display_elfarch() {
        #[cfg(feature = "arm64")]
        assert_eq!(format!("{}", Backend::Arm64), String::from("arm64"));
        #[cfg(feature = "i386")]
        assert_eq!(format!("{}", Backend::I386), String::from("i386"));
        #[cfg(feature = "riscv64")]
        assert_eq!(format!("{}", Backend::RiscV64), String::from("riscv64"));
        #[cfg(feature = "s390x")]
        assert_eq!(format!("{}", Backend::S390x), String::from("s390x"));
        #[cfg(feature = "x86_64")]
        assert_eq!(format!("{}", Backend::X86_64), String::from("x86_64"));
    }
}

/// Provides a safe way to use LLVM's disassembler for backends to use for unit testing, using the
/// `Disassembler` struct.
#[cfg(not(tarpaulin_include))]
#[cfg(all(test, not(cross_compiled), feature = "disasmtests"))]
mod test_utils {

    use super::Backend;
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
    fn target_info(arch: Backend) -> (&'static CStr, Option<&'static CStr>) {
        match arch {
            #[cfg(feature = "arm64")]
            // use a generic CPU for the arm64 and x86_64 backends.
            Backend::Arm64 => (c"aarch64-linux-gnu", None),
            #[cfg(feature = "x86_64")]
            Backend::X86_64 => (c"x86_64-linux-gnu", None),
            #[cfg(feature = "i386")]
            Backend::I386 => (c"i386-linux-gnu", None),
            #[cfg(feature = "riscv64")]
            // for riscv64, use the `C` "(Compressed Instructions)" extension
            Backend::RiscV64 => (c"riscv64-linux-gnu", Some(c"+c")),
            // for s390x, use the `high-word` to have access to the high-word facility needed for
            // some instructions used for larger values
            #[cfg(feature = "s390x")]
            Backend::S390x => (c"systemz-linux-gnu", Some(c"+high-word")),
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
        pub fn new(target: Backend) -> Self {
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
                // for x86 backends, use Intel syntax.
                // If this were after the PrintImmHex call or bitmasked in with it, it would
                // override it, resulting in decimal immediates, so it needs to be a separate call.
                #[cfg(feature = "i386")]
                if target == Backend::I386 {
                    assert_eq!(
                        1,
                        disassembler::LLVMSetDisasmOptions(
                            p,
                            disassembler::LLVMDisassembler_Option_AsmPrinterVariant,
                        ),
                        "failed to switch to Intel syntax"
                    );
                }
                #[cfg(feature = "x86_64")]
                if target == Backend::X86_64 {
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
                            .map(i8::cast_unsigned)
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
