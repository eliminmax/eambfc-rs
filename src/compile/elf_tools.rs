// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

pub(super) enum ElfClass {
    ELFClass64 = 2,
}

#[derive(Clone, Copy)]
pub(super) enum ByteOrdering {
    #[cfg(any(feature = "x86_64", feature = "riscv64", feature = "arm64"))]
    LittleEndian = 1,
    #[cfg(feature = "s390x")]
    BigEndian = 2,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum ElfArch {
    #[cfg(feature = "arm64")]
    Arm64 = 183, // EM_AARCH64
    #[cfg(feature = "riscv64")]
    RiscV64 = 243, // EM_RISCV
    #[cfg(feature = "s390x")]
    S390x = 22, // EM_S390
    #[cfg(feature = "x86_64")]
    X86_64 = 62, // EM_X86_64 (i.e. amd64)
}

impl std::fmt::Display for ElfArch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match *self {
                #[cfg(feature = "arm64")]
                ElfArch::Arm64 => "arm64",
                #[cfg(feature = "riscv64")]
                ElfArch::RiscV64 => "riscv64",
                #[cfg(feature = "s390x")]
                ElfArch::S390x => "s390x",
                #[cfg(feature = "x86_64")]
                ElfArch::X86_64 => "x86_64",
            }
        )
    }
}

impl Default for ElfArch {
    fn default() -> Self {
        match env!("EAMBFC_DEFAULT_ARCH") {
            #[cfg(feature = "arm64")]
            "arm64" => ElfArch::Arm64,
            #[cfg(feature = "riscv64")]
            "riscv64" => ElfArch::RiscV64,
            #[cfg(feature = "s390x")]
            "s390x" => ElfArch::S390x,
            #[cfg(feature = "x86_64")]
            "x86_64" => ElfArch::X86_64,
            _ => unreachable!("build.rs sets this to valid values only"),
        }
    }
}

pub(super) enum ElfVersion {
    EvCurrent = 1,
}

pub(super) enum ElfOsAbi {
    None,
}

pub(super) enum ElfType {
    Exec = 2,
}

pub(super) struct EIdent {
    pub class: ElfClass,
    pub data: ByteOrdering,
    pub osabi: ElfOsAbi,
}

impl From<EIdent> for [u8; 16] {
    fn from(e_ident: EIdent) -> [u8; 16] {
        let (osabi, abi_version) = match e_ident.osabi {
            ElfOsAbi::None => (0, 0),
        };
        #[rustfmt::skip]
        let arr: [u8; 16] = [
            // magic numbers
            0x7f, b'E', b'L', b'F',
            // 32 or 64 bit
            e_ident.class as u8,
            // byte ordering
            e_ident.data as u8,
            // Version of an ELF file - only valid value
            ElfVersion::EvCurrent as u8,
            // ABI and ABI version
            osabi, abi_version,
            // padding bytes
            0, 0, 0, 0, 0, 0, 0
        ];
        arr
    }
}

pub(super) struct Ehdr {
    pub ident: EIdent,
    pub elf_type: ElfType,
    pub machine: ElfArch,
    pub version: ElfVersion,
    pub entry: u64,
    pub phoff: u64,
    pub shoff: u64,
    pub flags: u32,
    pub ehsize: u16,
    pub phentsize: u16,
    pub phnum: u16,
    pub shentsize: u16,
    pub shnum: u16,
    pub shstrndx: u16,
}

pub(super) enum PType {
    Load = 1,
}

pub(super) struct Phdr {
    pub byte_order: ByteOrdering,
    pub header_type: PType,
    pub flags: u32,
    pub offset: u64,
    pub vaddr: u64,
    pub paddr: u64,
    pub filesz: u64,
    pub memsz: u64,
    pub align: u64,
}

pub(super) const EHDR_SIZE: u16 = 64;
pub(super) const PHDR_SIZE: u16 = 56;
// better this than having identical implementations, differing only in whether to_le_bytes or
// to_be_bytes are called.
macro_rules! serialize_ehdr {
    ($item:ident, $func:ident) => {{
        let mut v = Vec::with_capacity(usize::from(EHDR_SIZE));
        v.extend(<[u8; 16]>::from($item.ident));
        v.extend(($item.elf_type as u16).$func());
        v.extend(($item.machine as u16).$func());
        v.extend(($item.version as u32).$func());
        v.extend($item.entry.$func());
        v.extend($item.phoff.$func());
        v.extend($item.shoff.$func());
        v.extend($item.flags.$func());
        v.extend($item.ehsize.$func());
        v.extend($item.phentsize.$func());
        v.extend($item.phnum.$func());
        v.extend($item.shentsize.$func());
        v.extend($item.shnum.$func());
        v.extend($item.shstrndx.$func());
        v
    }};
}

macro_rules! serialize_phdr {
    ($item:ident, $func:ident) => {{
        let mut v = Vec::with_capacity(usize::from(PHDR_SIZE));
        v.extend(($item.header_type as u32).$func());
        v.extend($item.flags.$func());
        v.extend($item.offset.$func());
        v.extend($item.vaddr.$func());
        v.extend($item.paddr.$func());
        v.extend($item.filesz.$func());
        v.extend($item.memsz.$func());
        v.extend($item.align.$func());
        v
    }};
}

impl From<Ehdr> for Vec<u8> {
    fn from(item: Ehdr) -> Self {
        match item.ident.data {
            #[cfg(any(feature = "arm64", feature = "riscv64", feature = "x86_64"))]
            ByteOrdering::LittleEndian => serialize_ehdr!(item, to_le_bytes),
            #[cfg(feature = "s390x")]
            ByteOrdering::BigEndian => serialize_ehdr!(item, to_be_bytes),
        }
    }
}

// as endian-ness is not communicated in Phdr entries, it's added to the Phdr struct used within
// eambfc-rs for this.
impl From<Phdr> for Vec<u8> {
    fn from(item: Phdr) -> Self {
        match item.byte_order {
            #[cfg(any(feature = "arm64", feature = "riscv64", feature = "x86_64"))]
            ByteOrdering::LittleEndian => serialize_phdr!(item, to_le_bytes),
            #[cfg(feature = "s390x")]
            ByteOrdering::BigEndian => serialize_phdr!(item, to_be_bytes),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ElfArch;
    #[test]
    fn display_elfarch() {
        #[cfg(feature = "arm64")]
        assert_eq!(format!("{}", ElfArch::Arm64), String::from("arm64"));
        #[cfg(feature = "riscv64")]
        assert_eq!(format!("{}", ElfArch::RiscV64), String::from("riscv64"));
        #[cfg(feature = "s390x")]
        assert_eq!(format!("{}", ElfArch::S390x), String::from("s390x"));
        #[cfg(feature = "x86_64")]
        assert_eq!(format!("{}", ElfArch::X86_64), String::from("x86_64"));
    }
}
