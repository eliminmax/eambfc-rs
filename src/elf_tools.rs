// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

pub trait SerializePhdr {
    fn serialize(&self) -> &[u8];
}

#[derive(Debug)]
pub enum EIClass {
    ELFClass64 = 2,
}

#[derive(Debug, Copy, Clone)]
pub enum EIData {
    ELFDATA2LSB = 1, // 2's complement, little endian
    ELFDATA2MSB = 2, // 2's complement, big endian
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ELFArch {
    Arm64 = 183, // EM_AARCH64
    S390x = 22,  // EM_S390
    X86_64 = 62, // EM_X86_64 (i.e. amd64)
}

impl std::fmt::Display for ELFArch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match *self {
                ELFArch::Arm64 => "arm64",
                ELFArch::S390x => "s390x",
                ELFArch::X86_64 => "x86_64",
            }
        )
    }
}

pub const DEFAULT_ARCH: ELFArch =
    if cfg!(feature = "arm64") && (cfg!(target_arch = "aarch64") || !cfg!(feature = "x86_64")) {
        ELFArch::Arm64
    } else if cfg!(feature = "x86_64") {
        ELFArch::X86_64
    } else {
        ELFArch::S390x
    };

impl Default for ELFArch {
    fn default() -> Self {
        DEFAULT_ARCH
    }
}

#[derive(Debug)]
pub enum ELFVersion {
    EvCurrent = 1,
}

#[derive(Debug)]
pub enum ELFOSABI {
    None,
    SYSV,
}

#[derive(Debug)]
pub enum ELFType {
    Exec = 2,
}

#[derive(Debug)]
pub struct EIdent {
    pub ei_class: EIClass,
    pub ei_data: EIData,
    pub ei_osabi: ELFOSABI,
}

impl From<EIdent> for [u8; 16] {
    fn from(e_ident: EIdent) -> [u8; 16] {
        let (osabi, abi_version) = match e_ident.ei_osabi {
            ELFOSABI::None | ELFOSABI::SYSV => (0, 0),
        };
        #[rustfmt::skip]
        let arr: [u8; 16] = [
            // magic numbers
            0x7f, b'E', b'L', b'F',
            // 32 or 64 bit
            e_ident.ei_class as u8,
            // byte ordering
            e_ident.ei_data as u8,
            // Version of an ELF file - only valid value
            ELFVersion::EvCurrent as u8,
            // ABI and ABI version
            osabi, abi_version,
            // padding bytes
            0, 0, 0, 0, 0, 0, 0
        ];
        arr
    }
}

use EIData::{ELFDATA2LSB as LSB, ELFDATA2MSB as MSB};

pub struct Ehdr {
    pub e_ident: EIdent,
    pub e_type: ELFType,
    pub e_machine: ELFArch,
    pub e_version: ELFVersion,
    pub e_entry: u64,
    pub e_phoff: u64,
    pub e_shoff: u64,
    pub e_flags: u32,
    pub e_ehsize: u16,
    pub e_phentsize: u16,
    pub e_phnum: u16,
    pub e_shentsize: u16,
    pub e_shnum: u16,
    pub e_shstrndx: u16,
}

#[derive(Debug)]
pub enum PType {
    Load = 1,
}

pub struct Phdr {
    pub e_data: EIData,
    pub p_type: PType,
    pub p_flags: u32,
    pub p_offset: u64,
    pub p_vaddr: u64,
    pub p_paddr: u64,
    pub p_filesz: u64,
    pub p_memsz: u64,
    pub p_align: u64,
}

pub const EHDR_SIZE: u16 = 64;
pub const PHDR_SIZE: u16 = 56;
// better this than having identical implementations, differing only in whether to_le_bytes or
// to_be_bytes are called.
macro_rules! serialize_ehdr {
    ($item:ident, $func:ident) => {{
        let mut v = Vec::with_capacity(usize::from(EHDR_SIZE));
        v.extend(<[u8; 16]>::from($item.e_ident));
        v.extend(($item.e_type as u16).$func());
        v.extend(($item.e_machine as u16).$func());
        v.extend(($item.e_version as u32).$func());
        v.extend($item.e_entry.$func());
        v.extend($item.e_phoff.$func());
        v.extend($item.e_shoff.$func());
        v.extend($item.e_flags.$func());
        v.extend($item.e_ehsize.$func());
        v.extend($item.e_phentsize.$func());
        v.extend($item.e_phnum.$func());
        v.extend($item.e_shentsize.$func());
        v.extend($item.e_shnum.$func());
        v.extend($item.e_shstrndx.$func());
        v
    }};
}

macro_rules! serialize_phdr {
    ($item:ident, $func:ident) => {{
        let mut v = Vec::with_capacity(usize::from(PHDR_SIZE));
        v.extend(($item.p_type as u32).$func());
        v.extend($item.p_flags.$func());
        v.extend($item.p_offset.$func());
        v.extend($item.p_vaddr.$func());
        v.extend($item.p_paddr.$func());
        v.extend($item.p_filesz.$func());
        v.extend($item.p_memsz.$func());
        v.extend($item.p_align.$func());
        v
    }};
}

impl From<Ehdr> for Vec<u8> {
    fn from(item: Ehdr) -> Self {
        match item.e_ident.ei_data {
            LSB => serialize_ehdr!(item, to_le_bytes),
            MSB => serialize_ehdr!(item, to_be_bytes),
        }
    }
}

// as endian-ness is not communicated in Phdr entries, it's added to the Phdr struct used within
// eambfc-rs for this.
impl From<Phdr> for Vec<u8> {
    fn from(item: Phdr) -> Self {
        match item.e_data {
            LSB => serialize_phdr!(item, to_le_bytes),
            MSB => serialize_phdr!(item, to_be_bytes),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ELFArch;
    #[test]
    fn display_elfarch() {
        assert_eq!(format!("{}", ELFArch::Arm64), String::from("arm64"));
        assert_eq!(format!("{}", ELFArch::S390x), String::from("s390x"));
        assert_eq!(format!("{}", ELFArch::X86_64), String::from("x86_64"));
    }
}
