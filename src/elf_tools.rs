// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
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

#[derive(Debug, Copy, Clone)]
pub enum ELFArch {
    X86_64 = 62, // EM_X86_64 (i.e. amd64)
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
            ELFOSABI::None | ELFOSABI::SYSV => (0u8, 0u8),
        };
        #[rustfmt::skip]
        let arr: [u8; 16] = [
            // magic numbers
            0x7fu8, b'E', b'L', b'F',
            // 32 or 64 bit
            e_ident.ei_class as u8,
            // byte ordering
            e_ident.ei_data as u8,
            // Version of an ELF file - only valid value
            ELFVersion::EvCurrent as u8,
            // ABI and ABI version
            osabi, abi_version,
            // padding bytes
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8
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

// better this than having identical implementations, differing only in whether to_le_bytes or
// to_be_bytes are called.
macro_rules! serialize_ehdr {
    ($item:ident, $func:ident) => {{
        let e_ident: [u8; 16] = $item.e_ident.into();
        let mut v = Vec::from(e_ident);
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
        let mut v = Vec::from(($item.p_type as u32).$func());
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

// as endian-ness is not communicated in Phdr entries, check the ELFDATA_BYTE_ORDER constant
// provided in the arch_info module
impl From<Phdr> for Vec<u8> {
    fn from(item: Phdr) -> Self {
        match item.e_data {
            LSB => serialize_phdr!(item, to_le_bytes),
            MSB => serialize_phdr!(item, to_be_bytes),
        }
    }
}
