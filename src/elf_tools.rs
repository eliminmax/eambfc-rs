// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

pub trait SerializePhdr {
    fn serialize(&self) -> &[u8];
}

#[derive(Debug, Copy, Clone)]
pub enum ELFDataByteOrder {
    ELFDATA2LSB = 1, // 2's complement, little endian
    ELFDATA2MSB = 2, // 2's complement, big endian
}

#[derive(Debug, Copy, Clone)]
pub enum ELFArch {
    X86_64 = 62, // EM_X86_64 (i.e. amd64)
}

use ELFDataByteOrder::{ELFDATA2LSB as LSB, ELFDATA2MSB as MSB};

pub struct Ehdr {
    pub e_ident: [u8; 16],
    pub e_type: u16,
    pub e_machine: u16,
    pub e_version: u32,
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

pub struct Phdr {
    pub p_type: u32,
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
        let mut v = Vec::from($item.e_ident);
        v.extend($item.e_type.$func());
        v.extend($item.e_machine.$func());
        v.extend($item.e_version.$func());
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
        let mut v = Vec::from($item.p_type.$func());
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
        match super::instr_encoders::arch_info::ELFDATA_BYTE_ORDER {
            LSB => serialize_ehdr!(item, to_le_bytes),
            MSB => serialize_ehdr!(item, to_be_bytes),
        }
    }
}

// as endian-ness is not communicated in Phdr entries, check the ELFDATA_BYTE_ORDER constant
// provided in the arch_info module
impl From<Phdr> for Vec<u8> {
    fn from(item: Phdr) -> Self {
        match super::instr_encoders::arch_info::ELFDATA_BYTE_ORDER {
            LSB => serialize_phdr!(item, to_le_bytes),
            MSB => serialize_phdr!(item, to_be_bytes),
        }
    }
}
