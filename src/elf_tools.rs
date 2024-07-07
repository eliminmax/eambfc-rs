// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use libc::{Elf64_Ehdr, Elf64_Phdr};

pub fn serialize_ehdr64_le(ehdr: Elf64_Ehdr, dest: &mut Vec<u8>) {
    dest.extend(ehdr.e_ident);
    dest.extend(ehdr.e_type.to_le_bytes());
    dest.extend(ehdr.e_machine.to_le_bytes());
    dest.extend(ehdr.e_version.to_le_bytes());
    dest.extend(ehdr.e_entry.to_le_bytes());
    dest.extend(ehdr.e_phoff.to_le_bytes());
    dest.extend(ehdr.e_shoff.to_le_bytes());
    dest.extend(ehdr.e_flags.to_le_bytes());
    dest.extend(ehdr.e_ehsize.to_le_bytes());
    dest.extend(ehdr.e_phentsize.to_le_bytes());
    dest.extend(ehdr.e_phnum.to_le_bytes());
    dest.extend(ehdr.e_shentsize.to_le_bytes());
    dest.extend(ehdr.e_shnum.to_le_bytes());
    dest.extend(ehdr.e_shstrndx.to_le_bytes());
}

pub fn serialize_phdr64_le(phdr: Elf64_Phdr, dest: &mut Vec<u8>) {
    dest.extend(phdr.p_type.to_le_bytes());
    dest.extend(phdr.p_flags.to_le_bytes());
    dest.extend(phdr.p_offset.to_le_bytes());
    dest.extend(phdr.p_vaddr.to_le_bytes());
    dest.extend(phdr.p_paddr.to_le_bytes());
    dest.extend(phdr.p_filesz.to_le_bytes());
    dest.extend(phdr.p_memsz.to_le_bytes());
    dest.extend(phdr.p_align.to_le_bytes());
}
