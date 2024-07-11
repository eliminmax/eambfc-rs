// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use std::io::Write;

pub fn bfc_set_reg<T: Write>(reg: u8, imm: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_set_reg");
}
pub fn bfc_reg_copy<T: Write>(dst: u8, src: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_reg_copy");
}
pub fn bfc_syscall<T: Write>(f: &mut T, sz: &mut usize) {
    todo!("bfc_syscall");
}
pub fn bfc_jump_not_zero<T: Write>(reg: u8, offset: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_jump_not_zero");
}
pub fn bfc_jump_zero<T: Write>(reg: u8, offset: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_jump_zero");
}
pub fn bfc_inc_reg<T: Write>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_inc_reg");
}
pub fn bfc_dec_reg<T: Write>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_dec_reg");
}
pub fn bfc_inc_byte<T: Write>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_inc_byte");
}
pub fn bfc_dec_byte<T: Write>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_dec_byte");
}
pub fn bfc_add_reg_imm8<T: Write>(reg: u8, imm8: i8, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_reg_imm8");
}
pub fn bfc_sub_reg_imm8<T: Write>(reg: u8, imm8: i8, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_reg_imm8");
}
pub fn bfc_add_reg_imm16<T: Write>(reg: u8, imm16: i16, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_reg_imm16");
}
pub fn bfc_sub_reg_imm16<T: Write>(reg: u8, imm16: i16, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_reg_imm16");
}
pub fn bfc_add_reg_imm32<T: Write>(reg: u8, imm32: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_reg_imm32");
}
pub fn bfc_sub_reg_imm32<T: Write>(reg: u8, imm32: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_reg_imm32");
}
pub fn bfc_add_reg_imm64<T: Write>(reg: u8, imm64: i64, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_reg_imm64");
}
pub fn bfc_sub_reg_imm64<T: Write>(reg: u8, imm64: i64, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_reg_imm64");
}
pub fn bfc_add_mem<T: Write>(reg: u8, imm8: i8, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_mem");
}
pub fn bfc_sub_mem<T: Write>(reg: u8, imm8: i8, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_mem");
}
pub fn bfc_zero_mem<T: Write>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_zero_mem");
}
