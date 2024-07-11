// SPDX-FileCopyrightText: 2024 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use std::fmt::Debug;
use std::io::Write;

pub fn bfc_set_reg<T: Write + Debug>(reg: u8, imm: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_set_reg({reg:?}, {imm:?}, {f:?}, {sz:?})");
}
pub fn bfc_reg_copy<T: Write + Debug>(dst: u8, src: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_reg_copy({dst:?}, {src:?}, {f:?}, {sz:?})");
}
pub fn bfc_syscall<T: Write + Debug>(f: &mut T, sz: &mut usize) {
    todo!("bfc_syscall({f:?}, {sz:?})");
}
pub fn bfc_jump_not_zero<T: Write + Debug>(reg: u8, offset: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_jump_not_zero({reg:?}, {offset:?}, {f:?}, {sz:?})");
}
pub fn bfc_jump_zero<T: Write + Debug>(reg: u8, offset: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_jump_zero({reg:?}, {offset:?}, {f:?}, {sz:?})");
}
pub fn bfc_inc_reg<T: Write + Debug>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_inc_reg({reg:?}, {f:?}, {sz:?})");
}
pub fn bfc_dec_reg<T: Write + Debug>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_dec_reg({reg:?}, {f:?}, {sz:?})");
}
pub fn bfc_inc_byte<T: Write + Debug>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_inc_byte({reg:?}, {f:?}, {sz:?})");
}
pub fn bfc_dec_byte<T: Write + Debug>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_dec_byte({reg:?}, {f:?}, {sz:?})");
}
pub fn bfc_add_reg_imm8<T: Write + Debug>(reg: u8, imm8: i8, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_reg_imm8({reg:?}, {imm8:?}, {f:?}, {sz:?})");
}
pub fn bfc_sub_reg_imm8<T: Write + Debug>(reg: u8, imm8: i8, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_reg_imm8({reg:?}, {imm8:?}, {f:?}, {sz:?})");
}
pub fn bfc_add_reg_imm16<T: Write + Debug>(reg: u8, imm16: i16, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_reg_imm16({reg:?}, {imm16:?}, {f:?}, {sz:?})");
}
pub fn bfc_sub_reg_imm16<T: Write + Debug>(reg: u8, imm16: i16, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_reg_imm16({reg:?}, {imm16:?}, {f:?}, {sz:?})");
}
pub fn bfc_add_reg_imm32<T: Write + Debug>(reg: u8, imm32: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_reg_imm32({reg:?}, {imm32:?}, {f:?}, {sz:?})");
}
pub fn bfc_sub_reg_imm32<T: Write + Debug>(reg: u8, imm32: i32, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_reg_imm32({reg:?}, {imm32:?}, {f:?}, {sz:?})");
}
pub fn bfc_add_reg_imm64<T: Write + Debug>(reg: u8, imm64: i64, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_reg_imm64({reg:?}, {imm64:?}, {f:?}, {sz:?})");
}
pub fn bfc_sub_reg_imm64<T: Write + Debug>(reg: u8, imm64: i64, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_reg_imm64({reg:?}, {imm64:?}, {f:?}, {sz:?})");
}
pub fn bfc_add_mem<T: Write + Debug>(reg: u8, imm8: i8, f: &mut T, sz: &mut usize) {
    todo!("bfc_add_mem({reg:?}, {imm8:?}, {f:?}, {sz:?})");
}
pub fn bfc_sub_mem<T: Write + Debug>(reg: u8, imm8: i8, f: &mut T, sz: &mut usize) {
    todo!("bfc_sub_mem({reg:?}, {imm8:?}, {f:?}, {sz:?})");
}
pub fn bfc_zero_mem<T: Write + Debug>(reg: u8, f: &mut T, sz: &mut usize) {
    todo!("bfc_zero_mem({reg:?}, {f:?}, {sz:?})");
}
