use logic_form::Lit;
use std::{
    ffi::{c_int, c_uint, c_void},
    mem::transmute,
    slice::from_raw_parts,
};

use crate::Transys;

#[no_mangle]
pub extern "C" fn transys_drop(transys: *mut c_void) {
    let transys: Box<Transys> = unsafe { Box::from_raw(transys as *mut _) };
    drop(transys)
}

#[no_mangle]
pub extern "C" fn transys_cube_subsume_init(
    transys: *mut c_void,
    lit_ptr: *const Lit,
    lit_len: u32,
) -> c_int {
    let transys = unsafe { &*(transys as *const Transys) };
    let cube = unsafe { from_raw_parts(lit_ptr, lit_len as _) };
    transys.cube_subsume_init(cube) as c_int
}

#[no_mangle]
pub extern "C" fn transys_lit_next(transys: *mut c_void, lit: c_uint) -> c_uint {
    let transys = unsafe { &*(transys as *const Transys) };
    unsafe { transmute(transys.lit_next(transmute(lit))) }
}
