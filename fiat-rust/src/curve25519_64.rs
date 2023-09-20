//! Autogenerated: 'src/ExtractionOCaml/unsaturated_solinas' --lang Rust --inline 25519 64 '(auto)' '2^255 - 19' carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes relax carry_scmul121666
//! curve description: 25519
//! machine_wordsize = 64 (from "64")
//! requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes, relax, carry_scmul121666
//! n = 5 (from "(auto)")
//! s-c = 2^255 - [(1, 19)] (from "2^255 - 19")
//! tight_bounds_multiplier = 1 (from "")
//!
//! Computed values:
//!   carry_chain = [0, 1, 2, 3, 4, 0, 1]
//!   eval z = z[0] + (z[1] << 51) + (z[2] << 102) + (z[3] << 153) + (z[4] << 204)
//!   bytes_eval z = z[0] + (z[1] << 8) + (z[2] << 16) + (z[3] << 24) + (z[4] << 32) + (z[5] << 40) + (z[6] << 48) + (z[7] << 56) + (z[8] << 64) + (z[9] << 72) + (z[10] << 80) + (z[11] << 88) + (z[12] << 96) + (z[13] << 104) + (z[14] << 112) + (z[15] << 120) + (z[16] << 128) + (z[17] << 136) + (z[18] << 144) + (z[19] << 152) + (z[20] << 160) + (z[21] << 168) + (z[22] << 176) + (z[23] << 184) + (z[24] << 192) + (z[25] << 200) + (z[26] << 208) + (z[27] << 216) + (z[28] << 224) + (z[29] << 232) + (z[30] << 240) + (z[31] << 248)
//!   balance = [0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe]

#![allow(unused_parens)]
#![allow(non_camel_case_types)]

pub type fiat_25519_u1 = u8;
pub type fiat_25519_i1 = i8;
pub type fiat_25519_u2 = u8;
pub type fiat_25519_i2 = i8;

/** The type fiat_25519_loose_field_element is a field element with loose bounds. */
/** Bounds: [[0x0 ~> 0x18000000000000], [0x0 ~> 0x18000000000000], [0x0 ~> 0x18000000000000], [0x0 ~> 0x18000000000000], [0x0 ~> 0x18000000000000]] */
#[derive(Clone, Copy)]
pub struct fiat_25519_loose_field_element(pub [u64; 5]);

impl core::ops::Index<usize> for fiat_25519_loose_field_element {
    type Output = u64;
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl core::ops::IndexMut<usize> for fiat_25519_loose_field_element {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

/** The type fiat_25519_tight_field_element is a field element with tight bounds. */
/** Bounds: [[0x0 ~> 0x8000000000000], [0x0 ~> 0x8000000000000], [0x0 ~> 0x8000000000000], [0x0 ~> 0x8000000000000], [0x0 ~> 0x8000000000000]] */
#[derive(Clone, Copy)]
pub struct fiat_25519_tight_field_element(pub [u64; 5]);

impl core::ops::Index<usize> for fiat_25519_tight_field_element {
    type Output = u64;
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl core::ops::IndexMut<usize> for fiat_25519_tight_field_element {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}


/// The function fiat_25519_addcarryx_u51 is an addition with carry.
///
/// Postconditions:
///   out1 = (arg1 + arg2 + arg3) mod 2^51
///   out2 = ⌊(arg1 + arg2 + arg3) / 2^51⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x7ffffffffffff]
///   arg3: [0x0 ~> 0x7ffffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x7ffffffffffff]
///   out2: [0x0 ~> 0x1]
#[inline]
pub fn fiat_25519_addcarryx_u51(out1: &mut u64, out2: &mut fiat_25519_u1, arg1: fiat_25519_u1, arg2: u64, arg3: u64) -> () {
  let x1: u64 = (((arg1 as u64) + arg2) + arg3);
  let x2: u64 = (x1 & 0x7ffffffffffff);
  let x3: fiat_25519_u1 = ((x1 >> 51) as fiat_25519_u1);
  *out1 = x2;
  *out2 = x3;
}

/// The function fiat_25519_subborrowx_u51 is a subtraction with borrow.
///
/// Postconditions:
///   out1 = (-arg1 + arg2 + -arg3) mod 2^51
///   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^51⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x7ffffffffffff]
///   arg3: [0x0 ~> 0x7ffffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x7ffffffffffff]
///   out2: [0x0 ~> 0x1]
#[inline]
pub fn fiat_25519_subborrowx_u51(out1: &mut u64, out2: &mut fiat_25519_u1, arg1: fiat_25519_u1, arg2: u64, arg3: u64) -> () {
  let x1: i64 = ((((((arg2 as i128) - (arg1 as i128)) as i64) as i128) - (arg3 as i128)) as i64);
  let x2: fiat_25519_i1 = ((x1 >> 51) as fiat_25519_i1);
  let x3: u64 = (((x1 as i128) & (0x7ffffffffffff as i128)) as u64);
  *out1 = x3;
  *out2 = (((0x0 as fiat_25519_i2) - (x2 as fiat_25519_i2)) as fiat_25519_u1);
}

/// The function fiat_25519_cmovznz_u64 is a single-word conditional move.
///
/// Postconditions:
///   out1 = (if arg1 = 0 then arg2 else arg3)
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0xffffffffffffffff]
///   arg3: [0x0 ~> 0xffffffffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0xffffffffffffffff]
#[inline]
pub fn fiat_25519_cmovznz_u64(out1: &mut u64, arg1: fiat_25519_u1, arg2: u64, arg3: u64) -> () {
  let x1: fiat_25519_u1 = (!(!arg1));
  let x2: u64 = ((((((0x0 as fiat_25519_i2) - (x1 as fiat_25519_i2)) as fiat_25519_i1) as i128) & (0xffffffffffffffff as i128)) as u64);
  let x3: u64 = ((x2 & arg3) | ((!x2) & arg2));
  *out1 = x3;
}

/// The function fiat_25519_carry_mul multiplies two field elements and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 * eval arg2) mod m
///
#[inline]
pub fn fiat_25519_carry_mul(out1: &mut fiat_25519_tight_field_element, arg1: &fiat_25519_loose_field_element, arg2: &fiat_25519_loose_field_element) -> () {
  let x1: u128 = (((arg1[4]) as u128) * (((arg2[4]) * 0x13) as u128));
  let x2: u128 = (((arg1[4]) as u128) * (((arg2[3]) * 0x13) as u128));
  let x3: u128 = (((arg1[4]) as u128) * (((arg2[2]) * 0x13) as u128));
  let x4: u128 = (((arg1[4]) as u128) * (((arg2[1]) * 0x13) as u128));
  let x5: u128 = (((arg1[3]) as u128) * (((arg2[4]) * 0x13) as u128));
  let x6: u128 = (((arg1[3]) as u128) * (((arg2[3]) * 0x13) as u128));
  let x7: u128 = (((arg1[3]) as u128) * (((arg2[2]) * 0x13) as u128));
  let x8: u128 = (((arg1[2]) as u128) * (((arg2[4]) * 0x13) as u128));
  let x9: u128 = (((arg1[2]) as u128) * (((arg2[3]) * 0x13) as u128));
  let x10: u128 = (((arg1[1]) as u128) * (((arg2[4]) * 0x13) as u128));
  let x11: u128 = (((arg1[4]) as u128) * ((arg2[0]) as u128));
  let x12: u128 = (((arg1[3]) as u128) * ((arg2[1]) as u128));
  let x13: u128 = (((arg1[3]) as u128) * ((arg2[0]) as u128));
  let x14: u128 = (((arg1[2]) as u128) * ((arg2[2]) as u128));
  let x15: u128 = (((arg1[2]) as u128) * ((arg2[1]) as u128));
  let x16: u128 = (((arg1[2]) as u128) * ((arg2[0]) as u128));
  let x17: u128 = (((arg1[1]) as u128) * ((arg2[3]) as u128));
  let x18: u128 = (((arg1[1]) as u128) * ((arg2[2]) as u128));
  let x19: u128 = (((arg1[1]) as u128) * ((arg2[1]) as u128));
  let x20: u128 = (((arg1[1]) as u128) * ((arg2[0]) as u128));
  let x21: u128 = (((arg1[0]) as u128) * ((arg2[4]) as u128));
  let x22: u128 = (((arg1[0]) as u128) * ((arg2[3]) as u128));
  let x23: u128 = (((arg1[0]) as u128) * ((arg2[2]) as u128));
  let x24: u128 = (((arg1[0]) as u128) * ((arg2[1]) as u128));
  let x25: u128 = (((arg1[0]) as u128) * ((arg2[0]) as u128));
  let x26: u128 = (x25 + (x10 + (x9 + (x7 + x4))));
  let x27: u64 = ((x26 >> 51) as u64);
  let x28: u64 = ((x26 & (0x7ffffffffffff as u128)) as u64);
  let x29: u128 = (x21 + (x17 + (x14 + (x12 + x11))));
  let x30: u128 = (x22 + (x18 + (x15 + (x13 + x1))));
  let x31: u128 = (x23 + (x19 + (x16 + (x5 + x2))));
  let x32: u128 = (x24 + (x20 + (x8 + (x6 + x3))));
  let x33: u128 = ((x27 as u128) + x32);
  let x34: u64 = ((x33 >> 51) as u64);
  let x35: u64 = ((x33 & (0x7ffffffffffff as u128)) as u64);
  let x36: u128 = ((x34 as u128) + x31);
  let x37: u64 = ((x36 >> 51) as u64);
  let x38: u64 = ((x36 & (0x7ffffffffffff as u128)) as u64);
  let x39: u128 = ((x37 as u128) + x30);
  let x40: u64 = ((x39 >> 51) as u64);
  let x41: u64 = ((x39 & (0x7ffffffffffff as u128)) as u64);
  let x42: u128 = ((x40 as u128) + x29);
  let x43: u64 = ((x42 >> 51) as u64);
  let x44: u64 = ((x42 & (0x7ffffffffffff as u128)) as u64);
  let x45: u64 = (x43 * 0x13);
  let x46: u64 = (x28 + x45);
  let x47: u64 = (x46 >> 51);
  let x48: u64 = (x46 & 0x7ffffffffffff);
  let x49: u64 = (x47 + x35);
  let x50: fiat_25519_u1 = ((x49 >> 51) as fiat_25519_u1);
  let x51: u64 = (x49 & 0x7ffffffffffff);
  let x52: u64 = ((x50 as u64) + x38);
  out1[0] = x48;
  out1[1] = x51;
  out1[2] = x52;
  out1[3] = x41;
  out1[4] = x44;
}

/// The function fiat_25519_carry_square squares a field element and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 * eval arg1) mod m
///
#[inline]
pub fn fiat_25519_carry_square(out1: &mut fiat_25519_tight_field_element, arg1: &fiat_25519_loose_field_element) -> () {
  let x1: u64 = ((arg1[4]) * 0x13);
  let x2: u64 = (x1 * 0x2);
  let x3: u64 = ((arg1[4]) * 0x2);
  let x4: u64 = ((arg1[3]) * 0x13);
  let x5: u64 = (x4 * 0x2);
  let x6: u64 = ((arg1[3]) * 0x2);
  let x7: u64 = ((arg1[2]) * 0x2);
  let x8: u64 = ((arg1[1]) * 0x2);
  let x9: u128 = (((arg1[4]) as u128) * (x1 as u128));
  let x10: u128 = (((arg1[3]) as u128) * (x2 as u128));
  let x11: u128 = (((arg1[3]) as u128) * (x4 as u128));
  let x12: u128 = (((arg1[2]) as u128) * (x2 as u128));
  let x13: u128 = (((arg1[2]) as u128) * (x5 as u128));
  let x14: u128 = (((arg1[2]) as u128) * ((arg1[2]) as u128));
  let x15: u128 = (((arg1[1]) as u128) * (x2 as u128));
  let x16: u128 = (((arg1[1]) as u128) * (x6 as u128));
  let x17: u128 = (((arg1[1]) as u128) * (x7 as u128));
  let x18: u128 = (((arg1[1]) as u128) * ((arg1[1]) as u128));
  let x19: u128 = (((arg1[0]) as u128) * (x3 as u128));
  let x20: u128 = (((arg1[0]) as u128) * (x6 as u128));
  let x21: u128 = (((arg1[0]) as u128) * (x7 as u128));
  let x22: u128 = (((arg1[0]) as u128) * (x8 as u128));
  let x23: u128 = (((arg1[0]) as u128) * ((arg1[0]) as u128));
  let x24: u128 = (x23 + (x15 + x13));
  let x25: u64 = ((x24 >> 51) as u64);
  let x26: u64 = ((x24 & (0x7ffffffffffff as u128)) as u64);
  let x27: u128 = (x19 + (x16 + x14));
  let x28: u128 = (x20 + (x17 + x9));
  let x29: u128 = (x21 + (x18 + x10));
  let x30: u128 = (x22 + (x12 + x11));
  let x31: u128 = ((x25 as u128) + x30);
  let x32: u64 = ((x31 >> 51) as u64);
  let x33: u64 = ((x31 & (0x7ffffffffffff as u128)) as u64);
  let x34: u128 = ((x32 as u128) + x29);
  let x35: u64 = ((x34 >> 51) as u64);
  let x36: u64 = ((x34 & (0x7ffffffffffff as u128)) as u64);
  let x37: u128 = ((x35 as u128) + x28);
  let x38: u64 = ((x37 >> 51) as u64);
  let x39: u64 = ((x37 & (0x7ffffffffffff as u128)) as u64);
  let x40: u128 = ((x38 as u128) + x27);
  let x41: u64 = ((x40 >> 51) as u64);
  let x42: u64 = ((x40 & (0x7ffffffffffff as u128)) as u64);
  let x43: u64 = (x41 * 0x13);
  let x44: u64 = (x26 + x43);
  let x45: u64 = (x44 >> 51);
  let x46: u64 = (x44 & 0x7ffffffffffff);
  let x47: u64 = (x45 + x33);
  let x48: fiat_25519_u1 = ((x47 >> 51) as fiat_25519_u1);
  let x49: u64 = (x47 & 0x7ffffffffffff);
  let x50: u64 = ((x48 as u64) + x36);
  out1[0] = x46;
  out1[1] = x49;
  out1[2] = x50;
  out1[3] = x39;
  out1[4] = x42;
}

/// The function fiat_25519_carry reduces a field element.
///
/// Postconditions:
///   eval out1 mod m = eval arg1 mod m
///
#[inline]
pub fn fiat_25519_carry(out1: &mut fiat_25519_tight_field_element, arg1: &fiat_25519_loose_field_element) -> () {
  let x1: u64 = (arg1[0]);
  let x2: u64 = ((x1 >> 51) + (arg1[1]));
  let x3: u64 = ((x2 >> 51) + (arg1[2]));
  let x4: u64 = ((x3 >> 51) + (arg1[3]));
  let x5: u64 = ((x4 >> 51) + (arg1[4]));
  let x6: u64 = ((x1 & 0x7ffffffffffff) + ((x5 >> 51) * 0x13));
  let x7: u64 = ((((x6 >> 51) as fiat_25519_u1) as u64) + (x2 & 0x7ffffffffffff));
  let x8: u64 = (x6 & 0x7ffffffffffff);
  let x9: u64 = (x7 & 0x7ffffffffffff);
  let x10: u64 = ((((x7 >> 51) as fiat_25519_u1) as u64) + (x3 & 0x7ffffffffffff));
  let x11: u64 = (x4 & 0x7ffffffffffff);
  let x12: u64 = (x5 & 0x7ffffffffffff);
  out1[0] = x8;
  out1[1] = x9;
  out1[2] = x10;
  out1[3] = x11;
  out1[4] = x12;
}

/// The function fiat_25519_add adds two field elements.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 + eval arg2) mod m
///
#[inline]
pub fn fiat_25519_add(out1: &mut fiat_25519_loose_field_element, arg1: &fiat_25519_tight_field_element, arg2: &fiat_25519_tight_field_element) -> () {
  let x1: u64 = ((arg1[0]) + (arg2[0]));
  let x2: u64 = ((arg1[1]) + (arg2[1]));
  let x3: u64 = ((arg1[2]) + (arg2[2]));
  let x4: u64 = ((arg1[3]) + (arg2[3]));
  let x5: u64 = ((arg1[4]) + (arg2[4]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
}

/// The function fiat_25519_sub subtracts two field elements.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 - eval arg2) mod m
///
#[inline]
pub fn fiat_25519_sub(out1: &mut fiat_25519_loose_field_element, arg1: &fiat_25519_tight_field_element, arg2: &fiat_25519_tight_field_element) -> () {
  let x1: u64 = ((0xfffffffffffda + (arg1[0])) - (arg2[0]));
  let x2: u64 = ((0xffffffffffffe + (arg1[1])) - (arg2[1]));
  let x3: u64 = ((0xffffffffffffe + (arg1[2])) - (arg2[2]));
  let x4: u64 = ((0xffffffffffffe + (arg1[3])) - (arg2[3]));
  let x5: u64 = ((0xffffffffffffe + (arg1[4])) - (arg2[4]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
}

/// The function fiat_25519_opp negates a field element.
///
/// Postconditions:
///   eval out1 mod m = -eval arg1 mod m
///
#[inline]
pub fn fiat_25519_opp(out1: &mut fiat_25519_loose_field_element, arg1: &fiat_25519_tight_field_element) -> () {
  let x1: u64 = (0xfffffffffffda - (arg1[0]));
  let x2: u64 = (0xffffffffffffe - (arg1[1]));
  let x3: u64 = (0xffffffffffffe - (arg1[2]));
  let x4: u64 = (0xffffffffffffe - (arg1[3]));
  let x5: u64 = (0xffffffffffffe - (arg1[4]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
}

/// The function fiat_25519_selectznz is a multi-limb conditional select.
///
/// Postconditions:
///   out1 = (if arg1 = 0 then arg2 else arg3)
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
///   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
/// Output Bounds:
///   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
#[inline]
pub fn fiat_25519_selectznz(out1: &mut [u64; 5], arg1: fiat_25519_u1, arg2: &[u64; 5], arg3: &[u64; 5]) -> () {
  let mut x1: u64 = 0;
  fiat_25519_cmovznz_u64(&mut x1, arg1, (arg2[0]), (arg3[0]));
  let mut x2: u64 = 0;
  fiat_25519_cmovznz_u64(&mut x2, arg1, (arg2[1]), (arg3[1]));
  let mut x3: u64 = 0;
  fiat_25519_cmovznz_u64(&mut x3, arg1, (arg2[2]), (arg3[2]));
  let mut x4: u64 = 0;
  fiat_25519_cmovznz_u64(&mut x4, arg1, (arg2[3]), (arg3[3]));
  let mut x5: u64 = 0;
  fiat_25519_cmovznz_u64(&mut x5, arg1, (arg2[4]), (arg3[4]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
}

/// The function fiat_25519_to_bytes serializes a field element to bytes in little-endian order.
///
/// Postconditions:
///   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..31]
///
/// Output Bounds:
///   out1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x7f]]
#[inline]
pub fn fiat_25519_to_bytes(out1: &mut [u8; 32], arg1: &fiat_25519_tight_field_element) -> () {
  let mut x1: u64 = 0;
  let mut x2: fiat_25519_u1 = 0;
  fiat_25519_subborrowx_u51(&mut x1, &mut x2, 0x0, (arg1[0]), 0x7ffffffffffed);
  let mut x3: u64 = 0;
  let mut x4: fiat_25519_u1 = 0;
  fiat_25519_subborrowx_u51(&mut x3, &mut x4, x2, (arg1[1]), 0x7ffffffffffff);
  let mut x5: u64 = 0;
  let mut x6: fiat_25519_u1 = 0;
  fiat_25519_subborrowx_u51(&mut x5, &mut x6, x4, (arg1[2]), 0x7ffffffffffff);
  let mut x7: u64 = 0;
  let mut x8: fiat_25519_u1 = 0;
  fiat_25519_subborrowx_u51(&mut x7, &mut x8, x6, (arg1[3]), 0x7ffffffffffff);
  let mut x9: u64 = 0;
  let mut x10: fiat_25519_u1 = 0;
  fiat_25519_subborrowx_u51(&mut x9, &mut x10, x8, (arg1[4]), 0x7ffffffffffff);
  let mut x11: u64 = 0;
  fiat_25519_cmovznz_u64(&mut x11, x10, (0x0 as u64), 0xffffffffffffffff);
  let mut x12: u64 = 0;
  let mut x13: fiat_25519_u1 = 0;
  fiat_25519_addcarryx_u51(&mut x12, &mut x13, 0x0, x1, (x11 & 0x7ffffffffffed));
  let mut x14: u64 = 0;
  let mut x15: fiat_25519_u1 = 0;
  fiat_25519_addcarryx_u51(&mut x14, &mut x15, x13, x3, (x11 & 0x7ffffffffffff));
  let mut x16: u64 = 0;
  let mut x17: fiat_25519_u1 = 0;
  fiat_25519_addcarryx_u51(&mut x16, &mut x17, x15, x5, (x11 & 0x7ffffffffffff));
  let mut x18: u64 = 0;
  let mut x19: fiat_25519_u1 = 0;
  fiat_25519_addcarryx_u51(&mut x18, &mut x19, x17, x7, (x11 & 0x7ffffffffffff));
  let mut x20: u64 = 0;
  let mut x21: fiat_25519_u1 = 0;
  fiat_25519_addcarryx_u51(&mut x20, &mut x21, x19, x9, (x11 & 0x7ffffffffffff));
  let x22: u64 = (x20 << 4);
  let x23: u64 = (x18 * (0x2 as u64));
  let x24: u64 = (x16 << 6);
  let x25: u64 = (x14 << 3);
  let x26: u8 = ((x12 & (0xff as u64)) as u8);
  let x27: u64 = (x12 >> 8);
  let x28: u8 = ((x27 & (0xff as u64)) as u8);
  let x29: u64 = (x27 >> 8);
  let x30: u8 = ((x29 & (0xff as u64)) as u8);
  let x31: u64 = (x29 >> 8);
  let x32: u8 = ((x31 & (0xff as u64)) as u8);
  let x33: u64 = (x31 >> 8);
  let x34: u8 = ((x33 & (0xff as u64)) as u8);
  let x35: u64 = (x33 >> 8);
  let x36: u8 = ((x35 & (0xff as u64)) as u8);
  let x37: u8 = ((x35 >> 8) as u8);
  let x38: u64 = (x25 + (x37 as u64));
  let x39: u8 = ((x38 & (0xff as u64)) as u8);
  let x40: u64 = (x38 >> 8);
  let x41: u8 = ((x40 & (0xff as u64)) as u8);
  let x42: u64 = (x40 >> 8);
  let x43: u8 = ((x42 & (0xff as u64)) as u8);
  let x44: u64 = (x42 >> 8);
  let x45: u8 = ((x44 & (0xff as u64)) as u8);
  let x46: u64 = (x44 >> 8);
  let x47: u8 = ((x46 & (0xff as u64)) as u8);
  let x48: u64 = (x46 >> 8);
  let x49: u8 = ((x48 & (0xff as u64)) as u8);
  let x50: u8 = ((x48 >> 8) as u8);
  let x51: u64 = (x24 + (x50 as u64));
  let x52: u8 = ((x51 & (0xff as u64)) as u8);
  let x53: u64 = (x51 >> 8);
  let x54: u8 = ((x53 & (0xff as u64)) as u8);
  let x55: u64 = (x53 >> 8);
  let x56: u8 = ((x55 & (0xff as u64)) as u8);
  let x57: u64 = (x55 >> 8);
  let x58: u8 = ((x57 & (0xff as u64)) as u8);
  let x59: u64 = (x57 >> 8);
  let x60: u8 = ((x59 & (0xff as u64)) as u8);
  let x61: u64 = (x59 >> 8);
  let x62: u8 = ((x61 & (0xff as u64)) as u8);
  let x63: u64 = (x61 >> 8);
  let x64: u8 = ((x63 & (0xff as u64)) as u8);
  let x65: fiat_25519_u1 = ((x63 >> 8) as fiat_25519_u1);
  let x66: u64 = (x23 + (x65 as u64));
  let x67: u8 = ((x66 & (0xff as u64)) as u8);
  let x68: u64 = (x66 >> 8);
  let x69: u8 = ((x68 & (0xff as u64)) as u8);
  let x70: u64 = (x68 >> 8);
  let x71: u8 = ((x70 & (0xff as u64)) as u8);
  let x72: u64 = (x70 >> 8);
  let x73: u8 = ((x72 & (0xff as u64)) as u8);
  let x74: u64 = (x72 >> 8);
  let x75: u8 = ((x74 & (0xff as u64)) as u8);
  let x76: u64 = (x74 >> 8);
  let x77: u8 = ((x76 & (0xff as u64)) as u8);
  let x78: u8 = ((x76 >> 8) as u8);
  let x79: u64 = (x22 + (x78 as u64));
  let x80: u8 = ((x79 & (0xff as u64)) as u8);
  let x81: u64 = (x79 >> 8);
  let x82: u8 = ((x81 & (0xff as u64)) as u8);
  let x83: u64 = (x81 >> 8);
  let x84: u8 = ((x83 & (0xff as u64)) as u8);
  let x85: u64 = (x83 >> 8);
  let x86: u8 = ((x85 & (0xff as u64)) as u8);
  let x87: u64 = (x85 >> 8);
  let x88: u8 = ((x87 & (0xff as u64)) as u8);
  let x89: u64 = (x87 >> 8);
  let x90: u8 = ((x89 & (0xff as u64)) as u8);
  let x91: u8 = ((x89 >> 8) as u8);
  out1[0] = x26;
  out1[1] = x28;
  out1[2] = x30;
  out1[3] = x32;
  out1[4] = x34;
  out1[5] = x36;
  out1[6] = x39;
  out1[7] = x41;
  out1[8] = x43;
  out1[9] = x45;
  out1[10] = x47;
  out1[11] = x49;
  out1[12] = x52;
  out1[13] = x54;
  out1[14] = x56;
  out1[15] = x58;
  out1[16] = x60;
  out1[17] = x62;
  out1[18] = x64;
  out1[19] = x67;
  out1[20] = x69;
  out1[21] = x71;
  out1[22] = x73;
  out1[23] = x75;
  out1[24] = x77;
  out1[25] = x80;
  out1[26] = x82;
  out1[27] = x84;
  out1[28] = x86;
  out1[29] = x88;
  out1[30] = x90;
  out1[31] = x91;
}

/// The function fiat_25519_from_bytes deserializes a field element from bytes in little-endian order.
///
/// Postconditions:
///   eval out1 mod m = bytes_eval arg1 mod m
///
/// Input Bounds:
///   arg1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x7f]]
#[inline]
pub fn fiat_25519_from_bytes(out1: &mut fiat_25519_tight_field_element, arg1: &[u8; 32]) -> () {
  let x1: u64 = (((arg1[31]) as u64) << 44);
  let x2: u64 = (((arg1[30]) as u64) << 36);
  let x3: u64 = (((arg1[29]) as u64) << 28);
  let x4: u64 = (((arg1[28]) as u64) << 20);
  let x5: u64 = (((arg1[27]) as u64) << 12);
  let x6: u64 = (((arg1[26]) as u64) << 4);
  let x7: u64 = (((arg1[25]) as u64) << 47);
  let x8: u64 = (((arg1[24]) as u64) << 39);
  let x9: u64 = (((arg1[23]) as u64) << 31);
  let x10: u64 = (((arg1[22]) as u64) << 23);
  let x11: u64 = (((arg1[21]) as u64) << 15);
  let x12: u64 = (((arg1[20]) as u64) << 7);
  let x13: u64 = (((arg1[19]) as u64) << 50);
  let x14: u64 = (((arg1[18]) as u64) << 42);
  let x15: u64 = (((arg1[17]) as u64) << 34);
  let x16: u64 = (((arg1[16]) as u64) << 26);
  let x17: u64 = (((arg1[15]) as u64) << 18);
  let x18: u64 = (((arg1[14]) as u64) << 10);
  let x19: u64 = (((arg1[13]) as u64) << 2);
  let x20: u64 = (((arg1[12]) as u64) << 45);
  let x21: u64 = (((arg1[11]) as u64) << 37);
  let x22: u64 = (((arg1[10]) as u64) << 29);
  let x23: u64 = (((arg1[9]) as u64) << 21);
  let x24: u64 = (((arg1[8]) as u64) << 13);
  let x25: u64 = (((arg1[7]) as u64) << 5);
  let x26: u64 = (((arg1[6]) as u64) << 48);
  let x27: u64 = (((arg1[5]) as u64) << 40);
  let x28: u64 = (((arg1[4]) as u64) << 32);
  let x29: u64 = (((arg1[3]) as u64) << 24);
  let x30: u64 = (((arg1[2]) as u64) << 16);
  let x31: u64 = (((arg1[1]) as u64) << 8);
  let x32: u8 = (arg1[0]);
  let x33: u64 = (x31 + (x32 as u64));
  let x34: u64 = (x30 + x33);
  let x35: u64 = (x29 + x34);
  let x36: u64 = (x28 + x35);
  let x37: u64 = (x27 + x36);
  let x38: u64 = (x26 + x37);
  let x39: u64 = (x38 & 0x7ffffffffffff);
  let x40: u8 = ((x38 >> 51) as u8);
  let x41: u64 = (x25 + (x40 as u64));
  let x42: u64 = (x24 + x41);
  let x43: u64 = (x23 + x42);
  let x44: u64 = (x22 + x43);
  let x45: u64 = (x21 + x44);
  let x46: u64 = (x20 + x45);
  let x47: u64 = (x46 & 0x7ffffffffffff);
  let x48: u8 = ((x46 >> 51) as u8);
  let x49: u64 = (x19 + (x48 as u64));
  let x50: u64 = (x18 + x49);
  let x51: u64 = (x17 + x50);
  let x52: u64 = (x16 + x51);
  let x53: u64 = (x15 + x52);
  let x54: u64 = (x14 + x53);
  let x55: u64 = (x13 + x54);
  let x56: u64 = (x55 & 0x7ffffffffffff);
  let x57: u8 = ((x55 >> 51) as u8);
  let x58: u64 = (x12 + (x57 as u64));
  let x59: u64 = (x11 + x58);
  let x60: u64 = (x10 + x59);
  let x61: u64 = (x9 + x60);
  let x62: u64 = (x8 + x61);
  let x63: u64 = (x7 + x62);
  let x64: u64 = (x63 & 0x7ffffffffffff);
  let x65: u8 = ((x63 >> 51) as u8);
  let x66: u64 = (x6 + (x65 as u64));
  let x67: u64 = (x5 + x66);
  let x68: u64 = (x4 + x67);
  let x69: u64 = (x3 + x68);
  let x70: u64 = (x2 + x69);
  let x71: u64 = (x1 + x70);
  out1[0] = x39;
  out1[1] = x47;
  out1[2] = x56;
  out1[3] = x64;
  out1[4] = x71;
}

/// The function fiat_25519_relax is the identity function converting from tight field elements to loose field elements.
///
/// Postconditions:
///   out1 = arg1
///
#[inline]
pub fn fiat_25519_relax(out1: &mut fiat_25519_loose_field_element, arg1: &fiat_25519_tight_field_element) -> () {
  let x1: u64 = (arg1[0]);
  let x2: u64 = (arg1[1]);
  let x3: u64 = (arg1[2]);
  let x4: u64 = (arg1[3]);
  let x5: u64 = (arg1[4]);
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
}

/// The function fiat_25519_carry_scmul_121666 multiplies a field element by 121666 and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (121666 * eval arg1) mod m
///
#[inline]
pub fn fiat_25519_carry_scmul_121666(out1: &mut fiat_25519_tight_field_element, arg1: &fiat_25519_loose_field_element) -> () {
  let x1: u128 = ((0x1db42 as u128) * ((arg1[4]) as u128));
  let x2: u128 = ((0x1db42 as u128) * ((arg1[3]) as u128));
  let x3: u128 = ((0x1db42 as u128) * ((arg1[2]) as u128));
  let x4: u128 = ((0x1db42 as u128) * ((arg1[1]) as u128));
  let x5: u128 = ((0x1db42 as u128) * ((arg1[0]) as u128));
  let x6: u64 = ((x5 >> 51) as u64);
  let x7: u64 = ((x5 & (0x7ffffffffffff as u128)) as u64);
  let x8: u128 = ((x6 as u128) + x4);
  let x9: u64 = ((x8 >> 51) as u64);
  let x10: u64 = ((x8 & (0x7ffffffffffff as u128)) as u64);
  let x11: u128 = ((x9 as u128) + x3);
  let x12: u64 = ((x11 >> 51) as u64);
  let x13: u64 = ((x11 & (0x7ffffffffffff as u128)) as u64);
  let x14: u128 = ((x12 as u128) + x2);
  let x15: u64 = ((x14 >> 51) as u64);
  let x16: u64 = ((x14 & (0x7ffffffffffff as u128)) as u64);
  let x17: u128 = ((x15 as u128) + x1);
  let x18: u64 = ((x17 >> 51) as u64);
  let x19: u64 = ((x17 & (0x7ffffffffffff as u128)) as u64);
  let x20: u64 = (x18 * 0x13);
  let x21: u64 = (x7 + x20);
  let x22: fiat_25519_u1 = ((x21 >> 51) as fiat_25519_u1);
  let x23: u64 = (x21 & 0x7ffffffffffff);
  let x24: u64 = ((x22 as u64) + x10);
  let x25: fiat_25519_u1 = ((x24 >> 51) as fiat_25519_u1);
  let x26: u64 = (x24 & 0x7ffffffffffff);
  let x27: u64 = ((x25 as u64) + x13);
  out1[0] = x23;
  out1[1] = x26;
  out1[2] = x27;
  out1[3] = x16;
  out1[4] = x19;
}
