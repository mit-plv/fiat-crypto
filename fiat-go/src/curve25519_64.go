/* Autogenerated: src/ExtractionOCaml/unsaturated_solinas --lang Go --no-wide-int --cmovznz-by-mul 25519 64 '(auto)' '2^255 - 19' carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes carry_scmul121666 */
/* curve description: 25519 */
/* machine_wordsize = 64 (from "64") */
/* requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes, carry_scmul121666 */
/* n = 5 (from "(auto)") */
/* s-c = 2^255 - [(1, 19)] (from "2^255 - 19") */
/* tight_bounds_multiplier = 1.1 (from "") */
/*  */
/* Computed values: */
/* carry_chain = [0, 1, 2, 3, 4, 0, 1] */
/* eval z = z[0] + (z[1] << 51) + (z[2] << 102) + (z[3] << 153) + (z[4] << 204) */
/* bytes_eval z = z[0] + (z[1] << 8) + (z[2] << 16) + (z[3] << 24) + (z[4] << 32) + (z[5] << 40) + (z[6] << 48) + (z[7] << 56) + (z[8] << 64) + (z[9] << 72) + (z[10] << 80) + (z[11] << 88) + (z[12] << 96) + (z[13] << 104) + (z[14] << 112) + (z[15] << 120) + (z[16] << 128) + (z[17] << 136) + (z[18] << 144) + (z[19] << 152) + (z[20] << 160) + (z[21] << 168) + (z[22] << 176) + (z[23] << 184) + (z[24] << 192) + (z[25] << 200) + (z[26] << 208) + (z[27] << 216) + (z[28] << 224) + (z[29] << 232) + (z[30] << 240) + (z[31] << 248) */
/* balance = [0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe] */

package fiat_25519

import "math/bits"
type fiat_25519_uint1 uint8
type fiat_25519_int1 int8

/* The function fiat_25519_addcarryx_u64 is a thin wrapper around bits.Add64 that uses fiat_25519_uint1 rather than uint64 */
func fiat_25519_addcarryx_u64(x uint64, y uint64, carry fiat_25519_uint1) (uint64, fiat_25519_uint1) {
  var sum uint64
  var carryOut uint64
  sum, carryOut = bits.Add64(x, y, uint64(carry))
  return sum, fiat_25519_uint1(carryOut)
}

/* The function fiat_25519_subborrowx_u64 is a thin wrapper around bits.Sub64 that uses fiat_25519_uint1 rather than uint64 */
func fiat_25519_subborrowx_u64(x uint64, y uint64, carry fiat_25519_uint1) (uint64, fiat_25519_uint1) {
  var sum uint64
  var carryOut uint64
  sum, carryOut = bits.Sub64(x, y, uint64(carry))
  return sum, fiat_25519_uint1(carryOut)
}


/*
 * The function fiat_25519_addcarryx_u51 is an addition with carry.
 * Postconditions:
 *   out1 = (arg1 + arg2 + arg3) mod 2^51
 *   out2 = ⌊(arg1 + arg2 + arg3) / 2^51⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x7ffffffffffff]
 *   arg3: [0x0 ~> 0x7ffffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x7ffffffffffff]
 *   out2: [0x0 ~> 0x1]
 */
/*inline*/
func fiat_25519_addcarryx_u51(out1 *uint64, out2 *fiat_25519_uint1, arg1 fiat_25519_uint1, arg2 uint64, arg3 uint64) {
  var x1 uint64 = ((uint64(arg1) + arg2) + arg3)
  var x2 uint64 = (x1 & 0x7ffffffffffff)
  var x3 fiat_25519_uint1 = fiat_25519_uint1((x1 >> 51))
  *out1 = x2
  *out2 = x3
}

/*
 * The function fiat_25519_subborrowx_u51 is a subtraction with borrow.
 * Postconditions:
 *   out1 = (-arg1 + arg2 + -arg3) mod 2^51
 *   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^51⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x7ffffffffffff]
 *   arg3: [0x0 ~> 0x7ffffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x7ffffffffffff]
 *   out2: [0x0 ~> 0x1]
 */
/*inline*/
func fiat_25519_subborrowx_u51(out1 *uint64, out2 *fiat_25519_uint1, arg1 fiat_25519_uint1, arg2 uint64, arg3 uint64) {
  var x1 int64 = ((int64(arg2) - int64(arg1)) - int64(arg3))
  var x2 fiat_25519_int1 = fiat_25519_int1((x1 >> 51))
  var x3 uint64 = (uint64(x1) & 0x7ffffffffffff)
  *out1 = x3
  *out2 = (0x0 - fiat_25519_uint1(x2))
}

/*
 * The function fiat_25519_cmovznz_u64 is a single-word conditional move.
 * Postconditions:
 *   out1 = (if arg1 = 0 then arg2 else arg3)
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0xffffffffffffffff]
 *   arg3: [0x0 ~> 0xffffffffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xffffffffffffffff]
 */
/*inline*/
func fiat_25519_cmovznz_u64(out1 *uint64, arg1 fiat_25519_uint1, arg2 uint64, arg3 uint64) {
  var x1 uint64 = (uint64(arg1) * 0xffffffffffffffff)
  var x2 uint64 = ((x1 & arg3) | ((^x1) & arg2))
  *out1 = x2
}

/*
 * The function fiat_25519_carry_mul multiplies two field elements and reduces the result.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 * eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 *   arg2: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
/*inline*/
func fiat_25519_carry_mul(out1 *[5]uint64, arg1 *[5]uint64, arg2 *[5]uint64) {
  var x1 uint64
  var x2 uint64
  x2, x1 = bits.Mul64((arg1[4]), ((arg2[4]) * 0x13))
  var x3 uint64
  var x4 uint64
  x4, x3 = bits.Mul64((arg1[4]), ((arg2[3]) * 0x13))
  var x5 uint64
  var x6 uint64
  x6, x5 = bits.Mul64((arg1[4]), ((arg2[2]) * 0x13))
  var x7 uint64
  var x8 uint64
  x8, x7 = bits.Mul64((arg1[4]), ((arg2[1]) * 0x13))
  var x9 uint64
  var x10 uint64
  x10, x9 = bits.Mul64((arg1[3]), ((arg2[4]) * 0x13))
  var x11 uint64
  var x12 uint64
  x12, x11 = bits.Mul64((arg1[3]), ((arg2[3]) * 0x13))
  var x13 uint64
  var x14 uint64
  x14, x13 = bits.Mul64((arg1[3]), ((arg2[2]) * 0x13))
  var x15 uint64
  var x16 uint64
  x16, x15 = bits.Mul64((arg1[2]), ((arg2[4]) * 0x13))
  var x17 uint64
  var x18 uint64
  x18, x17 = bits.Mul64((arg1[2]), ((arg2[3]) * 0x13))
  var x19 uint64
  var x20 uint64
  x20, x19 = bits.Mul64((arg1[1]), ((arg2[4]) * 0x13))
  var x21 uint64
  var x22 uint64
  x22, x21 = bits.Mul64((arg1[4]), (arg2[0]))
  var x23 uint64
  var x24 uint64
  x24, x23 = bits.Mul64((arg1[3]), (arg2[1]))
  var x25 uint64
  var x26 uint64
  x26, x25 = bits.Mul64((arg1[3]), (arg2[0]))
  var x27 uint64
  var x28 uint64
  x28, x27 = bits.Mul64((arg1[2]), (arg2[2]))
  var x29 uint64
  var x30 uint64
  x30, x29 = bits.Mul64((arg1[2]), (arg2[1]))
  var x31 uint64
  var x32 uint64
  x32, x31 = bits.Mul64((arg1[2]), (arg2[0]))
  var x33 uint64
  var x34 uint64
  x34, x33 = bits.Mul64((arg1[1]), (arg2[3]))
  var x35 uint64
  var x36 uint64
  x36, x35 = bits.Mul64((arg1[1]), (arg2[2]))
  var x37 uint64
  var x38 uint64
  x38, x37 = bits.Mul64((arg1[1]), (arg2[1]))
  var x39 uint64
  var x40 uint64
  x40, x39 = bits.Mul64((arg1[1]), (arg2[0]))
  var x41 uint64
  var x42 uint64
  x42, x41 = bits.Mul64((arg1[0]), (arg2[4]))
  var x43 uint64
  var x44 uint64
  x44, x43 = bits.Mul64((arg1[0]), (arg2[3]))
  var x45 uint64
  var x46 uint64
  x46, x45 = bits.Mul64((arg1[0]), (arg2[2]))
  var x47 uint64
  var x48 uint64
  x48, x47 = bits.Mul64((arg1[0]), (arg2[1]))
  var x49 uint64
  var x50 uint64
  x50, x49 = bits.Mul64((arg1[0]), (arg2[0]))
  var x51 uint64
  var x52 fiat_25519_uint1
  x51, x52 = fiat_25519_addcarryx_u64(x13, x7, 0x0)
  var x53 uint64
  x53, _ = fiat_25519_addcarryx_u64(x14, x8, x52)
  var x55 uint64
  var x56 fiat_25519_uint1
  x55, x56 = fiat_25519_addcarryx_u64(x17, x51, 0x0)
  var x57 uint64
  x57, _ = fiat_25519_addcarryx_u64(x18, x53, x56)
  var x59 uint64
  var x60 fiat_25519_uint1
  x59, x60 = fiat_25519_addcarryx_u64(x19, x55, 0x0)
  var x61 uint64
  x61, _ = fiat_25519_addcarryx_u64(x20, x57, x60)
  var x63 uint64
  var x64 fiat_25519_uint1
  x63, x64 = fiat_25519_addcarryx_u64(x49, x59, 0x0)
  var x65 uint64
  x65, _ = fiat_25519_addcarryx_u64(x50, x61, x64)
  var x67 uint64 = ((x63 >> 51) | ((x65 << 13) & 0xffffffffffffffff))
  var x68 uint64 = (x63 & 0x7ffffffffffff)
  var x69 uint64
  var x70 fiat_25519_uint1
  x69, x70 = fiat_25519_addcarryx_u64(x23, x21, 0x0)
  var x71 uint64
  x71, _ = fiat_25519_addcarryx_u64(x24, x22, x70)
  var x73 uint64
  var x74 fiat_25519_uint1
  x73, x74 = fiat_25519_addcarryx_u64(x27, x69, 0x0)
  var x75 uint64
  x75, _ = fiat_25519_addcarryx_u64(x28, x71, x74)
  var x77 uint64
  var x78 fiat_25519_uint1
  x77, x78 = fiat_25519_addcarryx_u64(x33, x73, 0x0)
  var x79 uint64
  x79, _ = fiat_25519_addcarryx_u64(x34, x75, x78)
  var x81 uint64
  var x82 fiat_25519_uint1
  x81, x82 = fiat_25519_addcarryx_u64(x41, x77, 0x0)
  var x83 uint64
  x83, _ = fiat_25519_addcarryx_u64(x42, x79, x82)
  var x85 uint64
  var x86 fiat_25519_uint1
  x85, x86 = fiat_25519_addcarryx_u64(x25, x1, 0x0)
  var x87 uint64
  x87, _ = fiat_25519_addcarryx_u64(x26, x2, x86)
  var x89 uint64
  var x90 fiat_25519_uint1
  x89, x90 = fiat_25519_addcarryx_u64(x29, x85, 0x0)
  var x91 uint64
  x91, _ = fiat_25519_addcarryx_u64(x30, x87, x90)
  var x93 uint64
  var x94 fiat_25519_uint1
  x93, x94 = fiat_25519_addcarryx_u64(x35, x89, 0x0)
  var x95 uint64
  x95, _ = fiat_25519_addcarryx_u64(x36, x91, x94)
  var x97 uint64
  var x98 fiat_25519_uint1
  x97, x98 = fiat_25519_addcarryx_u64(x43, x93, 0x0)
  var x99 uint64
  x99, _ = fiat_25519_addcarryx_u64(x44, x95, x98)
  var x101 uint64
  var x102 fiat_25519_uint1
  x101, x102 = fiat_25519_addcarryx_u64(x9, x3, 0x0)
  var x103 uint64
  x103, _ = fiat_25519_addcarryx_u64(x10, x4, x102)
  var x105 uint64
  var x106 fiat_25519_uint1
  x105, x106 = fiat_25519_addcarryx_u64(x31, x101, 0x0)
  var x107 uint64
  x107, _ = fiat_25519_addcarryx_u64(x32, x103, x106)
  var x109 uint64
  var x110 fiat_25519_uint1
  x109, x110 = fiat_25519_addcarryx_u64(x37, x105, 0x0)
  var x111 uint64
  x111, _ = fiat_25519_addcarryx_u64(x38, x107, x110)
  var x113 uint64
  var x114 fiat_25519_uint1
  x113, x114 = fiat_25519_addcarryx_u64(x45, x109, 0x0)
  var x115 uint64
  x115, _ = fiat_25519_addcarryx_u64(x46, x111, x114)
  var x117 uint64
  var x118 fiat_25519_uint1
  x117, x118 = fiat_25519_addcarryx_u64(x11, x5, 0x0)
  var x119 uint64
  x119, _ = fiat_25519_addcarryx_u64(x12, x6, x118)
  var x121 uint64
  var x122 fiat_25519_uint1
  x121, x122 = fiat_25519_addcarryx_u64(x15, x117, 0x0)
  var x123 uint64
  x123, _ = fiat_25519_addcarryx_u64(x16, x119, x122)
  var x125 uint64
  var x126 fiat_25519_uint1
  x125, x126 = fiat_25519_addcarryx_u64(x39, x121, 0x0)
  var x127 uint64
  x127, _ = fiat_25519_addcarryx_u64(x40, x123, x126)
  var x129 uint64
  var x130 fiat_25519_uint1
  x129, x130 = fiat_25519_addcarryx_u64(x47, x125, 0x0)
  var x131 uint64
  x131, _ = fiat_25519_addcarryx_u64(x48, x127, x130)
  var x133 uint64
  var x134 fiat_25519_uint1
  x133, x134 = fiat_25519_addcarryx_u64(x67, x129, 0x0)
  var x135 uint64 = (uint64(x134) + x131)
  var x136 uint64 = ((x133 >> 51) | ((x135 << 13) & 0xffffffffffffffff))
  var x137 uint64 = (x133 & 0x7ffffffffffff)
  var x138 uint64
  var x139 fiat_25519_uint1
  x138, x139 = fiat_25519_addcarryx_u64(x136, x113, 0x0)
  var x140 uint64 = (uint64(x139) + x115)
  var x141 uint64 = ((x138 >> 51) | ((x140 << 13) & 0xffffffffffffffff))
  var x142 uint64 = (x138 & 0x7ffffffffffff)
  var x143 uint64
  var x144 fiat_25519_uint1
  x143, x144 = fiat_25519_addcarryx_u64(x141, x97, 0x0)
  var x145 uint64 = (uint64(x144) + x99)
  var x146 uint64 = ((x143 >> 51) | ((x145 << 13) & 0xffffffffffffffff))
  var x147 uint64 = (x143 & 0x7ffffffffffff)
  var x148 uint64
  var x149 fiat_25519_uint1
  x148, x149 = fiat_25519_addcarryx_u64(x146, x81, 0x0)
  var x150 uint64 = (uint64(x149) + x83)
  var x151 uint64 = ((x148 >> 51) | ((x150 << 13) & 0xffffffffffffffff))
  var x152 uint64 = (x148 & 0x7ffffffffffff)
  var x153 uint64 = (x151 * 0x13)
  var x154 uint64 = (x68 + x153)
  var x155 uint64 = (x154 >> 51)
  var x156 uint64 = (x154 & 0x7ffffffffffff)
  var x157 uint64 = (x155 + x137)
  var x158 fiat_25519_uint1 = fiat_25519_uint1((x157 >> 51))
  var x159 uint64 = (x157 & 0x7ffffffffffff)
  var x160 uint64 = (uint64(x158) + x142)
  out1[0] = x156
  out1[1] = x159
  out1[2] = x160
  out1[3] = x147
  out1[4] = x152
}

/*
 * The function fiat_25519_carry_square squares a field element and reduces the result.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 * eval arg1) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
/*inline*/
func fiat_25519_carry_square(out1 *[5]uint64, arg1 *[5]uint64) {
  var x1 uint64 = ((arg1[4]) * 0x13)
  var x2 uint64 = (x1 * 0x2)
  var x3 uint64 = ((arg1[4]) * 0x2)
  var x4 uint64 = ((arg1[3]) * 0x13)
  var x5 uint64 = (x4 * 0x2)
  var x6 uint64 = ((arg1[3]) * 0x2)
  var x7 uint64 = ((arg1[2]) * 0x2)
  var x8 uint64 = ((arg1[1]) * 0x2)
  var x9 uint64
  var x10 uint64
  x10, x9 = bits.Mul64((arg1[4]), x1)
  var x11 uint64
  var x12 uint64
  x12, x11 = bits.Mul64((arg1[3]), x2)
  var x13 uint64
  var x14 uint64
  x14, x13 = bits.Mul64((arg1[3]), x4)
  var x15 uint64
  var x16 uint64
  x16, x15 = bits.Mul64((arg1[2]), x2)
  var x17 uint64
  var x18 uint64
  x18, x17 = bits.Mul64((arg1[2]), x5)
  var x19 uint64
  var x20 uint64
  x20, x19 = bits.Mul64((arg1[2]), (arg1[2]))
  var x21 uint64
  var x22 uint64
  x22, x21 = bits.Mul64((arg1[1]), x2)
  var x23 uint64
  var x24 uint64
  x24, x23 = bits.Mul64((arg1[1]), x6)
  var x25 uint64
  var x26 uint64
  x26, x25 = bits.Mul64((arg1[1]), x7)
  var x27 uint64
  var x28 uint64
  x28, x27 = bits.Mul64((arg1[1]), (arg1[1]))
  var x29 uint64
  var x30 uint64
  x30, x29 = bits.Mul64((arg1[0]), x3)
  var x31 uint64
  var x32 uint64
  x32, x31 = bits.Mul64((arg1[0]), x6)
  var x33 uint64
  var x34 uint64
  x34, x33 = bits.Mul64((arg1[0]), x7)
  var x35 uint64
  var x36 uint64
  x36, x35 = bits.Mul64((arg1[0]), x8)
  var x37 uint64
  var x38 uint64
  x38, x37 = bits.Mul64((arg1[0]), (arg1[0]))
  var x39 uint64
  var x40 fiat_25519_uint1
  x39, x40 = fiat_25519_addcarryx_u64(x21, x17, 0x0)
  var x41 uint64
  x41, _ = fiat_25519_addcarryx_u64(x22, x18, x40)
  var x43 uint64
  var x44 fiat_25519_uint1
  x43, x44 = fiat_25519_addcarryx_u64(x37, x39, 0x0)
  var x45 uint64
  x45, _ = fiat_25519_addcarryx_u64(x38, x41, x44)
  var x47 uint64 = ((x43 >> 51) | ((x45 << 13) & 0xffffffffffffffff))
  var x48 uint64 = (x43 & 0x7ffffffffffff)
  var x49 uint64
  var x50 fiat_25519_uint1
  x49, x50 = fiat_25519_addcarryx_u64(x23, x19, 0x0)
  var x51 uint64
  x51, _ = fiat_25519_addcarryx_u64(x24, x20, x50)
  var x53 uint64
  var x54 fiat_25519_uint1
  x53, x54 = fiat_25519_addcarryx_u64(x29, x49, 0x0)
  var x55 uint64
  x55, _ = fiat_25519_addcarryx_u64(x30, x51, x54)
  var x57 uint64
  var x58 fiat_25519_uint1
  x57, x58 = fiat_25519_addcarryx_u64(x25, x9, 0x0)
  var x59 uint64
  x59, _ = fiat_25519_addcarryx_u64(x26, x10, x58)
  var x61 uint64
  var x62 fiat_25519_uint1
  x61, x62 = fiat_25519_addcarryx_u64(x31, x57, 0x0)
  var x63 uint64
  x63, _ = fiat_25519_addcarryx_u64(x32, x59, x62)
  var x65 uint64
  var x66 fiat_25519_uint1
  x65, x66 = fiat_25519_addcarryx_u64(x27, x11, 0x0)
  var x67 uint64
  x67, _ = fiat_25519_addcarryx_u64(x28, x12, x66)
  var x69 uint64
  var x70 fiat_25519_uint1
  x69, x70 = fiat_25519_addcarryx_u64(x33, x65, 0x0)
  var x71 uint64
  x71, _ = fiat_25519_addcarryx_u64(x34, x67, x70)
  var x73 uint64
  var x74 fiat_25519_uint1
  x73, x74 = fiat_25519_addcarryx_u64(x15, x13, 0x0)
  var x75 uint64
  x75, _ = fiat_25519_addcarryx_u64(x16, x14, x74)
  var x77 uint64
  var x78 fiat_25519_uint1
  x77, x78 = fiat_25519_addcarryx_u64(x35, x73, 0x0)
  var x79 uint64
  x79, _ = fiat_25519_addcarryx_u64(x36, x75, x78)
  var x81 uint64
  var x82 fiat_25519_uint1
  x81, x82 = fiat_25519_addcarryx_u64(x47, x77, 0x0)
  var x83 uint64 = (uint64(x82) + x79)
  var x84 uint64 = ((x81 >> 51) | ((x83 << 13) & 0xffffffffffffffff))
  var x85 uint64 = (x81 & 0x7ffffffffffff)
  var x86 uint64
  var x87 fiat_25519_uint1
  x86, x87 = fiat_25519_addcarryx_u64(x84, x69, 0x0)
  var x88 uint64 = (uint64(x87) + x71)
  var x89 uint64 = ((x86 >> 51) | ((x88 << 13) & 0xffffffffffffffff))
  var x90 uint64 = (x86 & 0x7ffffffffffff)
  var x91 uint64
  var x92 fiat_25519_uint1
  x91, x92 = fiat_25519_addcarryx_u64(x89, x61, 0x0)
  var x93 uint64 = (uint64(x92) + x63)
  var x94 uint64 = ((x91 >> 51) | ((x93 << 13) & 0xffffffffffffffff))
  var x95 uint64 = (x91 & 0x7ffffffffffff)
  var x96 uint64
  var x97 fiat_25519_uint1
  x96, x97 = fiat_25519_addcarryx_u64(x94, x53, 0x0)
  var x98 uint64 = (uint64(x97) + x55)
  var x99 uint64 = ((x96 >> 51) | ((x98 << 13) & 0xffffffffffffffff))
  var x100 uint64 = (x96 & 0x7ffffffffffff)
  var x101 uint64 = (x99 * 0x13)
  var x102 uint64 = (x48 + x101)
  var x103 uint64 = (x102 >> 51)
  var x104 uint64 = (x102 & 0x7ffffffffffff)
  var x105 uint64 = (x103 + x85)
  var x106 fiat_25519_uint1 = fiat_25519_uint1((x105 >> 51))
  var x107 uint64 = (x105 & 0x7ffffffffffff)
  var x108 uint64 = (uint64(x106) + x90)
  out1[0] = x104
  out1[1] = x107
  out1[2] = x108
  out1[3] = x95
  out1[4] = x100
}

/*
 * The function fiat_25519_carry reduces a field element.
 * Postconditions:
 *   eval out1 mod m = eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
/*inline*/
func fiat_25519_carry(out1 *[5]uint64, arg1 *[5]uint64) {
  var x1 uint64 = (arg1[0])
  var x2 uint64 = ((x1 >> 51) + (arg1[1]))
  var x3 uint64 = ((x2 >> 51) + (arg1[2]))
  var x4 uint64 = ((x3 >> 51) + (arg1[3]))
  var x5 uint64 = ((x4 >> 51) + (arg1[4]))
  var x6 uint64 = ((x1 & 0x7ffffffffffff) + ((x5 >> 51) * 0x13))
  var x7 uint64 = (uint64(fiat_25519_uint1((x6 >> 51))) + (x2 & 0x7ffffffffffff))
  var x8 uint64 = (x6 & 0x7ffffffffffff)
  var x9 uint64 = (x7 & 0x7ffffffffffff)
  var x10 uint64 = (uint64(fiat_25519_uint1((x7 >> 51))) + (x3 & 0x7ffffffffffff))
  var x11 uint64 = (x4 & 0x7ffffffffffff)
  var x12 uint64 = (x5 & 0x7ffffffffffff)
  out1[0] = x8
  out1[1] = x9
  out1[2] = x10
  out1[3] = x11
  out1[4] = x12
}

/*
 * The function fiat_25519_add adds two field elements.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 + eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 *   arg2: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 */
/*inline*/
func fiat_25519_add(out1 *[5]uint64, arg1 *[5]uint64, arg2 *[5]uint64) {
  var x1 uint64 = ((arg1[0]) + (arg2[0]))
  var x2 uint64 = ((arg1[1]) + (arg2[1]))
  var x3 uint64 = ((arg1[2]) + (arg2[2]))
  var x4 uint64 = ((arg1[3]) + (arg2[3]))
  var x5 uint64 = ((arg1[4]) + (arg2[4]))
  out1[0] = x1
  out1[1] = x2
  out1[2] = x3
  out1[3] = x4
  out1[4] = x5
}

/*
 * The function fiat_25519_sub subtracts two field elements.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 - eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 *   arg2: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 */
/*inline*/
func fiat_25519_sub(out1 *[5]uint64, arg1 *[5]uint64, arg2 *[5]uint64) {
  var x1 uint64 = ((0xfffffffffffda + (arg1[0])) - (arg2[0]))
  var x2 uint64 = ((0xffffffffffffe + (arg1[1])) - (arg2[1]))
  var x3 uint64 = ((0xffffffffffffe + (arg1[2])) - (arg2[2]))
  var x4 uint64 = ((0xffffffffffffe + (arg1[3])) - (arg2[3]))
  var x5 uint64 = ((0xffffffffffffe + (arg1[4])) - (arg2[4]))
  out1[0] = x1
  out1[1] = x2
  out1[2] = x3
  out1[3] = x4
  out1[4] = x5
}

/*
 * The function fiat_25519_opp negates a field element.
 * Postconditions:
 *   eval out1 mod m = -eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 */
/*inline*/
func fiat_25519_opp(out1 *[5]uint64, arg1 *[5]uint64) {
  var x1 uint64 = (0xfffffffffffda - (arg1[0]))
  var x2 uint64 = (0xffffffffffffe - (arg1[1]))
  var x3 uint64 = (0xffffffffffffe - (arg1[2]))
  var x4 uint64 = (0xffffffffffffe - (arg1[3]))
  var x5 uint64 = (0xffffffffffffe - (arg1[4]))
  out1[0] = x1
  out1[1] = x2
  out1[2] = x3
  out1[3] = x4
  out1[4] = x5
}

/*
 * The function fiat_25519_selectznz is a multi-limb conditional select.
 * Postconditions:
 *   eval out1 = (if arg1 = 0 then eval arg2 else eval arg3)
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */
/*inline*/
func fiat_25519_selectznz(out1 *[5]uint64, arg1 fiat_25519_uint1, arg2 *[5]uint64, arg3 *[5]uint64) {
  var x1 uint64
  fiat_25519_cmovznz_u64(&x1, arg1, (arg2[0]), (arg3[0]))
  var x2 uint64
  fiat_25519_cmovznz_u64(&x2, arg1, (arg2[1]), (arg3[1]))
  var x3 uint64
  fiat_25519_cmovznz_u64(&x3, arg1, (arg2[2]), (arg3[2]))
  var x4 uint64
  fiat_25519_cmovznz_u64(&x4, arg1, (arg2[3]), (arg3[3]))
  var x5 uint64
  fiat_25519_cmovznz_u64(&x5, arg1, (arg2[4]), (arg3[4]))
  out1[0] = x1
  out1[1] = x2
  out1[2] = x3
  out1[3] = x4
  out1[4] = x5
}

/*
 * The function fiat_25519_to_bytes serializes a field element to bytes in little-endian order.
 * Postconditions:
 *   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..31]
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x7f]]
 */
/*inline*/
func fiat_25519_to_bytes(out1 *[32]uint8, arg1 *[5]uint64) {
  var x1 uint64
  var x2 fiat_25519_uint1
  fiat_25519_subborrowx_u51(&x1, &x2, 0x0, (arg1[0]), 0x7ffffffffffed)
  var x3 uint64
  var x4 fiat_25519_uint1
  fiat_25519_subborrowx_u51(&x3, &x4, x2, (arg1[1]), 0x7ffffffffffff)
  var x5 uint64
  var x6 fiat_25519_uint1
  fiat_25519_subborrowx_u51(&x5, &x6, x4, (arg1[2]), 0x7ffffffffffff)
  var x7 uint64
  var x8 fiat_25519_uint1
  fiat_25519_subborrowx_u51(&x7, &x8, x6, (arg1[3]), 0x7ffffffffffff)
  var x9 uint64
  var x10 fiat_25519_uint1
  fiat_25519_subborrowx_u51(&x9, &x10, x8, (arg1[4]), 0x7ffffffffffff)
  var x11 uint64
  fiat_25519_cmovznz_u64(&x11, x10, uint64(0x0), 0xffffffffffffffff)
  var x12 uint64
  var x13 fiat_25519_uint1
  fiat_25519_addcarryx_u51(&x12, &x13, 0x0, x1, (x11 & 0x7ffffffffffed))
  var x14 uint64
  var x15 fiat_25519_uint1
  fiat_25519_addcarryx_u51(&x14, &x15, x13, x3, (x11 & 0x7ffffffffffff))
  var x16 uint64
  var x17 fiat_25519_uint1
  fiat_25519_addcarryx_u51(&x16, &x17, x15, x5, (x11 & 0x7ffffffffffff))
  var x18 uint64
  var x19 fiat_25519_uint1
  fiat_25519_addcarryx_u51(&x18, &x19, x17, x7, (x11 & 0x7ffffffffffff))
  var x20 uint64
  var x21 fiat_25519_uint1
  fiat_25519_addcarryx_u51(&x20, &x21, x19, x9, (x11 & 0x7ffffffffffff))
  var x22 uint64 = (x20 << 4)
  var x23 uint64 = (x18 * uint64(0x2))
  var x24 uint64 = (x16 << 6)
  var x25 uint64 = (x14 << 3)
  var x26 uint8 = (uint8(x12) & 0xff)
  var x27 uint64 = (x12 >> 8)
  var x28 uint8 = (uint8(x27) & 0xff)
  var x29 uint64 = (x27 >> 8)
  var x30 uint8 = (uint8(x29) & 0xff)
  var x31 uint64 = (x29 >> 8)
  var x32 uint8 = (uint8(x31) & 0xff)
  var x33 uint64 = (x31 >> 8)
  var x34 uint8 = (uint8(x33) & 0xff)
  var x35 uint64 = (x33 >> 8)
  var x36 uint8 = (uint8(x35) & 0xff)
  var x37 uint8 = uint8((x35 >> 8))
  var x38 uint64 = (x25 + uint64(x37))
  var x39 uint8 = (uint8(x38) & 0xff)
  var x40 uint64 = (x38 >> 8)
  var x41 uint8 = (uint8(x40) & 0xff)
  var x42 uint64 = (x40 >> 8)
  var x43 uint8 = (uint8(x42) & 0xff)
  var x44 uint64 = (x42 >> 8)
  var x45 uint8 = (uint8(x44) & 0xff)
  var x46 uint64 = (x44 >> 8)
  var x47 uint8 = (uint8(x46) & 0xff)
  var x48 uint64 = (x46 >> 8)
  var x49 uint8 = (uint8(x48) & 0xff)
  var x50 uint8 = uint8((x48 >> 8))
  var x51 uint64 = (x24 + uint64(x50))
  var x52 uint8 = (uint8(x51) & 0xff)
  var x53 uint64 = (x51 >> 8)
  var x54 uint8 = (uint8(x53) & 0xff)
  var x55 uint64 = (x53 >> 8)
  var x56 uint8 = (uint8(x55) & 0xff)
  var x57 uint64 = (x55 >> 8)
  var x58 uint8 = (uint8(x57) & 0xff)
  var x59 uint64 = (x57 >> 8)
  var x60 uint8 = (uint8(x59) & 0xff)
  var x61 uint64 = (x59 >> 8)
  var x62 uint8 = (uint8(x61) & 0xff)
  var x63 uint64 = (x61 >> 8)
  var x64 uint8 = (uint8(x63) & 0xff)
  var x65 fiat_25519_uint1 = fiat_25519_uint1((x63 >> 8))
  var x66 uint64 = (x23 + uint64(x65))
  var x67 uint8 = (uint8(x66) & 0xff)
  var x68 uint64 = (x66 >> 8)
  var x69 uint8 = (uint8(x68) & 0xff)
  var x70 uint64 = (x68 >> 8)
  var x71 uint8 = (uint8(x70) & 0xff)
  var x72 uint64 = (x70 >> 8)
  var x73 uint8 = (uint8(x72) & 0xff)
  var x74 uint64 = (x72 >> 8)
  var x75 uint8 = (uint8(x74) & 0xff)
  var x76 uint64 = (x74 >> 8)
  var x77 uint8 = (uint8(x76) & 0xff)
  var x78 uint8 = uint8((x76 >> 8))
  var x79 uint64 = (x22 + uint64(x78))
  var x80 uint8 = (uint8(x79) & 0xff)
  var x81 uint64 = (x79 >> 8)
  var x82 uint8 = (uint8(x81) & 0xff)
  var x83 uint64 = (x81 >> 8)
  var x84 uint8 = (uint8(x83) & 0xff)
  var x85 uint64 = (x83 >> 8)
  var x86 uint8 = (uint8(x85) & 0xff)
  var x87 uint64 = (x85 >> 8)
  var x88 uint8 = (uint8(x87) & 0xff)
  var x89 uint64 = (x87 >> 8)
  var x90 uint8 = (uint8(x89) & 0xff)
  var x91 uint8 = uint8((x89 >> 8))
  out1[0] = x26
  out1[1] = x28
  out1[2] = x30
  out1[3] = x32
  out1[4] = x34
  out1[5] = x36
  out1[6] = x39
  out1[7] = x41
  out1[8] = x43
  out1[9] = x45
  out1[10] = x47
  out1[11] = x49
  out1[12] = x52
  out1[13] = x54
  out1[14] = x56
  out1[15] = x58
  out1[16] = x60
  out1[17] = x62
  out1[18] = x64
  out1[19] = x67
  out1[20] = x69
  out1[21] = x71
  out1[22] = x73
  out1[23] = x75
  out1[24] = x77
  out1[25] = x80
  out1[26] = x82
  out1[27] = x84
  out1[28] = x86
  out1[29] = x88
  out1[30] = x90
  out1[31] = x91
}

/*
 * The function fiat_25519_from_bytes deserializes a field element from bytes in little-endian order.
 * Postconditions:
 *   eval out1 mod m = bytes_eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x7f]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
/*inline*/
func fiat_25519_from_bytes(out1 *[5]uint64, arg1 *[32]uint8) {
  var x1 uint64 = (uint64((arg1[31])) << 44)
  var x2 uint64 = (uint64((arg1[30])) << 36)
  var x3 uint64 = (uint64((arg1[29])) << 28)
  var x4 uint64 = (uint64((arg1[28])) << 20)
  var x5 uint64 = (uint64((arg1[27])) << 12)
  var x6 uint64 = (uint64((arg1[26])) << 4)
  var x7 uint64 = (uint64((arg1[25])) << 47)
  var x8 uint64 = (uint64((arg1[24])) << 39)
  var x9 uint64 = (uint64((arg1[23])) << 31)
  var x10 uint64 = (uint64((arg1[22])) << 23)
  var x11 uint64 = (uint64((arg1[21])) << 15)
  var x12 uint64 = (uint64((arg1[20])) << 7)
  var x13 uint64 = (uint64((arg1[19])) << 50)
  var x14 uint64 = (uint64((arg1[18])) << 42)
  var x15 uint64 = (uint64((arg1[17])) << 34)
  var x16 uint64 = (uint64((arg1[16])) << 26)
  var x17 uint64 = (uint64((arg1[15])) << 18)
  var x18 uint64 = (uint64((arg1[14])) << 10)
  var x19 uint64 = (uint64((arg1[13])) << 2)
  var x20 uint64 = (uint64((arg1[12])) << 45)
  var x21 uint64 = (uint64((arg1[11])) << 37)
  var x22 uint64 = (uint64((arg1[10])) << 29)
  var x23 uint64 = (uint64((arg1[9])) << 21)
  var x24 uint64 = (uint64((arg1[8])) << 13)
  var x25 uint64 = (uint64((arg1[7])) << 5)
  var x26 uint64 = (uint64((arg1[6])) << 48)
  var x27 uint64 = (uint64((arg1[5])) << 40)
  var x28 uint64 = (uint64((arg1[4])) << 32)
  var x29 uint64 = (uint64((arg1[3])) << 24)
  var x30 uint64 = (uint64((arg1[2])) << 16)
  var x31 uint64 = (uint64((arg1[1])) << 8)
  var x32 uint8 = (arg1[0])
  var x33 uint64 = (x31 + uint64(x32))
  var x34 uint64 = (x30 + x33)
  var x35 uint64 = (x29 + x34)
  var x36 uint64 = (x28 + x35)
  var x37 uint64 = (x27 + x36)
  var x38 uint64 = (x26 + x37)
  var x39 uint64 = (x38 & 0x7ffffffffffff)
  var x40 uint8 = uint8((x38 >> 51))
  var x41 uint64 = (x25 + uint64(x40))
  var x42 uint64 = (x24 + x41)
  var x43 uint64 = (x23 + x42)
  var x44 uint64 = (x22 + x43)
  var x45 uint64 = (x21 + x44)
  var x46 uint64 = (x20 + x45)
  var x47 uint64 = (x46 & 0x7ffffffffffff)
  var x48 uint8 = uint8((x46 >> 51))
  var x49 uint64 = (x19 + uint64(x48))
  var x50 uint64 = (x18 + x49)
  var x51 uint64 = (x17 + x50)
  var x52 uint64 = (x16 + x51)
  var x53 uint64 = (x15 + x52)
  var x54 uint64 = (x14 + x53)
  var x55 uint64 = (x13 + x54)
  var x56 uint64 = (x55 & 0x7ffffffffffff)
  var x57 uint8 = uint8((x55 >> 51))
  var x58 uint64 = (x12 + uint64(x57))
  var x59 uint64 = (x11 + x58)
  var x60 uint64 = (x10 + x59)
  var x61 uint64 = (x9 + x60)
  var x62 uint64 = (x8 + x61)
  var x63 uint64 = (x7 + x62)
  var x64 uint64 = (x63 & 0x7ffffffffffff)
  var x65 uint8 = uint8((x63 >> 51))
  var x66 uint64 = (x6 + uint64(x65))
  var x67 uint64 = (x5 + x66)
  var x68 uint64 = (x4 + x67)
  var x69 uint64 = (x3 + x68)
  var x70 uint64 = (x2 + x69)
  var x71 uint64 = (x1 + x70)
  out1[0] = x39
  out1[1] = x47
  out1[2] = x56
  out1[3] = x64
  out1[4] = x71
}

/*
 * The function fiat_25519_carry_scmul_121666 multiplies a field element by 121666 and reduces the result.
 * Postconditions:
 *   eval out1 mod m = (121666 * eval arg1) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
/*inline*/
func fiat_25519_carry_scmul_121666(out1 *[5]uint64, arg1 *[5]uint64) {
  var x1 uint64
  var x2 uint64
  x2, x1 = bits.Mul64(0x1db42, (arg1[4]))
  var x3 uint64
  var x4 uint64
  x4, x3 = bits.Mul64(0x1db42, (arg1[3]))
  var x5 uint64
  var x6 uint64
  x6, x5 = bits.Mul64(0x1db42, (arg1[2]))
  var x7 uint64
  var x8 uint64
  x8, x7 = bits.Mul64(0x1db42, (arg1[1]))
  var x9 uint64
  var x10 uint64
  x10, x9 = bits.Mul64(0x1db42, (arg1[0]))
  var x11 uint64 = ((x9 >> 51) | ((x10 << 13) & 0xffffffffffffffff))
  var x12 uint64 = (x9 & 0x7ffffffffffff)
  var x13 uint64
  var x14 fiat_25519_uint1
  x13, x14 = fiat_25519_addcarryx_u64(x11, x7, 0x0)
  var x15 uint64 = (uint64(x14) + x8)
  var x16 uint64 = ((x13 >> 51) | ((x15 << 13) & 0xffffffffffffffff))
  var x17 uint64 = (x13 & 0x7ffffffffffff)
  var x18 uint64
  var x19 fiat_25519_uint1
  x18, x19 = fiat_25519_addcarryx_u64(x16, x5, 0x0)
  var x20 uint64 = (uint64(x19) + x6)
  var x21 uint64 = ((x18 >> 51) | ((x20 << 13) & 0xffffffffffffffff))
  var x22 uint64 = (x18 & 0x7ffffffffffff)
  var x23 uint64
  var x24 fiat_25519_uint1
  x23, x24 = fiat_25519_addcarryx_u64(x21, x3, 0x0)
  var x25 uint64 = (uint64(x24) + x4)
  var x26 uint64 = ((x23 >> 51) | ((x25 << 13) & 0xffffffffffffffff))
  var x27 uint64 = (x23 & 0x7ffffffffffff)
  var x28 uint64
  var x29 fiat_25519_uint1
  x28, x29 = fiat_25519_addcarryx_u64(x26, x1, 0x0)
  var x30 uint64 = (uint64(x29) + x2)
  var x31 uint64 = ((x28 >> 51) | ((x30 << 13) & 0xffffffffffffffff))
  var x32 uint64 = (x28 & 0x7ffffffffffff)
  var x33 uint64 = (x31 * 0x13)
  var x34 uint64 = (x12 + x33)
  var x35 fiat_25519_uint1 = fiat_25519_uint1((x34 >> 51))
  var x36 uint64 = (x34 & 0x7ffffffffffff)
  var x37 uint64 = (uint64(x35) + x17)
  var x38 fiat_25519_uint1 = fiat_25519_uint1((x37 >> 51))
  var x39 uint64 = (x37 & 0x7ffffffffffff)
  var x40 uint64 = (uint64(x38) + x22)
  out1[0] = x36
  out1[1] = x39
  out1[2] = x40
  out1[3] = x27
  out1[4] = x32
}

