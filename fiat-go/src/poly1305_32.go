/* Autogenerated: src/ExtractionOCaml/unsaturated_solinas --lang=Go --cmovznz-by-mul --widen-carry --widen-bytes poly1305 5 '2^130 - 5' 32 carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes */
/* curve description: poly1305 */
/* requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes */
/* n = 5 (from "5") */
/* s-c = 2^130 - [(1, 5)] (from "2^130 - 5") */
/* machine_wordsize = 32 (from "32") */

/* Computed values: */
/* carry_chain = [0, 1, 2, 3, 4, 0, 1] */

package fiat_poly1305



/*
 * The function fiat_poly1305_addcarryx_u26 is an addition with carry.
 * Postconditions:
 *   out1 = (arg1 + arg2 + arg3) mod 2^26
 *   out2 = ⌊(arg1 + arg2 + arg3) / 2^26⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x3ffffff]
 *   arg3: [0x0 ~> 0x3ffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x3ffffff]
 *   out2: [0x0 ~> 0x1]
 */
/*inline*/
func fiat_poly1305_addcarryx_u26(out1 *uint32, out2 *uint32, arg1 uint32, arg2 uint32, arg3 uint32) {
  var x1 uint32 = ((arg1 + arg2) + arg3)
  var x2 uint32 = (x1 & 0x3ffffff)
  var x3 uint32 = (x1 >> 26)
  *out1 = x2
  *out2 = x3
}

/*
 * The function fiat_poly1305_subborrowx_u26 is a subtraction with borrow.
 * Postconditions:
 *   out1 = (-arg1 + arg2 + -arg3) mod 2^26
 *   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^26⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x3ffffff]
 *   arg3: [0x0 ~> 0x3ffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x3ffffff]
 *   out2: [0x0 ~> 0x1]
 */
/*inline*/
func fiat_poly1305_subborrowx_u26(out1 *uint32, out2 *uint32, arg1 uint32, arg2 uint32, arg3 uint32) {
  var x1 int32 = ((int32(arg2) - int32(arg1)) - int32(arg3))
  var x2 int32 = (x1 >> 26)
  var x3 uint32 = (uint32(x1) & 0x3ffffff)
  *out1 = x3
  *out2 = (uint32(0x0) - uint32(x2))
}

/*
 * The function fiat_poly1305_cmovznz_u32 is a single-word conditional move.
 * Postconditions:
 *   out1 = (if arg1 = 0 then arg2 else arg3)
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0xffffffff]
 *   arg3: [0x0 ~> 0xffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xffffffff]
 */
/*inline*/
func fiat_poly1305_cmovznz_u32(out1 *uint32, arg1 uint32, arg2 uint32, arg3 uint32) {
  var x1 uint32 = (arg1 * 0xffffffff)
  var x2 uint32 = ((x1 & arg3) | ((^x1) & arg2))
  *out1 = x2
}

/*
 * The function fiat_poly1305_carry_mul multiplies two field elements and reduces the result.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 * eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 *   arg2: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 */
/*inline*/
func fiat_poly1305_carry_mul(out1 *[5]uint32, arg1 *[5]uint32, arg2 *[5]uint32) {
  var x1 uint64 = (uint64((arg1[4])) * uint64(((arg2[4]) * 0x5)))
  var x2 uint64 = (uint64((arg1[4])) * uint64(((arg2[3]) * 0x5)))
  var x3 uint64 = (uint64((arg1[4])) * uint64(((arg2[2]) * 0x5)))
  var x4 uint64 = (uint64((arg1[4])) * uint64(((arg2[1]) * 0x5)))
  var x5 uint64 = (uint64((arg1[3])) * uint64(((arg2[4]) * 0x5)))
  var x6 uint64 = (uint64((arg1[3])) * uint64(((arg2[3]) * 0x5)))
  var x7 uint64 = (uint64((arg1[3])) * uint64(((arg2[2]) * 0x5)))
  var x8 uint64 = (uint64((arg1[2])) * uint64(((arg2[4]) * 0x5)))
  var x9 uint64 = (uint64((arg1[2])) * uint64(((arg2[3]) * 0x5)))
  var x10 uint64 = (uint64((arg1[1])) * uint64(((arg2[4]) * 0x5)))
  var x11 uint64 = (uint64((arg1[4])) * uint64((arg2[0])))
  var x12 uint64 = (uint64((arg1[3])) * uint64((arg2[1])))
  var x13 uint64 = (uint64((arg1[3])) * uint64((arg2[0])))
  var x14 uint64 = (uint64((arg1[2])) * uint64((arg2[2])))
  var x15 uint64 = (uint64((arg1[2])) * uint64((arg2[1])))
  var x16 uint64 = (uint64((arg1[2])) * uint64((arg2[0])))
  var x17 uint64 = (uint64((arg1[1])) * uint64((arg2[3])))
  var x18 uint64 = (uint64((arg1[1])) * uint64((arg2[2])))
  var x19 uint64 = (uint64((arg1[1])) * uint64((arg2[1])))
  var x20 uint64 = (uint64((arg1[1])) * uint64((arg2[0])))
  var x21 uint64 = (uint64((arg1[0])) * uint64((arg2[4])))
  var x22 uint64 = (uint64((arg1[0])) * uint64((arg2[3])))
  var x23 uint64 = (uint64((arg1[0])) * uint64((arg2[2])))
  var x24 uint64 = (uint64((arg1[0])) * uint64((arg2[1])))
  var x25 uint64 = (uint64((arg1[0])) * uint64((arg2[0])))
  var x26 uint64 = (x25 + (x10 + (x9 + (x7 + x4))))
  var x27 uint64 = (x26 >> 26)
  var x28 uint32 = (uint32(x26) & 0x3ffffff)
  var x29 uint64 = (x21 + (x17 + (x14 + (x12 + x11))))
  var x30 uint64 = (x22 + (x18 + (x15 + (x13 + x1))))
  var x31 uint64 = (x23 + (x19 + (x16 + (x5 + x2))))
  var x32 uint64 = (x24 + (x20 + (x8 + (x6 + x3))))
  var x33 uint64 = (x27 + x32)
  var x34 uint64 = (x33 >> 26)
  var x35 uint32 = (uint32(x33) & 0x3ffffff)
  var x36 uint64 = (x34 + x31)
  var x37 uint64 = (x36 >> 26)
  var x38 uint32 = (uint32(x36) & 0x3ffffff)
  var x39 uint64 = (x37 + x30)
  var x40 uint64 = (x39 >> 26)
  var x41 uint32 = (uint32(x39) & 0x3ffffff)
  var x42 uint64 = (x40 + x29)
  var x43 uint32 = uint32((x42 >> 26))
  var x44 uint32 = (uint32(x42) & 0x3ffffff)
  var x45 uint64 = (uint64(x43) * uint64(0x5))
  var x46 uint64 = (uint64(x28) + x45)
  var x47 uint32 = uint32((x46 >> 26))
  var x48 uint32 = (uint32(x46) & 0x3ffffff)
  var x49 uint32 = (x47 + x35)
  var x50 uint32 = (x49 >> 26)
  var x51 uint32 = (x49 & 0x3ffffff)
  var x52 uint32 = (x50 + x38)
  out1[0] = x48
  out1[1] = x51
  out1[2] = x52
  out1[3] = x41
  out1[4] = x44
}

/*
 * The function fiat_poly1305_carry_square squares a field element and reduces the result.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 * eval arg1) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 */
/*inline*/
func fiat_poly1305_carry_square(out1 *[5]uint32, arg1 *[5]uint32) {
  var x1 uint32 = ((arg1[4]) * 0x5)
  var x2 uint32 = (x1 * 0x2)
  var x3 uint32 = ((arg1[4]) * 0x2)
  var x4 uint32 = ((arg1[3]) * 0x5)
  var x5 uint32 = (x4 * 0x2)
  var x6 uint32 = ((arg1[3]) * 0x2)
  var x7 uint32 = ((arg1[2]) * 0x2)
  var x8 uint32 = ((arg1[1]) * 0x2)
  var x9 uint64 = (uint64((arg1[4])) * uint64(x1))
  var x10 uint64 = (uint64((arg1[3])) * uint64(x2))
  var x11 uint64 = (uint64((arg1[3])) * uint64(x4))
  var x12 uint64 = (uint64((arg1[2])) * uint64(x2))
  var x13 uint64 = (uint64((arg1[2])) * uint64(x5))
  var x14 uint64 = (uint64((arg1[2])) * uint64((arg1[2])))
  var x15 uint64 = (uint64((arg1[1])) * uint64(x2))
  var x16 uint64 = (uint64((arg1[1])) * uint64(x6))
  var x17 uint64 = (uint64((arg1[1])) * uint64(x7))
  var x18 uint64 = (uint64((arg1[1])) * uint64((arg1[1])))
  var x19 uint64 = (uint64((arg1[0])) * uint64(x3))
  var x20 uint64 = (uint64((arg1[0])) * uint64(x6))
  var x21 uint64 = (uint64((arg1[0])) * uint64(x7))
  var x22 uint64 = (uint64((arg1[0])) * uint64(x8))
  var x23 uint64 = (uint64((arg1[0])) * uint64((arg1[0])))
  var x24 uint64 = (x23 + (x15 + x13))
  var x25 uint64 = (x24 >> 26)
  var x26 uint32 = (uint32(x24) & 0x3ffffff)
  var x27 uint64 = (x19 + (x16 + x14))
  var x28 uint64 = (x20 + (x17 + x9))
  var x29 uint64 = (x21 + (x18 + x10))
  var x30 uint64 = (x22 + (x12 + x11))
  var x31 uint64 = (x25 + x30)
  var x32 uint64 = (x31 >> 26)
  var x33 uint32 = (uint32(x31) & 0x3ffffff)
  var x34 uint64 = (x32 + x29)
  var x35 uint64 = (x34 >> 26)
  var x36 uint32 = (uint32(x34) & 0x3ffffff)
  var x37 uint64 = (x35 + x28)
  var x38 uint64 = (x37 >> 26)
  var x39 uint32 = (uint32(x37) & 0x3ffffff)
  var x40 uint64 = (x38 + x27)
  var x41 uint32 = uint32((x40 >> 26))
  var x42 uint32 = (uint32(x40) & 0x3ffffff)
  var x43 uint64 = (uint64(x41) * uint64(0x5))
  var x44 uint64 = (uint64(x26) + x43)
  var x45 uint32 = uint32((x44 >> 26))
  var x46 uint32 = (uint32(x44) & 0x3ffffff)
  var x47 uint32 = (x45 + x33)
  var x48 uint32 = (x47 >> 26)
  var x49 uint32 = (x47 & 0x3ffffff)
  var x50 uint32 = (x48 + x36)
  out1[0] = x46
  out1[1] = x49
  out1[2] = x50
  out1[3] = x39
  out1[4] = x42
}

/*
 * The function fiat_poly1305_carry reduces a field element.
 * Postconditions:
 *   eval out1 mod m = eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 */
/*inline*/
func fiat_poly1305_carry(out1 *[5]uint32, arg1 *[5]uint32) {
  var x1 uint32 = (arg1[0])
  var x2 uint32 = ((x1 >> 26) + (arg1[1]))
  var x3 uint32 = ((x2 >> 26) + (arg1[2]))
  var x4 uint32 = ((x3 >> 26) + (arg1[3]))
  var x5 uint32 = ((x4 >> 26) + (arg1[4]))
  var x6 uint32 = ((x1 & 0x3ffffff) + ((x5 >> 26) * 0x5))
  var x7 uint32 = ((x6 >> 26) + (x2 & 0x3ffffff))
  var x8 uint32 = (x6 & 0x3ffffff)
  var x9 uint32 = (x7 & 0x3ffffff)
  var x10 uint32 = ((x7 >> 26) + (x3 & 0x3ffffff))
  var x11 uint32 = (x4 & 0x3ffffff)
  var x12 uint32 = (x5 & 0x3ffffff)
  out1[0] = x8
  out1[1] = x9
  out1[2] = x10
  out1[3] = x11
  out1[4] = x12
}

/*
 * The function fiat_poly1305_add adds two field elements.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 + eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 *   arg2: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 */
/*inline*/
func fiat_poly1305_add(out1 *[5]uint32, arg1 *[5]uint32, arg2 *[5]uint32) {
  var x1 uint32 = ((arg1[0]) + (arg2[0]))
  var x2 uint32 = ((arg1[1]) + (arg2[1]))
  var x3 uint32 = ((arg1[2]) + (arg2[2]))
  var x4 uint32 = ((arg1[3]) + (arg2[3]))
  var x5 uint32 = ((arg1[4]) + (arg2[4]))
  out1[0] = x1
  out1[1] = x2
  out1[2] = x3
  out1[3] = x4
  out1[4] = x5
}

/*
 * The function fiat_poly1305_sub subtracts two field elements.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 - eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 *   arg2: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 */
/*inline*/
func fiat_poly1305_sub(out1 *[5]uint32, arg1 *[5]uint32, arg2 *[5]uint32) {
  var x1 uint32 = ((0x7fffff6 + (arg1[0])) - (arg2[0]))
  var x2 uint32 = ((0x7fffffe + (arg1[1])) - (arg2[1]))
  var x3 uint32 = ((0x7fffffe + (arg1[2])) - (arg2[2]))
  var x4 uint32 = ((0x7fffffe + (arg1[3])) - (arg2[3]))
  var x5 uint32 = ((0x7fffffe + (arg1[4])) - (arg2[4]))
  out1[0] = x1
  out1[1] = x2
  out1[2] = x3
  out1[3] = x4
  out1[4] = x5
}

/*
 * The function fiat_poly1305_opp negates a field element.
 * Postconditions:
 *   eval out1 mod m = -eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 */
/*inline*/
func fiat_poly1305_opp(out1 *[5]uint32, arg1 *[5]uint32) {
  var x1 uint32 = (0x7fffff6 - (arg1[0]))
  var x2 uint32 = (0x7fffffe - (arg1[1]))
  var x3 uint32 = (0x7fffffe - (arg1[2]))
  var x4 uint32 = (0x7fffffe - (arg1[3]))
  var x5 uint32 = (0x7fffffe - (arg1[4]))
  out1[0] = x1
  out1[1] = x2
  out1[2] = x3
  out1[3] = x4
  out1[4] = x5
}

/*
 * The function fiat_poly1305_selectznz is a multi-limb conditional select.
 * Postconditions:
 *   eval out1 = (if arg1 = 0 then eval arg2 else eval arg3)
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
 *   arg3: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
 */
/*inline*/
func fiat_poly1305_selectznz(out1 *[5]uint32, arg1 uint32, arg2 *[5]uint32, arg3 *[5]uint32) {
  var x1 uint32
  fiat_poly1305_cmovznz_u32(&x1, arg1, (arg2[0]), (arg3[0]))
  var x2 uint32
  fiat_poly1305_cmovznz_u32(&x2, arg1, (arg2[1]), (arg3[1]))
  var x3 uint32
  fiat_poly1305_cmovznz_u32(&x3, arg1, (arg2[2]), (arg3[2]))
  var x4 uint32
  fiat_poly1305_cmovznz_u32(&x4, arg1, (arg2[3]), (arg3[3]))
  var x5 uint32
  fiat_poly1305_cmovznz_u32(&x5, arg1, (arg2[4]), (arg3[4]))
  out1[0] = x1
  out1[1] = x2
  out1[2] = x3
  out1[3] = x4
  out1[4] = x5
}

/*
 * The function fiat_poly1305_to_bytes serializes a field element to bytes in little-endian order.
 * Postconditions:
 *   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..16]
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 */
/*inline*/
func fiat_poly1305_to_bytes(out1 *[17]uint32, arg1 *[5]uint32) {
  var x1 uint32
  var x2 uint32
  fiat_poly1305_subborrowx_u26(&x1, &x2, uint32(0x0), (arg1[0]), 0x3fffffb)
  var x3 uint32
  var x4 uint32
  fiat_poly1305_subborrowx_u26(&x3, &x4, x2, (arg1[1]), 0x3ffffff)
  var x5 uint32
  var x6 uint32
  fiat_poly1305_subborrowx_u26(&x5, &x6, x4, (arg1[2]), 0x3ffffff)
  var x7 uint32
  var x8 uint32
  fiat_poly1305_subborrowx_u26(&x7, &x8, x6, (arg1[3]), 0x3ffffff)
  var x9 uint32
  var x10 uint32
  fiat_poly1305_subborrowx_u26(&x9, &x10, x8, (arg1[4]), 0x3ffffff)
  var x11 uint32
  fiat_poly1305_cmovznz_u32(&x11, x10, uint32(0x0), 0xffffffff)
  var x12 uint32
  var x13 uint32
  fiat_poly1305_addcarryx_u26(&x12, &x13, 0x0, x1, (x11 & 0x3fffffb))
  var x14 uint32
  var x15 uint32
  fiat_poly1305_addcarryx_u26(&x14, &x15, x13, x3, (x11 & 0x3ffffff))
  var x16 uint32
  var x17 uint32
  fiat_poly1305_addcarryx_u26(&x16, &x17, x15, x5, (x11 & 0x3ffffff))
  var x18 uint32
  var x19 uint32
  fiat_poly1305_addcarryx_u26(&x18, &x19, x17, x7, (x11 & 0x3ffffff))
  var x20 uint32
  var x21 uint32
  fiat_poly1305_addcarryx_u26(&x20, &x21, x19, x9, (x11 & 0x3ffffff))
  var x22 uint32 = (x18 << 6)
  var x23 uint32 = (x16 << 4)
  var x24 uint32 = (x14 << 2)
  var x25 uint32 = (x12 >> 8)
  var x26 uint32 = (x12 & 0xff)
  var x27 uint32 = (x25 >> 8)
  var x28 uint32 = (x25 & 0xff)
  var x29 uint32 = (x27 >> 8)
  var x30 uint32 = (x27 & 0xff)
  var x31 uint32 = (x29 + x24)
  var x32 uint32 = (x31 >> 8)
  var x33 uint32 = (x31 & 0xff)
  var x34 uint32 = (x32 >> 8)
  var x35 uint32 = (x32 & 0xff)
  var x36 uint32 = (x34 >> 8)
  var x37 uint32 = (x34 & 0xff)
  var x38 uint32 = (x36 + x23)
  var x39 uint32 = (x38 >> 8)
  var x40 uint32 = (x38 & 0xff)
  var x41 uint32 = (x39 >> 8)
  var x42 uint32 = (x39 & 0xff)
  var x43 uint32 = (x41 >> 8)
  var x44 uint32 = (x41 & 0xff)
  var x45 uint32 = (x43 + x22)
  var x46 uint32 = (x45 >> 8)
  var x47 uint32 = (x45 & 0xff)
  var x48 uint32 = (x46 >> 8)
  var x49 uint32 = (x46 & 0xff)
  var x50 uint32 = (x48 >> 8)
  var x51 uint32 = (x48 & 0xff)
  var x52 uint32 = (x50 & 0xff)
  var x53 uint32 = (x20 >> 8)
  var x54 uint32 = (x20 & 0xff)
  var x55 uint32 = (x53 >> 8)
  var x56 uint32 = (x53 & 0xff)
  var x57 uint32 = (x55 >> 8)
  var x58 uint32 = (x55 & 0xff)
  out1[0] = x26
  out1[1] = x28
  out1[2] = x30
  out1[3] = x33
  out1[4] = x35
  out1[5] = x37
  out1[6] = x40
  out1[7] = x42
  out1[8] = x44
  out1[9] = x47
  out1[10] = x49
  out1[11] = x51
  out1[12] = x52
  out1[13] = x54
  out1[14] = x56
  out1[15] = x58
  out1[16] = x57
}

/*
 * The function fiat_poly1305_from_bytes deserializes a field element from bytes in little-endian order.
 * Postconditions:
 *   eval out1 mod m = bytes_eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 */
/*inline*/
func fiat_poly1305_from_bytes(out1 *[5]uint32, arg1 *[17]uint32) {
  var x1 uint32 = ((arg1[16]) << 24)
  var x2 uint32 = ((arg1[15]) << 16)
  var x3 uint32 = ((arg1[14]) << 8)
  var x4 uint32 = (arg1[13])
  var x5 uint32 = ((arg1[12]) << 18)
  var x6 uint32 = ((arg1[11]) << 10)
  var x7 uint32 = ((arg1[10]) << 2)
  var x8 uint32 = ((arg1[9]) << 20)
  var x9 uint32 = ((arg1[8]) << 12)
  var x10 uint32 = ((arg1[7]) << 4)
  var x11 uint32 = ((arg1[6]) << 22)
  var x12 uint32 = ((arg1[5]) << 14)
  var x13 uint32 = ((arg1[4]) << 6)
  var x14 uint32 = ((arg1[3]) << 24)
  var x15 uint32 = ((arg1[2]) << 16)
  var x16 uint32 = ((arg1[1]) << 8)
  var x17 uint32 = (arg1[0])
  var x18 uint32 = (x17 + (x16 + (x15 + x14)))
  var x19 uint32 = (x18 >> 26)
  var x20 uint32 = (x18 & 0x3ffffff)
  var x21 uint32 = (x4 + (x3 + (x2 + x1)))
  var x22 uint32 = (x7 + (x6 + x5))
  var x23 uint32 = (x10 + (x9 + x8))
  var x24 uint32 = (x13 + (x12 + x11))
  var x25 uint32 = (x19 + x24)
  var x26 uint32 = (x25 >> 26)
  var x27 uint32 = (x25 & 0x3ffffff)
  var x28 uint32 = (x26 + x23)
  var x29 uint32 = (x28 >> 26)
  var x30 uint32 = (x28 & 0x3ffffff)
  var x31 uint32 = (x29 + x22)
  var x32 uint32 = (x31 & 0x3ffffff)
  out1[0] = x20
  out1[1] = x27
  out1[2] = x30
  out1[3] = x32
  out1[4] = x21
}

