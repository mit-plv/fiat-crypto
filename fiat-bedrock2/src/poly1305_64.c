/* Autogenerated: src/ExtractionOCaml/bedrock2_unsaturated_solinas --lang bedrock2 --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select poly1305 64 3 '2^130 - 5' carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes */
/* curve description: poly1305 */
/* machine_wordsize = 64 (from "64") */
/* requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes */
/* n = 3 (from "3") */
/* s-c = 2^130 - [(1, 5)] (from "2^130 - 5") */
/* tight_bounds_multiplier = 1 (from "") */
/*  */
/* Computed values: */
/* carry_chain = [0, 1, 2, 0, 1] */
/* eval z = z[0] + (z[1] << 44) + (z[2] << 87) */
/* bytes_eval z = z[0] + (z[1] << 8) + (z[2] << 16) + (z[3] << 24) + (z[4] << 32) + (z[5] << 40) + (z[6] << 48) + (z[7] << 56) + (z[8] << 64) + (z[9] << 72) + (z[10] << 80) + (z[11] << 88) + (z[12] << 96) + (z[13] << 104) + (z[14] << 112) + (z[15] << 120) + (z[16] << 128) */
/* balance = [0x1ffffffffff6, 0xffffffffffe, 0xffffffffffe] */

#include <stdint.h>
#include <memory.h>

// LITTLE-ENDIAN memory access is REQUIRED
// the following two functions are required to work around -fstrict-aliasing
static inline uintptr_t _br2_load(uintptr_t a, size_t sz) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sz);
  return r;
}

static inline void _br2_store(uintptr_t a, uintptr_t v, size_t sz) {
  memcpy((void*)a, &v, sz);
}



/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x300000000000], [0x0 ~> 0x180000000000], [0x0 ~> 0x180000000000]]
 *   in1: [[0x0 ~> 0x300000000000], [0x0 ~> 0x180000000000], [0x0 ~> 0x180000000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 */
void fiat_poly1305_carry_mul(uintptr_t out0, uintptr_t in0, uintptr_t in1) {
  uintptr_t x2, x1, x5, x4, x0, x3, x8, x10, x25, x11, x26, x9, x24, x22, x29, x23, x30, x27, x31, x28, x12, x14, x35, x15, x36, x13, x34, x18, x39, x19, x40, x37, x6, x16, x43, x17, x44, x7, x42, x20, x47, x21, x48, x45, x46, x32, x51, x49, x52, x50, x38, x53, x56, x41, x57, x55, x58, x33, x60, x61, x62, x54, x64, x65, x59, x63, x66, x67, x68, x69, x70;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  x3 = _br2_load((in1)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x4 = _br2_load((in1)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x5 = _br2_load((in1)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x6 = (x2)*((x5)*((uintptr_t)5ULL));
  x7 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*((x5)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x2)*((x5)*((uintptr_t)5ULL)))>>64;
  x8 = (x2)*((x4)*((uintptr_t)10ULL));
  x9 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*((x4)*((uintptr_t)10ULL)))>>32 : ((__uint128_t)(x2)*((x4)*((uintptr_t)10ULL)))>>64;
  x10 = (x1)*((x5)*((uintptr_t)10ULL));
  x11 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*((x5)*((uintptr_t)10ULL)))>>32 : ((__uint128_t)(x1)*((x5)*((uintptr_t)10ULL)))>>64;
  x12 = (x2)*(x3);
  x13 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x3))>>32 : ((__uint128_t)(x2)*(x3))>>64;
  x14 = (x1)*((x4)*((uintptr_t)2ULL));
  x15 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*((x4)*((uintptr_t)2ULL)))>>32 : ((__uint128_t)(x1)*((x4)*((uintptr_t)2ULL)))>>64;
  x16 = (x1)*(x3);
  x17 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x3))>>32 : ((__uint128_t)(x1)*(x3))>>64;
  x18 = (x0)*(x5);
  x19 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x5))>>32 : ((__uint128_t)(x0)*(x5))>>64;
  x20 = (x0)*(x4);
  x21 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x4))>>32 : ((__uint128_t)(x0)*(x4))>>64;
  x22 = (x0)*(x3);
  x23 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x3))>>32 : ((__uint128_t)(x0)*(x3))>>64;
  x24 = (x10)+(x8);
  x25 = (x24)<(x10);
  x26 = (x25)+(x11);
  x27 = (x26)+(x9);
  x28 = (x22)+(x24);
  x29 = (x28)<(x22);
  x30 = (x29)+(x23);
  x31 = (x30)+(x27);
  x32 = ((x28)>>((uintptr_t)44ULL))|((x31)<<((uintptr_t)20ULL));
  x33 = (x28)&((uintptr_t)17592186044415ULL);
  x34 = (x14)+(x12);
  x35 = (x34)<(x14);
  x36 = (x35)+(x15);
  x37 = (x36)+(x13);
  x38 = (x18)+(x34);
  x39 = (x38)<(x18);
  x40 = (x39)+(x19);
  x41 = (x40)+(x37);
  x42 = (x16)+(x6);
  x43 = (x42)<(x16);
  x44 = (x43)+(x17);
  x45 = (x44)+(x7);
  x46 = (x20)+(x42);
  x47 = (x46)<(x20);
  x48 = (x47)+(x21);
  x49 = (x48)+(x45);
  x50 = (x32)+(x46);
  x51 = (x50)<(x32);
  x52 = (x51)+(x49);
  x53 = ((x50)>>((uintptr_t)43ULL))|((x52)<<((uintptr_t)21ULL));
  x54 = (x50)&((uintptr_t)8796093022207ULL);
  x55 = (x53)+(x38);
  x56 = (x55)<(x53);
  x57 = (x56)+(x41);
  x58 = ((x55)>>((uintptr_t)43ULL))|((x57)<<((uintptr_t)21ULL));
  x59 = (x55)&((uintptr_t)8796093022207ULL);
  x60 = (x58)*((uintptr_t)5ULL);
  x61 = (x33)+(x60);
  x62 = (x61)>>((uintptr_t)44ULL);
  x63 = (x61)&((uintptr_t)17592186044415ULL);
  x64 = (x62)+(x54);
  x65 = (x64)>>((uintptr_t)43ULL);
  x66 = (x64)&((uintptr_t)8796093022207ULL);
  x67 = (x65)+(x59);
  x68 = x63;
  x69 = x66;
  x70 = x67;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x68, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)8ULL), x69, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)16ULL), x70, sizeof(uintptr_t));
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x300000000000], [0x0 ~> 0x180000000000], [0x0 ~> 0x180000000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 */
void fiat_poly1305_carry_square(uintptr_t out0, uintptr_t in0) {
  uintptr_t x2, x3, x4, x1, x5, x6, x0, x9, x17, x20, x18, x21, x10, x22, x19, x11, x13, x26, x14, x27, x12, x7, x15, x30, x16, x31, x8, x29, x23, x34, x32, x35, x33, x25, x36, x39, x28, x40, x38, x41, x24, x43, x44, x45, x37, x47, x48, x42, x46, x49, x50, x51, x52, x53;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x3 = (x2)*((uintptr_t)5ULL);
  x4 = (x3)*((uintptr_t)2ULL);
  x5 = (x2)*((uintptr_t)2ULL);
  x6 = (x1)*((uintptr_t)2ULL);
  x7 = (x2)*(x3);
  x8 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x3))>>32 : ((__uint128_t)(x2)*(x3))>>64;
  x9 = (x1)*((x4)*((uintptr_t)2ULL));
  x10 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*((x4)*((uintptr_t)2ULL)))>>32 : ((__uint128_t)(x1)*((x4)*((uintptr_t)2ULL)))>>64;
  x11 = (x1)*((x1)*((uintptr_t)2ULL));
  x12 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*((x1)*((uintptr_t)2ULL)))>>32 : ((__uint128_t)(x1)*((x1)*((uintptr_t)2ULL)))>>64;
  x13 = (x0)*(x5);
  x14 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x5))>>32 : ((__uint128_t)(x0)*(x5))>>64;
  x15 = (x0)*(x6);
  x16 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x6))>>32 : ((__uint128_t)(x0)*(x6))>>64;
  x17 = (x0)*(x0);
  x18 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x0))>>32 : ((__uint128_t)(x0)*(x0))>>64;
  x19 = (x17)+(x9);
  x20 = (x19)<(x17);
  x21 = (x20)+(x18);
  x22 = (x21)+(x10);
  x23 = ((x19)>>((uintptr_t)44ULL))|((x22)<<((uintptr_t)20ULL));
  x24 = (x19)&((uintptr_t)17592186044415ULL);
  x25 = (x13)+(x11);
  x26 = (x25)<(x13);
  x27 = (x26)+(x14);
  x28 = (x27)+(x12);
  x29 = (x15)+(x7);
  x30 = (x29)<(x15);
  x31 = (x30)+(x16);
  x32 = (x31)+(x8);
  x33 = (x23)+(x29);
  x34 = (x33)<(x23);
  x35 = (x34)+(x32);
  x36 = ((x33)>>((uintptr_t)43ULL))|((x35)<<((uintptr_t)21ULL));
  x37 = (x33)&((uintptr_t)8796093022207ULL);
  x38 = (x36)+(x25);
  x39 = (x38)<(x36);
  x40 = (x39)+(x28);
  x41 = ((x38)>>((uintptr_t)43ULL))|((x40)<<((uintptr_t)21ULL));
  x42 = (x38)&((uintptr_t)8796093022207ULL);
  x43 = (x41)*((uintptr_t)5ULL);
  x44 = (x24)+(x43);
  x45 = (x44)>>((uintptr_t)44ULL);
  x46 = (x44)&((uintptr_t)17592186044415ULL);
  x47 = (x45)+(x37);
  x48 = (x47)>>((uintptr_t)43ULL);
  x49 = (x47)&((uintptr_t)8796093022207ULL);
  x50 = (x48)+(x42);
  x51 = x46;
  x52 = x49;
  x53 = x50;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x51, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)8ULL), x52, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)16ULL), x53, sizeof(uintptr_t));
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x300000000000], [0x0 ~> 0x180000000000], [0x0 ~> 0x180000000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 */
void fiat_poly1305_carry(uintptr_t out0, uintptr_t in0) {
  uintptr_t x0, x1, x2, x3, x4, x6, x7, x5, x8, x9, x10, x11, x12, x13;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x3 = x0;
  x4 = ((x3)>>((uintptr_t)44ULL))+(x1);
  x5 = ((x4)>>((uintptr_t)43ULL))+(x2);
  x6 = ((x3)&((uintptr_t)17592186044415ULL))+(((x5)>>((uintptr_t)43ULL))*((uintptr_t)5ULL));
  x7 = ((x6)>>((uintptr_t)44ULL))+((x4)&((uintptr_t)8796093022207ULL));
  x8 = (x6)&((uintptr_t)17592186044415ULL);
  x9 = (x7)&((uintptr_t)8796093022207ULL);
  x10 = ((x7)>>((uintptr_t)43ULL))+((x5)&((uintptr_t)8796093022207ULL));
  x11 = x8;
  x12 = x9;
  x13 = x10;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x11, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)8ULL), x12, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)16ULL), x13, sizeof(uintptr_t));
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 *   in1: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x300000000000], [0x0 ~> 0x180000000000], [0x0 ~> 0x180000000000]]
 */
void fiat_poly1305_add(uintptr_t out0, uintptr_t in0, uintptr_t in1) {
  uintptr_t x0, x3, x1, x4, x2, x5, x6, x7, x8, x9, x10, x11;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  x3 = _br2_load((in1)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x4 = _br2_load((in1)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x5 = _br2_load((in1)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x6 = (x0)+(x3);
  x7 = (x1)+(x4);
  x8 = (x2)+(x5);
  x9 = x6;
  x10 = x7;
  x11 = x8;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x9, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)8ULL), x10, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)16ULL), x11, sizeof(uintptr_t));
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 *   in1: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x300000000000], [0x0 ~> 0x180000000000], [0x0 ~> 0x180000000000]]
 */
void fiat_poly1305_sub(uintptr_t out0, uintptr_t in0, uintptr_t in1) {
  uintptr_t x0, x3, x1, x4, x2, x5, x6, x7, x8, x9, x10, x11;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  x3 = _br2_load((in1)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x4 = _br2_load((in1)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x5 = _br2_load((in1)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x6 = (((uintptr_t)35184372088822ULL)+(x0))-(x3);
  x7 = (((uintptr_t)17592186044414ULL)+(x1))-(x4);
  x8 = (((uintptr_t)17592186044414ULL)+(x2))-(x5);
  x9 = x6;
  x10 = x7;
  x11 = x8;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x9, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)8ULL), x10, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)16ULL), x11, sizeof(uintptr_t));
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x300000000000], [0x0 ~> 0x180000000000], [0x0 ~> 0x180000000000]]
 */
void fiat_poly1305_opp(uintptr_t out0, uintptr_t in0) {
  uintptr_t x0, x1, x2, x3, x4, x5, x6, x7, x8;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x3 = ((uintptr_t)35184372088822ULL)-(x0);
  x4 = ((uintptr_t)17592186044414ULL)-(x1);
  x5 = ((uintptr_t)17592186044414ULL)-(x2);
  x6 = x3;
  x7 = x4;
  x8 = x5;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x6, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)8ULL), x7, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)16ULL), x8, sizeof(uintptr_t));
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [0x0 ~> 0x1]
 *   in1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   in2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */
void fiat_poly1305_selectznz(uintptr_t out0, uintptr_t in0, uintptr_t in1, uintptr_t in2) {
  uintptr_t x3, x6, x0, x7, x4, x9, x1, x10, x5, x12, x2, x13, x8, x11, x14, x15, x16, x17;
  /*skip*/
  x0 = _br2_load((in1)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x1 = _br2_load((in1)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x2 = _br2_load((in1)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  x3 = _br2_load((in2)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x4 = _br2_load((in2)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x5 = _br2_load((in2)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x6 = ((uintptr_t)-1ULL)+((in0)==((uintptr_t)0ULL));
  x7 = (x6)^((uintptr_t)18446744073709551615ULL);
  x8 = ((x3)&(x6))|((x0)&(x7));
  x9 = ((uintptr_t)-1ULL)+((in0)==((uintptr_t)0ULL));
  x10 = (x9)^((uintptr_t)18446744073709551615ULL);
  x11 = ((x4)&(x9))|((x1)&(x10));
  x12 = ((uintptr_t)-1ULL)+((in0)==((uintptr_t)0ULL));
  x13 = (x12)^((uintptr_t)18446744073709551615ULL);
  x14 = ((x5)&(x12))|((x2)&(x13));
  x15 = x8;
  x16 = x11;
  x17 = x14;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x15, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)8ULL), x16, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)16ULL), x17, sizeof(uintptr_t));
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 */
void fiat_poly1305_to_bytes(uintptr_t out0, uintptr_t in0) {
  uintptr_t x0, x4, x5, x6, x3, x1, x8, x9, x10, x12, x13, x11, x2, x15, x16, x17, x19, x20, x18, x22, x7, x24, x25, x27, x14, x28, x29, x31, x30, x32, x34, x21, x35, x23, x36, x37, x33, x26, x41, x43, x45, x47, x39, x49, x50, x52, x54, x56, x58, x38, x60, x61, x63, x65, x67, x69, x71, x40, x42, x44, x46, x48, x51, x53, x55, x57, x59, x62, x64, x66, x68, x70, x72, x73, x74, x75, x76, x77, x78, x79, x80, x81, x82, x83, x84, x85, x86, x87, x88, x89, x90;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x3 = (x0)-((uintptr_t)17592186044411ULL);
  x4 = (x0)<(x3);
  x5 = (x3)<(x3);
  x6 = (x4)+(x5);
  x7 = (x3)&((uintptr_t)17592186044415ULL);
  x8 = ((x6)<<((uintptr_t)20ULL))-((x3)>>((uintptr_t)44ULL));
  x9 = (x1)-((uintptr_t)8796093022207ULL);
  x10 = (x1)<(x9);
  x11 = (x9)-(x8);
  x12 = (x9)<(x11);
  x13 = (x10)+(x12);
  x14 = (x11)&((uintptr_t)8796093022207ULL);
  x15 = ((x13)<<((uintptr_t)21ULL))-((x11)>>((uintptr_t)43ULL));
  x16 = (x2)-((uintptr_t)8796093022207ULL);
  x17 = (x2)<(x16);
  x18 = (x16)-(x15);
  x19 = (x16)<(x18);
  x20 = (x17)+(x19);
  x21 = (x18)&((uintptr_t)8796093022207ULL);
  x22 = ((x20)<<((uintptr_t)21ULL))-((x18)>>((uintptr_t)43ULL));
  x23 = ((uintptr_t)-1ULL)+((x22)==((uintptr_t)0ULL));
  x24 = (x7)+((x23)&((uintptr_t)17592186044411ULL));
  x25 = (x24)<(x7);
  x26 = (x24)&((uintptr_t)17592186044415ULL);
  x27 = ((x24)>>((uintptr_t)44ULL))+((x25)<<((uintptr_t)20ULL));
  x28 = (x27)+(x14);
  x29 = (x28)<(x14);
  x30 = (x28)+((x23)&((uintptr_t)8796093022207ULL));
  x31 = (x30)<((x23)&((uintptr_t)8796093022207ULL));
  x32 = (x29)+(x31);
  x33 = (x30)&((uintptr_t)8796093022207ULL);
  x34 = ((x30)>>((uintptr_t)43ULL))+((x32)<<((uintptr_t)21ULL));
  x35 = (x34)+(x21);
  x36 = (x35)+((x23)&((uintptr_t)8796093022207ULL));
  x37 = (x36)&((uintptr_t)8796093022207ULL);
  x38 = (x37)<<((uintptr_t)7ULL);
  x39 = (x33)<<((uintptr_t)4ULL);
  x40 = (x26)&((uintptr_t)255ULL);
  x41 = (x26)>>((uintptr_t)8ULL);
  x42 = (x41)&((uintptr_t)255ULL);
  x43 = (x41)>>((uintptr_t)8ULL);
  x44 = (x43)&((uintptr_t)255ULL);
  x45 = (x43)>>((uintptr_t)8ULL);
  x46 = (x45)&((uintptr_t)255ULL);
  x47 = (x45)>>((uintptr_t)8ULL);
  x48 = (x47)&((uintptr_t)255ULL);
  x49 = (x47)>>((uintptr_t)8ULL);
  x50 = (x39)+(x49);
  x51 = (x50)&((uintptr_t)255ULL);
  x52 = (x50)>>((uintptr_t)8ULL);
  x53 = (x52)&((uintptr_t)255ULL);
  x54 = (x52)>>((uintptr_t)8ULL);
  x55 = (x54)&((uintptr_t)255ULL);
  x56 = (x54)>>((uintptr_t)8ULL);
  x57 = (x56)&((uintptr_t)255ULL);
  x58 = (x56)>>((uintptr_t)8ULL);
  x59 = (x58)&((uintptr_t)255ULL);
  x60 = (x58)>>((uintptr_t)8ULL);
  x61 = (x38)+(x60);
  x62 = (x61)&((uintptr_t)255ULL);
  x63 = (x61)>>((uintptr_t)8ULL);
  x64 = (x63)&((uintptr_t)255ULL);
  x65 = (x63)>>((uintptr_t)8ULL);
  x66 = (x65)&((uintptr_t)255ULL);
  x67 = (x65)>>((uintptr_t)8ULL);
  x68 = (x67)&((uintptr_t)255ULL);
  x69 = (x67)>>((uintptr_t)8ULL);
  x70 = (x69)&((uintptr_t)255ULL);
  x71 = (x69)>>((uintptr_t)8ULL);
  x72 = (x71)&((uintptr_t)255ULL);
  x73 = (x71)>>((uintptr_t)8ULL);
  x74 = x40;
  x75 = x42;
  x76 = x44;
  x77 = x46;
  x78 = x48;
  x79 = x51;
  x80 = x53;
  x81 = x55;
  x82 = x57;
  x83 = x59;
  x84 = x62;
  x85 = x64;
  x86 = x66;
  x87 = x68;
  x88 = x70;
  x89 = x72;
  x90 = x73;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x74, 1);
  _br2_store((out0)+((uintptr_t)1ULL), x75, 1);
  _br2_store((out0)+((uintptr_t)2ULL), x76, 1);
  _br2_store((out0)+((uintptr_t)3ULL), x77, 1);
  _br2_store((out0)+((uintptr_t)4ULL), x78, 1);
  _br2_store((out0)+((uintptr_t)5ULL), x79, 1);
  _br2_store((out0)+((uintptr_t)6ULL), x80, 1);
  _br2_store((out0)+((uintptr_t)7ULL), x81, 1);
  _br2_store((out0)+((uintptr_t)8ULL), x82, 1);
  _br2_store((out0)+((uintptr_t)9ULL), x83, 1);
  _br2_store((out0)+((uintptr_t)10ULL), x84, 1);
  _br2_store((out0)+((uintptr_t)11ULL), x85, 1);
  _br2_store((out0)+((uintptr_t)12ULL), x86, 1);
  _br2_store((out0)+((uintptr_t)13ULL), x87, 1);
  _br2_store((out0)+((uintptr_t)14ULL), x88, 1);
  _br2_store((out0)+((uintptr_t)15ULL), x89, 1);
  _br2_store((out0)+((uintptr_t)16ULL), x90, 1);
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
 */
void fiat_poly1305_from_bytes(uintptr_t out0, uintptr_t in0) {
  uintptr_t x16, x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0, x32, x33, x31, x34, x30, x35, x29, x36, x28, x37, x38, x27, x40, x26, x41, x25, x42, x24, x43, x23, x44, x45, x22, x47, x21, x48, x20, x49, x19, x50, x18, x51, x17, x52, x39, x46, x53, x54, x55, x56;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), 1);
  x1 = _br2_load((in0)+((uintptr_t)1ULL), 1);
  x2 = _br2_load((in0)+((uintptr_t)2ULL), 1);
  x3 = _br2_load((in0)+((uintptr_t)3ULL), 1);
  x4 = _br2_load((in0)+((uintptr_t)4ULL), 1);
  x5 = _br2_load((in0)+((uintptr_t)5ULL), 1);
  x6 = _br2_load((in0)+((uintptr_t)6ULL), 1);
  x7 = _br2_load((in0)+((uintptr_t)7ULL), 1);
  x8 = _br2_load((in0)+((uintptr_t)8ULL), 1);
  x9 = _br2_load((in0)+((uintptr_t)9ULL), 1);
  x10 = _br2_load((in0)+((uintptr_t)10ULL), 1);
  x11 = _br2_load((in0)+((uintptr_t)11ULL), 1);
  x12 = _br2_load((in0)+((uintptr_t)12ULL), 1);
  x13 = _br2_load((in0)+((uintptr_t)13ULL), 1);
  x14 = _br2_load((in0)+((uintptr_t)14ULL), 1);
  x15 = _br2_load((in0)+((uintptr_t)15ULL), 1);
  x16 = _br2_load((in0)+((uintptr_t)16ULL), 1);
  /*skip*/
  /*skip*/
  x17 = (x16)<<((uintptr_t)41ULL);
  x18 = (x15)<<((uintptr_t)33ULL);
  x19 = (x14)<<((uintptr_t)25ULL);
  x20 = (x13)<<((uintptr_t)17ULL);
  x21 = (x12)<<((uintptr_t)9ULL);
  x22 = (x11)*((uintptr_t)2ULL);
  x23 = (x10)<<((uintptr_t)36ULL);
  x24 = (x9)<<((uintptr_t)28ULL);
  x25 = (x8)<<((uintptr_t)20ULL);
  x26 = (x7)<<((uintptr_t)12ULL);
  x27 = (x6)<<((uintptr_t)4ULL);
  x28 = (x5)<<((uintptr_t)40ULL);
  x29 = (x4)<<((uintptr_t)32ULL);
  x30 = (x3)<<((uintptr_t)24ULL);
  x31 = (x2)<<((uintptr_t)16ULL);
  x32 = (x1)<<((uintptr_t)8ULL);
  x33 = x0;
  x34 = (x32)+(x33);
  x35 = (x31)+(x34);
  x36 = (x30)+(x35);
  x37 = (x29)+(x36);
  x38 = (x28)+(x37);
  x39 = (x38)&((uintptr_t)17592186044415ULL);
  x40 = (x38)>>((uintptr_t)44ULL);
  x41 = (x27)+(x40);
  x42 = (x26)+(x41);
  x43 = (x25)+(x42);
  x44 = (x24)+(x43);
  x45 = (x23)+(x44);
  x46 = (x45)&((uintptr_t)8796093022207ULL);
  x47 = (x45)>>((uintptr_t)43ULL);
  x48 = (x22)+(x47);
  x49 = (x21)+(x48);
  x50 = (x20)+(x49);
  x51 = (x19)+(x50);
  x52 = (x18)+(x51);
  x53 = (x17)+(x52);
  x54 = x39;
  x55 = x46;
  x56 = x53;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x54, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)8ULL), x55, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)16ULL), x56, sizeof(uintptr_t));
  /*skip*/
  return;
}


