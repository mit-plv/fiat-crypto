/* Autogenerated: 'src/ExtractionOCaml/dettman_multiplication' --inline --static --use-value-barrier secp256k1_dettman 32 10 22 '2^256 - 4294968273' mul32 square32 */
/* curve description: secp256k1_dettman */
/* machine_wordsize = 32 (from "32") */
/* requested operations: mul32, square32 */
/* n = 10 (from "10") */
/* last_limb_width = 22 (from "22") */
/* s-c = 2^256 - [(1, 4294968273)] (from "2^256 - 4294968273") */
/* inbounds_multiplier: None (from "") */
/*  */
/* Computed values: */
/*  */
/*  */

#include <stdint.h>
#if defined(__GNUC__) || defined(__clang__)
#  define FIAT_SECP256K1_DETTMAN_FIAT_INLINE __inline__
#else
#  define FIAT_SECP256K1_DETTMAN_FIAT_INLINE
#endif

#if (-1 & 3) != 3
#error "This code only works on a two's complement system"
#endif


/*
 * The function fiat_secp256k1_dettman_mul32 multiplies two field elements.
 *
 * Postconditions:
 *   eval out1 mod 115792089237316195423570985008687907853269984665640564039457584007908834671663 = (eval arg1 * eval arg2) mod 115792089237316195423570985008687907853269984665640564039457584007908834671663
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7ffffe]]
 *   arg2: [[0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7ffffe]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x5fffff]]
 */
static FIAT_SECP256K1_DETTMAN_FIAT_INLINE void fiat_secp256k1_dettman_mul32(uint32_t out1[10], const uint32_t arg1[10], const uint32_t arg2[10]) {
  uint64_t x1;
  uint32_t x2;
  uint32_t x3;
  uint64_t x4;
  uint32_t x5;
  uint32_t x6;
  uint64_t x7;
  uint32_t x8;
  uint64_t x9;
  uint32_t x10;
  uint32_t x11;
  uint64_t x12;
  uint32_t x13;
  uint32_t x14;
  uint32_t x15;
  uint32_t x16;
  uint64_t x17;
  uint32_t x18;
  uint32_t x19;
  uint64_t x20;
  uint32_t x21;
  uint32_t x22;
  uint64_t x23;
  uint32_t x24;
  uint32_t x25;
  uint64_t x26;
  uint32_t x27;
  uint32_t x28;
  uint64_t x29;
  uint32_t x30;
  uint32_t x31;
  uint64_t x32;
  uint32_t x33;
  uint32_t x34;
  uint64_t x35;
  uint32_t x36;
  uint32_t x37;
  uint64_t x38;
  uint32_t x39;
  uint32_t x40;
  uint64_t x41;
  uint32_t x42;
  uint32_t x43;
  uint64_t x44;
  uint32_t x45;
  uint32_t x46;
  uint64_t x47;
  uint32_t x48;
  uint32_t x49;
  uint64_t x50;
  uint32_t x51;
  uint32_t x52;
  uint64_t x53;
  uint32_t x54;
  uint64_t x55;
  uint32_t x56;
  uint32_t x57;
  uint64_t x58;
  uint32_t x59;
  uint32_t x60;
  uint64_t x61;
  uint32_t x62;
  uint32_t x63;
  uint32_t x64;
  x1 = (((uint64_t)(arg1[8]) * (arg2[9])) + ((uint64_t)(arg1[9]) * (arg2[8])));
  x2 = (uint32_t)(x1 >> 26);
  x3 = (uint32_t)(x1 & UINT32_C(0x3ffffff));
  x4 = ((((uint64_t)(arg1[0]) * (arg2[7])) + (((uint64_t)(arg1[1]) * (arg2[6])) + (((uint64_t)(arg1[2]) * (arg2[5])) + (((uint64_t)(arg1[3]) * (arg2[4])) + (((uint64_t)(arg1[4]) * (arg2[3])) + (((uint64_t)(arg1[5]) * (arg2[2])) + (((uint64_t)(arg1[6]) * (arg2[1])) + ((uint64_t)(arg1[7]) * (arg2[0]))))))))) + ((uint64_t)x3 * UINT16_C(0x3d10)));
  x5 = (uint32_t)(x4 >> 26);
  x6 = (uint32_t)(x4 & UINT32_C(0x3ffffff));
  x7 = (x2 + ((uint64_t)(arg1[9]) * (arg2[9])));
  x8 = (uint32_t)(x7 >> 32);
  x9 = ((x5 + ((((uint64_t)(arg1[0]) * (arg2[8])) + (((uint64_t)(arg1[1]) * (arg2[7])) + (((uint64_t)(arg1[2]) * (arg2[6])) + (((uint64_t)(arg1[3]) * (arg2[5])) + (((uint64_t)(arg1[4]) * (arg2[4])) + (((uint64_t)(arg1[5]) * (arg2[3])) + (((uint64_t)(arg1[6]) * (arg2[2])) + (((uint64_t)(arg1[7]) * (arg2[1])) + ((uint64_t)(arg1[8]) * (arg2[0])))))))))) + ((uint64_t)x3 << 10))) + ((uint64_t)(uint32_t)x7 * UINT16_C(0x3d10)));
  x10 = (uint32_t)(x9 >> 26);
  x11 = (uint32_t)(x9 & UINT32_C(0x3ffffff));
  x12 = ((x10 + ((((uint64_t)(arg1[0]) * (arg2[9])) + (((uint64_t)(arg1[1]) * (arg2[8])) + (((uint64_t)(arg1[2]) * (arg2[7])) + (((uint64_t)(arg1[3]) * (arg2[6])) + (((uint64_t)(arg1[4]) * (arg2[5])) + (((uint64_t)(arg1[5]) * (arg2[4])) + (((uint64_t)(arg1[6]) * (arg2[3])) + (((uint64_t)(arg1[7]) * (arg2[2])) + (((uint64_t)(arg1[8]) * (arg2[1])) + ((uint64_t)(arg1[9]) * (arg2[0]))))))))))) + ((uint64_t)(uint32_t)x7 << 10))) + ((uint64_t)x8 * UINT32_C(0xf4400)));
  x13 = (uint32_t)(x12 >> 26);
  x14 = (uint32_t)(x12 & UINT32_C(0x3ffffff));
  x15 = (x14 >> 22);
  x16 = (x14 & UINT32_C(0x3fffff));
  x17 = (x13 + ((((uint64_t)(arg1[1]) * (arg2[9])) + (((uint64_t)(arg1[2]) * (arg2[8])) + (((uint64_t)(arg1[3]) * (arg2[7])) + (((uint64_t)(arg1[4]) * (arg2[6])) + (((uint64_t)(arg1[5]) * (arg2[5])) + (((uint64_t)(arg1[6]) * (arg2[4])) + (((uint64_t)(arg1[7]) * (arg2[3])) + (((uint64_t)(arg1[8]) * (arg2[2])) + ((uint64_t)(arg1[9]) * (arg2[1])))))))))) + (x8 << 16)));
  x18 = (uint32_t)(x17 >> 26);
  x19 = (uint32_t)(x17 & UINT32_C(0x3ffffff));
  x20 = (((uint64_t)(arg1[0]) * (arg2[0])) + ((uint64_t)(x15 + (x19 << 4)) * UINT16_C(0x3d1)));
  x21 = (uint32_t)(x20 >> 26);
  x22 = (uint32_t)(x20 & UINT32_C(0x3ffffff));
  x23 = (x18 + (((uint64_t)(arg1[2]) * (arg2[9])) + (((uint64_t)(arg1[3]) * (arg2[8])) + (((uint64_t)(arg1[4]) * (arg2[7])) + (((uint64_t)(arg1[5]) * (arg2[6])) + (((uint64_t)(arg1[6]) * (arg2[5])) + (((uint64_t)(arg1[7]) * (arg2[4])) + (((uint64_t)(arg1[8]) * (arg2[3])) + ((uint64_t)(arg1[9]) * (arg2[2]))))))))));
  x24 = (uint32_t)(x23 >> 26);
  x25 = (uint32_t)(x23 & UINT32_C(0x3ffffff));
  x26 = ((x21 + ((((uint64_t)(arg1[0]) * (arg2[1])) + ((uint64_t)(arg1[1]) * (arg2[0]))) + ((uint64_t)(x15 + (x19 << 4)) << 6))) + ((uint64_t)x25 * UINT16_C(0x3d10)));
  x27 = (uint32_t)(x26 >> 26);
  x28 = (uint32_t)(x26 & UINT32_C(0x3ffffff));
  x29 = (x24 + (((uint64_t)(arg1[3]) * (arg2[9])) + (((uint64_t)(arg1[4]) * (arg2[8])) + (((uint64_t)(arg1[5]) * (arg2[7])) + (((uint64_t)(arg1[6]) * (arg2[6])) + (((uint64_t)(arg1[7]) * (arg2[5])) + (((uint64_t)(arg1[8]) * (arg2[4])) + ((uint64_t)(arg1[9]) * (arg2[3])))))))));
  x30 = (uint32_t)(x29 >> 26);
  x31 = (uint32_t)(x29 & UINT32_C(0x3ffffff));
  x32 = ((x27 + ((((uint64_t)(arg1[0]) * (arg2[2])) + (((uint64_t)(arg1[1]) * (arg2[1])) + ((uint64_t)(arg1[2]) * (arg2[0])))) + ((uint64_t)x25 << 10))) + ((uint64_t)x31 * UINT16_C(0x3d10)));
  x33 = (uint32_t)(x32 >> 26);
  x34 = (uint32_t)(x32 & UINT32_C(0x3ffffff));
  x35 = (x30 + (((uint64_t)(arg1[4]) * (arg2[9])) + (((uint64_t)(arg1[5]) * (arg2[8])) + (((uint64_t)(arg1[6]) * (arg2[7])) + (((uint64_t)(arg1[7]) * (arg2[6])) + (((uint64_t)(arg1[8]) * (arg2[5])) + ((uint64_t)(arg1[9]) * (arg2[4]))))))));
  x36 = (uint32_t)(x35 >> 26);
  x37 = (uint32_t)(x35 & UINT32_C(0x3ffffff));
  x38 = ((x33 + ((((uint64_t)(arg1[0]) * (arg2[3])) + (((uint64_t)(arg1[1]) * (arg2[2])) + (((uint64_t)(arg1[2]) * (arg2[1])) + ((uint64_t)(arg1[3]) * (arg2[0]))))) + ((uint64_t)x31 << 10))) + ((uint64_t)x37 * UINT16_C(0x3d10)));
  x39 = (uint32_t)(x38 >> 26);
  x40 = (uint32_t)(x38 & UINT32_C(0x3ffffff));
  x41 = (x36 + (((uint64_t)(arg1[5]) * (arg2[9])) + (((uint64_t)(arg1[6]) * (arg2[8])) + (((uint64_t)(arg1[7]) * (arg2[7])) + (((uint64_t)(arg1[8]) * (arg2[6])) + ((uint64_t)(arg1[9]) * (arg2[5])))))));
  x42 = (uint32_t)(x41 >> 26);
  x43 = (uint32_t)(x41 & UINT32_C(0x3ffffff));
  x44 = ((x39 + ((((uint64_t)(arg1[0]) * (arg2[4])) + (((uint64_t)(arg1[1]) * (arg2[3])) + (((uint64_t)(arg1[2]) * (arg2[2])) + (((uint64_t)(arg1[3]) * (arg2[1])) + ((uint64_t)(arg1[4]) * (arg2[0])))))) + ((uint64_t)x37 << 10))) + ((uint64_t)x43 * UINT16_C(0x3d10)));
  x45 = (uint32_t)(x44 >> 26);
  x46 = (uint32_t)(x44 & UINT32_C(0x3ffffff));
  x47 = (x42 + (((uint64_t)(arg1[6]) * (arg2[9])) + (((uint64_t)(arg1[7]) * (arg2[8])) + (((uint64_t)(arg1[8]) * (arg2[7])) + ((uint64_t)(arg1[9]) * (arg2[6]))))));
  x48 = (uint32_t)(x47 >> 26);
  x49 = (uint32_t)(x47 & UINT32_C(0x3ffffff));
  x50 = ((x45 + ((((uint64_t)(arg1[0]) * (arg2[5])) + (((uint64_t)(arg1[1]) * (arg2[4])) + (((uint64_t)(arg1[2]) * (arg2[3])) + (((uint64_t)(arg1[3]) * (arg2[2])) + (((uint64_t)(arg1[4]) * (arg2[1])) + ((uint64_t)(arg1[5]) * (arg2[0]))))))) + ((uint64_t)x43 << 10))) + ((uint64_t)x49 * UINT16_C(0x3d10)));
  x51 = (uint32_t)(x50 >> 26);
  x52 = (uint32_t)(x50 & UINT32_C(0x3ffffff));
  x53 = (x48 + (((uint64_t)(arg1[7]) * (arg2[9])) + (((uint64_t)(arg1[8]) * (arg2[8])) + ((uint64_t)(arg1[9]) * (arg2[7])))));
  x54 = (uint32_t)(x53 >> 32);
  x55 = ((x51 + ((((uint64_t)(arg1[0]) * (arg2[6])) + (((uint64_t)(arg1[1]) * (arg2[5])) + (((uint64_t)(arg1[2]) * (arg2[4])) + (((uint64_t)(arg1[3]) * (arg2[3])) + (((uint64_t)(arg1[4]) * (arg2[2])) + (((uint64_t)(arg1[5]) * (arg2[1])) + ((uint64_t)(arg1[6]) * (arg2[0])))))))) + ((uint64_t)x49 << 10))) + ((uint64_t)(uint32_t)x53 * UINT16_C(0x3d10)));
  x56 = (uint32_t)(x55 >> 26);
  x57 = (uint32_t)(x55 & UINT32_C(0x3ffffff));
  x58 = ((x56 + (x6 + ((uint64_t)(uint32_t)x53 << 10))) + ((uint64_t)x54 * UINT32_C(0xf4400)));
  x59 = (uint32_t)(x58 >> 26);
  x60 = (uint32_t)(x58 & UINT32_C(0x3ffffff));
  x61 = (x59 + (x11 + ((uint64_t)x54 << 16)));
  x62 = (uint32_t)(x61 >> 26);
  x63 = (uint32_t)(x61 & UINT32_C(0x3ffffff));
  x64 = (x62 + x16);
  out1[0] = x22;
  out1[1] = x28;
  out1[2] = x34;
  out1[3] = x40;
  out1[4] = x46;
  out1[5] = x52;
  out1[6] = x57;
  out1[7] = x60;
  out1[8] = x63;
  out1[9] = x64;
}

/*
 * The function fiat_secp256k1_dettman_square32 squares a field element.
 *
 * Postconditions:
 *   eval out1 mod 115792089237316195423570985008687907853269984665640564039457584007908834671663 = (eval arg1 * eval arg1) mod 115792089237316195423570985008687907853269984665640564039457584007908834671663
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7ffffe]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x7fffffe], [0x0 ~> 0x5fffff]]
 */
static FIAT_SECP256K1_DETTMAN_FIAT_INLINE void fiat_secp256k1_dettman_square32(uint32_t out1[10], const uint32_t arg1[10]) {
  uint32_t x1;
  uint32_t x2;
  uint32_t x3;
  uint32_t x4;
  uint32_t x5;
  uint32_t x6;
  uint32_t x7;
  uint32_t x8;
  uint32_t x9;
  uint64_t x10;
  uint32_t x11;
  uint32_t x12;
  uint64_t x13;
  uint32_t x14;
  uint32_t x15;
  uint64_t x16;
  uint32_t x17;
  uint64_t x18;
  uint32_t x19;
  uint32_t x20;
  uint64_t x21;
  uint32_t x22;
  uint32_t x23;
  uint32_t x24;
  uint32_t x25;
  uint64_t x26;
  uint32_t x27;
  uint32_t x28;
  uint64_t x29;
  uint32_t x30;
  uint32_t x31;
  uint64_t x32;
  uint32_t x33;
  uint32_t x34;
  uint64_t x35;
  uint32_t x36;
  uint32_t x37;
  uint64_t x38;
  uint32_t x39;
  uint32_t x40;
  uint64_t x41;
  uint32_t x42;
  uint32_t x43;
  uint64_t x44;
  uint32_t x45;
  uint32_t x46;
  uint64_t x47;
  uint32_t x48;
  uint32_t x49;
  uint64_t x50;
  uint32_t x51;
  uint32_t x52;
  uint64_t x53;
  uint32_t x54;
  uint32_t x55;
  uint64_t x56;
  uint32_t x57;
  uint32_t x58;
  uint64_t x59;
  uint32_t x60;
  uint32_t x61;
  uint64_t x62;
  uint32_t x63;
  uint64_t x64;
  uint32_t x65;
  uint32_t x66;
  uint64_t x67;
  uint32_t x68;
  uint32_t x69;
  uint64_t x70;
  uint32_t x71;
  uint32_t x72;
  uint32_t x73;
  x1 = ((arg1[8]) * 0x2);
  x2 = ((arg1[7]) * 0x2);
  x3 = ((arg1[6]) * 0x2);
  x4 = ((arg1[5]) * 0x2);
  x5 = ((arg1[4]) * 0x2);
  x6 = ((arg1[3]) * 0x2);
  x7 = ((arg1[2]) * 0x2);
  x8 = ((arg1[1]) * 0x2);
  x9 = ((arg1[0]) * 0x2);
  x10 = ((uint64_t)x1 * (arg1[9]));
  x11 = (uint32_t)(x10 >> 26);
  x12 = (uint32_t)(x10 & UINT32_C(0x3ffffff));
  x13 = ((((uint64_t)x9 * (arg1[7])) + (((uint64_t)x8 * (arg1[6])) + (((uint64_t)x7 * (arg1[5])) + ((uint64_t)x6 * (arg1[4]))))) + ((uint64_t)x12 * UINT16_C(0x3d10)));
  x14 = (uint32_t)(x13 >> 26);
  x15 = (uint32_t)(x13 & UINT32_C(0x3ffffff));
  x16 = (x11 + ((uint64_t)(arg1[9]) * (arg1[9])));
  x17 = (uint32_t)(x16 >> 32);
  x18 = ((x14 + ((((uint64_t)x9 * (arg1[8])) + (((uint64_t)x8 * (arg1[7])) + (((uint64_t)x7 * (arg1[6])) + (((uint64_t)x6 * (arg1[5])) + ((uint64_t)(arg1[4]) * (arg1[4])))))) + ((uint64_t)x12 << 10))) + ((uint64_t)(uint32_t)x16 * UINT16_C(0x3d10)));
  x19 = (uint32_t)(x18 >> 26);
  x20 = (uint32_t)(x18 & UINT32_C(0x3ffffff));
  x21 = ((x19 + ((((uint64_t)x9 * (arg1[9])) + (((uint64_t)x8 * (arg1[8])) + (((uint64_t)x7 * (arg1[7])) + (((uint64_t)x6 * (arg1[6])) + ((uint64_t)x5 * (arg1[5])))))) + ((uint64_t)(uint32_t)x16 << 10))) + ((uint64_t)x17 * UINT32_C(0xf4400)));
  x22 = (uint32_t)(x21 >> 26);
  x23 = (uint32_t)(x21 & UINT32_C(0x3ffffff));
  x24 = (x23 >> 22);
  x25 = (x23 & UINT32_C(0x3fffff));
  x26 = (x22 + ((((uint64_t)x8 * (arg1[9])) + (((uint64_t)x7 * (arg1[8])) + (((uint64_t)x6 * (arg1[7])) + (((uint64_t)x5 * (arg1[6])) + ((uint64_t)(arg1[5]) * (arg1[5])))))) + (x17 << 16)));
  x27 = (uint32_t)(x26 >> 26);
  x28 = (uint32_t)(x26 & UINT32_C(0x3ffffff));
  x29 = (((uint64_t)(arg1[0]) * (arg1[0])) + ((uint64_t)(x24 + (x28 << 4)) * UINT16_C(0x3d1)));
  x30 = (uint32_t)(x29 >> 26);
  x31 = (uint32_t)(x29 & UINT32_C(0x3ffffff));
  x32 = (x27 + (((uint64_t)x7 * (arg1[9])) + (((uint64_t)x6 * (arg1[8])) + (((uint64_t)x5 * (arg1[7])) + ((uint64_t)x4 * (arg1[6]))))));
  x33 = (uint32_t)(x32 >> 26);
  x34 = (uint32_t)(x32 & UINT32_C(0x3ffffff));
  x35 = ((x30 + (((uint64_t)x9 * (arg1[1])) + ((uint64_t)(x24 + (x28 << 4)) << 6))) + ((uint64_t)x34 * UINT16_C(0x3d10)));
  x36 = (uint32_t)(x35 >> 26);
  x37 = (uint32_t)(x35 & UINT32_C(0x3ffffff));
  x38 = (x33 + (((uint64_t)x6 * (arg1[9])) + (((uint64_t)x5 * (arg1[8])) + (((uint64_t)x4 * (arg1[7])) + ((uint64_t)(arg1[6]) * (arg1[6]))))));
  x39 = (uint32_t)(x38 >> 26);
  x40 = (uint32_t)(x38 & UINT32_C(0x3ffffff));
  x41 = ((x36 + ((((uint64_t)x9 * (arg1[2])) + ((uint64_t)(arg1[1]) * (arg1[1]))) + ((uint64_t)x34 << 10))) + ((uint64_t)x40 * UINT16_C(0x3d10)));
  x42 = (uint32_t)(x41 >> 26);
  x43 = (uint32_t)(x41 & UINT32_C(0x3ffffff));
  x44 = (x39 + (((uint64_t)x5 * (arg1[9])) + (((uint64_t)x4 * (arg1[8])) + ((uint64_t)x3 * (arg1[7])))));
  x45 = (uint32_t)(x44 >> 26);
  x46 = (uint32_t)(x44 & UINT32_C(0x3ffffff));
  x47 = ((x42 + ((((uint64_t)x9 * (arg1[3])) + ((uint64_t)x8 * (arg1[2]))) + ((uint64_t)x40 << 10))) + ((uint64_t)x46 * UINT16_C(0x3d10)));
  x48 = (uint32_t)(x47 >> 26);
  x49 = (uint32_t)(x47 & UINT32_C(0x3ffffff));
  x50 = (x45 + (((uint64_t)x4 * (arg1[9])) + (((uint64_t)x3 * (arg1[8])) + ((uint64_t)(arg1[7]) * (arg1[7])))));
  x51 = (uint32_t)(x50 >> 26);
  x52 = (uint32_t)(x50 & UINT32_C(0x3ffffff));
  x53 = ((x48 + ((((uint64_t)x9 * (arg1[4])) + (((uint64_t)x8 * (arg1[3])) + ((uint64_t)(arg1[2]) * (arg1[2])))) + ((uint64_t)x46 << 10))) + ((uint64_t)x52 * UINT16_C(0x3d10)));
  x54 = (uint32_t)(x53 >> 26);
  x55 = (uint32_t)(x53 & UINT32_C(0x3ffffff));
  x56 = (x51 + (((uint64_t)x3 * (arg1[9])) + ((uint64_t)x2 * (arg1[8]))));
  x57 = (uint32_t)(x56 >> 26);
  x58 = (uint32_t)(x56 & UINT32_C(0x3ffffff));
  x59 = ((x54 + ((((uint64_t)x9 * (arg1[5])) + (((uint64_t)x8 * (arg1[4])) + ((uint64_t)x7 * (arg1[3])))) + ((uint64_t)x52 << 10))) + ((uint64_t)x58 * UINT16_C(0x3d10)));
  x60 = (uint32_t)(x59 >> 26);
  x61 = (uint32_t)(x59 & UINT32_C(0x3ffffff));
  x62 = (x57 + (((uint64_t)x2 * (arg1[9])) + ((uint64_t)(arg1[8]) * (arg1[8]))));
  x63 = (uint32_t)(x62 >> 32);
  x64 = ((x60 + ((((uint64_t)x9 * (arg1[6])) + (((uint64_t)x8 * (arg1[5])) + (((uint64_t)x7 * (arg1[4])) + ((uint64_t)(arg1[3]) * (arg1[3]))))) + ((uint64_t)x58 << 10))) + ((uint64_t)(uint32_t)x62 * UINT16_C(0x3d10)));
  x65 = (uint32_t)(x64 >> 26);
  x66 = (uint32_t)(x64 & UINT32_C(0x3ffffff));
  x67 = ((x65 + (x15 + ((uint64_t)(uint32_t)x62 << 10))) + ((uint64_t)x63 * UINT32_C(0xf4400)));
  x68 = (uint32_t)(x67 >> 26);
  x69 = (uint32_t)(x67 & UINT32_C(0x3ffffff));
  x70 = (x68 + (x20 + ((uint64_t)x63 << 16)));
  x71 = (uint32_t)(x70 >> 26);
  x72 = (uint32_t)(x70 & UINT32_C(0x3ffffff));
  x73 = (x71 + x25);
  out1[0] = x31;
  out1[1] = x37;
  out1[2] = x43;
  out1[3] = x49;
  out1[4] = x55;
  out1[5] = x61;
  out1[6] = x66;
  out1[7] = x69;
  out1[8] = x72;
  out1[9] = x73;
}