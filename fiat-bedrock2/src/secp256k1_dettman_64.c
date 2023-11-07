/* Autogenerated: 'src/ExtractionOCaml/bedrock2_dettman_multiplication' --lang bedrock2 --static --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select --no-field-element-typedefs secp256k1_dettman 64 5 48 2 '2^256 - 4294968273' mul square */
/* curve description: secp256k1_dettman */
/* machine_wordsize = 64 (from "64") */
/* requested operations: mul, square */
/* n = 5 (from "5") */
/* last_limb_width = 48 (from "48") */
/* last_reduction = 2 (from "2") */
/* s-c = 2^256 - [(1, 4294968273)] (from "2^256 - 4294968273") */
/* inbounds_multiplier: None (from "") */
/*  */
/* Computed values: */
/*  */
/*  */

#include <stdint.h>
#include <string.h>
#include <assert.h>

static __attribute__((constructor)) void _br2_preconditions(void) {
  static_assert(~(intptr_t)0 == -(intptr_t)1, "two's complement");
  assert(((void)"two's complement", ~(intptr_t)0 == -(intptr_t)1));
  uintptr_t u = 1;
  assert(((void)"little-endian", 1 == *(unsigned char *)&u));
  intptr_t i = 1;
  assert(((void)"little-endian", 1 == *(unsigned char *)&i));
}

// We use memcpy to work around -fstrict-aliasing.
// A plain memcpy is enough on clang 10, but not on gcc 10, which fails
// to infer the bounds on an integer loaded by memcpy.
// Adding a range mask after memcpy in turn makes slower code in clang.
// Loading individual bytes, shifting them together, and or-ing is fast
// on clang and sometimes on GCC, but other times GCC inlines individual
// byte operations without reconstructing wider accesses.
// The little-endian idiom below seems fast in gcc 9+ and clang 10.
static inline  __attribute__((always_inline, unused))
uintptr_t _br2_load(uintptr_t a, uintptr_t sz) {
  switch (sz) {
  case 1: { uint8_t  r = 0; memcpy(&r, (void*)a, 1); return r; }
  case 2: { uint16_t r = 0; memcpy(&r, (void*)a, 2); return r; }
  case 4: { uint32_t r = 0; memcpy(&r, (void*)a, 4); return r; }
  case 8: { uint64_t r = 0; memcpy(&r, (void*)a, 8); return r; }
  default: __builtin_unreachable();
  }
}

static inline __attribute__((always_inline, unused))
void _br2_store(uintptr_t a, uintptr_t v, uintptr_t sz) {
  memcpy((void*)a, &v, sz);
}

static inline __attribute__((always_inline, unused))
uintptr_t _br2_mulhuu(uintptr_t a, uintptr_t b) {
  #if (UINTPTR_MAX == (UINTMAX_C(1)<<31) - 1 + (UINTMAX_C(1)<<31))
	  return ((uint64_t)a * b) >> 32;
  #elif (UINTPTR_MAX == (UINTMAX_C(1)<<63) - 1 + (UINTMAX_C(1)<<63))
    return ((unsigned __int128)a * b) >> 64;
  #else
    #error "32-bit or 64-bit uintptr_t required"
  #endif
}

static inline __attribute__((always_inline, unused))
uintptr_t _br2_divu(uintptr_t a, uintptr_t b) {
  if (!b) return -1;
  return a/b;
}

static inline __attribute__((always_inline, unused))
uintptr_t _br2_remu(uintptr_t a, uintptr_t b) {
  if (!b) return a;
  return a%b;
}

static inline __attribute__((always_inline, unused))
uintptr_t _br2_shamt(uintptr_t a) {
  return a&(sizeof(uintptr_t)*8-1);
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
 *   in1: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x17fffffffffff]]
 */
static
void internal_fiat_secp256k1_dettman_mul(uintptr_t out0, uintptr_t in0, uintptr_t in1) {
  uintptr_t x10, x14, x16, x19, x17, x20, x15, x18, x22, x25, x23, x26, x21, x24, x28, x31, x29, x32, x27, x12, x30, x35, x33, x36, x13, x37, x34, x11, x42, x44, x47, x45, x48, x43, x46, x50, x53, x51, x54, x49, x52, x56, x59, x57, x60, x55, x58, x62, x65, x63, x66, x61, x64, x38, x69, x67, x40, x68, x72, x70, x73, x41, x74, x71, x77, x79, x82, x80, x83, x78, x81, x85, x88, x86, x89, x84, x87, x91, x94, x92, x95, x90, x93, x75, x98, x96, x99, x97, x76, x102, x101, x104, x106, x109, x107, x110, x105, x111, x108, x114, x116, x119, x117, x120, x115, x118, x122, x125, x123, x126, x121, x124, x100, x129, x127, x130, x128, x132, x135, x137, x140, x138, x141, x136, x139, x112, x144, x142, x133, x143, x147, x145, x148, x134, x149, x146, x4, x8, x3, x9, x152, x154, x157, x155, x158, x153, x156, x131, x161, x159, x160, x2, x5, x1, x6, x165, x167, x170, x168, x171, x166, x0, x7, x169, x173, x176, x174, x177, x172, x175, x150, x180, x178, x163, x179, x183, x181, x184, x164, x185, x182, x162, x188, x186, x39, x191, x189, x192, x190, x193, x103, x113, x151, x187, x194, x195, x196, x197, x198, x199, x200;
  x0 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(0))), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(8))), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(16))), sizeof(uintptr_t));
  x3 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(24))), sizeof(uintptr_t));
  x4 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(32))), sizeof(uintptr_t));
  /*skip*/
  x5 = _br2_load((in1)+((uintptr_t)(UINTMAX_C(0))), sizeof(uintptr_t));
  x6 = _br2_load((in1)+((uintptr_t)(UINTMAX_C(8))), sizeof(uintptr_t));
  x7 = _br2_load((in1)+((uintptr_t)(UINTMAX_C(16))), sizeof(uintptr_t));
  x8 = _br2_load((in1)+((uintptr_t)(UINTMAX_C(24))), sizeof(uintptr_t));
  x9 = _br2_load((in1)+((uintptr_t)(UINTMAX_C(32))), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x10 = (x4)*(x9);
  x11 = _br2_mulhuu((x4), (x9));
  x12 = (x10)*((uintptr_t)(UINTMAX_C(68719492368)));
  x13 = _br2_mulhuu((x10), ((uintptr_t)(UINTMAX_C(68719492368))));
  x14 = (x3)*(x5);
  x15 = _br2_mulhuu((x3), (x5));
  x16 = (x2)*(x6);
  x17 = _br2_mulhuu((x2), (x6));
  x18 = (x16)+(x14);
  x19 = (uintptr_t)((x18)<(x16));
  x20 = (x19)+(x17);
  x21 = (x20)+(x15);
  x22 = (x1)*(x7);
  x23 = _br2_mulhuu((x1), (x7));
  x24 = (x22)+(x18);
  x25 = (uintptr_t)((x24)<(x22));
  x26 = (x25)+(x23);
  x27 = (x26)+(x21);
  x28 = (x0)*(x8);
  x29 = _br2_mulhuu((x0), (x8));
  x30 = (x28)+(x24);
  x31 = (uintptr_t)((x30)<(x28));
  x32 = (x31)+(x29);
  x33 = (x32)+(x27);
  x34 = (x30)+(x12);
  x35 = (uintptr_t)((x34)<(x30));
  x36 = (x35)+(x33);
  x37 = (x36)+(x13);
  x38 = ((x34)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x37)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x39 = (x34)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x40 = (x11)*((uintptr_t)(UINTMAX_C(281475040739328)));
  x41 = _br2_mulhuu((x11), ((uintptr_t)(UINTMAX_C(281475040739328))));
  x42 = (x4)*(x5);
  x43 = _br2_mulhuu((x4), (x5));
  x44 = (x3)*(x6);
  x45 = _br2_mulhuu((x3), (x6));
  x46 = (x44)+(x42);
  x47 = (uintptr_t)((x46)<(x44));
  x48 = (x47)+(x45);
  x49 = (x48)+(x43);
  x50 = (x2)*(x7);
  x51 = _br2_mulhuu((x2), (x7));
  x52 = (x50)+(x46);
  x53 = (uintptr_t)((x52)<(x50));
  x54 = (x53)+(x51);
  x55 = (x54)+(x49);
  x56 = (x1)*(x8);
  x57 = _br2_mulhuu((x1), (x8));
  x58 = (x56)+(x52);
  x59 = (uintptr_t)((x58)<(x56));
  x60 = (x59)+(x57);
  x61 = (x60)+(x55);
  x62 = (x0)*(x9);
  x63 = _br2_mulhuu((x0), (x9));
  x64 = (x62)+(x58);
  x65 = (uintptr_t)((x64)<(x62));
  x66 = (x65)+(x63);
  x67 = (x66)+(x61);
  x68 = (x38)+(x64);
  x69 = (uintptr_t)((x68)<(x38));
  x70 = (x69)+(x67);
  x71 = (x68)+(x40);
  x72 = (uintptr_t)((x71)<(x68));
  x73 = (x72)+(x70);
  x74 = (x73)+(x41);
  x75 = ((x71)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x74)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x76 = (x71)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x77 = (x4)*(x6);
  x78 = _br2_mulhuu((x4), (x6));
  x79 = (x3)*(x7);
  x80 = _br2_mulhuu((x3), (x7));
  x81 = (x79)+(x77);
  x82 = (uintptr_t)((x81)<(x79));
  x83 = (x82)+(x80);
  x84 = (x83)+(x78);
  x85 = (x2)*(x8);
  x86 = _br2_mulhuu((x2), (x8));
  x87 = (x85)+(x81);
  x88 = (uintptr_t)((x87)<(x85));
  x89 = (x88)+(x86);
  x90 = (x89)+(x84);
  x91 = (x1)*(x9);
  x92 = _br2_mulhuu((x1), (x9));
  x93 = (x91)+(x87);
  x94 = (uintptr_t)((x93)<(x91));
  x95 = (x94)+(x92);
  x96 = (x95)+(x90);
  x97 = (x75)+(x93);
  x98 = (uintptr_t)((x97)<(x75));
  x99 = (x98)+(x96);
  x100 = ((x97)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x99)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x101 = (x97)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x102 = (x76)>>_br2_shamt((uintptr_t)(UINTMAX_C(48)));
  x103 = (x76)&((uintptr_t)(UINTMAX_C(281474976710655)));
  x104 = ((x102)+((x101)<<_br2_shamt((uintptr_t)(UINTMAX_C(4)))))*((uintptr_t)(UINTMAX_C(4294968273)));
  x105 = _br2_mulhuu(((x102)+((x101)<<_br2_shamt((uintptr_t)(UINTMAX_C(4))))), ((uintptr_t)(UINTMAX_C(4294968273))));
  x106 = (x0)*(x5);
  x107 = _br2_mulhuu((x0), (x5));
  x108 = (x106)+(x104);
  x109 = (uintptr_t)((x108)<(x106));
  x110 = (x109)+(x107);
  x111 = (x110)+(x105);
  x112 = ((x108)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x111)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x113 = (x108)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x114 = (x4)*(x7);
  x115 = _br2_mulhuu((x4), (x7));
  x116 = (x3)*(x8);
  x117 = _br2_mulhuu((x3), (x8));
  x118 = (x116)+(x114);
  x119 = (uintptr_t)((x118)<(x116));
  x120 = (x119)+(x117);
  x121 = (x120)+(x115);
  x122 = (x2)*(x9);
  x123 = _br2_mulhuu((x2), (x9));
  x124 = (x122)+(x118);
  x125 = (uintptr_t)((x124)<(x122));
  x126 = (x125)+(x123);
  x127 = (x126)+(x121);
  x128 = (x100)+(x124);
  x129 = (uintptr_t)((x128)<(x100));
  x130 = (x129)+(x127);
  x131 = ((x128)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x130)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x132 = (x128)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x133 = (x132)*((uintptr_t)(UINTMAX_C(68719492368)));
  x134 = _br2_mulhuu((x132), ((uintptr_t)(UINTMAX_C(68719492368))));
  x135 = (x1)*(x5);
  x136 = _br2_mulhuu((x1), (x5));
  x137 = (x0)*(x6);
  x138 = _br2_mulhuu((x0), (x6));
  x139 = (x137)+(x135);
  x140 = (uintptr_t)((x139)<(x137));
  x141 = (x140)+(x138);
  x142 = (x141)+(x136);
  x143 = (x112)+(x139);
  x144 = (uintptr_t)((x143)<(x112));
  x145 = (x144)+(x142);
  x146 = (x143)+(x133);
  x147 = (uintptr_t)((x146)<(x143));
  x148 = (x147)+(x145);
  x149 = (x148)+(x134);
  x150 = ((x146)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x149)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x151 = (x146)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x152 = (x4)*(x8);
  x153 = _br2_mulhuu((x4), (x8));
  x154 = (x3)*(x9);
  x155 = _br2_mulhuu((x3), (x9));
  x156 = (x154)+(x152);
  x157 = (uintptr_t)((x156)<(x154));
  x158 = (x157)+(x155);
  x159 = (x158)+(x153);
  x160 = (x131)+(x156);
  x161 = (uintptr_t)((x160)<(x131));
  x162 = (x161)+(x159);
  x163 = (x160)*((uintptr_t)(UINTMAX_C(68719492368)));
  x164 = _br2_mulhuu((x160), ((uintptr_t)(UINTMAX_C(68719492368))));
  x165 = (x2)*(x5);
  x166 = _br2_mulhuu((x2), (x5));
  x167 = (x1)*(x6);
  x168 = _br2_mulhuu((x1), (x6));
  x169 = (x167)+(x165);
  x170 = (uintptr_t)((x169)<(x167));
  x171 = (x170)+(x168);
  x172 = (x171)+(x166);
  x173 = (x0)*(x7);
  x174 = _br2_mulhuu((x0), (x7));
  x175 = (x173)+(x169);
  x176 = (uintptr_t)((x175)<(x173));
  x177 = (x176)+(x174);
  x178 = (x177)+(x172);
  x179 = (x150)+(x175);
  x180 = (uintptr_t)((x179)<(x150));
  x181 = (x180)+(x178);
  x182 = (x179)+(x163);
  x183 = (uintptr_t)((x182)<(x179));
  x184 = (x183)+(x181);
  x185 = (x184)+(x164);
  x186 = ((x182)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x185)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x187 = (x182)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x188 = (x162)*((uintptr_t)(UINTMAX_C(281475040739328)));
  x189 = _br2_mulhuu((x162), ((uintptr_t)(UINTMAX_C(281475040739328))));
  x190 = ((x186)+(x39))+(x188);
  x191 = (uintptr_t)((x190)<((x186)+(x39)));
  x192 = (x191)+(x189);
  x193 = ((x190)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x192)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x194 = (x190)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x195 = (x193)+(x103);
  x196 = x113;
  x197 = x151;
  x198 = x187;
  x199 = x194;
  x200 = x195;
  /*skip*/
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(0))), x196, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(8))), x197, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(16))), x198, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(24))), x199, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(32))), x200, sizeof(uintptr_t));
  /*skip*/
  return;
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_secp256k1_dettman_mul(uint64_t out1[5], const uint64_t arg1[5], const uint64_t arg2[5]) {
  internal_fiat_secp256k1_dettman_mul((uintptr_t)out1, (uintptr_t)arg1, (uintptr_t)arg2);
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x17fffffffffff]]
 */
static
void internal_fiat_secp256k1_dettman_square(uintptr_t out0, uintptr_t in0) {
  uintptr_t x9, x13, x15, x18, x16, x19, x14, x11, x17, x22, x20, x23, x12, x24, x21, x10, x29, x31, x34, x32, x35, x30, x33, x37, x40, x38, x41, x36, x39, x25, x44, x42, x27, x43, x47, x45, x48, x28, x49, x46, x7, x52, x54, x57, x55, x58, x53, x56, x50, x61, x59, x62, x60, x51, x65, x64, x0, x67, x69, x72, x70, x73, x68, x74, x71, x3, x6, x77, x79, x82, x80, x83, x78, x81, x63, x86, x84, x87, x85, x89, x92, x75, x95, x93, x90, x94, x98, x96, x99, x91, x100, x97, x5, x4, x103, x88, x106, x104, x105, x1, x8, x2, x110, x112, x115, x113, x116, x111, x114, x101, x119, x117, x108, x118, x122, x120, x123, x109, x124, x121, x107, x127, x125, x26, x130, x128, x131, x129, x132, x66, x76, x102, x126, x133, x134, x135, x136, x137, x138, x139;
  x0 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(0))), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(8))), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(16))), sizeof(uintptr_t));
  x3 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(24))), sizeof(uintptr_t));
  x4 = _br2_load((in0)+((uintptr_t)(UINTMAX_C(32))), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x5 = (x3)*((uintptr_t)(UINTMAX_C(2)));
  x6 = (x2)*((uintptr_t)(UINTMAX_C(2)));
  x7 = (x1)*((uintptr_t)(UINTMAX_C(2)));
  x8 = (x0)*((uintptr_t)(UINTMAX_C(2)));
  x9 = (x4)*(x4);
  x10 = _br2_mulhuu((x4), (x4));
  x11 = (x9)*((uintptr_t)(UINTMAX_C(68719492368)));
  x12 = _br2_mulhuu((x9), ((uintptr_t)(UINTMAX_C(68719492368))));
  x13 = (x7)*(x2);
  x14 = _br2_mulhuu((x7), (x2));
  x15 = (x8)*(x3);
  x16 = _br2_mulhuu((x8), (x3));
  x17 = (x15)+(x13);
  x18 = (uintptr_t)((x17)<(x15));
  x19 = (x18)+(x16);
  x20 = (x19)+(x14);
  x21 = (x17)+(x11);
  x22 = (uintptr_t)((x21)<(x17));
  x23 = (x22)+(x20);
  x24 = (x23)+(x12);
  x25 = ((x21)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x24)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x26 = (x21)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x27 = (x10)*((uintptr_t)(UINTMAX_C(281475040739328)));
  x28 = _br2_mulhuu((x10), ((uintptr_t)(UINTMAX_C(281475040739328))));
  x29 = (x2)*(x2);
  x30 = _br2_mulhuu((x2), (x2));
  x31 = (x7)*(x3);
  x32 = _br2_mulhuu((x7), (x3));
  x33 = (x31)+(x29);
  x34 = (uintptr_t)((x33)<(x31));
  x35 = (x34)+(x32);
  x36 = (x35)+(x30);
  x37 = (x8)*(x4);
  x38 = _br2_mulhuu((x8), (x4));
  x39 = (x37)+(x33);
  x40 = (uintptr_t)((x39)<(x37));
  x41 = (x40)+(x38);
  x42 = (x41)+(x36);
  x43 = (x25)+(x39);
  x44 = (uintptr_t)((x43)<(x25));
  x45 = (x44)+(x42);
  x46 = (x43)+(x27);
  x47 = (uintptr_t)((x46)<(x43));
  x48 = (x47)+(x45);
  x49 = (x48)+(x28);
  x50 = ((x46)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x49)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x51 = (x46)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x52 = (x6)*(x3);
  x53 = _br2_mulhuu((x6), (x3));
  x54 = (x7)*(x4);
  x55 = _br2_mulhuu((x7), (x4));
  x56 = (x54)+(x52);
  x57 = (uintptr_t)((x56)<(x54));
  x58 = (x57)+(x55);
  x59 = (x58)+(x53);
  x60 = (x50)+(x56);
  x61 = (uintptr_t)((x60)<(x50));
  x62 = (x61)+(x59);
  x63 = ((x60)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x62)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x64 = (x60)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x65 = (x51)>>_br2_shamt((uintptr_t)(UINTMAX_C(48)));
  x66 = (x51)&((uintptr_t)(UINTMAX_C(281474976710655)));
  x67 = ((x65)+((x64)<<_br2_shamt((uintptr_t)(UINTMAX_C(4)))))*((uintptr_t)(UINTMAX_C(4294968273)));
  x68 = _br2_mulhuu(((x65)+((x64)<<_br2_shamt((uintptr_t)(UINTMAX_C(4))))), ((uintptr_t)(UINTMAX_C(4294968273))));
  x69 = (x0)*(x0);
  x70 = _br2_mulhuu((x0), (x0));
  x71 = (x69)+(x67);
  x72 = (uintptr_t)((x71)<(x69));
  x73 = (x72)+(x70);
  x74 = (x73)+(x68);
  x75 = ((x71)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x74)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x76 = (x71)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x77 = (x3)*(x3);
  x78 = _br2_mulhuu((x3), (x3));
  x79 = (x6)*(x4);
  x80 = _br2_mulhuu((x6), (x4));
  x81 = (x79)+(x77);
  x82 = (uintptr_t)((x81)<(x79));
  x83 = (x82)+(x80);
  x84 = (x83)+(x78);
  x85 = (x63)+(x81);
  x86 = (uintptr_t)((x85)<(x63));
  x87 = (x86)+(x84);
  x88 = ((x85)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x87)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x89 = (x85)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x90 = (x89)*((uintptr_t)(UINTMAX_C(68719492368)));
  x91 = _br2_mulhuu((x89), ((uintptr_t)(UINTMAX_C(68719492368))));
  x92 = (x8)*(x1);
  x93 = _br2_mulhuu((x8), (x1));
  x94 = (x75)+(x92);
  x95 = (uintptr_t)((x94)<(x75));
  x96 = (x95)+(x93);
  x97 = (x94)+(x90);
  x98 = (uintptr_t)((x97)<(x94));
  x99 = (x98)+(x96);
  x100 = (x99)+(x91);
  x101 = ((x97)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x100)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x102 = (x97)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x103 = (x5)*(x4);
  x104 = _br2_mulhuu((x5), (x4));
  x105 = (x88)+(x103);
  x106 = (uintptr_t)((x105)<(x88));
  x107 = (x106)+(x104);
  x108 = (x105)*((uintptr_t)(UINTMAX_C(68719492368)));
  x109 = _br2_mulhuu((x105), ((uintptr_t)(UINTMAX_C(68719492368))));
  x110 = (x1)*(x1);
  x111 = _br2_mulhuu((x1), (x1));
  x112 = (x8)*(x2);
  x113 = _br2_mulhuu((x8), (x2));
  x114 = (x112)+(x110);
  x115 = (uintptr_t)((x114)<(x112));
  x116 = (x115)+(x113);
  x117 = (x116)+(x111);
  x118 = (x101)+(x114);
  x119 = (uintptr_t)((x118)<(x101));
  x120 = (x119)+(x117);
  x121 = (x118)+(x108);
  x122 = (uintptr_t)((x121)<(x118));
  x123 = (x122)+(x120);
  x124 = (x123)+(x109);
  x125 = ((x121)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x124)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x126 = (x121)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x127 = (x107)*((uintptr_t)(UINTMAX_C(281475040739328)));
  x128 = _br2_mulhuu((x107), ((uintptr_t)(UINTMAX_C(281475040739328))));
  x129 = ((x125)+(x26))+(x127);
  x130 = (uintptr_t)((x129)<((x125)+(x26)));
  x131 = (x130)+(x128);
  x132 = ((x129)>>_br2_shamt((uintptr_t)(UINTMAX_C(52))))|((x131)<<_br2_shamt((uintptr_t)(UINTMAX_C(12))));
  x133 = (x129)&((uintptr_t)(UINTMAX_C(4503599627370495)));
  x134 = (x132)+(x66);
  x135 = x76;
  x136 = x102;
  x137 = x126;
  x138 = x133;
  x139 = x134;
  /*skip*/
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(0))), x135, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(8))), x136, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(16))), x137, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(24))), x138, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)(UINTMAX_C(32))), x139, sizeof(uintptr_t));
  /*skip*/
  return;
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_secp256k1_dettman_square(uint64_t out1[5], const uint64_t arg1[5]) {
  internal_fiat_secp256k1_dettman_square((uintptr_t)out1, (uintptr_t)arg1);
}
