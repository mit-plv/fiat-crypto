/* Autogenerated: src/ExtractionOCaml/bedrock2_unsaturated_solinas --lang bedrock2 --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select poly1305 32 '(auto)' '2^130 - 5' carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes */
/* curve description: poly1305 */
/* machine_wordsize = 32 (from "32") */
/* requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes */
/* n = 5 (from "(auto)") */
/* s-c = 2^130 - [(1, 5)] (from "2^130 - 5") */
/* tight_bounds_multiplier = 1 (from "") */
/*  */
/* Computed values: */
/* carry_chain = [0, 1, 2, 3, 4, 0, 1] */
/* eval z = z[0] + (z[1] << 26) + (z[2] << 52) + (z[3] << 78) + (z[4] << 104) */
/* bytes_eval z = z[0] + (z[1] << 8) + (z[2] << 16) + (z[3] << 24) + (z[4] << 32) + (z[5] << 40) + (z[6] << 48) + (z[7] << 56) + (z[8] << 64) + (z[9] << 72) + (z[10] << 80) + (z[11] << 88) + (z[12] << 96) + (z[13] << 104) + (z[14] << 112) + (z[15] << 120) + (z[16] << 128) */
/* balance = [0x7fffff6, 0x7fffffe, 0x7fffffe, 0x7fffffe, 0x7fffffe] */

#include <stdint.h>


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
 *   in1: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 */
void fiat_poly1305_carry_mul(uintptr_t out0, uintptr_t in0, uintptr_t in1) {
  uintptr_t x4, x3, x2, x1, x9, x8, x7, x6, x0, x5, x16, x22, x61, x23, x62, x17, x60, x26, x65, x27, x66, x63, x64, x28, x69, x29, x70, x67, x68, x58, x73, x59, x74, x71, x75, x72, x30, x32, x80, x33, x81, x31, x79, x36, x84, x37, x85, x82, x83, x42, x88, x43, x89, x86, x87, x50, x92, x51, x93, x90, x10, x34, x96, x35, x97, x11, x95, x38, x100, x39, x101, x98, x99, x44, x104, x45, x105, x102, x103, x52, x108, x53, x109, x106, x12, x18, x112, x19, x113, x13, x111, x40, x116, x41, x117, x114, x115, x46, x120, x47, x121, x118, x119, x54, x124, x55, x125, x122, x14, x20, x128, x21, x129, x15, x127, x24, x132, x25, x133, x130, x131, x48, x136, x49, x137, x134, x135, x56, x140, x57, x141, x138, x139, x76, x144, x77, x145, x142, x146, x143, x123, x147, x151, x148, x152, x126, x153, x150, x107, x154, x158, x155, x159, x110, x160, x157, x91, x161, x165, x162, x166, x94, x167, x164, x168, x170, x78, x173, x171, x174, x172, x175, x149, x177, x178, x156, x176, x179, x180, x163, x169, x181, x182, x183, x184, x185;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)4ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)12ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  /*skip*/
  x5 = *(uintptr_t*)((in1)+((uintptr_t)0ULL));
  x6 = *(uintptr_t*)((in1)+((uintptr_t)4ULL));
  x7 = *(uintptr_t*)((in1)+((uintptr_t)8ULL));
  x8 = *(uintptr_t*)((in1)+((uintptr_t)12ULL));
  x9 = *(uintptr_t*)((in1)+((uintptr_t)16ULL));
  /*skip*/
  /*skip*/
  x10 = (x4)*((x9)*((uintptr_t)5ULL));
  x11 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*((x9)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x4)*((x9)*((uintptr_t)5ULL)))>>64;
  x12 = (x4)*((x8)*((uintptr_t)5ULL));
  x13 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*((x8)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x4)*((x8)*((uintptr_t)5ULL)))>>64;
  x14 = (x4)*((x7)*((uintptr_t)5ULL));
  x15 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*((x7)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x4)*((x7)*((uintptr_t)5ULL)))>>64;
  x16 = (x4)*((x6)*((uintptr_t)5ULL));
  x17 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*((x6)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x4)*((x6)*((uintptr_t)5ULL)))>>64;
  x18 = (x3)*((x9)*((uintptr_t)5ULL));
  x19 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*((x9)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x3)*((x9)*((uintptr_t)5ULL)))>>64;
  x20 = (x3)*((x8)*((uintptr_t)5ULL));
  x21 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*((x8)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x3)*((x8)*((uintptr_t)5ULL)))>>64;
  x22 = (x3)*((x7)*((uintptr_t)5ULL));
  x23 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*((x7)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x3)*((x7)*((uintptr_t)5ULL)))>>64;
  x24 = (x2)*((x9)*((uintptr_t)5ULL));
  x25 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*((x9)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x2)*((x9)*((uintptr_t)5ULL)))>>64;
  x26 = (x2)*((x8)*((uintptr_t)5ULL));
  x27 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*((x8)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x2)*((x8)*((uintptr_t)5ULL)))>>64;
  x28 = (x1)*((x9)*((uintptr_t)5ULL));
  x29 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*((x9)*((uintptr_t)5ULL)))>>32 : ((__uint128_t)(x1)*((x9)*((uintptr_t)5ULL)))>>64;
  x30 = (x4)*(x5);
  x31 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*(x5))>>32 : ((__uint128_t)(x4)*(x5))>>64;
  x32 = (x3)*(x6);
  x33 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*(x6))>>32 : ((__uint128_t)(x3)*(x6))>>64;
  x34 = (x3)*(x5);
  x35 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*(x5))>>32 : ((__uint128_t)(x3)*(x5))>>64;
  x36 = (x2)*(x7);
  x37 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x7))>>32 : ((__uint128_t)(x2)*(x7))>>64;
  x38 = (x2)*(x6);
  x39 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x6))>>32 : ((__uint128_t)(x2)*(x6))>>64;
  x40 = (x2)*(x5);
  x41 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x5))>>32 : ((__uint128_t)(x2)*(x5))>>64;
  x42 = (x1)*(x8);
  x43 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x8))>>32 : ((__uint128_t)(x1)*(x8))>>64;
  x44 = (x1)*(x7);
  x45 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x7))>>32 : ((__uint128_t)(x1)*(x7))>>64;
  x46 = (x1)*(x6);
  x47 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x6))>>32 : ((__uint128_t)(x1)*(x6))>>64;
  x48 = (x1)*(x5);
  x49 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x5))>>32 : ((__uint128_t)(x1)*(x5))>>64;
  x50 = (x0)*(x9);
  x51 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x9))>>32 : ((__uint128_t)(x0)*(x9))>>64;
  x52 = (x0)*(x8);
  x53 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x8))>>32 : ((__uint128_t)(x0)*(x8))>>64;
  x54 = (x0)*(x7);
  x55 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x7))>>32 : ((__uint128_t)(x0)*(x7))>>64;
  x56 = (x0)*(x6);
  x57 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x6))>>32 : ((__uint128_t)(x0)*(x6))>>64;
  x58 = (x0)*(x5);
  x59 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x5))>>32 : ((__uint128_t)(x0)*(x5))>>64;
  x60 = (x22)+(x16);
  x61 = (x60)<(x22);
  x62 = (x61)+(x23);
  x63 = (x62)+(x17);
  x64 = (x26)+(x60);
  x65 = (x64)<(x26);
  x66 = (x65)+(x27);
  x67 = (x66)+(x63);
  x68 = (x28)+(x64);
  x69 = (x68)<(x28);
  x70 = (x69)+(x29);
  x71 = (x70)+(x67);
  x72 = (x58)+(x68);
  x73 = (x72)<(x58);
  x74 = (x73)+(x59);
  x75 = (x74)+(x71);
  x76 = ((x72)>>((uintptr_t)26ULL))|((x75)<<((uintptr_t)6ULL));
  x77 = (x75)>>((uintptr_t)26ULL);
  x78 = (x72)&((uintptr_t)67108863ULL);
  x79 = (x32)+(x30);
  x80 = (x79)<(x32);
  x81 = (x80)+(x33);
  x82 = (x81)+(x31);
  x83 = (x36)+(x79);
  x84 = (x83)<(x36);
  x85 = (x84)+(x37);
  x86 = (x85)+(x82);
  x87 = (x42)+(x83);
  x88 = (x87)<(x42);
  x89 = (x88)+(x43);
  x90 = (x89)+(x86);
  x91 = (x50)+(x87);
  x92 = (x91)<(x50);
  x93 = (x92)+(x51);
  x94 = (x93)+(x90);
  x95 = (x34)+(x10);
  x96 = (x95)<(x34);
  x97 = (x96)+(x35);
  x98 = (x97)+(x11);
  x99 = (x38)+(x95);
  x100 = (x99)<(x38);
  x101 = (x100)+(x39);
  x102 = (x101)+(x98);
  x103 = (x44)+(x99);
  x104 = (x103)<(x44);
  x105 = (x104)+(x45);
  x106 = (x105)+(x102);
  x107 = (x52)+(x103);
  x108 = (x107)<(x52);
  x109 = (x108)+(x53);
  x110 = (x109)+(x106);
  x111 = (x18)+(x12);
  x112 = (x111)<(x18);
  x113 = (x112)+(x19);
  x114 = (x113)+(x13);
  x115 = (x40)+(x111);
  x116 = (x115)<(x40);
  x117 = (x116)+(x41);
  x118 = (x117)+(x114);
  x119 = (x46)+(x115);
  x120 = (x119)<(x46);
  x121 = (x120)+(x47);
  x122 = (x121)+(x118);
  x123 = (x54)+(x119);
  x124 = (x123)<(x54);
  x125 = (x124)+(x55);
  x126 = (x125)+(x122);
  x127 = (x20)+(x14);
  x128 = (x127)<(x20);
  x129 = (x128)+(x21);
  x130 = (x129)+(x15);
  x131 = (x24)+(x127);
  x132 = (x131)<(x24);
  x133 = (x132)+(x25);
  x134 = (x133)+(x130);
  x135 = (x48)+(x131);
  x136 = (x135)<(x48);
  x137 = (x136)+(x49);
  x138 = (x137)+(x134);
  x139 = (x56)+(x135);
  x140 = (x139)<(x56);
  x141 = (x140)+(x57);
  x142 = (x141)+(x138);
  x143 = (x76)+(x139);
  x144 = (x143)<(x76);
  x145 = (x144)+(x77);
  x146 = (x145)+(x142);
  x147 = ((x143)>>((uintptr_t)26ULL))|((x146)<<((uintptr_t)6ULL));
  x148 = (x146)>>((uintptr_t)26ULL);
  x149 = (x143)&((uintptr_t)67108863ULL);
  x150 = (x147)+(x123);
  x151 = (x150)<(x147);
  x152 = (x151)+(x148);
  x153 = (x152)+(x126);
  x154 = ((x150)>>((uintptr_t)26ULL))|((x153)<<((uintptr_t)6ULL));
  x155 = (x153)>>((uintptr_t)26ULL);
  x156 = (x150)&((uintptr_t)67108863ULL);
  x157 = (x154)+(x107);
  x158 = (x157)<(x154);
  x159 = (x158)+(x155);
  x160 = (x159)+(x110);
  x161 = ((x157)>>((uintptr_t)26ULL))|((x160)<<((uintptr_t)6ULL));
  x162 = (x160)>>((uintptr_t)26ULL);
  x163 = (x157)&((uintptr_t)67108863ULL);
  x164 = (x161)+(x91);
  x165 = (x164)<(x161);
  x166 = (x165)+(x162);
  x167 = (x166)+(x94);
  x168 = ((x164)>>((uintptr_t)26ULL))|((x167)<<((uintptr_t)6ULL));
  x169 = (x164)&((uintptr_t)67108863ULL);
  x170 = (x168)*((uintptr_t)5ULL);
  x171 = sizeof(intptr_t) == 4 ? ((uint64_t)(x168)*((uintptr_t)5ULL))>>32 : ((__uint128_t)(x168)*((uintptr_t)5ULL))>>64;
  x172 = (x78)+(x170);
  x173 = (x172)<(x78);
  x174 = (x173)+(x171);
  x175 = ((x172)>>((uintptr_t)26ULL))|((x174)<<((uintptr_t)6ULL));
  x176 = (x172)&((uintptr_t)67108863ULL);
  x177 = (x175)+(x149);
  x178 = (x177)>>((uintptr_t)26ULL);
  x179 = (x177)&((uintptr_t)67108863ULL);
  x180 = (x178)+(x156);
  x181 = x176;
  x182 = x179;
  x183 = x180;
  x184 = x163;
  x185 = x169;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x181;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x182;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x183;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x184;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x185;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 */
void fiat_poly1305_carry_square(uintptr_t out0, uintptr_t in0) {
  uintptr_t x4, x5, x3, x8, x9, x2, x6, x1, x7, x10, x11, x12, x0, x21, x25, x44, x26, x45, x22, x43, x41, x48, x42, x49, x46, x50, x47, x23, x27, x55, x28, x56, x24, x54, x33, x59, x34, x60, x57, x13, x29, x63, x30, x64, x14, x62, x35, x67, x36, x68, x65, x15, x31, x71, x32, x72, x16, x70, x37, x75, x38, x76, x73, x17, x19, x79, x20, x80, x18, x78, x39, x83, x40, x84, x81, x82, x51, x87, x52, x88, x85, x89, x86, x74, x90, x94, x91, x95, x77, x96, x93, x66, x97, x101, x98, x102, x69, x103, x100, x58, x104, x108, x105, x109, x61, x110, x107, x111, x113, x53, x116, x114, x117, x115, x118, x92, x120, x121, x99, x119, x122, x123, x106, x112, x124, x125, x126, x127, x128;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)4ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)12ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  /*skip*/
  /*skip*/
  x5 = (x4)*((uintptr_t)5ULL);
  x6 = (x5)*((uintptr_t)2ULL);
  x7 = (x4)*((uintptr_t)2ULL);
  x8 = (x3)*((uintptr_t)5ULL);
  x9 = (x8)*((uintptr_t)2ULL);
  x10 = (x3)*((uintptr_t)2ULL);
  x11 = (x2)*((uintptr_t)2ULL);
  x12 = (x1)*((uintptr_t)2ULL);
  x13 = (x4)*(x5);
  x14 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*(x5))>>32 : ((__uint128_t)(x4)*(x5))>>64;
  x15 = (x3)*(x6);
  x16 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*(x6))>>32 : ((__uint128_t)(x3)*(x6))>>64;
  x17 = (x3)*(x8);
  x18 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*(x8))>>32 : ((__uint128_t)(x3)*(x8))>>64;
  x19 = (x2)*(x6);
  x20 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x6))>>32 : ((__uint128_t)(x2)*(x6))>>64;
  x21 = (x2)*(x9);
  x22 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x9))>>32 : ((__uint128_t)(x2)*(x9))>>64;
  x23 = (x2)*(x2);
  x24 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x2))>>32 : ((__uint128_t)(x2)*(x2))>>64;
  x25 = (x1)*(x6);
  x26 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x6))>>32 : ((__uint128_t)(x1)*(x6))>>64;
  x27 = (x1)*(x10);
  x28 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x10))>>32 : ((__uint128_t)(x1)*(x10))>>64;
  x29 = (x1)*(x11);
  x30 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x11))>>32 : ((__uint128_t)(x1)*(x11))>>64;
  x31 = (x1)*(x1);
  x32 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x1))>>32 : ((__uint128_t)(x1)*(x1))>>64;
  x33 = (x0)*(x7);
  x34 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x7))>>32 : ((__uint128_t)(x0)*(x7))>>64;
  x35 = (x0)*(x10);
  x36 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x10))>>32 : ((__uint128_t)(x0)*(x10))>>64;
  x37 = (x0)*(x11);
  x38 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x11))>>32 : ((__uint128_t)(x0)*(x11))>>64;
  x39 = (x0)*(x12);
  x40 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x12))>>32 : ((__uint128_t)(x0)*(x12))>>64;
  x41 = (x0)*(x0);
  x42 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x0))>>32 : ((__uint128_t)(x0)*(x0))>>64;
  x43 = (x25)+(x21);
  x44 = (x43)<(x25);
  x45 = (x44)+(x26);
  x46 = (x45)+(x22);
  x47 = (x41)+(x43);
  x48 = (x47)<(x41);
  x49 = (x48)+(x42);
  x50 = (x49)+(x46);
  x51 = ((x47)>>((uintptr_t)26ULL))|((x50)<<((uintptr_t)6ULL));
  x52 = (x50)>>((uintptr_t)26ULL);
  x53 = (x47)&((uintptr_t)67108863ULL);
  x54 = (x27)+(x23);
  x55 = (x54)<(x27);
  x56 = (x55)+(x28);
  x57 = (x56)+(x24);
  x58 = (x33)+(x54);
  x59 = (x58)<(x33);
  x60 = (x59)+(x34);
  x61 = (x60)+(x57);
  x62 = (x29)+(x13);
  x63 = (x62)<(x29);
  x64 = (x63)+(x30);
  x65 = (x64)+(x14);
  x66 = (x35)+(x62);
  x67 = (x66)<(x35);
  x68 = (x67)+(x36);
  x69 = (x68)+(x65);
  x70 = (x31)+(x15);
  x71 = (x70)<(x31);
  x72 = (x71)+(x32);
  x73 = (x72)+(x16);
  x74 = (x37)+(x70);
  x75 = (x74)<(x37);
  x76 = (x75)+(x38);
  x77 = (x76)+(x73);
  x78 = (x19)+(x17);
  x79 = (x78)<(x19);
  x80 = (x79)+(x20);
  x81 = (x80)+(x18);
  x82 = (x39)+(x78);
  x83 = (x82)<(x39);
  x84 = (x83)+(x40);
  x85 = (x84)+(x81);
  x86 = (x51)+(x82);
  x87 = (x86)<(x51);
  x88 = (x87)+(x52);
  x89 = (x88)+(x85);
  x90 = ((x86)>>((uintptr_t)26ULL))|((x89)<<((uintptr_t)6ULL));
  x91 = (x89)>>((uintptr_t)26ULL);
  x92 = (x86)&((uintptr_t)67108863ULL);
  x93 = (x90)+(x74);
  x94 = (x93)<(x90);
  x95 = (x94)+(x91);
  x96 = (x95)+(x77);
  x97 = ((x93)>>((uintptr_t)26ULL))|((x96)<<((uintptr_t)6ULL));
  x98 = (x96)>>((uintptr_t)26ULL);
  x99 = (x93)&((uintptr_t)67108863ULL);
  x100 = (x97)+(x66);
  x101 = (x100)<(x97);
  x102 = (x101)+(x98);
  x103 = (x102)+(x69);
  x104 = ((x100)>>((uintptr_t)26ULL))|((x103)<<((uintptr_t)6ULL));
  x105 = (x103)>>((uintptr_t)26ULL);
  x106 = (x100)&((uintptr_t)67108863ULL);
  x107 = (x104)+(x58);
  x108 = (x107)<(x104);
  x109 = (x108)+(x105);
  x110 = (x109)+(x61);
  x111 = ((x107)>>((uintptr_t)26ULL))|((x110)<<((uintptr_t)6ULL));
  x112 = (x107)&((uintptr_t)67108863ULL);
  x113 = (x111)*((uintptr_t)5ULL);
  x114 = sizeof(intptr_t) == 4 ? ((uint64_t)(x111)*((uintptr_t)5ULL))>>32 : ((__uint128_t)(x111)*((uintptr_t)5ULL))>>64;
  x115 = (x53)+(x113);
  x116 = (x115)<(x53);
  x117 = (x116)+(x114);
  x118 = ((x115)>>((uintptr_t)26ULL))|((x117)<<((uintptr_t)6ULL));
  x119 = (x115)&((uintptr_t)67108863ULL);
  x120 = (x118)+(x92);
  x121 = (x120)>>((uintptr_t)26ULL);
  x122 = (x120)&((uintptr_t)67108863ULL);
  x123 = (x121)+(x99);
  x124 = x119;
  x125 = x122;
  x126 = x123;
  x127 = x106;
  x128 = x112;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x124;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x125;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x126;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x127;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x128;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 */
void fiat_poly1305_carry(uintptr_t out0, uintptr_t in0) {
  uintptr_t x0, x1, x2, x3, x4, x5, x6, x10, x11, x7, x8, x9, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)4ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)12ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  /*skip*/
  /*skip*/
  x5 = x0;
  x6 = ((x5)>>((uintptr_t)26ULL))+(x1);
  x7 = ((x6)>>((uintptr_t)26ULL))+(x2);
  x8 = ((x7)>>((uintptr_t)26ULL))+(x3);
  x9 = ((x8)>>((uintptr_t)26ULL))+(x4);
  x10 = ((x5)&((uintptr_t)67108863ULL))+(((x9)>>((uintptr_t)26ULL))*((uintptr_t)5ULL));
  x11 = ((x10)>>((uintptr_t)26ULL))+((x6)&((uintptr_t)67108863ULL));
  x12 = (x10)&((uintptr_t)67108863ULL);
  x13 = (x11)&((uintptr_t)67108863ULL);
  x14 = ((x11)>>((uintptr_t)26ULL))+((x7)&((uintptr_t)67108863ULL));
  x15 = (x8)&((uintptr_t)67108863ULL);
  x16 = (x9)&((uintptr_t)67108863ULL);
  x17 = x12;
  x18 = x13;
  x19 = x14;
  x20 = x15;
  x21 = x16;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x17;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x18;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x19;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x20;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x21;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 *   in1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
 */
void fiat_poly1305_add(uintptr_t out0, uintptr_t in0, uintptr_t in1) {
  uintptr_t x0, x5, x1, x6, x2, x7, x3, x8, x4, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)4ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)12ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  /*skip*/
  x5 = *(uintptr_t*)((in1)+((uintptr_t)0ULL));
  x6 = *(uintptr_t*)((in1)+((uintptr_t)4ULL));
  x7 = *(uintptr_t*)((in1)+((uintptr_t)8ULL));
  x8 = *(uintptr_t*)((in1)+((uintptr_t)12ULL));
  x9 = *(uintptr_t*)((in1)+((uintptr_t)16ULL));
  /*skip*/
  /*skip*/
  x10 = (x0)+(x5);
  x11 = (x1)+(x6);
  x12 = (x2)+(x7);
  x13 = (x3)+(x8);
  x14 = (x4)+(x9);
  x15 = x10;
  x16 = x11;
  x17 = x12;
  x18 = x13;
  x19 = x14;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x15;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x16;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x17;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x18;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x19;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 *   in1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
 */
void fiat_poly1305_sub(uintptr_t out0, uintptr_t in0, uintptr_t in1) {
  uintptr_t x0, x5, x1, x6, x2, x7, x3, x8, x4, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)4ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)12ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  /*skip*/
  x5 = *(uintptr_t*)((in1)+((uintptr_t)0ULL));
  x6 = *(uintptr_t*)((in1)+((uintptr_t)4ULL));
  x7 = *(uintptr_t*)((in1)+((uintptr_t)8ULL));
  x8 = *(uintptr_t*)((in1)+((uintptr_t)12ULL));
  x9 = *(uintptr_t*)((in1)+((uintptr_t)16ULL));
  /*skip*/
  /*skip*/
  x10 = (((uintptr_t)134217718ULL)+(x0))-(x5);
  x11 = (((uintptr_t)134217726ULL)+(x1))-(x6);
  x12 = (((uintptr_t)134217726ULL)+(x2))-(x7);
  x13 = (((uintptr_t)134217726ULL)+(x3))-(x8);
  x14 = (((uintptr_t)134217726ULL)+(x4))-(x9);
  x15 = x10;
  x16 = x11;
  x17 = x12;
  x18 = x13;
  x19 = x14;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x15;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x16;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x17;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x18;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x19;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
 */
void fiat_poly1305_opp(uintptr_t out0, uintptr_t in0) {
  uintptr_t x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)4ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)12ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  /*skip*/
  /*skip*/
  x5 = ((uintptr_t)134217718ULL)-(x0);
  x6 = ((uintptr_t)134217726ULL)-(x1);
  x7 = ((uintptr_t)134217726ULL)-(x2);
  x8 = ((uintptr_t)134217726ULL)-(x3);
  x9 = ((uintptr_t)134217726ULL)-(x4);
  x10 = x5;
  x11 = x6;
  x12 = x7;
  x13 = x8;
  x14 = x9;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x10;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x11;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x12;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x13;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x14;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [0x0 ~> 0x1]
 *   in1: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
 *   in2: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
 */
void fiat_poly1305_selectznz(uintptr_t out0, uintptr_t in0, uintptr_t in1, uintptr_t in2) {
  uintptr_t x5, x10, x0, x11, x6, x13, x1, x14, x7, x16, x2, x17, x8, x19, x3, x20, x9, x22, x4, x23, x12, x15, x18, x21, x24, x25, x26, x27, x28, x29;
  /*skip*/
  x0 = *(uintptr_t*)((in1)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in1)+((uintptr_t)4ULL));
  x2 = *(uintptr_t*)((in1)+((uintptr_t)8ULL));
  x3 = *(uintptr_t*)((in1)+((uintptr_t)12ULL));
  x4 = *(uintptr_t*)((in1)+((uintptr_t)16ULL));
  /*skip*/
  x5 = *(uintptr_t*)((in2)+((uintptr_t)0ULL));
  x6 = *(uintptr_t*)((in2)+((uintptr_t)4ULL));
  x7 = *(uintptr_t*)((in2)+((uintptr_t)8ULL));
  x8 = *(uintptr_t*)((in2)+((uintptr_t)12ULL));
  x9 = *(uintptr_t*)((in2)+((uintptr_t)16ULL));
  /*skip*/
  /*skip*/
  x10 = ((uintptr_t)-1ULL)+((in0)==((uintptr_t)0ULL));
  x11 = (x10)^((uintptr_t)4294967295ULL);
  x12 = ((x5)&(x10))|((x0)&(x11));
  x13 = ((uintptr_t)-1ULL)+((in0)==((uintptr_t)0ULL));
  x14 = (x13)^((uintptr_t)4294967295ULL);
  x15 = ((x6)&(x13))|((x1)&(x14));
  x16 = ((uintptr_t)-1ULL)+((in0)==((uintptr_t)0ULL));
  x17 = (x16)^((uintptr_t)4294967295ULL);
  x18 = ((x7)&(x16))|((x2)&(x17));
  x19 = ((uintptr_t)-1ULL)+((in0)==((uintptr_t)0ULL));
  x20 = (x19)^((uintptr_t)4294967295ULL);
  x21 = ((x8)&(x19))|((x3)&(x20));
  x22 = ((uintptr_t)-1ULL)+((in0)==((uintptr_t)0ULL));
  x23 = (x22)^((uintptr_t)4294967295ULL);
  x24 = ((x9)&(x22))|((x4)&(x23));
  x25 = x12;
  x26 = x15;
  x27 = x18;
  x28 = x21;
  x29 = x24;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x25;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x26;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x27;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x28;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x29;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 */
void fiat_poly1305_to_bytes(uintptr_t out0, uintptr_t in0) {
  uintptr_t x0, x6, x7, x8, x5, x1, x10, x11, x12, x14, x15, x13, x2, x17, x18, x19, x21, x22, x20, x3, x24, x25, x26, x28, x29, x27, x4, x31, x32, x33, x35, x36, x34, x38, x9, x40, x41, x43, x16, x44, x45, x47, x46, x48, x50, x23, x51, x52, x54, x53, x55, x57, x30, x58, x59, x61, x60, x62, x64, x37, x65, x39, x66, x63, x56, x49, x42, x72, x74, x70, x76, x77, x79, x81, x69, x83, x84, x86, x88, x68, x90, x91, x93, x95, x67, x99, x101, x71, x73, x75, x78, x80, x82, x85, x87, x89, x92, x94, x96, x97, x98, x100, x102, x103, x104, x105, x106, x107, x108, x109, x110, x111, x112, x113, x114, x115, x116, x117, x118, x119, x120;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)4ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)12ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  /*skip*/
  /*skip*/
  x5 = (x0)-((uintptr_t)67108859ULL);
  x6 = (x0)<(x5);
  x7 = (x5)<(x5);
  x8 = (x6)+(x7);
  x9 = (x5)&((uintptr_t)67108863ULL);
  x10 = ((x8)<<((uintptr_t)6ULL))-((x5)>>((uintptr_t)26ULL));
  x11 = (x1)-((uintptr_t)67108863ULL);
  x12 = (x1)<(x11);
  x13 = (x11)-(x10);
  x14 = (x11)<(x13);
  x15 = (x12)+(x14);
  x16 = (x13)&((uintptr_t)67108863ULL);
  x17 = ((x15)<<((uintptr_t)6ULL))-((x13)>>((uintptr_t)26ULL));
  x18 = (x2)-((uintptr_t)67108863ULL);
  x19 = (x2)<(x18);
  x20 = (x18)-(x17);
  x21 = (x18)<(x20);
  x22 = (x19)+(x21);
  x23 = (x20)&((uintptr_t)67108863ULL);
  x24 = ((x22)<<((uintptr_t)6ULL))-((x20)>>((uintptr_t)26ULL));
  x25 = (x3)-((uintptr_t)67108863ULL);
  x26 = (x3)<(x25);
  x27 = (x25)-(x24);
  x28 = (x25)<(x27);
  x29 = (x26)+(x28);
  x30 = (x27)&((uintptr_t)67108863ULL);
  x31 = ((x29)<<((uintptr_t)6ULL))-((x27)>>((uintptr_t)26ULL));
  x32 = (x4)-((uintptr_t)67108863ULL);
  x33 = (x4)<(x32);
  x34 = (x32)-(x31);
  x35 = (x32)<(x34);
  x36 = (x33)+(x35);
  x37 = (x34)&((uintptr_t)67108863ULL);
  x38 = ((x36)<<((uintptr_t)6ULL))-((x34)>>((uintptr_t)26ULL));
  x39 = ((uintptr_t)-1ULL)+((x38)==((uintptr_t)0ULL));
  x40 = (x9)+((x39)&((uintptr_t)67108859ULL));
  x41 = (x40)<(x9);
  x42 = (x40)&((uintptr_t)67108863ULL);
  x43 = ((x40)>>((uintptr_t)26ULL))+((x41)<<((uintptr_t)6ULL));
  x44 = (x43)+(x16);
  x45 = (x44)<(x16);
  x46 = (x44)+((x39)&((uintptr_t)67108863ULL));
  x47 = (x46)<((x39)&((uintptr_t)67108863ULL));
  x48 = (x45)+(x47);
  x49 = (x46)&((uintptr_t)67108863ULL);
  x50 = ((x46)>>((uintptr_t)26ULL))+((x48)<<((uintptr_t)6ULL));
  x51 = (x50)+(x23);
  x52 = (x51)<(x23);
  x53 = (x51)+((x39)&((uintptr_t)67108863ULL));
  x54 = (x53)<((x39)&((uintptr_t)67108863ULL));
  x55 = (x52)+(x54);
  x56 = (x53)&((uintptr_t)67108863ULL);
  x57 = ((x53)>>((uintptr_t)26ULL))+((x55)<<((uintptr_t)6ULL));
  x58 = (x57)+(x30);
  x59 = (x58)<(x30);
  x60 = (x58)+((x39)&((uintptr_t)67108863ULL));
  x61 = (x60)<((x39)&((uintptr_t)67108863ULL));
  x62 = (x59)+(x61);
  x63 = (x60)&((uintptr_t)67108863ULL);
  x64 = ((x60)>>((uintptr_t)26ULL))+((x62)<<((uintptr_t)6ULL));
  x65 = (x64)+(x37);
  x66 = (x65)+((x39)&((uintptr_t)67108863ULL));
  x67 = (x66)&((uintptr_t)67108863ULL);
  x68 = (x63)<<((uintptr_t)6ULL);
  x69 = (x56)<<((uintptr_t)4ULL);
  x70 = (x49)<<((uintptr_t)2ULL);
  x71 = (x42)&((uintptr_t)255ULL);
  x72 = (x42)>>((uintptr_t)8ULL);
  x73 = (x72)&((uintptr_t)255ULL);
  x74 = (x72)>>((uintptr_t)8ULL);
  x75 = (x74)&((uintptr_t)255ULL);
  x76 = (x74)>>((uintptr_t)8ULL);
  x77 = (x70)+(x76);
  x78 = (x77)&((uintptr_t)255ULL);
  x79 = (x77)>>((uintptr_t)8ULL);
  x80 = (x79)&((uintptr_t)255ULL);
  x81 = (x79)>>((uintptr_t)8ULL);
  x82 = (x81)&((uintptr_t)255ULL);
  x83 = (x81)>>((uintptr_t)8ULL);
  x84 = (x69)+(x83);
  x85 = (x84)&((uintptr_t)255ULL);
  x86 = (x84)>>((uintptr_t)8ULL);
  x87 = (x86)&((uintptr_t)255ULL);
  x88 = (x86)>>((uintptr_t)8ULL);
  x89 = (x88)&((uintptr_t)255ULL);
  x90 = (x88)>>((uintptr_t)8ULL);
  x91 = (x68)+(x90);
  x92 = (x91)&((uintptr_t)255ULL);
  x93 = (x91)>>((uintptr_t)8ULL);
  x94 = (x93)&((uintptr_t)255ULL);
  x95 = (x93)>>((uintptr_t)8ULL);
  x96 = (x95)&((uintptr_t)255ULL);
  x97 = (x95)>>((uintptr_t)8ULL);
  x98 = (x67)&((uintptr_t)255ULL);
  x99 = (x67)>>((uintptr_t)8ULL);
  x100 = (x99)&((uintptr_t)255ULL);
  x101 = (x99)>>((uintptr_t)8ULL);
  x102 = (x101)&((uintptr_t)255ULL);
  x103 = (x101)>>((uintptr_t)8ULL);
  x104 = x71;
  x105 = x73;
  x106 = x75;
  x107 = x78;
  x108 = x80;
  x109 = x82;
  x110 = x85;
  x111 = x87;
  x112 = x89;
  x113 = x92;
  x114 = x94;
  x115 = x96;
  x116 = x97;
  x117 = x98;
  x118 = x100;
  x119 = x102;
  x120 = x103;
  /*skip*/
  *(uint8_t*)((out0)+((uintptr_t)0ULL)) = x104;
  *(uint8_t*)((out0)+((uintptr_t)1ULL)) = x105;
  *(uint8_t*)((out0)+((uintptr_t)2ULL)) = x106;
  *(uint8_t*)((out0)+((uintptr_t)3ULL)) = x107;
  *(uint8_t*)((out0)+((uintptr_t)4ULL)) = x108;
  *(uint8_t*)((out0)+((uintptr_t)5ULL)) = x109;
  *(uint8_t*)((out0)+((uintptr_t)6ULL)) = x110;
  *(uint8_t*)((out0)+((uintptr_t)7ULL)) = x111;
  *(uint8_t*)((out0)+((uintptr_t)8ULL)) = x112;
  *(uint8_t*)((out0)+((uintptr_t)9ULL)) = x113;
  *(uint8_t*)((out0)+((uintptr_t)10ULL)) = x114;
  *(uint8_t*)((out0)+((uintptr_t)11ULL)) = x115;
  *(uint8_t*)((out0)+((uintptr_t)12ULL)) = x116;
  *(uint8_t*)((out0)+((uintptr_t)13ULL)) = x117;
  *(uint8_t*)((out0)+((uintptr_t)14ULL)) = x118;
  *(uint8_t*)((out0)+((uintptr_t)15ULL)) = x119;
  *(uint8_t*)((out0)+((uintptr_t)16ULL)) = x120;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 */
void fiat_poly1305_from_bytes(uintptr_t out0, uintptr_t in0) {
  uintptr_t x16, x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0, x32, x33, x31, x34, x30, x35, x36, x29, x38, x28, x39, x27, x40, x41, x26, x43, x25, x44, x24, x45, x46, x23, x48, x22, x49, x21, x50, x19, x20, x18, x52, x17, x53, x37, x42, x47, x51, x54, x55, x56, x57, x58, x59;
  x0 = *(uint8_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uint8_t*)((in0)+((uintptr_t)1ULL));
  x2 = *(uint8_t*)((in0)+((uintptr_t)2ULL));
  x3 = *(uint8_t*)((in0)+((uintptr_t)3ULL));
  x4 = *(uint8_t*)((in0)+((uintptr_t)4ULL));
  x5 = *(uint8_t*)((in0)+((uintptr_t)5ULL));
  x6 = *(uint8_t*)((in0)+((uintptr_t)6ULL));
  x7 = *(uint8_t*)((in0)+((uintptr_t)7ULL));
  x8 = *(uint8_t*)((in0)+((uintptr_t)8ULL));
  x9 = *(uint8_t*)((in0)+((uintptr_t)9ULL));
  x10 = *(uint8_t*)((in0)+((uintptr_t)10ULL));
  x11 = *(uint8_t*)((in0)+((uintptr_t)11ULL));
  x12 = *(uint8_t*)((in0)+((uintptr_t)12ULL));
  x13 = *(uint8_t*)((in0)+((uintptr_t)13ULL));
  x14 = *(uint8_t*)((in0)+((uintptr_t)14ULL));
  x15 = *(uint8_t*)((in0)+((uintptr_t)15ULL));
  x16 = *(uint8_t*)((in0)+((uintptr_t)16ULL));
  /*skip*/
  /*skip*/
  x17 = (x16)<<((uintptr_t)24ULL);
  x18 = (x15)<<((uintptr_t)16ULL);
  x19 = (x14)<<((uintptr_t)8ULL);
  x20 = x13;
  x21 = (x12)<<((uintptr_t)18ULL);
  x22 = (x11)<<((uintptr_t)10ULL);
  x23 = (x10)<<((uintptr_t)2ULL);
  x24 = (x9)<<((uintptr_t)20ULL);
  x25 = (x8)<<((uintptr_t)12ULL);
  x26 = (x7)<<((uintptr_t)4ULL);
  x27 = (x6)<<((uintptr_t)22ULL);
  x28 = (x5)<<((uintptr_t)14ULL);
  x29 = (x4)<<((uintptr_t)6ULL);
  x30 = (x3)<<((uintptr_t)24ULL);
  x31 = (x2)<<((uintptr_t)16ULL);
  x32 = (x1)<<((uintptr_t)8ULL);
  x33 = x0;
  x34 = (x32)+(x33);
  x35 = (x31)+(x34);
  x36 = (x30)+(x35);
  x37 = (x36)&((uintptr_t)67108863ULL);
  x38 = (x36)>>((uintptr_t)26ULL);
  x39 = (x29)+(x38);
  x40 = (x28)+(x39);
  x41 = (x27)+(x40);
  x42 = (x41)&((uintptr_t)67108863ULL);
  x43 = (x41)>>((uintptr_t)26ULL);
  x44 = (x26)+(x43);
  x45 = (x25)+(x44);
  x46 = (x24)+(x45);
  x47 = (x46)&((uintptr_t)67108863ULL);
  x48 = (x46)>>((uintptr_t)26ULL);
  x49 = (x23)+(x48);
  x50 = (x22)+(x49);
  x51 = (x21)+(x50);
  x52 = (x19)+(x20);
  x53 = (x18)+(x52);
  x54 = (x17)+(x53);
  x55 = x37;
  x56 = x42;
  x57 = x47;
  x58 = x51;
  x59 = x54;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x55;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x56;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x57;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x58;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x59;
  /*skip*/
  return;
}


