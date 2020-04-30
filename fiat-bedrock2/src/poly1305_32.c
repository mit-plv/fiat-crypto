/* Autogenerated: src/ExtractionOCaml/bedrock2_unsaturated_solinas --lang=bedrock2 --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select poly1305 5 '2^130 - 5' 32 carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes */
/* curve description: poly1305 */
/* requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes */
/* n = 5 (from "5") */
/* s-c = 2^130 - [(1, 5)] (from "2^130 - 5") */
/* machine_wordsize = 32 (from "32") */

/* Computed values: */
/* carry_chain = [0, 1, 2, 3, 4, 0, 1] */

#include <stdint.h>


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 *   in1: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 */
void fiat_poly1305_carry_mul(uintptr_t in0, uintptr_t in1, uintptr_t out0) {
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
 *   in0: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 */
void fiat_poly1305_carry_square(uintptr_t in0, uintptr_t out0) {
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
 *   in0: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 */
void fiat_poly1305_carry(uintptr_t in0, uintptr_t out0) {
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
 *   in0: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 *   in1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 */
void fiat_poly1305_add(uintptr_t in0, uintptr_t in1, uintptr_t out0) {
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
 *   in0: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 *   in1: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 */
void fiat_poly1305_sub(uintptr_t in0, uintptr_t in1, uintptr_t out0) {
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
 *   in0: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332], [0x0 ~> 0xd333332]]
 */
void fiat_poly1305_opp(uintptr_t in0, uintptr_t out0) {
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
void fiat_poly1305_selectznz(uintptr_t in0, uintptr_t in1, uintptr_t in2, uintptr_t out0) {
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
 *   in0: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 */
void fiat_poly1305_to_bytes(uintptr_t in0, uintptr_t out0) {
  uintptr_t x0, x6, x7, x8, x5, x1, x10, x11, x12, x14, x15, x13, x2, x17, x18, x19, x21, x22, x20, x3, x24, x25, x26, x28, x29, x27, x4, x31, x32, x33, x35, x36, x34, x38, x9, x40, x41, x43, x16, x44, x45, x47, x46, x48, x50, x23, x51, x52, x54, x53, x55, x57, x30, x58, x59, x61, x60, x62, x64, x37, x65, x39, x66, x63, x56, x49, x42, x71, x73, x75, x70, x77, x78, x80, x82, x69, x84, x85, x87, x89, x68, x91, x92, x94, x96, x67, x99, x101, x72, x74, x76, x79, x81, x83, x86, x88, x90, x93, x95, x97, x98, x100, x102, x104, x103, x105, x106, x107, x108, x109, x110, x111, x112, x113, x114, x115, x116, x117, x118, x119, x120, x121;
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
  x71 = (x42)>>((uintptr_t)8ULL);
  x72 = (x42)&((uintptr_t)255ULL);
  x73 = (x71)>>((uintptr_t)8ULL);
  x74 = (x71)&((uintptr_t)255ULL);
  x75 = (x73)>>((uintptr_t)8ULL);
  x76 = (x73)&((uintptr_t)255ULL);
  x77 = (x75)+(x70);
  x78 = (x77)>>((uintptr_t)8ULL);
  x79 = (x77)&((uintptr_t)255ULL);
  x80 = (x78)>>((uintptr_t)8ULL);
  x81 = (x78)&((uintptr_t)255ULL);
  x82 = (x80)>>((uintptr_t)8ULL);
  x83 = (x80)&((uintptr_t)255ULL);
  x84 = (x82)+(x69);
  x85 = (x84)>>((uintptr_t)8ULL);
  x86 = (x84)&((uintptr_t)255ULL);
  x87 = (x85)>>((uintptr_t)8ULL);
  x88 = (x85)&((uintptr_t)255ULL);
  x89 = (x87)>>((uintptr_t)8ULL);
  x90 = (x87)&((uintptr_t)255ULL);
  x91 = (x89)+(x68);
  x92 = (x91)>>((uintptr_t)8ULL);
  x93 = (x91)&((uintptr_t)255ULL);
  x94 = (x92)>>((uintptr_t)8ULL);
  x95 = (x92)&((uintptr_t)255ULL);
  x96 = (x94)>>((uintptr_t)8ULL);
  x97 = (x94)&((uintptr_t)255ULL);
  x98 = (x96)&((uintptr_t)255ULL);
  x99 = (x67)>>((uintptr_t)8ULL);
  x100 = (x67)&((uintptr_t)255ULL);
  x101 = (x99)>>((uintptr_t)8ULL);
  x102 = (x99)&((uintptr_t)255ULL);
  x103 = (x101)>>((uintptr_t)8ULL);
  x104 = (x101)&((uintptr_t)255ULL);
  x105 = x72;
  x106 = x74;
  x107 = x76;
  x108 = x79;
  x109 = x81;
  x110 = x83;
  x111 = x86;
  x112 = x88;
  x113 = x90;
  x114 = x93;
  x115 = x95;
  x116 = x97;
  x117 = x98;
  x118 = x100;
  x119 = x102;
  x120 = x104;
  x121 = x103;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x105;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x106;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x107;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x108;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x109;
  *(uintptr_t*)((out0)+((uintptr_t)20ULL)) = x110;
  *(uintptr_t*)((out0)+((uintptr_t)24ULL)) = x111;
  *(uintptr_t*)((out0)+((uintptr_t)28ULL)) = x112;
  *(uintptr_t*)((out0)+((uintptr_t)32ULL)) = x113;
  *(uintptr_t*)((out0)+((uintptr_t)36ULL)) = x114;
  *(uintptr_t*)((out0)+((uintptr_t)40ULL)) = x115;
  *(uintptr_t*)((out0)+((uintptr_t)44ULL)) = x116;
  *(uintptr_t*)((out0)+((uintptr_t)48ULL)) = x117;
  *(uintptr_t*)((out0)+((uintptr_t)52ULL)) = x118;
  *(uintptr_t*)((out0)+((uintptr_t)56ULL)) = x119;
  *(uintptr_t*)((out0)+((uintptr_t)60ULL)) = x120;
  *(uintptr_t*)((out0)+((uintptr_t)64ULL)) = x121;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666], [0x0 ~> 0x4666666]]
 */
void fiat_poly1305_from_bytes(uintptr_t in0, uintptr_t out0) {
  uintptr_t x16, x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0, x33, x32, x31, x30, x34, x20, x19, x18, x17, x23, x22, x21, x26, x25, x24, x29, x28, x27, x35, x40, x41, x42, x39, x44, x45, x38, x47, x36, x43, x46, x48, x37, x49, x50, x51, x52, x53;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)4ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)12ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  x5 = *(uintptr_t*)((in0)+((uintptr_t)20ULL));
  x6 = *(uintptr_t*)((in0)+((uintptr_t)24ULL));
  x7 = *(uintptr_t*)((in0)+((uintptr_t)28ULL));
  x8 = *(uintptr_t*)((in0)+((uintptr_t)32ULL));
  x9 = *(uintptr_t*)((in0)+((uintptr_t)36ULL));
  x10 = *(uintptr_t*)((in0)+((uintptr_t)40ULL));
  x11 = *(uintptr_t*)((in0)+((uintptr_t)44ULL));
  x12 = *(uintptr_t*)((in0)+((uintptr_t)48ULL));
  x13 = *(uintptr_t*)((in0)+((uintptr_t)52ULL));
  x14 = *(uintptr_t*)((in0)+((uintptr_t)56ULL));
  x15 = *(uintptr_t*)((in0)+((uintptr_t)60ULL));
  x16 = *(uintptr_t*)((in0)+((uintptr_t)64ULL));
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
  x34 = (x33)+((x32)+((x31)+(x30)));
  x35 = (x34)>>((uintptr_t)26ULL);
  x36 = (x34)&((uintptr_t)67108863ULL);
  x37 = (x20)+((x19)+((x18)+(x17)));
  x38 = (x23)+((x22)+(x21));
  x39 = (x26)+((x25)+(x24));
  x40 = (x29)+((x28)+(x27));
  x41 = (x35)+(x40);
  x42 = (x41)>>((uintptr_t)26ULL);
  x43 = (x41)&((uintptr_t)67108863ULL);
  x44 = (x42)+(x39);
  x45 = (x44)>>((uintptr_t)26ULL);
  x46 = (x44)&((uintptr_t)67108863ULL);
  x47 = (x45)+(x38);
  x48 = (x47)&((uintptr_t)67108863ULL);
  x49 = x36;
  x50 = x43;
  x51 = x46;
  x52 = x48;
  x53 = x37;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x49;
  *(uintptr_t*)((out0)+((uintptr_t)4ULL)) = x50;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x51;
  *(uintptr_t*)((out0)+((uintptr_t)12ULL)) = x52;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x53;
  /*skip*/
  return;
}


