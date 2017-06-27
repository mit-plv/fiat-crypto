#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "p256.h"

#undef force_inline
#define force_inline __attribute__((always_inline))

#define uint64_t long long unsigned int

inline uint64_t cmovcq(uint64_t c, uint64_t out_z, uint64_t out_nz) {
    uint64_t all_set_if_zero = (c-1);
    return (all_set_if_zero & out_z) | ((~all_set_if_zero)&out_nz);
}

inline uint64_t fenonzero(uint64_t x5, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint64_t x7 = x6 | x5;
{  uint64_t x8 = x4 | x7;
{  uint64_t x9 = x2 | x8;
return x9;
}}}

inline void feadd(uint64_t* out, uint64_t x8, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x14, uint64_t x15, uint64_t x13, uint64_t x11)
{  uint64_t x17; uint8_t x18 = _addcarryx_u64(0x0, x5, x11, &x17);
{  uint64_t x20; uint8_t x21 = _addcarryx_u64(x18, x7, x13, &x20);
{  uint64_t x23; uint8_t x24 = _addcarryx_u64(x21, x9, x15, &x23);
{  uint64_t x26; uint8_t x27 = _addcarryx_u64(x24, x8, x14, &x26);
{  uint64_t x29; uint8_t x30 = _subborrow_u64(0x0, x17, 0xffffffffffffffffL, &x29);
{  uint64_t x32; uint8_t x33 = _subborrow_u64(x30, x20, 0xffffffff, &x32);
{  uint64_t x35; uint8_t x36 = _subborrow_u64(x33, x23, 0x0, &x35);
{  uint64_t x38; uint8_t x39 = _subborrow_u64(x36, x26, 0xffffffff00000001L, &x38);
{  uint64_t _; uint8_t x43 = _subborrow_u64(x39, x27, 0, &_);
{  uint64_t x44 = cmovcq(x43, x38, x26);
{  uint64_t x45 = cmovcq(x43, x35, x23);
{  uint64_t x46 = cmovcq(x43, x32, x20);
{  uint64_t x47 = cmovcq(x43, x29, x17);
out[0] = x44;
out[1] = x45;
out[2] = x46;
out[3] = x47;
}}}}}}}}}}}}}

inline void fesub(uint64_t* out, uint64_t x8, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x14, uint64_t x15, uint64_t x13, uint64_t x11)
{  uint64_t x17; uint8_t x18 = _subborrow_u64(0x0, x5, x11, &x17);
{  uint64_t x20; uint8_t x21 = _subborrow_u64(x18, x7, x13, &x20);
{  uint64_t x23; uint8_t x24 = _subborrow_u64(x21, x9, x15, &x23);
{  uint64_t x26; uint8_t x27 = _subborrow_u64(x24, x8, x14, &x26);
{  uint64_t x28 = (uint64_t) (x27 == 0 ? 0x0 : 0xffffffffffffffffL); // subborrow_u64(x27, 0, 0)
{  uint64_t x31; uint8_t x32 = _addcarryx_u64(0x0, x17, x28 & 0xffffffffffffffffL, &x31);
{  uint64_t x35; uint8_t x36 = _addcarryx_u64(x32, x20, x28 & 0xffffffff, &x35);
{  uint64_t x38; uint8_t x39 = _addcarryx_u64(x36, x23, 0x0, &x38);
{  uint64_t x40; uint8_t _ = _addcarryx_u64(x39, x26, (x28 & 0xffffffff00000001L), &x40);
out[0] = x40;
out[1] = x38;
out[2] = x35;
out[3] = x31;
}}}}}}}}}

inline void feopp(uint64_t* out, uint64_t x5, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint64_t x8; uint8_t x9 = _subborrow_u64(0x0, 0x0, x2, &x8);
{  uint64_t x11; uint8_t x12 = _subborrow_u64(x9, 0x0, x4, &x11);
{  uint64_t x14; uint8_t x15 = _subborrow_u64(x12, 0x0, x6, &x14);
{  uint64_t x17; uint8_t x18 = _subborrow_u64(x15, 0x0, x5, &x17);
{  uint64_t x19 = (uint64_t) (x18 == 0 ? 0x0 : 0xffffffffffffffffL); // subborrow
{  uint64_t x22; uint8_t x23 = _addcarryx_u64(0x0, x8, x19 & 0xffffffffffffffffL, &x22);
{  uint64_t x26; uint8_t x27 = _addcarryx_u64(x23, x11, x19 & 0xffffffff, &x26);
{  uint64_t x29; uint8_t x30 = _addcarryx_u64(x27, x14, 0x0, &x29);
{  uint64_t x31; uint8_t _ = _addcarryx_u64(x30, x17, x19 & 0xffffffff00000001L, &x31);
out[0] = x31;
out[1] = x29;
out[2] = x26;
out[3] = x22;
}}}}}}}}}

inline void force_inline femul(uint64_t* out, uint64_t x8, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x14, uint64_t x15, uint64_t x13, uint64_t x11)
{  uint64_t x17; uint64_t x18 = _mulx_u64(x5, x11, &x17);
{  uint64_t x20; uint64_t x21 = _mulx_u64(x5, x13, &x20);
{  uint64_t x23; uint64_t x24 = _mulx_u64(x5, x15, &x23);
{  uint64_t x26; uint64_t x27 = _mulx_u64(x5, x14, &x26);
{  uint64_t x29; uint8_t x30 = _addcarryx_u64(0x0, x18, x20, &x29);
{  uint64_t x32; uint8_t x33 = _addcarryx_u64(x30, x21, x23, &x32);
{  uint64_t x35; uint8_t x36 = _addcarryx_u64(x33, x24, x26, &x35);
{  uint64_t x38; uint8_t _ = _addcarryx_u64(0x0, x36, x27, &x38);
{  uint64_t x41; uint64_t x42 = _mulx_u64(x17, 0xffffffffffffffffL, &x41);
{  uint64_t x44; uint64_t x45 = _mulx_u64(x17, 0xffffffff, &x44);
{  uint64_t x47; uint64_t x48 = _mulx_u64(x17, 0xffffffff00000001L, &x47);
{  uint64_t x50; uint8_t x51 = _addcarryx_u64(0x0, x42, x44, &x50);
{  uint64_t x53; uint8_t x54 = _addcarryx_u64(x51, x45, 0x0, &x53);
{  uint64_t x56; uint8_t x57 = _addcarryx_u64(x54, 0x0, x47, &x56);
{  uint64_t x59; uint8_t _ = _addcarryx_u64(0x0, x57, x48, &x59);
{  uint64_t _; uint8_t x63 = _addcarryx_u64(0x0, x17, x41, &_);
{  uint64_t x65; uint8_t x66 = _addcarryx_u64(x63, x29, x50, &x65);
{  uint64_t x68; uint8_t x69 = _addcarryx_u64(x66, x32, x53, &x68);
{  uint64_t x71; uint8_t x72 = _addcarryx_u64(x69, x35, x56, &x71);
{  uint64_t x74; uint8_t x75 = _addcarryx_u64(x72, x38, x59, &x74);
{  uint64_t x77; uint64_t x78 = _mulx_u64(x7, x11, &x77);
{  uint64_t x80; uint64_t x81 = _mulx_u64(x7, x13, &x80);
{  uint64_t x83; uint64_t x84 = _mulx_u64(x7, x15, &x83);
{  uint64_t x86; uint64_t x87 = _mulx_u64(x7, x14, &x86);
{  uint64_t x89; uint8_t x90 = _addcarryx_u64(0x0, x78, x80, &x89);
{  uint64_t x92; uint8_t x93 = _addcarryx_u64(x90, x81, x83, &x92);
{  uint64_t x95; uint8_t x96 = _addcarryx_u64(x93, x84, x86, &x95);
{  uint64_t x98; uint8_t _ = _addcarryx_u64(0x0, x96, x87, &x98);
{  uint64_t x101; uint8_t x102 = _addcarryx_u64(0x0, x65, x77, &x101);
{  uint64_t x104; uint8_t x105 = _addcarryx_u64(x102, x68, x89, &x104);
{  uint64_t x107; uint8_t x108 = _addcarryx_u64(x105, x71, x92, &x107);
{  uint64_t x110; uint8_t x111 = _addcarryx_u64(x108, x74, x95, &x110);
{  uint64_t x113; uint8_t x114 = _addcarryx_u64(x111, x75, x98, &x113);
{  uint64_t x116; uint64_t x117 = _mulx_u64(x101, 0xffffffffffffffffL, &x116);
{  uint64_t x119; uint64_t x120 = _mulx_u64(x101, 0xffffffff, &x119);
{  uint64_t x122; uint64_t x123 = _mulx_u64(x101, 0xffffffff00000001L, &x122);
{  uint64_t x125; uint8_t x126 = _addcarryx_u64(0x0, x117, x119, &x125);
{  uint64_t x128; uint8_t x129 = _addcarryx_u64(x126, x120, 0x0, &x128);
{  uint64_t x131; uint8_t x132 = _addcarryx_u64(x129, 0x0, x122, &x131);
{  uint64_t x134; uint8_t _ = _addcarryx_u64(0x0, x132, x123, &x134);
{  uint64_t _; uint8_t x138 = _addcarryx_u64(0x0, x101, x116, &_);
{  uint64_t x140; uint8_t x141 = _addcarryx_u64(x138, x104, x125, &x140);
{  uint64_t x143; uint8_t x144 = _addcarryx_u64(x141, x107, x128, &x143);
{  uint64_t x146; uint8_t x147 = _addcarryx_u64(x144, x110, x131, &x146);
{  uint64_t x149; uint8_t x150 = _addcarryx_u64(x147, x113, x134, &x149);
{  uint8_t x151 = x150 + x114;
{  uint64_t x153; uint64_t x154 = _mulx_u64(x9, x11, &x153);
{  uint64_t x156; uint64_t x157 = _mulx_u64(x9, x13, &x156);
{  uint64_t x159; uint64_t x160 = _mulx_u64(x9, x15, &x159);
{  uint64_t x162; uint64_t x163 = _mulx_u64(x9, x14, &x162);
{  uint64_t x165; uint8_t x166 = _addcarryx_u64(0x0, x154, x156, &x165);
{  uint64_t x168; uint8_t x169 = _addcarryx_u64(x166, x157, x159, &x168);
{  uint64_t x171; uint8_t x172 = _addcarryx_u64(x169, x160, x162, &x171);
{  uint64_t x174; uint8_t _ = _addcarryx_u64(0x0, x172, x163, &x174);
{  uint64_t x177; uint8_t x178 = _addcarryx_u64(0x0, x140, x153, &x177);
{  uint64_t x180; uint8_t x181 = _addcarryx_u64(x178, x143, x165, &x180);
{  uint64_t x183; uint8_t x184 = _addcarryx_u64(x181, x146, x168, &x183);
{  uint64_t x186; uint8_t x187 = _addcarryx_u64(x184, x149, x171, &x186);
{  uint64_t x189; uint8_t x190 = _addcarryx_u64(x187, x151, x174, &x189);
{  uint64_t x192; uint64_t x193 = _mulx_u64(x177, 0xffffffffffffffffL, &x192);
{  uint64_t x195; uint64_t x196 = _mulx_u64(x177, 0xffffffff, &x195);
{  uint64_t x198; uint64_t x199 = _mulx_u64(x177, 0xffffffff00000001L, &x198);
{  uint64_t x201; uint8_t x202 = _addcarryx_u64(0x0, x193, x195, &x201);
{  uint64_t x204; uint8_t x205 = _addcarryx_u64(x202, x196, 0x0, &x204);
{  uint64_t x207; uint8_t x208 = _addcarryx_u64(x205, 0x0, x198, &x207);
{  uint64_t x210; uint8_t _ = _addcarryx_u64(0x0, x208, x199, &x210);
{  uint64_t _; uint8_t x214 = _addcarryx_u64(0x0, x177, x192, &_);
{  uint64_t x216; uint8_t x217 = _addcarryx_u64(x214, x180, x201, &x216);
{  uint64_t x219; uint8_t x220 = _addcarryx_u64(x217, x183, x204, &x219);
{  uint64_t x222; uint8_t x223 = _addcarryx_u64(x220, x186, x207, &x222);
{  uint64_t x225; uint8_t x226 = _addcarryx_u64(x223, x189, x210, &x225);
{  uint8_t x227 = x226 + x190;
{  uint64_t x229; uint64_t x230 = _mulx_u64(x8, x11, &x229);
{  uint64_t x232; uint64_t x233 = _mulx_u64(x8, x13, &x232);
{  uint64_t x235; uint64_t x236 = _mulx_u64(x8, x15, &x235);
{  uint64_t x238; uint64_t x239 = _mulx_u64(x8, x14, &x238);
{  uint64_t x241; uint8_t x242 = _addcarryx_u64(0x0, x230, x232, &x241);
{  uint64_t x244; uint8_t x245 = _addcarryx_u64(x242, x233, x235, &x244);
{  uint64_t x247; uint8_t x248 = _addcarryx_u64(x245, x236, x238, &x247);
{  uint64_t x250; uint8_t _ = _addcarryx_u64(0x0, x248, x239, &x250);
{  uint64_t x253; uint8_t x254 = _addcarryx_u64(0x0, x216, x229, &x253);
{  uint64_t x256; uint8_t x257 = _addcarryx_u64(x254, x219, x241, &x256);
{  uint64_t x259; uint8_t x260 = _addcarryx_u64(x257, x222, x244, &x259);
{  uint64_t x262; uint8_t x263 = _addcarryx_u64(x260, x225, x247, &x262);
{  uint64_t x265; uint8_t x266 = _addcarryx_u64(x263, x227, x250, &x265);
{  uint64_t x268; uint64_t x269 = _mulx_u64(x253, 0xffffffffffffffffL, &x268);
{  uint64_t x271; uint64_t x272 = _mulx_u64(x253, 0xffffffff, &x271);
{  uint64_t x274; uint64_t x275 = _mulx_u64(x253, 0xffffffff00000001L, &x274);
{  uint64_t x277; uint8_t x278 = _addcarryx_u64(0x0, x269, x271, &x277);
{  uint64_t x280; uint8_t x281 = _addcarryx_u64(x278, x272, 0x0, &x280);
{  uint64_t x283; uint8_t x284 = _addcarryx_u64(x281, 0x0, x274, &x283);
{  uint64_t x286; uint8_t _ = _addcarryx_u64(0x0, x284, x275, &x286);
{  uint64_t _; uint8_t x290 = _addcarryx_u64(0x0, x253, x268, &_);
{  uint64_t x292; uint8_t x293 = _addcarryx_u64(x290, x256, x277, &x292);
{  uint64_t x295; uint8_t x296 = _addcarryx_u64(x293, x259, x280, &x295);
{  uint64_t x298; uint8_t x299 = _addcarryx_u64(x296, x262, x283, &x298);
{  uint64_t x301; uint8_t x302 = _addcarryx_u64(x299, x265, x286, &x301);
{  uint8_t x303 = x302 + x266;
{  uint64_t x305; uint8_t x306 = _subborrow_u64(0x0, x292, 0xffffffffffffffffL, &x305);
{  uint64_t x308; uint8_t x309 = _subborrow_u64(x306, x295, 0xffffffff, &x308);
{  uint64_t x311; uint8_t x312 = _subborrow_u64(x309, x298, 0x0, &x311);
{  uint64_t x314; uint8_t x315 = _subborrow_u64(x312, x301, 0xffffffff00000001L, &x314);
{  uint64_t _; uint8_t x319 = _subborrow_u64(x315, x303, 0, &_);
{  uint64_t x320 = cmovcq(x319, x314, x301);
{  uint64_t x321 = cmovcq(x319, x311, x298);
{  uint64_t x322 = cmovcq(x319, x308, x295);
{  uint64_t x323 = cmovcq(x319, x305, x292);
out[0] = x320;
out[1] = x321;
out[2] = x322;
out[3] = x323;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

inline void force_inline fesquare(uint64_t* out, uint64_t x8, uint64_t x9, uint64_t x7, uint64_t x5)
{  uint64_t x14 = x8; uint64_t x15 = x9; uint64_t x13 = x7; uint64_t x11 = x5;
{  uint64_t x17; uint64_t x18 = _mulx_u64(x5, x11, &x17);
{  uint64_t x20; uint64_t x21 = _mulx_u64(x5, x13, &x20);
{  uint64_t x23; uint64_t x24 = _mulx_u64(x5, x15, &x23);
{  uint64_t x26; uint64_t x27 = _mulx_u64(x5, x14, &x26);
{  uint64_t x29; uint8_t x30 = _addcarryx_u64(0x0, x18, x20, &x29);
{  uint64_t x32; uint8_t x33 = _addcarryx_u64(x30, x21, x23, &x32);
{  uint64_t x35; uint8_t x36 = _addcarryx_u64(x33, x24, x26, &x35);
{  uint64_t x38; uint8_t _ = _addcarryx_u64(0x0, x36, x27, &x38);
{  uint64_t x41; uint64_t x42 = _mulx_u64(x17, 0xffffffffffffffffL, &x41);
{  uint64_t x44; uint64_t x45 = _mulx_u64(x17, 0xffffffff, &x44);
{  uint64_t x47; uint64_t x48 = _mulx_u64(x17, 0xffffffff00000001L, &x47);
{  uint64_t x50; uint8_t x51 = _addcarryx_u64(0x0, x42, x44, &x50);
{  uint64_t x53; uint8_t x54 = _addcarryx_u64(x51, x45, 0x0, &x53);
{  uint64_t x56; uint8_t x57 = _addcarryx_u64(x54, 0x0, x47, &x56);
{  uint64_t x59; uint8_t _ = _addcarryx_u64(0x0, x57, x48, &x59);
{  uint64_t _; uint8_t x63 = _addcarryx_u64(0x0, x17, x41, &_);
{  uint64_t x65; uint8_t x66 = _addcarryx_u64(x63, x29, x50, &x65);
{  uint64_t x68; uint8_t x69 = _addcarryx_u64(x66, x32, x53, &x68);
{  uint64_t x71; uint8_t x72 = _addcarryx_u64(x69, x35, x56, &x71);
{  uint64_t x74; uint8_t x75 = _addcarryx_u64(x72, x38, x59, &x74);
{  uint64_t x77; uint64_t x78 = _mulx_u64(x7, x11, &x77);
{  uint64_t x80; uint64_t x81 = _mulx_u64(x7, x13, &x80);
{  uint64_t x83; uint64_t x84 = _mulx_u64(x7, x15, &x83);
{  uint64_t x86; uint64_t x87 = _mulx_u64(x7, x14, &x86);
{  uint64_t x89; uint8_t x90 = _addcarryx_u64(0x0, x78, x80, &x89);
{  uint64_t x92; uint8_t x93 = _addcarryx_u64(x90, x81, x83, &x92);
{  uint64_t x95; uint8_t x96 = _addcarryx_u64(x93, x84, x86, &x95);
{  uint64_t x98; uint8_t _ = _addcarryx_u64(0x0, x96, x87, &x98);
{  uint64_t x101; uint8_t x102 = _addcarryx_u64(0x0, x65, x77, &x101);
{  uint64_t x104; uint8_t x105 = _addcarryx_u64(x102, x68, x89, &x104);
{  uint64_t x107; uint8_t x108 = _addcarryx_u64(x105, x71, x92, &x107);
{  uint64_t x110; uint8_t x111 = _addcarryx_u64(x108, x74, x95, &x110);
{  uint64_t x113; uint8_t x114 = _addcarryx_u64(x111, x75, x98, &x113);
{  uint64_t x116; uint64_t x117 = _mulx_u64(x101, 0xffffffffffffffffL, &x116);
{  uint64_t x119; uint64_t x120 = _mulx_u64(x101, 0xffffffff, &x119);
{  uint64_t x122; uint64_t x123 = _mulx_u64(x101, 0xffffffff00000001L, &x122);
{  uint64_t x125; uint8_t x126 = _addcarryx_u64(0x0, x117, x119, &x125);
{  uint64_t x128; uint8_t x129 = _addcarryx_u64(x126, x120, 0x0, &x128);
{  uint64_t x131; uint8_t x132 = _addcarryx_u64(x129, 0x0, x122, &x131);
{  uint64_t x134; uint8_t _ = _addcarryx_u64(0x0, x132, x123, &x134);
{  uint64_t _; uint8_t x138 = _addcarryx_u64(0x0, x101, x116, &_);
{  uint64_t x140; uint8_t x141 = _addcarryx_u64(x138, x104, x125, &x140);
{  uint64_t x143; uint8_t x144 = _addcarryx_u64(x141, x107, x128, &x143);
{  uint64_t x146; uint8_t x147 = _addcarryx_u64(x144, x110, x131, &x146);
{  uint64_t x149; uint8_t x150 = _addcarryx_u64(x147, x113, x134, &x149);
{  uint8_t x151 = x150 + x114;
{  uint64_t x153; uint64_t x154 = _mulx_u64(x9, x11, &x153);
{  uint64_t x156; uint64_t x157 = _mulx_u64(x9, x13, &x156);
{  uint64_t x159; uint64_t x160 = _mulx_u64(x9, x15, &x159);
{  uint64_t x162; uint64_t x163 = _mulx_u64(x9, x14, &x162);
{  uint64_t x165; uint8_t x166 = _addcarryx_u64(0x0, x154, x156, &x165);
{  uint64_t x168; uint8_t x169 = _addcarryx_u64(x166, x157, x159, &x168);
{  uint64_t x171; uint8_t x172 = _addcarryx_u64(x169, x160, x162, &x171);
{  uint64_t x174; uint8_t _ = _addcarryx_u64(0x0, x172, x163, &x174);
{  uint64_t x177; uint8_t x178 = _addcarryx_u64(0x0, x140, x153, &x177);
{  uint64_t x180; uint8_t x181 = _addcarryx_u64(x178, x143, x165, &x180);
{  uint64_t x183; uint8_t x184 = _addcarryx_u64(x181, x146, x168, &x183);
{  uint64_t x186; uint8_t x187 = _addcarryx_u64(x184, x149, x171, &x186);
{  uint64_t x189; uint8_t x190 = _addcarryx_u64(x187, x151, x174, &x189);
{  uint64_t x192; uint64_t x193 = _mulx_u64(x177, 0xffffffffffffffffL, &x192);
{  uint64_t x195; uint64_t x196 = _mulx_u64(x177, 0xffffffff, &x195);
{  uint64_t x198; uint64_t x199 = _mulx_u64(x177, 0xffffffff00000001L, &x198);
{  uint64_t x201; uint8_t x202 = _addcarryx_u64(0x0, x193, x195, &x201);
{  uint64_t x204; uint8_t x205 = _addcarryx_u64(x202, x196, 0x0, &x204);
{  uint64_t x207; uint8_t x208 = _addcarryx_u64(x205, 0x0, x198, &x207);
{  uint64_t x210; uint8_t _ = _addcarryx_u64(0x0, x208, x199, &x210);
{  uint64_t _; uint8_t x214 = _addcarryx_u64(0x0, x177, x192, &_);
{  uint64_t x216; uint8_t x217 = _addcarryx_u64(x214, x180, x201, &x216);
{  uint64_t x219; uint8_t x220 = _addcarryx_u64(x217, x183, x204, &x219);
{  uint64_t x222; uint8_t x223 = _addcarryx_u64(x220, x186, x207, &x222);
{  uint64_t x225; uint8_t x226 = _addcarryx_u64(x223, x189, x210, &x225);
{  uint8_t x227 = x226 + x190;
{  uint64_t x229; uint64_t x230 = _mulx_u64(x8, x11, &x229);
{  uint64_t x232; uint64_t x233 = _mulx_u64(x8, x13, &x232);
{  uint64_t x235; uint64_t x236 = _mulx_u64(x8, x15, &x235);
{  uint64_t x238; uint64_t x239 = _mulx_u64(x8, x14, &x238);
{  uint64_t x241; uint8_t x242 = _addcarryx_u64(0x0, x230, x232, &x241);
{  uint64_t x244; uint8_t x245 = _addcarryx_u64(x242, x233, x235, &x244);
{  uint64_t x247; uint8_t x248 = _addcarryx_u64(x245, x236, x238, &x247);
{  uint64_t x250; uint8_t _ = _addcarryx_u64(0x0, x248, x239, &x250);
{  uint64_t x253; uint8_t x254 = _addcarryx_u64(0x0, x216, x229, &x253);
{  uint64_t x256; uint8_t x257 = _addcarryx_u64(x254, x219, x241, &x256);
{  uint64_t x259; uint8_t x260 = _addcarryx_u64(x257, x222, x244, &x259);
{  uint64_t x262; uint8_t x263 = _addcarryx_u64(x260, x225, x247, &x262);
{  uint64_t x265; uint8_t x266 = _addcarryx_u64(x263, x227, x250, &x265);
{  uint64_t x268; uint64_t x269 = _mulx_u64(x253, 0xffffffffffffffffL, &x268);
{  uint64_t x271; uint64_t x272 = _mulx_u64(x253, 0xffffffff, &x271);
{  uint64_t x274; uint64_t x275 = _mulx_u64(x253, 0xffffffff00000001L, &x274);
{  uint64_t x277; uint8_t x278 = _addcarryx_u64(0x0, x269, x271, &x277);
{  uint64_t x280; uint8_t x281 = _addcarryx_u64(x278, x272, 0x0, &x280);
{  uint64_t x283; uint8_t x284 = _addcarryx_u64(x281, 0x0, x274, &x283);
{  uint64_t x286; uint8_t _ = _addcarryx_u64(0x0, x284, x275, &x286);
{  uint64_t _; uint8_t x290 = _addcarryx_u64(0x0, x253, x268, &_);
{  uint64_t x292; uint8_t x293 = _addcarryx_u64(x290, x256, x277, &x292);
{  uint64_t x295; uint8_t x296 = _addcarryx_u64(x293, x259, x280, &x295);
{  uint64_t x298; uint8_t x299 = _addcarryx_u64(x296, x262, x283, &x298);
{  uint64_t x301; uint8_t x302 = _addcarryx_u64(x299, x265, x286, &x301);
{  uint8_t x303 = x302 + x266;
{  uint64_t x305; uint8_t x306 = _subborrow_u64(0x0, x292, 0xffffffffffffffffL, &x305);
{  uint64_t x308; uint8_t x309 = _subborrow_u64(x306, x295, 0xffffffff, &x308);
{  uint64_t x311; uint8_t x312 = _subborrow_u64(x309, x298, 0x0, &x311);
{  uint64_t x314; uint8_t x315 = _subborrow_u64(x312, x301, 0xffffffff00000001L, &x314);
{  uint64_t _; uint8_t x319 = _subborrow_u64(x315, x303, 0, &_);
{  uint64_t x320 = cmovcq(x319, x314, x301);
{  uint64_t x321 = cmovcq(x319, x311, x298);
{  uint64_t x322 = cmovcq(x319, x308, x295);
{  uint64_t x323 = cmovcq(x319, x305, x292);
out[0] = x320;
out[1] = x321;
out[2] = x322;
out[3] = x323;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}


void p256_jacobian_add_affine(
    uint64_t P1[12],
    uint64_t P2[8],
    uint64_t P3[12]
) {
    uint64_t* X1 = P1;
    uint64_t* Y1 = P1+4;
    uint64_t* Z1 = P1+8;
    uint64_t* X2 = P2;
    uint64_t* Y2 = P2+4;
    uint64_t* X3 = P3;
    uint64_t* Y3 = P3+4;
    uint64_t* Z3 = P3+8;
    uint64_t ZZ[4] = {0};  fesquare(ZZ, Z1[3], Z1[2], Z1[1], Z1[0]);
    uint64_t P1z = !fenonzero(Z1[3], Z1[2], Z1[1], Z1[0]);
    uint64_t U2[4] = {0};  femul(ZZ, ZZ[3], ZZ[2], ZZ[1], ZZ[0], X2[3], X2[2], X2[1], X2[0]);
    uint64_t X2nz = fenonzero(X2[3], X2[2], X2[1], X2[0]);
    uint64_t ZZZ[4] = {0};  femul(ZZZ, ZZ[3], ZZ[2], ZZ[1], ZZ[0], Z1[3], Z1[2], Z1[1], Z1[0]);
    uint64_t H[4] = {0};  fesub(H, U2[3], U2[2], U2[1], U2[0], X1[3], X1[2], X1[1], X1[0]);
                           femul(Z3, Z1[3], Z1[2], Z1[1], Z1[0], H[3], H[2], H[1], H[0]);
    uint64_t P2z = !(X2nz | fenonzero(Y2[3], Y2[2], Y2[1], Y2[0]));
    uint64_t S2[4] = {0};  femul(S2, ZZZ[3], ZZZ[2], ZZZ[1], ZZZ[0], Y2[3], Y2[2], Y2[1], Y2[0]);
    uint64_t R[4] = {0};  fesub(R, S2[3], S2[2], S2[1], S2[0], Y1[3], Y1[2], Y1[1], Y1[0]);
    uint64_t HH[4] = {0};  fesquare(HH, H[3], H[2], H[1], H[0]);
    uint64_t RR[4] = {0};  fesquare(RR, R[3], R[2], R[1], R[0]);
    uint64_t HHH[4] = {0};  femul(HHH, HH[3], HH[2], HH[1], HH[0], H[3], H[2], H[1], H[0]);
    Z3[3] = cmovcq(P1z, Z3[3], 0x0000000000000001);
    Z3[2] = cmovcq(P1z, Z3[2], 0xffffffff00000000);
    Z3[1] = cmovcq(P1z, Z3[1], 0xffffffffffffffff);
    Z3[0] = cmovcq(P1z, Z3[0], 0xffffffffffffffff);
    Z3[3] = cmovcq(P2z, Z3[3], Z1[3]);
    Z3[2] = cmovcq(P2z, Z3[2], Z1[2]);
    Z3[1] = cmovcq(P2z, Z3[1], Z1[1]);
    Z3[0] = cmovcq(P2z, Z3[0], Z1[0]);
    uint64_t HHX[4] = {0};  femul(HH, HH[3], HH[2], HH[1], HH[0], X1[3], X1[2], X1[1], X1[0]);
    uint64_t T10[4] = {0};  feadd(T10, HHX[3], HHX[2], HHX[1], HHX[0], HHX[3], HHX[2], HHX[1], HHX[0]);
    uint64_t E4[4] = {0};  fesub(E4, RR[3], RR[2], RR[1], RR[0], T10[3], T10[2], T10[1], T10[0]);
                           fesub(X3, E4[3], E4[2], E4[1], E4[0], HHH[3], HHH[2], HHH[1], HHH[0]);
    X3[3] = cmovcq(P1z, X3[3], X2[3]);
    X3[2] = cmovcq(P1z, X3[2], X2[2]);
    X3[1] = cmovcq(P1z, X3[1], X2[1]);
    X3[0] = cmovcq(P1z, X3[0], X2[0]);
    X3[3] = cmovcq(P2z, X3[3], X1[3]);
    X3[2] = cmovcq(P2z, X3[2], X1[2]);
    X3[1] = cmovcq(P2z, X3[1], X1[1]);
    X3[0] = cmovcq(P2z, X3[0], X1[0]);
    uint64_t T13[4] = {0}; femul(T13, HHH[3], HHH[2], HHH[1], HHH[0], Y1[3], Y1[2], Y1[1], Y1[0]);
    uint64_t T11[4] = {0}; fesub(T11, HHX[3], HHX[2], HHX[1], HHX[0], X3[3], X3[2], X3[1], X3[0]);
    uint64_t T12[4] = {0}; femul(T12, T11[3], T11[2], T11[1], T11[0], R[3], R[2], R[1], R[0]);
                           fesub(Y3, T12[3], T12[2], T12[1], T12[0], T13[3], T13[2], T13[1], T13[0]);
    Y3[3] = cmovcq(P1z, Y3[3], Y2[3]);
    Y3[2] = cmovcq(P1z, Y3[2], Y2[2]);
    Y3[1] = cmovcq(P1z, Y3[1], Y2[1]);
    Y3[0] = cmovcq(P1z, Y3[0], Y2[0]);
    Y3[3] = cmovcq(P2z, Y3[3], Y1[3]);
    Y3[2] = cmovcq(P2z, Y3[2], Y1[2]);
    Y3[1] = cmovcq(P2z, Y3[1], Y1[1]);
    Y3[0] = cmovcq(P2z, Y3[0], Y1[0]);
}
