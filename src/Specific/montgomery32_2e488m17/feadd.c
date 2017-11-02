#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "feadd.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline feadd(uint64_t* out, uint64_t x32, uint64_t x33, uint64_t x31, uint64_t x29, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x62, uint64_t x63, uint64_t x61, uint64_t x59, uint64_t x57, uint64_t x55, uint64_t x53, uint64_t x51, uint64_t x49, uint64_t x47, uint64_t x45, uint64_t x43, uint64_t x41, uint64_t x39, uint64_t x37, uint64_t x35)
{  uint32_t x65; uint8_t x66 = _addcarryx_u32(0x0, x5, x35, &x65);
{  uint32_t x68; uint8_t x69 = _addcarryx_u32(x66, x7, x37, &x68);
{  uint32_t x71; uint8_t x72 = _addcarryx_u32(x69, x9, x39, &x71);
{  uint32_t x74; uint8_t x75 = _addcarryx_u32(x72, x11, x41, &x74);
{  uint32_t x77; uint8_t x78 = _addcarryx_u32(x75, x13, x43, &x77);
{  uint32_t x80; uint8_t x81 = _addcarryx_u32(x78, x15, x45, &x80);
{  uint32_t x83; uint8_t x84 = _addcarryx_u32(x81, x17, x47, &x83);
{  uint32_t x86; uint8_t x87 = _addcarryx_u32(x84, x19, x49, &x86);
{  uint32_t x89; uint8_t x90 = _addcarryx_u32(x87, x21, x51, &x89);
{  uint32_t x92; uint8_t x93 = _addcarryx_u32(x90, x23, x53, &x92);
{  uint32_t x95; uint8_t x96 = _addcarryx_u32(x93, x25, x55, &x95);
{  uint32_t x98; uint8_t x99 = _addcarryx_u32(x96, x27, x57, &x98);
{  uint32_t x101; uint8_t x102 = _addcarryx_u32(x99, x29, x59, &x101);
{  uint32_t x104; uint8_t x105 = _addcarryx_u32(x102, x31, x61, &x104);
{  uint32_t x107; uint8_t x108 = _addcarryx_u32(x105, x33, x63, &x107);
{  uint32_t x110; uint8_t x111 = _addcarryx_u32(x108, x32, x62, &x110);
{  uint32_t x113; uint8_t x114 = _subborrow_u32(0x0, x65, 0xffffffef, &x113);
{  uint32_t x116; uint8_t x117 = _subborrow_u32(x114, x68, 0xffffffff, &x116);
{  uint32_t x119; uint8_t x120 = _subborrow_u32(x117, x71, 0xffffffff, &x119);
{  uint32_t x122; uint8_t x123 = _subborrow_u32(x120, x74, 0xffffffff, &x122);
{  uint32_t x125; uint8_t x126 = _subborrow_u32(x123, x77, 0xffffffff, &x125);
{  uint32_t x128; uint8_t x129 = _subborrow_u32(x126, x80, 0xffffffff, &x128);
{  uint32_t x131; uint8_t x132 = _subborrow_u32(x129, x83, 0xffffffff, &x131);
{  uint32_t x134; uint8_t x135 = _subborrow_u32(x132, x86, 0xffffffff, &x134);
{  uint32_t x137; uint8_t x138 = _subborrow_u32(x135, x89, 0xffffffff, &x137);
{  uint32_t x140; uint8_t x141 = _subborrow_u32(x138, x92, 0xffffffff, &x140);
{  uint32_t x143; uint8_t x144 = _subborrow_u32(x141, x95, 0xffffffff, &x143);
{  uint32_t x146; uint8_t x147 = _subborrow_u32(x144, x98, 0xffffffff, &x146);
{  uint32_t x149; uint8_t x150 = _subborrow_u32(x147, x101, 0xffffffff, &x149);
{  uint32_t x152; uint8_t x153 = _subborrow_u32(x150, x104, 0xffffffff, &x152);
{  uint32_t x155; uint8_t x156 = _subborrow_u32(x153, x107, 0xffffffff, &x155);
{  uint32_t x158; uint8_t x159 = _subborrow_u32(x156, x110, 0xff, &x158);
{  uint32_t _; uint8_t x162 = _subborrow_u32(x159, x111, 0x0, &_);
{  uint32_t x163 = cmovznz(x162, x158, x110);
{  uint32_t x164 = cmovznz(x162, x155, x107);
{  uint32_t x165 = cmovznz(x162, x152, x104);
{  uint32_t x166 = cmovznz(x162, x149, x101);
{  uint32_t x167 = cmovznz(x162, x146, x98);
{  uint32_t x168 = cmovznz(x162, x143, x95);
{  uint32_t x169 = cmovznz(x162, x140, x92);
{  uint32_t x170 = cmovznz(x162, x137, x89);
{  uint32_t x171 = cmovznz(x162, x134, x86);
{  uint32_t x172 = cmovznz(x162, x131, x83);
{  uint32_t x173 = cmovznz(x162, x128, x80);
{  uint32_t x174 = cmovznz(x162, x125, x77);
{  uint32_t x175 = cmovznz(x162, x122, x74);
{  uint32_t x176 = cmovznz(x162, x119, x71);
{  uint32_t x177 = cmovznz(x162, x116, x68);
{  uint32_t x178 = cmovznz(x162, x113, x65);
out[0] = x163;
out[1] = x164;
out[2] = x165;
out[3] = x166;
out[4] = x167;
out[5] = x168;
out[6] = x169;
out[7] = x170;
out[8] = x171;
out[9] = x172;
out[10] = x173;
out[11] = x174;
out[12] = x175;
out[13] = x176;
out[14] = x177;
out[15] = x178;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[16];
