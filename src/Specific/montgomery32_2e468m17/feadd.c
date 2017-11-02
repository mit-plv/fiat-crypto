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

void force_inline feadd(uint64_t* out, uint64_t x30, uint64_t x31, uint64_t x29, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x58, uint64_t x59, uint64_t x57, uint64_t x55, uint64_t x53, uint64_t x51, uint64_t x49, uint64_t x47, uint64_t x45, uint64_t x43, uint64_t x41, uint64_t x39, uint64_t x37, uint64_t x35, uint64_t x33)
{  uint32_t x61; uint8_t x62 = _addcarryx_u32(0x0, x5, x33, &x61);
{  uint32_t x64; uint8_t x65 = _addcarryx_u32(x62, x7, x35, &x64);
{  uint32_t x67; uint8_t x68 = _addcarryx_u32(x65, x9, x37, &x67);
{  uint32_t x70; uint8_t x71 = _addcarryx_u32(x68, x11, x39, &x70);
{  uint32_t x73; uint8_t x74 = _addcarryx_u32(x71, x13, x41, &x73);
{  uint32_t x76; uint8_t x77 = _addcarryx_u32(x74, x15, x43, &x76);
{  uint32_t x79; uint8_t x80 = _addcarryx_u32(x77, x17, x45, &x79);
{  uint32_t x82; uint8_t x83 = _addcarryx_u32(x80, x19, x47, &x82);
{  uint32_t x85; uint8_t x86 = _addcarryx_u32(x83, x21, x49, &x85);
{  uint32_t x88; uint8_t x89 = _addcarryx_u32(x86, x23, x51, &x88);
{  uint32_t x91; uint8_t x92 = _addcarryx_u32(x89, x25, x53, &x91);
{  uint32_t x94; uint8_t x95 = _addcarryx_u32(x92, x27, x55, &x94);
{  uint32_t x97; uint8_t x98 = _addcarryx_u32(x95, x29, x57, &x97);
{  uint32_t x100; uint8_t x101 = _addcarryx_u32(x98, x31, x59, &x100);
{  uint32_t x103; uint8_t x104 = _addcarryx_u32(x101, x30, x58, &x103);
{  uint32_t x106; uint8_t x107 = _subborrow_u32(0x0, x61, 0xffffffef, &x106);
{  uint32_t x109; uint8_t x110 = _subborrow_u32(x107, x64, 0xffffffff, &x109);
{  uint32_t x112; uint8_t x113 = _subborrow_u32(x110, x67, 0xffffffff, &x112);
{  uint32_t x115; uint8_t x116 = _subborrow_u32(x113, x70, 0xffffffff, &x115);
{  uint32_t x118; uint8_t x119 = _subborrow_u32(x116, x73, 0xffffffff, &x118);
{  uint32_t x121; uint8_t x122 = _subborrow_u32(x119, x76, 0xffffffff, &x121);
{  uint32_t x124; uint8_t x125 = _subborrow_u32(x122, x79, 0xffffffff, &x124);
{  uint32_t x127; uint8_t x128 = _subborrow_u32(x125, x82, 0xffffffff, &x127);
{  uint32_t x130; uint8_t x131 = _subborrow_u32(x128, x85, 0xffffffff, &x130);
{  uint32_t x133; uint8_t x134 = _subborrow_u32(x131, x88, 0xffffffff, &x133);
{  uint32_t x136; uint8_t x137 = _subborrow_u32(x134, x91, 0xffffffff, &x136);
{  uint32_t x139; uint8_t x140 = _subborrow_u32(x137, x94, 0xffffffff, &x139);
{  uint32_t x142; uint8_t x143 = _subborrow_u32(x140, x97, 0xffffffff, &x142);
{  uint32_t x145; uint8_t x146 = _subborrow_u32(x143, x100, 0xffffffff, &x145);
{  uint32_t x148; uint8_t x149 = _subborrow_u32(x146, x103, 0xfffff, &x148);
{  uint32_t _; uint8_t x152 = _subborrow_u32(x149, x104, 0x0, &_);
{  uint32_t x153 = cmovznz(x152, x148, x103);
{  uint32_t x154 = cmovznz(x152, x145, x100);
{  uint32_t x155 = cmovznz(x152, x142, x97);
{  uint32_t x156 = cmovznz(x152, x139, x94);
{  uint32_t x157 = cmovznz(x152, x136, x91);
{  uint32_t x158 = cmovznz(x152, x133, x88);
{  uint32_t x159 = cmovznz(x152, x130, x85);
{  uint32_t x160 = cmovznz(x152, x127, x82);
{  uint32_t x161 = cmovznz(x152, x124, x79);
{  uint32_t x162 = cmovznz(x152, x121, x76);
{  uint32_t x163 = cmovznz(x152, x118, x73);
{  uint32_t x164 = cmovznz(x152, x115, x70);
{  uint32_t x165 = cmovznz(x152, x112, x67);
{  uint32_t x166 = cmovznz(x152, x109, x64);
{  uint32_t x167 = cmovznz(x152, x106, x61);
out[0] = x153;
out[1] = x154;
out[2] = x155;
out[3] = x156;
out[4] = x157;
out[5] = x158;
out[6] = x159;
out[7] = x160;
out[8] = x161;
out[9] = x162;
out[10] = x163;
out[11] = x164;
out[12] = x165;
out[13] = x166;
out[14] = x167;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[15];
