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

void force_inline feadd(uint64_t* out, uint64_t x28, uint64_t x29, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x54, uint64_t x55, uint64_t x53, uint64_t x51, uint64_t x49, uint64_t x47, uint64_t x45, uint64_t x43, uint64_t x41, uint64_t x39, uint64_t x37, uint64_t x35, uint64_t x33, uint64_t x31)
{  uint32_t x57; uint8_t x58 = _addcarryx_u32(0x0, x5, x31, &x57);
{  uint32_t x60; uint8_t x61 = _addcarryx_u32(x58, x7, x33, &x60);
{  uint32_t x63; uint8_t x64 = _addcarryx_u32(x61, x9, x35, &x63);
{  uint32_t x66; uint8_t x67 = _addcarryx_u32(x64, x11, x37, &x66);
{  uint32_t x69; uint8_t x70 = _addcarryx_u32(x67, x13, x39, &x69);
{  uint32_t x72; uint8_t x73 = _addcarryx_u32(x70, x15, x41, &x72);
{  uint32_t x75; uint8_t x76 = _addcarryx_u32(x73, x17, x43, &x75);
{  uint32_t x78; uint8_t x79 = _addcarryx_u32(x76, x19, x45, &x78);
{  uint32_t x81; uint8_t x82 = _addcarryx_u32(x79, x21, x47, &x81);
{  uint32_t x84; uint8_t x85 = _addcarryx_u32(x82, x23, x49, &x84);
{  uint32_t x87; uint8_t x88 = _addcarryx_u32(x85, x25, x51, &x87);
{  uint32_t x90; uint8_t x91 = _addcarryx_u32(x88, x27, x53, &x90);
{  uint32_t x93; uint8_t x94 = _addcarryx_u32(x91, x29, x55, &x93);
{  uint32_t x96; uint8_t x97 = _addcarryx_u32(x94, x28, x54, &x96);
{  uint32_t x99; uint8_t x100 = _subborrow_u32(0x0, x57, 0xffffffff, &x99);
{  uint32_t x102; uint8_t x103 = _subborrow_u32(x100, x60, 0xffffffff, &x102);
{  uint32_t x105; uint8_t x106 = _subborrow_u32(x103, x63, 0xffffffff, &x105);
{  uint32_t x108; uint8_t x109 = _subborrow_u32(x106, x66, 0xffffffff, &x108);
{  uint32_t x111; uint8_t x112 = _subborrow_u32(x109, x69, 0xffffffff, &x111);
{  uint32_t x114; uint8_t x115 = _subborrow_u32(x112, x72, 0xffffffff, &x114);
{  uint32_t x117; uint8_t x118 = _subborrow_u32(x115, x75, 0xffffffff, &x117);
{  uint32_t x120; uint8_t x121 = _subborrow_u32(x118, x78, 0xfffffffe, &x120);
{  uint32_t x123; uint8_t x124 = _subborrow_u32(x121, x81, 0xffffffff, &x123);
{  uint32_t x126; uint8_t x127 = _subborrow_u32(x124, x84, 0xffffffff, &x126);
{  uint32_t x129; uint8_t x130 = _subborrow_u32(x127, x87, 0xffffffff, &x129);
{  uint32_t x132; uint8_t x133 = _subborrow_u32(x130, x90, 0xffffffff, &x132);
{  uint32_t x135; uint8_t x136 = _subborrow_u32(x133, x93, 0xffffffff, &x135);
{  uint32_t x138; uint8_t x139 = _subborrow_u32(x136, x96, 0xffffffff, &x138);
{  uint32_t _; uint8_t x142 = _subborrow_u32(x139, x97, 0x0, &_);
{  uint32_t x143 = cmovznz(x142, x138, x96);
{  uint32_t x144 = cmovznz(x142, x135, x93);
{  uint32_t x145 = cmovznz(x142, x132, x90);
{  uint32_t x146 = cmovznz(x142, x129, x87);
{  uint32_t x147 = cmovznz(x142, x126, x84);
{  uint32_t x148 = cmovznz(x142, x123, x81);
{  uint32_t x149 = cmovznz(x142, x120, x78);
{  uint32_t x150 = cmovznz(x142, x117, x75);
{  uint32_t x151 = cmovznz(x142, x114, x72);
{  uint32_t x152 = cmovznz(x142, x111, x69);
{  uint32_t x153 = cmovznz(x142, x108, x66);
{  uint32_t x154 = cmovznz(x142, x105, x63);
{  uint32_t x155 = cmovznz(x142, x102, x60);
{  uint32_t x156 = cmovznz(x142, x99, x57);
out[0] = x143;
out[1] = x144;
out[2] = x145;
out[3] = x146;
out[4] = x147;
out[5] = x148;
out[6] = x149;
out[7] = x150;
out[8] = x151;
out[9] = x152;
out[10] = x153;
out[11] = x154;
out[12] = x155;
out[13] = x156;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[14];
