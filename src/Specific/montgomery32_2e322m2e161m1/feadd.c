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

void force_inline feadd(uint64_t* out, uint64_t x22, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x42, uint64_t x43, uint64_t x41, uint64_t x39, uint64_t x37, uint64_t x35, uint64_t x33, uint64_t x31, uint64_t x29, uint64_t x27, uint64_t x25)
{  uint32_t x45; uint8_t x46 = _addcarryx_u32(0x0, x5, x25, &x45);
{  uint32_t x48; uint8_t x49 = _addcarryx_u32(x46, x7, x27, &x48);
{  uint32_t x51; uint8_t x52 = _addcarryx_u32(x49, x9, x29, &x51);
{  uint32_t x54; uint8_t x55 = _addcarryx_u32(x52, x11, x31, &x54);
{  uint32_t x57; uint8_t x58 = _addcarryx_u32(x55, x13, x33, &x57);
{  uint32_t x60; uint8_t x61 = _addcarryx_u32(x58, x15, x35, &x60);
{  uint32_t x63; uint8_t x64 = _addcarryx_u32(x61, x17, x37, &x63);
{  uint32_t x66; uint8_t x67 = _addcarryx_u32(x64, x19, x39, &x66);
{  uint32_t x69; uint8_t x70 = _addcarryx_u32(x67, x21, x41, &x69);
{  uint32_t x72; uint8_t x73 = _addcarryx_u32(x70, x23, x43, &x72);
{  uint32_t x75; uint8_t x76 = _addcarryx_u32(x73, x22, x42, &x75);
{  uint32_t x78; uint8_t x79 = _subborrow_u32(0x0, x45, 0xffffffff, &x78);
{  uint32_t x81; uint8_t x82 = _subborrow_u32(x79, x48, 0xffffffff, &x81);
{  uint32_t x84; uint8_t x85 = _subborrow_u32(x82, x51, 0xffffffff, &x84);
{  uint32_t x87; uint8_t x88 = _subborrow_u32(x85, x54, 0xffffffff, &x87);
{  uint32_t x90; uint8_t x91 = _subborrow_u32(x88, x57, 0xffffffff, &x90);
{  uint32_t x93; uint8_t x94 = _subborrow_u32(x91, x60, 0xfffffffd, &x93);
{  uint32_t x96; uint8_t x97 = _subborrow_u32(x94, x63, 0xffffffff, &x96);
{  uint32_t x99; uint8_t x100 = _subborrow_u32(x97, x66, 0xffffffff, &x99);
{  uint32_t x102; uint8_t x103 = _subborrow_u32(x100, x69, 0xffffffff, &x102);
{  uint32_t x105; uint8_t x106 = _subborrow_u32(x103, x72, 0xffffffff, &x105);
{  uint32_t x108; uint8_t x109 = _subborrow_u32(x106, x75, 0x3, &x108);
{  uint32_t _; uint8_t x112 = _subborrow_u32(x109, x76, 0x0, &_);
{  uint32_t x113 = cmovznz(x112, x108, x75);
{  uint32_t x114 = cmovznz(x112, x105, x72);
{  uint32_t x115 = cmovznz(x112, x102, x69);
{  uint32_t x116 = cmovznz(x112, x99, x66);
{  uint32_t x117 = cmovznz(x112, x96, x63);
{  uint32_t x118 = cmovznz(x112, x93, x60);
{  uint32_t x119 = cmovznz(x112, x90, x57);
{  uint32_t x120 = cmovznz(x112, x87, x54);
{  uint32_t x121 = cmovznz(x112, x84, x51);
{  uint32_t x122 = cmovznz(x112, x81, x48);
{  uint32_t x123 = cmovznz(x112, x78, x45);
out[0] = x113;
out[1] = x114;
out[2] = x115;
out[3] = x116;
out[4] = x117;
out[5] = x118;
out[6] = x119;
out[7] = x120;
out[8] = x121;
out[9] = x122;
out[10] = x123;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[11];
