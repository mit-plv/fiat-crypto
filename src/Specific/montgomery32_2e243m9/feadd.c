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

void force_inline feadd(uint64_t* out, uint64_t x16, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x30, uint64_t x31, uint64_t x29, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19)
{  uint32_t x33; uint8_t x34 = _addcarryx_u32(0x0, x5, x19, &x33);
{  uint32_t x36; uint8_t x37 = _addcarryx_u32(x34, x7, x21, &x36);
{  uint32_t x39; uint8_t x40 = _addcarryx_u32(x37, x9, x23, &x39);
{  uint32_t x42; uint8_t x43 = _addcarryx_u32(x40, x11, x25, &x42);
{  uint32_t x45; uint8_t x46 = _addcarryx_u32(x43, x13, x27, &x45);
{  uint32_t x48; uint8_t x49 = _addcarryx_u32(x46, x15, x29, &x48);
{  uint32_t x51; uint8_t x52 = _addcarryx_u32(x49, x17, x31, &x51);
{  uint32_t x54; uint8_t x55 = _addcarryx_u32(x52, x16, x30, &x54);
{  uint32_t x57; uint8_t x58 = _subborrow_u32(0x0, x33, 0xfffffff7, &x57);
{  uint32_t x60; uint8_t x61 = _subborrow_u32(x58, x36, 0xffffffff, &x60);
{  uint32_t x63; uint8_t x64 = _subborrow_u32(x61, x39, 0xffffffff, &x63);
{  uint32_t x66; uint8_t x67 = _subborrow_u32(x64, x42, 0xffffffff, &x66);
{  uint32_t x69; uint8_t x70 = _subborrow_u32(x67, x45, 0xffffffff, &x69);
{  uint32_t x72; uint8_t x73 = _subborrow_u32(x70, x48, 0xffffffff, &x72);
{  uint32_t x75; uint8_t x76 = _subborrow_u32(x73, x51, 0xffffffff, &x75);
{  uint32_t x78; uint8_t x79 = _subborrow_u32(x76, x54, 0x7ffff, &x78);
{  uint32_t _; uint8_t x82 = _subborrow_u32(x79, x55, 0x0, &_);
{  uint32_t x83 = cmovznz(x82, x78, x54);
{  uint32_t x84 = cmovznz(x82, x75, x51);
{  uint32_t x85 = cmovznz(x82, x72, x48);
{  uint32_t x86 = cmovznz(x82, x69, x45);
{  uint32_t x87 = cmovznz(x82, x66, x42);
{  uint32_t x88 = cmovznz(x82, x63, x39);
{  uint32_t x89 = cmovznz(x82, x60, x36);
{  uint32_t x90 = cmovznz(x82, x57, x33);
out[0] = x83;
out[1] = x84;
out[2] = x85;
out[3] = x86;
out[4] = x87;
out[5] = x88;
out[6] = x89;
out[7] = x90;
}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[8];
