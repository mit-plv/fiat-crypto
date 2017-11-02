#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "fesub.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline fesub(uint64_t* out, uint64_t x10, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x18, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13)
{  uint32_t x21; uint8_t x22 = _subborrow_u32(0x0, x5, x13, &x21);
{  uint32_t x24; uint8_t x25 = _subborrow_u32(x22, x7, x15, &x24);
{  uint32_t x27; uint8_t x28 = _subborrow_u32(x25, x9, x17, &x27);
{  uint32_t x30; uint8_t x31 = _subborrow_u32(x28, x11, x19, &x30);
{  uint32_t x33; uint8_t x34 = _subborrow_u32(x31, x10, x18, &x33);
{  uint32_t x35 = (uint32_t)cmovznz(x34, 0x0, 0xffffffff);
{  uint32_t x36 = (x35 & 0xfffffffb);
{  uint32_t x38; uint8_t x39 = _addcarryx_u32(0x0, x21, x36, &x38);
{  uint32_t x40 = (x35 & 0xffffffff);
{  uint32_t x42; uint8_t x43 = _addcarryx_u32(x39, x24, x40, &x42);
{  uint32_t x44 = (x35 & 0xffffffff);
{  uint32_t x46; uint8_t x47 = _addcarryx_u32(x43, x27, x44, &x46);
{  uint32_t x48 = (x35 & 0xffffffff);
{  uint32_t x50; uint8_t x51 = _addcarryx_u32(x47, x30, x48, &x50);
{  uint8_t x52 = ((uint8_t)x35 & 0x3);
{  uint32_t x54; uint8_t _ = _addcarryx_u32(x51, x33, x52, &x54);
out[0] = x54;
out[1] = x50;
out[2] = x46;
out[3] = x42;
out[4] = x38;
}}}}}}}}}}}}}}}}
// caller: uint64_t out[5];
