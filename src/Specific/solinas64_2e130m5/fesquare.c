#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "fesquare.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline fesquare(uint64_t* out, uint64_t x3, uint64_t x4, uint64_t x2)
{  uint128_t x5 = (((uint128_t)x2 * x3) + ((0x2 * ((uint128_t)x4 * x4)) + ((uint128_t)x3 * x2)));
{  uint128_t x6 = ((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) + (0x5 * ((uint128_t)x3 * x3)));
{  uint128_t x7 = (((uint128_t)x2 * x2) + (0x5 * ((0x2 * ((uint128_t)x4 * x3)) + (0x2 * ((uint128_t)x3 * x4)))));
{  uint64_t x8 = (uint64_t) (x7 >> 0x2c);
{  uint64_t x9 = ((uint64_t)x7 & 0xfffffffffff);
{  uint128_t x10 = (x8 + x6);
{  uint64_t x11 = (uint64_t) (x10 >> 0x2b);
{  uint64_t x12 = ((uint64_t)x10 & 0x7ffffffffff);
{  uint128_t x13 = (x11 + x5);
{  uint64_t x14 = (uint64_t) (x13 >> 0x2b);
{  uint64_t x15 = ((uint64_t)x13 & 0x7ffffffffff);
{  uint64_t x16 = (x9 + (0x5 * x14));
{  uint64_t x17 = (x16 >> 0x2c);
{  uint64_t x18 = (x16 & 0xfffffffffff);
{  uint64_t x19 = (x17 + x12);
{  uint64_t x20 = (x19 >> 0x2b);
{  uint64_t x21 = (x19 & 0x7ffffffffff);
out[0] = x20 + x15;
out[1] = x21;
out[2] = x18;
}}}}}}}}}}}}}}}}}
// caller: uint64_t out[3];
