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

void force_inline fesquare(uint64_t* out, uint64_t x5, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint128_t x7 = (((uint128_t)(x4 + x5) * (x4 + x5)) - ((uint128_t)x4 * x4));
{  uint128_t x8 = ((((uint128_t)(x2 + x6) * (x4 + x5)) + ((uint128_t)(x4 + x5) * (x2 + x6))) - (((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)));
{  uint128_t x9 = (((uint128_t)(x2 + x6) * (x2 + x6)) - ((uint128_t)x2 * x2));
{  uint128_t x10 = (((((uint128_t)x4 * x4) + ((uint128_t)x5 * x5)) + x9) + x7);
{  uint128_t x11 = ((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) + (((uint128_t)x6 * x5) + ((uint128_t)x5 * x6)));
{  uint128_t x12 = ((((uint128_t)x2 * x2) + ((uint128_t)x6 * x6)) + x7);
{  uint64_t x13 = (uint64_t) (x11 >> 0x36);
{  uint64_t x14 = ((uint64_t)x11 & 0x3fffffffffffff);
{  uint64_t x15 = (uint64_t) (x8 >> 0x36);
{  uint64_t x16 = ((uint64_t)x8 & 0x3fffffffffffff);
{  uint128_t x17 = (((uint128_t)0x40000000000000 * x15) + x16);
{  uint64_t x18 = (uint64_t) (x17 >> 0x36);
{  uint64_t x19 = ((uint64_t)x17 & 0x3fffffffffffff);
{  uint128_t x20 = ((x13 + x10) + x18);
{  uint64_t x21 = (uint64_t) (x20 >> 0x36);
{  uint64_t x22 = ((uint64_t)x20 & 0x3fffffffffffff);
{  uint128_t x23 = (x12 + x18);
{  uint64_t x24 = (uint64_t) (x23 >> 0x36);
{  uint64_t x25 = ((uint64_t)x23 & 0x3fffffffffffff);
{  uint64_t x26 = (x21 + x19);
{  uint64_t x27 = (x26 >> 0x36);
{  uint64_t x28 = (x26 & 0x3fffffffffffff);
{  uint64_t x29 = (x24 + x14);
{  uint64_t x30 = (x29 >> 0x36);
{  uint64_t x31 = (x29 & 0x3fffffffffffff);
{  uint64_t x32 = ((0x40000000000000 * x27) + x28);
{  uint64_t x33 = (x32 >> 0x36);
{  uint64_t x34 = (x32 & 0x3fffffffffffff);
{  uint64_t x35 = ((x30 + x22) + x33);
{  uint64_t x36 = (x35 >> 0x36);
{  uint64_t x37 = (x35 & 0x3fffffffffffff);
{  uint64_t x38 = (x25 + x33);
{  uint64_t x39 = (x38 >> 0x36);
{  uint64_t x40 = (x38 & 0x3fffffffffffff);
out[0] = x36 + x34;
out[1] = x37;
out[2] = x39 + x31;
out[3] = x40;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[4];
