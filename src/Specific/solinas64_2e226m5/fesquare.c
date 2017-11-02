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
{  uint128_t x7 = (((uint128_t)x2 * x5) + (((uint128_t)x4 * x6) + (((uint128_t)x6 * x4) + ((uint128_t)x5 * x2))));
{  uint128_t x8 = ((((uint128_t)x2 * x6) + ((0x2 * ((uint128_t)x4 * x4)) + ((uint128_t)x6 * x2))) + (0x5 * (0x2 * ((uint128_t)x5 * x5))));
{  uint128_t x9 = ((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) + (0x5 * (((uint128_t)x6 * x5) + ((uint128_t)x5 * x6))));
{  uint128_t x10 = (((uint128_t)x2 * x2) + (0x5 * ((0x2 * ((uint128_t)x4 * x5)) + (((uint128_t)x6 * x6) + (0x2 * ((uint128_t)x5 * x4))))));
{  uint64_t x11 = (uint64_t) (x10 >> 0x39);
{  uint64_t x12 = ((uint64_t)x10 & 0x1ffffffffffffff);
{  uint128_t x13 = (x11 + x9);
{  uint128_t x14 = (x13 >> 0x38);
{  uint64_t x15 = ((uint64_t)x13 & 0xffffffffffffff);
{  uint128_t x16 = (x14 + x8);
{  uint64_t x17 = (uint64_t) (x16 >> 0x39);
{  uint64_t x18 = ((uint64_t)x16 & 0x1ffffffffffffff);
{  uint128_t x19 = (x17 + x7);
{  uint64_t x20 = (uint64_t) (x19 >> 0x38);
{  uint64_t x21 = ((uint64_t)x19 & 0xffffffffffffff);
{  uint128_t x22 = (x12 + ((uint128_t)0x5 * x20));
{  uint64_t x23 = (uint64_t) (x22 >> 0x39);
{  uint64_t x24 = ((uint64_t)x22 & 0x1ffffffffffffff);
{  uint64_t x25 = (x23 + x15);
{  uint64_t x26 = (x25 >> 0x38);
{  uint64_t x27 = (x25 & 0xffffffffffffff);
out[0] = x21;
out[1] = x26 + x18;
out[2] = x27;
out[3] = x24;
}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[4];
