#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "femul.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline femul(uint64_t* out, uint64_t x8, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x14, uint64_t x15, uint64_t x13, uint64_t x11)
{  uint128_t x16 = (((uint128_t)x5 * x14) + (((uint128_t)x7 * x15) + (((uint128_t)x9 * x13) + ((uint128_t)x8 * x11))));
{  uint128_t x17 = ((((uint128_t)x5 * x15) + (((uint128_t)x7 * x13) + ((uint128_t)x9 * x11))) + (0xf * ((uint128_t)x8 * x14)));
{  uint128_t x18 = ((((uint128_t)x5 * x13) + ((uint128_t)x7 * x11)) + (0xf * (((uint128_t)x9 * x14) + ((uint128_t)x8 * x15))));
{  uint128_t x19 = (((uint128_t)x5 * x11) + (0xf * (((uint128_t)x7 * x14) + (((uint128_t)x9 * x15) + ((uint128_t)x8 * x13)))));
{  uint64_t x20 = (uint64_t) (x19 >> 0x31);
{  uint64_t x21 = ((uint64_t)x19 & 0x1ffffffffffff);
{  uint128_t x22 = (x20 + x18);
{  uint64_t x23 = (uint64_t) (x22 >> 0x31);
{  uint64_t x24 = ((uint64_t)x22 & 0x1ffffffffffff);
{  uint128_t x25 = (x23 + x17);
{  uint64_t x26 = (uint64_t) (x25 >> 0x31);
{  uint64_t x27 = ((uint64_t)x25 & 0x1ffffffffffff);
{  uint128_t x28 = (x26 + x16);
{  uint64_t x29 = (uint64_t) (x28 >> 0x31);
{  uint64_t x30 = ((uint64_t)x28 & 0x1ffffffffffff);
{  uint64_t x31 = (x21 + (0xf * x29));
{  uint64_t x32 = (x31 >> 0x31);
{  uint64_t x33 = (x31 & 0x1ffffffffffff);
{  uint64_t x34 = (x32 + x24);
{  uint64_t x35 = (x34 >> 0x31);
{  uint64_t x36 = (x34 & 0x1ffffffffffff);
out[0] = x30;
out[1] = x35 + x27;
out[2] = x36;
out[3] = x33;
}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[4];
