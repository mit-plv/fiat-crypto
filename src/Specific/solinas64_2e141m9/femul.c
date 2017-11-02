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

void force_inline femul(uint64_t* out, uint64_t x6, uint64_t x7, uint64_t x5, uint64_t x10, uint64_t x11, uint64_t x9)
{  uint128_t x12 = (((uint128_t)x5 * x10) + (((uint128_t)x7 * x11) + ((uint128_t)x6 * x9)));
{  uint128_t x13 = ((((uint128_t)x5 * x11) + ((uint128_t)x7 * x9)) + (0x9 * ((uint128_t)x6 * x10)));
{  uint128_t x14 = (((uint128_t)x5 * x9) + (0x9 * (((uint128_t)x7 * x10) + ((uint128_t)x6 * x11))));
{  uint64_t x15 = (uint64_t) (x14 >> 0x2f);
{  uint64_t x16 = ((uint64_t)x14 & 0x7fffffffffff);
{  uint128_t x17 = (x15 + x13);
{  uint64_t x18 = (uint64_t) (x17 >> 0x2f);
{  uint64_t x19 = ((uint64_t)x17 & 0x7fffffffffff);
{  uint128_t x20 = (x18 + x12);
{  uint64_t x21 = (uint64_t) (x20 >> 0x2f);
{  uint64_t x22 = ((uint64_t)x20 & 0x7fffffffffff);
{  uint64_t x23 = (x16 + (0x9 * x21));
{  uint64_t x24 = (x23 >> 0x2f);
{  uint64_t x25 = (x23 & 0x7fffffffffff);
{  uint64_t x26 = (x24 + x19);
{  uint64_t x27 = (x26 >> 0x2f);
{  uint64_t x28 = (x26 & 0x7fffffffffff);
out[0] = x27 + x22;
out[1] = x28;
out[2] = x25;
}}}}}}}}}}}}}}}}}
// caller: uint64_t out[3];
