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
{  uint128_t x16 = ((((uint128_t)x5 * x14) + (((uint128_t)x7 * x15) + (((uint128_t)x9 * x13) + ((uint128_t)x8 * x11)))) + (0x10000 * ((uint128_t)x8 * x14)));
{  uint128_t x17 = ((((uint128_t)x5 * x15) + (((uint128_t)x7 * x13) + ((uint128_t)x9 * x11))) + (((uint128_t)x8 * x14) + (0x10000 * (((uint128_t)x9 * x14) + ((uint128_t)x8 * x15)))));
{  uint128_t x18 = ((((uint128_t)x5 * x13) + ((uint128_t)x7 * x11)) + ((((uint128_t)x9 * x14) + ((uint128_t)x8 * x15)) + (0x10000 * (((uint128_t)x7 * x14) + (((uint128_t)x9 * x15) + ((uint128_t)x8 * x13))))));
{  uint128_t x19 = (((uint128_t)x5 * x11) + (((uint128_t)x7 * x14) + (((uint128_t)x9 * x15) + ((uint128_t)x8 * x13))));
{  uint64_t x20 = (uint64_t) (x19 >> 0x30);
{  uint64_t x21 = ((uint64_t)x19 & 0xffffffffffff);
{  uint128_t x22 = (x16 >> 0x30);
{  uint64_t x23 = ((uint64_t)x16 & 0xffffffffffff);
{  uint128_t x24 = ((0x1000000000000 * x22) + x23);
{  uint128_t x25 = (x24 >> 0x30);
{  uint64_t x26 = ((uint64_t)x24 & 0xffffffffffff);
{  uint128_t x27 = ((x20 + x18) + (0x10000 * x25));
{  uint128_t x28 = (x27 >> 0x30);
{  uint64_t x29 = ((uint64_t)x27 & 0xffffffffffff);
{  uint128_t x30 = (x21 + x25);
{  uint64_t x31 = (uint64_t) (x30 >> 0x30);
{  uint64_t x32 = ((uint64_t)x30 & 0xffffffffffff);
{  uint128_t x33 = (x28 + x17);
{  uint128_t x34 = (x33 >> 0x30);
{  uint64_t x35 = ((uint64_t)x33 & 0xffffffffffff);
{  uint128_t x36 = (x34 + x26);
{  uint64_t x37 = (uint64_t) (x36 >> 0x30);
{  uint64_t x38 = ((uint64_t)x36 & 0xffffffffffff);
{  uint128_t x39 = (((uint128_t)0x1000000000000 * x37) + x38);
{  uint64_t x40 = (uint64_t) (x39 >> 0x30);
{  uint64_t x41 = ((uint64_t)x39 & 0xffffffffffff);
{  uint64_t x42 = ((x31 + x29) + (0x10000 * x40));
{  uint64_t x43 = (x42 >> 0x30);
{  uint64_t x44 = (x42 & 0xffffffffffff);
{  uint64_t x45 = (x32 + x40);
{  uint64_t x46 = (x45 >> 0x30);
{  uint64_t x47 = (x45 & 0xffffffffffff);
out[0] = x41;
out[1] = x43 + x35;
out[2] = x46 + x44;
out[3] = x47;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[4];
