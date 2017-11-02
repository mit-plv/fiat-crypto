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
{  uint128_t x16 = (((uint128_t)(x7 + x8) * (x13 + x14)) - ((uint128_t)x7 * x13));
{  uint128_t x17 = ((((uint128_t)(x5 + x9) * (x13 + x14)) + ((uint128_t)(x7 + x8) * (x11 + x15))) - (((uint128_t)x5 * x13) + ((uint128_t)x7 * x11)));
{  uint128_t x18 = (((uint128_t)(x5 + x9) * (x11 + x15)) - ((uint128_t)x5 * x11));
{  uint128_t x19 = (((((uint128_t)x7 * x13) + ((uint128_t)x8 * x14)) + x18) + x16);
{  uint128_t x20 = ((((uint128_t)x5 * x13) + ((uint128_t)x7 * x11)) + (((uint128_t)x9 * x14) + ((uint128_t)x8 * x15)));
{  uint128_t x21 = ((((uint128_t)x5 * x11) + ((uint128_t)x9 * x15)) + x16);
{  uint64_t x22 = (uint64_t) (x20 >> 0x36);
{  uint64_t x23 = ((uint64_t)x20 & 0x3fffffffffffff);
{  uint64_t x24 = (uint64_t) (x17 >> 0x36);
{  uint64_t x25 = ((uint64_t)x17 & 0x3fffffffffffff);
{  uint128_t x26 = (((uint128_t)0x40000000000000 * x24) + x25);
{  uint64_t x27 = (uint64_t) (x26 >> 0x36);
{  uint64_t x28 = ((uint64_t)x26 & 0x3fffffffffffff);
{  uint128_t x29 = ((x22 + x19) + x27);
{  uint64_t x30 = (uint64_t) (x29 >> 0x36);
{  uint64_t x31 = ((uint64_t)x29 & 0x3fffffffffffff);
{  uint128_t x32 = (x21 + x27);
{  uint64_t x33 = (uint64_t) (x32 >> 0x36);
{  uint64_t x34 = ((uint64_t)x32 & 0x3fffffffffffff);
{  uint64_t x35 = (x30 + x28);
{  uint64_t x36 = (x35 >> 0x36);
{  uint64_t x37 = (x35 & 0x3fffffffffffff);
{  uint64_t x38 = (x33 + x23);
{  uint64_t x39 = (x38 >> 0x36);
{  uint64_t x40 = (x38 & 0x3fffffffffffff);
{  uint64_t x41 = ((0x40000000000000 * x36) + x37);
{  uint64_t x42 = (x41 >> 0x36);
{  uint64_t x43 = (x41 & 0x3fffffffffffff);
{  uint64_t x44 = ((x39 + x31) + x42);
{  uint64_t x45 = (x44 >> 0x36);
{  uint64_t x46 = (x44 & 0x3fffffffffffff);
{  uint64_t x47 = (x34 + x42);
{  uint64_t x48 = (x47 >> 0x36);
{  uint64_t x49 = (x47 & 0x3fffffffffffff);
out[0] = x45 + x43;
out[1] = x46;
out[2] = x48 + x40;
out[3] = x49;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[4];
