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

void force_inline fesquare(uint64_t* out, uint64_t x7, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint128_t x9 = (((uint128_t)x2 * x7) + (((uint128_t)x4 * x8) + (((uint128_t)x6 * x6) + (((uint128_t)x8 * x4) + ((uint128_t)x7 * x2)))));
{  uint128_t x10 = ((((uint128_t)x2 * x8) + (((uint128_t)x4 * x6) + (((uint128_t)x6 * x4) + ((uint128_t)x8 * x2)))) + (((uint128_t)x7 * x7) + ((0x2 * ((uint128_t)x7 * x7)) + (0x10 * ((uint128_t)x7 * x7)))));
{  uint128_t x11 = ((((uint128_t)x2 * x6) + (((uint128_t)x4 * x4) + ((uint128_t)x6 * x2))) + ((((uint128_t)x8 * x7) + ((uint128_t)x7 * x8)) + ((0x2 * (((uint128_t)x8 * x7) + ((uint128_t)x7 * x8))) + (0x10 * (((uint128_t)x8 * x7) + ((uint128_t)x7 * x8))))));
{  uint128_t x12 = ((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) + ((((uint128_t)x6 * x7) + (((uint128_t)x8 * x8) + ((uint128_t)x7 * x6))) + ((0x2 * (((uint128_t)x6 * x7) + (((uint128_t)x8 * x8) + ((uint128_t)x7 * x6)))) + (0x10 * (((uint128_t)x6 * x7) + (((uint128_t)x8 * x8) + ((uint128_t)x7 * x6)))))));
{  uint128_t x13 = (((uint128_t)x2 * x2) + ((((uint128_t)x4 * x7) + (((uint128_t)x6 * x8) + (((uint128_t)x8 * x6) + ((uint128_t)x7 * x4)))) + ((0x2 * (((uint128_t)x4 * x7) + (((uint128_t)x6 * x8) + (((uint128_t)x8 * x6) + ((uint128_t)x7 * x4))))) + (0x10 * (((uint128_t)x4 * x7) + (((uint128_t)x6 * x8) + (((uint128_t)x8 * x6) + ((uint128_t)x7 * x4))))))));
{  uint64_t x14 = (uint64_t) (x9 >> 0x33);
{  uint64_t x15 = ((uint64_t)x9 & 0x7ffffffffffff);
{  uint128_t x16 = (((uint128_t)0x8000000000000 * x14) + x15);
{  uint64_t x17 = (uint64_t) (x16 >> 0x33);
{  uint64_t x18 = ((uint64_t)x16 & 0x7ffffffffffff);
{  uint128_t x19 = (((uint128_t)0x8000000000000 * x17) + x18);
{  uint64_t x20 = (uint64_t) (x19 >> 0x33);
{  uint64_t x21 = ((uint64_t)x19 & 0x7ffffffffffff);
{  uint128_t x22 = (((uint128_t)0x8000000000000 * x20) + x21);
{  uint64_t x23 = (uint64_t) (x22 >> 0x33);
{  uint64_t x24 = ((uint64_t)x22 & 0x7ffffffffffff);
{  uint128_t x25 = (x13 + (x23 + ((0x2 * x23) + (0x10 * x23))));
{  uint64_t x26 = (uint64_t) (x25 >> 0x33);
{  uint64_t x27 = ((uint64_t)x25 & 0x7ffffffffffff);
{  uint128_t x28 = (x26 + x12);
{  uint64_t x29 = (uint64_t) (x28 >> 0x33);
{  uint64_t x30 = ((uint64_t)x28 & 0x7ffffffffffff);
{  uint128_t x31 = (x29 + x11);
{  uint64_t x32 = (uint64_t) (x31 >> 0x33);
{  uint64_t x33 = ((uint64_t)x31 & 0x7ffffffffffff);
{  uint128_t x34 = (x32 + x10);
{  uint64_t x35 = (uint64_t) (x34 >> 0x33);
{  uint64_t x36 = ((uint64_t)x34 & 0x7ffffffffffff);
{  uint64_t x37 = (x35 + x24);
{  uint64_t x38 = (x37 >> 0x33);
{  uint64_t x39 = (x37 & 0x7ffffffffffff);
{  uint64_t x40 = (x27 + (x38 + ((0x2 * x38) + (0x10 * x38))));
{  uint64_t x41 = (x40 >> 0x33);
{  uint64_t x42 = (x40 & 0x7ffffffffffff);
{  uint64_t x43 = (x42 >> 0x33);
{  uint64_t x44 = (x42 & 0x7ffffffffffff);
{  uint64_t x45 = (x44 >> 0x33);
{  uint64_t x46 = (x44 & 0x7ffffffffffff);
out[0] = x39;
out[1] = x36;
out[2] = x33;
out[3] = x45 + x43 + x41 + x30;
out[4] = x46;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[5];
