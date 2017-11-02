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

void force_inline fesquare(uint64_t* out, uint64_t x9, uint64_t x10, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint128_t x11 = (((uint128_t)x2 * x9) + (((uint128_t)x4 * x10) + (((uint128_t)x6 * x8) + (((uint128_t)x8 * x6) + (((uint128_t)x10 * x4) + ((uint128_t)x9 * x2))))));
{  uint128_t x12 = ((((uint128_t)x2 * x10) + (((uint128_t)x4 * x8) + (((uint128_t)x6 * x6) + (((uint128_t)x8 * x4) + ((uint128_t)x10 * x2))))) + (0x3 * ((uint128_t)x9 * x9)));
{  uint128_t x13 = ((((uint128_t)x2 * x8) + (((uint128_t)x4 * x6) + (((uint128_t)x6 * x4) + ((uint128_t)x8 * x2)))) + (0x3 * (((uint128_t)x10 * x9) + ((uint128_t)x9 * x10))));
{  uint128_t x14 = ((((uint128_t)x2 * x6) + (((uint128_t)x4 * x4) + ((uint128_t)x6 * x2))) + (0x3 * (((uint128_t)x8 * x9) + (((uint128_t)x10 * x10) + ((uint128_t)x9 * x8)))));
{  uint128_t x15 = ((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) + (0x3 * (((uint128_t)x6 * x9) + (((uint128_t)x8 * x10) + (((uint128_t)x10 * x8) + ((uint128_t)x9 * x6))))));
{  uint128_t x16 = (((uint128_t)x2 * x2) + (0x3 * (((uint128_t)x4 * x9) + (((uint128_t)x6 * x10) + (((uint128_t)x8 * x8) + (((uint128_t)x10 * x6) + ((uint128_t)x9 * x4)))))));
{  uint64_t x17 = (uint64_t) (x16 >> 0x38);
{  uint64_t x18 = ((uint64_t)x16 & 0xffffffffffffff);
{  uint128_t x19 = (x17 + x15);
{  uint64_t x20 = (uint64_t) (x19 >> 0x38);
{  uint64_t x21 = ((uint64_t)x19 & 0xffffffffffffff);
{  uint128_t x22 = (x20 + x14);
{  uint64_t x23 = (uint64_t) (x22 >> 0x38);
{  uint64_t x24 = ((uint64_t)x22 & 0xffffffffffffff);
{  uint128_t x25 = (x23 + x13);
{  uint64_t x26 = (uint64_t) (x25 >> 0x38);
{  uint64_t x27 = ((uint64_t)x25 & 0xffffffffffffff);
{  uint128_t x28 = (x26 + x12);
{  uint64_t x29 = (uint64_t) (x28 >> 0x38);
{  uint64_t x30 = ((uint64_t)x28 & 0xffffffffffffff);
{  uint128_t x31 = (x29 + x11);
{  uint64_t x32 = (uint64_t) (x31 >> 0x38);
{  uint64_t x33 = ((uint64_t)x31 & 0xffffffffffffff);
{  uint64_t x34 = (x18 + (0x3 * x32));
{  uint64_t x35 = (x34 >> 0x38);
{  uint64_t x36 = (x34 & 0xffffffffffffff);
{  uint64_t x37 = (x35 + x21);
{  uint64_t x38 = (x37 >> 0x38);
{  uint64_t x39 = (x37 & 0xffffffffffffff);
out[0] = x33;
out[1] = x30;
out[2] = x27;
out[3] = x38 + x24;
out[4] = x39;
out[5] = x36;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[6];
