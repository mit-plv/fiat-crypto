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
{  ℤ x9 = (((uint64_t)x2 * x7) +ℤ (((uint64_t)x4 * x8) +ℤ (((uint64_t)x6 * x6) +ℤ (((uint64_t)x8 * x4) +ℤ ((uint64_t)x7 * x2)))));
{  ℤ x10 = ((((uint64_t)x2 * x8) +ℤ (((uint64_t)x4 * x6) +ℤ (((uint64_t)x6 * x4) +ℤ ((uint64_t)x8 * x2)))) +ℤ (0x3 *ℤ ((uint64_t)x7 * x7)));
{  ℤ x11 = ((((uint64_t)x2 * x6) +ℤ (((uint64_t)x4 * x4) +ℤ ((uint64_t)x6 * x2))) +ℤ (0x3 *ℤ (((uint64_t)x8 * x7) +ℤ ((uint64_t)x7 * x8))));
{  ℤ x12 = ((((uint64_t)x2 * x4) +ℤ ((uint64_t)x4 * x2)) +ℤ (0x3 *ℤ (((uint64_t)x6 * x7) +ℤ (((uint64_t)x8 * x8) +ℤ ((uint64_t)x7 * x6)))));
{  ℤ x13 = (((uint64_t)x2 * x2) +ℤ (0x3 *ℤ (((uint64_t)x4 * x7) +ℤ (((uint64_t)x6 * x8) +ℤ (((uint64_t)x8 * x6) +ℤ ((uint64_t)x7 * x4))))));
{  uint64_t x14 = (x13 >> 0x1e);
{  uint32_t x15 = (x13 & 0x3fffffff);
{  ℤ x16 = (x14 +ℤ x12);
{  uint64_t x17 = (x16 >> 0x1e);
{  uint32_t x18 = (x16 & 0x3fffffff);
{  ℤ x19 = (x17 +ℤ x11);
{  uint64_t x20 = (x19 >> 0x1e);
{  uint32_t x21 = (x19 & 0x3fffffff);
{  ℤ x22 = (x20 +ℤ x10);
{  uint64_t x23 = (x22 >> 0x1e);
{  uint32_t x24 = (x22 & 0x3fffffff);
{  ℤ x25 = (x23 +ℤ x9);
{  uint64_t x26 = (x25 >> 0x1e);
{  uint32_t x27 = (x25 & 0x3fffffff);
{  uint64_t x28 = (x15 + (0x3 * x26));
{  uint32_t x29 = (uint32_t) (x28 >> 0x1e);
{  uint32_t x30 = ((uint32_t)x28 & 0x3fffffff);
{  uint32_t x31 = (x29 + x18);
{  uint32_t x32 = (x31 >> 0x1e);
{  uint32_t x33 = (x31 & 0x3fffffff);
out[0] = x27;
out[1] = x24;
out[2] = x32 + x21;
out[3] = x33;
out[4] = x30;
}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[5];
