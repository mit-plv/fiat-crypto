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

void force_inline fesquare(uint64_t* out, uint64_t x11, uint64_t x12, uint64_t x10, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint64_t x13 = (((uint64_t)x2 * x11) + (((uint64_t)x4 * x12) + (((uint64_t)x6 * x10) + (((uint64_t)x8 * x8) + (((uint64_t)x10 * x6) + (((uint64_t)x12 * x4) + ((uint64_t)x11 * x2)))))));
{  uint64_t x14 = ((((uint64_t)x2 * x12) + (((uint64_t)x4 * x10) + (((uint64_t)x6 * x8) + (((uint64_t)x8 * x6) + (((uint64_t)x10 * x4) + ((uint64_t)x12 * x2)))))) + (0xf * ((uint64_t)x11 * x11)));
{  ℤ x15 = ((((uint64_t)x2 * x10) + (((uint64_t)x4 * x8) + (((uint64_t)x6 * x6) + (((uint64_t)x8 * x4) + ((uint64_t)x10 * x2))))) +ℤ (0xf *ℤ (((uint64_t)x12 * x11) + ((uint64_t)x11 * x12))));
{  ℤ x16 = ((((uint64_t)x2 * x8) + (((uint64_t)x4 * x6) + (((uint64_t)x6 * x4) + ((uint64_t)x8 * x2)))) +ℤ (0xf *ℤ (((uint64_t)x10 * x11) + (((uint64_t)x12 * x12) + ((uint64_t)x11 * x10)))));
{  ℤ x17 = ((((uint64_t)x2 * x6) + (((uint64_t)x4 * x4) + ((uint64_t)x6 * x2))) +ℤ (0xf *ℤ (((uint64_t)x8 * x11) + (((uint64_t)x10 * x12) + (((uint64_t)x12 * x10) + ((uint64_t)x11 * x8))))));
{  ℤ x18 = ((((uint64_t)x2 * x4) + ((uint64_t)x4 * x2)) +ℤ (0xf *ℤ (((uint64_t)x6 * x11) + (((uint64_t)x8 * x12) + (((uint64_t)x10 * x10) + (((uint64_t)x12 * x8) + ((uint64_t)x11 * x6)))))));
{  ℤ x19 = (((uint64_t)x2 * x2) +ℤ (0xf *ℤ (((uint64_t)x4 * x11) + (((uint64_t)x6 * x12) + (((uint64_t)x8 * x10) + (((uint64_t)x10 * x8) + (((uint64_t)x12 * x6) + ((uint64_t)x11 * x4))))))));
{  uint64_t x20 = (x19 >> 0x1c);
{  uint32_t x21 = (x19 & 0xfffffff);
{  ℤ x22 = (x20 +ℤ x18);
{  uint64_t x23 = (x22 >> 0x1c);
{  uint32_t x24 = (x22 & 0xfffffff);
{  ℤ x25 = (x23 +ℤ x17);
{  uint64_t x26 = (x25 >> 0x1c);
{  uint32_t x27 = (x25 & 0xfffffff);
{  ℤ x28 = (x26 +ℤ x16);
{  uint64_t x29 = (x28 >> 0x1c);
{  uint32_t x30 = (x28 & 0xfffffff);
{  ℤ x31 = (x29 +ℤ x15);
{  uint64_t x32 = (x31 >> 0x1c);
{  uint32_t x33 = (x31 & 0xfffffff);
{  uint64_t x34 = (x32 + x14);
{  uint64_t x35 = (x34 >> 0x1c);
{  uint32_t x36 = ((uint32_t)x34 & 0xfffffff);
{  uint64_t x37 = (x35 + x13);
{  uint64_t x38 = (x37 >> 0x1c);
{  uint32_t x39 = ((uint32_t)x37 & 0xfffffff);
{  uint64_t x40 = (x21 + (0xf * x38));
{  uint32_t x41 = (uint32_t) (x40 >> 0x1c);
{  uint32_t x42 = ((uint32_t)x40 & 0xfffffff);
{  uint32_t x43 = (x41 + x24);
{  uint32_t x44 = (x43 >> 0x1c);
{  uint32_t x45 = (x43 & 0xfffffff);
out[0] = x39;
out[1] = x36;
out[2] = x33;
out[3] = x30;
out[4] = x44 + x27;
out[5] = x45;
out[6] = x42;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[7];
