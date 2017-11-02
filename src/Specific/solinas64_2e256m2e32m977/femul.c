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

void force_inline femul(uint64_t* out, uint64_t x10, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x18, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13)
{  uint128_t x20 = (((uint128_t)x5 * x18) + ((0x2 * ((uint128_t)x7 * x19)) + ((0x2 * ((uint128_t)x9 * x17)) + ((0x2 * ((uint128_t)x11 * x15)) + ((uint128_t)x10 * x13)))));
{  ℤ x21 = ((((uint128_t)x5 * x19) + ((0x2 * ((uint128_t)x7 * x17)) + ((0x2 * ((uint128_t)x9 * x15)) + ((uint128_t)x11 * x13)))) +ℤ ((0x3d1 * ((uint128_t)x10 * x18)) +ℤ (0x100000000 *ℤ ((uint128_t)x10 * x18))));
{  ℤ x22 = ((((uint128_t)x5 * x17) + ((0x2 * ((uint128_t)x7 * x15)) + ((uint128_t)x9 * x13))) +ℤ ((0x3d1 * (((uint128_t)x11 * x18) + ((uint128_t)x10 * x19))) +ℤ (0x100000000 *ℤ (((uint128_t)x11 * x18) + ((uint128_t)x10 * x19)))));
{  ℤ x23 = ((((uint128_t)x5 * x15) + ((uint128_t)x7 * x13)) +ℤ ((0x3d1 * (((uint128_t)x9 * x18) + (((uint128_t)x11 * x19) + ((uint128_t)x10 * x17)))) +ℤ (0x100000000 *ℤ (((uint128_t)x9 * x18) + (((uint128_t)x11 * x19) + ((uint128_t)x10 * x17))))));
{  ℤ x24 = (((uint128_t)x5 * x13) +ℤ ((0x3d1 * ((0x2 * ((uint128_t)x7 * x18)) + ((0x2 * ((uint128_t)x9 * x19)) + ((0x2 * ((uint128_t)x11 * x17)) + (0x2 * ((uint128_t)x10 * x15)))))) +ℤ (0x100000000 *ℤ ((0x2 * ((uint128_t)x7 * x18)) + ((0x2 * ((uint128_t)x9 * x19)) + ((0x2 * ((uint128_t)x11 * x17)) + (0x2 * ((uint128_t)x10 * x15))))))));
{  uint64_t x25 = (uint64_t) (x20 >> 0x33);
{  uint64_t x26 = ((uint64_t)x20 & 0x7ffffffffffff);
{  uint128_t x27 = (((uint128_t)0x8000000000000 * x25) + x26);
{  uint64_t x28 = (uint64_t) (x27 >> 0x33);
{  uint64_t x29 = ((uint64_t)x27 & 0x7ffffffffffff);
{  uint128_t x30 = (((uint128_t)0x8000000000000 * x28) + x29);
{  uint64_t x31 = (uint64_t) (x30 >> 0x33);
{  uint64_t x32 = ((uint64_t)x30 & 0x7ffffffffffff);
{  ℤ x33 = (x24 +ℤ (((uint128_t)0x3d1 * x31) + ((uint128_t)0x100000000 * x31)));
{  uint128_t x34 = (x33 >> 0x34);
{  uint64_t x35 = (x33 & 0xfffffffffffff);
{  ℤ x36 = (x34 +ℤ x23);
{  uint128_t x37 = (x36 >> 0x33);
{  uint64_t x38 = (x36 & 0x7ffffffffffff);
{  ℤ x39 = (x37 +ℤ x22);
{  uint128_t x40 = (x39 >> 0x33);
{  uint64_t x41 = (x39 & 0x7ffffffffffff);
{  ℤ x42 = (x40 +ℤ x21);
{  uint128_t x43 = (x42 >> 0x33);
{  uint64_t x44 = (x42 & 0x7ffffffffffff);
{  uint128_t x45 = (x43 + x32);
{  uint64_t x46 = (uint64_t) (x45 >> 0x33);
{  uint64_t x47 = ((uint64_t)x45 & 0x7ffffffffffff);
{  uint128_t x48 = (x35 + ((0x3d1 * x46) + ((uint128_t)0x100000000 * x46)));
{  uint64_t x49 = (uint64_t) (x48 >> 0x34);
{  uint64_t x50 = ((uint64_t)x48 & 0xfffffffffffff);
{  uint64_t x51 = (x50 >> 0x34);
{  uint64_t x52 = (x50 & 0xfffffffffffff);
out[0] = x47;
out[1] = x44;
out[2] = x41;
out[3] = x51 + x49 + x38;
out[4] = x52;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[5];
