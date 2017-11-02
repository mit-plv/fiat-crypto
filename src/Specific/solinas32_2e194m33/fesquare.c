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

void force_inline fesquare(uint64_t* out, uint64_t x13, uint64_t x14, uint64_t x12, uint64_t x10, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint64_t x15 = (((uint64_t)x2 * x13) + ((0x2 * ((uint64_t)x4 * x14)) + ((0x2 * ((uint64_t)x6 * x12)) + (((uint64_t)x8 * x10) + (((uint64_t)x10 * x8) + ((0x2 * ((uint64_t)x12 * x6)) + ((0x2 * ((uint64_t)x14 * x4)) + ((uint64_t)x13 * x2))))))));
{  uint64_t x16 = ((((uint64_t)x2 * x14) + ((0x2 * ((uint64_t)x4 * x12)) + (((uint64_t)x6 * x10) + (((uint64_t)x8 * x8) + (((uint64_t)x10 * x6) + ((0x2 * ((uint64_t)x12 * x4)) + ((uint64_t)x14 * x2))))))) + (0x21 * ((uint64_t)x13 * x13)));
{  uint64_t x17 = ((((uint64_t)x2 * x12) + (((uint64_t)x4 * x10) + (((uint64_t)x6 * x8) + (((uint64_t)x8 * x6) + (((uint64_t)x10 * x4) + ((uint64_t)x12 * x2)))))) + (0x21 * (((uint64_t)x14 * x13) + ((uint64_t)x13 * x14))));
{  uint64_t x18 = ((((uint64_t)x2 * x10) + ((0x2 * ((uint64_t)x4 * x8)) + ((0x2 * ((uint64_t)x6 * x6)) + ((0x2 * ((uint64_t)x8 * x4)) + ((uint64_t)x10 * x2))))) + (0x21 * ((0x2 * ((uint64_t)x12 * x13)) + ((0x2 * ((uint64_t)x14 * x14)) + (0x2 * ((uint64_t)x13 * x12))))));
{  uint64_t x19 = ((((uint64_t)x2 * x8) + ((0x2 * ((uint64_t)x4 * x6)) + ((0x2 * ((uint64_t)x6 * x4)) + ((uint64_t)x8 * x2)))) + (0x21 * (((uint64_t)x10 * x13) + ((0x2 * ((uint64_t)x12 * x14)) + ((0x2 * ((uint64_t)x14 * x12)) + ((uint64_t)x13 * x10))))));
{  uint64_t x20 = ((((uint64_t)x2 * x6) + ((0x2 * ((uint64_t)x4 * x4)) + ((uint64_t)x6 * x2))) + (0x21 * (((uint64_t)x8 * x13) + (((uint64_t)x10 * x14) + ((0x2 * ((uint64_t)x12 * x12)) + (((uint64_t)x14 * x10) + ((uint64_t)x13 * x8)))))));
{  uint64_t x21 = ((((uint64_t)x2 * x4) + ((uint64_t)x4 * x2)) + (0x21 * (((uint64_t)x6 * x13) + (((uint64_t)x8 * x14) + (((uint64_t)x10 * x12) + (((uint64_t)x12 * x10) + (((uint64_t)x14 * x8) + ((uint64_t)x13 * x6))))))));
{  uint64_t x22 = (((uint64_t)x2 * x2) + (0x21 * ((0x2 * ((uint64_t)x4 * x13)) + ((0x2 * ((uint64_t)x6 * x14)) + ((0x2 * ((uint64_t)x8 * x12)) + (((uint64_t)x10 * x10) + ((0x2 * ((uint64_t)x12 * x8)) + ((0x2 * ((uint64_t)x14 * x6)) + (0x2 * ((uint64_t)x13 * x4))))))))));
{  uint64_t x23 = (x22 >> 0x19);
{  uint32_t x24 = ((uint32_t)x22 & 0x1ffffff);
{  uint64_t x25 = (x23 + x21);
{  uint64_t x26 = (x25 >> 0x18);
{  uint32_t x27 = ((uint32_t)x25 & 0xffffff);
{  uint64_t x28 = (x26 + x20);
{  uint64_t x29 = (x28 >> 0x18);
{  uint32_t x30 = ((uint32_t)x28 & 0xffffff);
{  uint64_t x31 = (x29 + x19);
{  uint64_t x32 = (x31 >> 0x18);
{  uint32_t x33 = ((uint32_t)x31 & 0xffffff);
{  uint64_t x34 = (x32 + x18);
{  uint64_t x35 = (x34 >> 0x19);
{  uint32_t x36 = ((uint32_t)x34 & 0x1ffffff);
{  uint64_t x37 = (x35 + x17);
{  uint64_t x38 = (x37 >> 0x18);
{  uint32_t x39 = ((uint32_t)x37 & 0xffffff);
{  uint64_t x40 = (x38 + x16);
{  uint64_t x41 = (x40 >> 0x18);
{  uint32_t x42 = ((uint32_t)x40 & 0xffffff);
{  uint64_t x43 = (x41 + x15);
{  uint32_t x44 = (uint32_t) (x43 >> 0x18);
{  uint32_t x45 = ((uint32_t)x43 & 0xffffff);
{  uint64_t x46 = (x24 + ((uint64_t)0x21 * x44));
{  uint32_t x47 = (uint32_t) (x46 >> 0x19);
{  uint32_t x48 = ((uint32_t)x46 & 0x1ffffff);
{  uint32_t x49 = (x47 + x27);
{  uint32_t x50 = (x49 >> 0x18);
{  uint32_t x51 = (x49 & 0xffffff);
out[0] = x45;
out[1] = x42;
out[2] = x39;
out[3] = x36;
out[4] = x33;
out[5] = x50 + x30;
out[6] = x51;
out[7] = x48;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[8];
