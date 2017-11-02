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
{  uint64_t x15 = (((uint64_t)(x8 + x13) * (x8 + x13)) - ((uint64_t)x8 * x8));
{  uint64_t x16 = ((((uint64_t)(x6 + x14) * (x8 + x13)) + ((uint64_t)(x8 + x13) * (x6 + x14))) - (((uint64_t)x6 * x8) + ((uint64_t)x8 * x6)));
{  uint64_t x17 = ((((uint64_t)(x4 + x12) * (x8 + x13)) + (((uint64_t)(x6 + x14) * (x6 + x14)) + ((uint64_t)(x8 + x13) * (x4 + x12)))) - (((uint64_t)x4 * x8) + (((uint64_t)x6 * x6) + ((uint64_t)x8 * x4))));
{  uint64_t x18 = ((((uint64_t)(x2 + x10) * (x8 + x13)) + (((uint64_t)(x4 + x12) * (x6 + x14)) + (((uint64_t)(x6 + x14) * (x4 + x12)) + ((uint64_t)(x8 + x13) * (x2 + x10))))) - (((uint64_t)x2 * x8) + (((uint64_t)x4 * x6) + (((uint64_t)x6 * x4) + ((uint64_t)x8 * x2)))));
{  uint64_t x19 = ((((uint64_t)(x2 + x10) * (x6 + x14)) + (((uint64_t)(x4 + x12) * (x4 + x12)) + ((uint64_t)(x6 + x14) * (x2 + x10)))) - (((uint64_t)x2 * x6) + (((uint64_t)x4 * x4) + ((uint64_t)x6 * x2))));
{  uint64_t x20 = ((((uint64_t)(x2 + x10) * (x4 + x12)) + ((uint64_t)(x4 + x12) * (x2 + x10))) - (((uint64_t)x2 * x4) + ((uint64_t)x4 * x2)));
{  uint64_t x21 = (((uint64_t)(x2 + x10) * (x2 + x10)) - ((uint64_t)x2 * x2));
{  uint64_t x22 = (((((uint64_t)x8 * x8) + ((uint64_t)x13 * x13)) + x19) + x15);
{  uint64_t x23 = ((((((uint64_t)x6 * x8) + ((uint64_t)x8 * x6)) + (((uint64_t)x14 * x13) + ((uint64_t)x13 * x14))) + x20) + x16);
{  uint64_t x24 = ((((((uint64_t)x4 * x8) + (((uint64_t)x6 * x6) + ((uint64_t)x8 * x4))) + (((uint64_t)x12 * x13) + (((uint64_t)x14 * x14) + ((uint64_t)x13 * x12)))) + x21) + x17);
{  uint64_t x25 = ((((uint64_t)x2 * x8) + (((uint64_t)x4 * x6) + (((uint64_t)x6 * x4) + ((uint64_t)x8 * x2)))) + (((uint64_t)x10 * x13) + (((uint64_t)x12 * x14) + (((uint64_t)x14 * x12) + ((uint64_t)x13 * x10)))));
{  uint64_t x26 = (((((uint64_t)x2 * x6) + (((uint64_t)x4 * x4) + ((uint64_t)x6 * x2))) + (((uint64_t)x10 * x14) + (((uint64_t)x12 * x12) + ((uint64_t)x14 * x10)))) + x15);
{  uint64_t x27 = (((((uint64_t)x2 * x4) + ((uint64_t)x4 * x2)) + (((uint64_t)x10 * x12) + ((uint64_t)x12 * x10))) + x16);
{  uint64_t x28 = ((((uint64_t)x2 * x2) + ((uint64_t)x10 * x10)) + x17);
{  uint64_t x29 = (x25 >> 0x1b);
{  uint32_t x30 = ((uint32_t)x25 & 0x7ffffff);
{  uint64_t x31 = (x18 >> 0x1b);
{  uint32_t x32 = ((uint32_t)x18 & 0x7ffffff);
{  uint64_t x33 = ((0x8000000 * x31) + x32);
{  uint64_t x34 = (x33 >> 0x1b);
{  uint32_t x35 = ((uint32_t)x33 & 0x7ffffff);
{  uint64_t x36 = ((x29 + x24) + x34);
{  uint64_t x37 = (x36 >> 0x1b);
{  uint32_t x38 = ((uint32_t)x36 & 0x7ffffff);
{  uint64_t x39 = (x28 + x34);
{  uint64_t x40 = (x39 >> 0x1b);
{  uint32_t x41 = ((uint32_t)x39 & 0x7ffffff);
{  uint64_t x42 = (x37 + x23);
{  uint64_t x43 = (x42 >> 0x1b);
{  uint32_t x44 = ((uint32_t)x42 & 0x7ffffff);
{  uint64_t x45 = (x40 + x27);
{  uint64_t x46 = (x45 >> 0x1b);
{  uint32_t x47 = ((uint32_t)x45 & 0x7ffffff);
{  uint64_t x48 = (x43 + x22);
{  uint64_t x49 = (x48 >> 0x1b);
{  uint32_t x50 = ((uint32_t)x48 & 0x7ffffff);
{  uint64_t x51 = (x46 + x26);
{  uint64_t x52 = (x51 >> 0x1b);
{  uint32_t x53 = ((uint32_t)x51 & 0x7ffffff);
{  uint64_t x54 = (x49 + x35);
{  uint32_t x55 = (uint32_t) (x54 >> 0x1b);
{  uint32_t x56 = ((uint32_t)x54 & 0x7ffffff);
{  uint64_t x57 = (x52 + x30);
{  uint32_t x58 = (uint32_t) (x57 >> 0x1b);
{  uint32_t x59 = ((uint32_t)x57 & 0x7ffffff);
{  uint64_t x60 = (((uint64_t)0x8000000 * x55) + x56);
{  uint32_t x61 = (uint32_t) (x60 >> 0x1b);
{  uint32_t x62 = ((uint32_t)x60 & 0x7ffffff);
{  uint32_t x63 = ((x58 + x38) + x61);
{  uint32_t x64 = (x63 >> 0x1b);
{  uint32_t x65 = (x63 & 0x7ffffff);
{  uint32_t x66 = (x41 + x61);
{  uint32_t x67 = (x66 >> 0x1b);
{  uint32_t x68 = (x66 & 0x7ffffff);
out[0] = x62;
out[1] = x50;
out[2] = x64 + x44;
out[3] = x65;
out[4] = x59;
out[5] = x53;
out[6] = x67 + x47;
out[7] = x68;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[8];
