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
{  uint128_t x15 = (((uint128_t)(x8 + x13) * (x8 + x13)) - ((uint128_t)x8 * x8));
{  uint128_t x16 = ((((uint128_t)(x6 + x14) * (x8 + x13)) + ((uint128_t)(x8 + x13) * (x6 + x14))) - (((uint128_t)x6 * x8) + ((uint128_t)x8 * x6)));
{  uint128_t x17 = ((((uint128_t)(x4 + x12) * (x8 + x13)) + (((uint128_t)(x6 + x14) * (x6 + x14)) + ((uint128_t)(x8 + x13) * (x4 + x12)))) - (((uint128_t)x4 * x8) + (((uint128_t)x6 * x6) + ((uint128_t)x8 * x4))));
{  uint128_t x18 = ((((uint128_t)(x2 + x10) * (x8 + x13)) + (((uint128_t)(x4 + x12) * (x6 + x14)) + (((uint128_t)(x6 + x14) * (x4 + x12)) + ((uint128_t)(x8 + x13) * (x2 + x10))))) - (((uint128_t)x2 * x8) + (((uint128_t)x4 * x6) + (((uint128_t)x6 * x4) + ((uint128_t)x8 * x2)))));
{  uint128_t x19 = ((((uint128_t)(x2 + x10) * (x6 + x14)) + (((uint128_t)(x4 + x12) * (x4 + x12)) + ((uint128_t)(x6 + x14) * (x2 + x10)))) - (((uint128_t)x2 * x6) + (((uint128_t)x4 * x4) + ((uint128_t)x6 * x2))));
{  uint128_t x20 = ((((uint128_t)(x2 + x10) * (x4 + x12)) + ((uint128_t)(x4 + x12) * (x2 + x10))) - (((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)));
{  uint128_t x21 = (((uint128_t)(x2 + x10) * (x2 + x10)) - ((uint128_t)x2 * x2));
{  uint128_t x22 = (((((uint128_t)x8 * x8) + ((uint128_t)x13 * x13)) + x19) + x15);
{  uint128_t x23 = ((((((uint128_t)x6 * x8) + ((uint128_t)x8 * x6)) + (((uint128_t)x14 * x13) + ((uint128_t)x13 * x14))) + x20) + x16);
{  uint128_t x24 = ((((((uint128_t)x4 * x8) + (((uint128_t)x6 * x6) + ((uint128_t)x8 * x4))) + (((uint128_t)x12 * x13) + (((uint128_t)x14 * x14) + ((uint128_t)x13 * x12)))) + x21) + x17);
{  uint128_t x25 = ((((uint128_t)x2 * x8) + (((uint128_t)x4 * x6) + (((uint128_t)x6 * x4) + ((uint128_t)x8 * x2)))) + (((uint128_t)x10 * x13) + (((uint128_t)x12 * x14) + (((uint128_t)x14 * x12) + ((uint128_t)x13 * x10)))));
{  uint128_t x26 = (((((uint128_t)x2 * x6) + (((uint128_t)x4 * x4) + ((uint128_t)x6 * x2))) + (((uint128_t)x10 * x14) + (((uint128_t)x12 * x12) + ((uint128_t)x14 * x10)))) + x15);
{  uint128_t x27 = (((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) + (((uint128_t)x10 * x12) + ((uint128_t)x12 * x10))) + x16);
{  uint128_t x28 = ((((uint128_t)x2 * x2) + ((uint128_t)x10 * x10)) + x17);
{  uint64_t x29 = (uint64_t) (x25 >> 0x34);
{  uint64_t x30 = ((uint64_t)x25 & 0xfffffffffffff);
{  uint64_t x31 = (uint64_t) (x18 >> 0x34);
{  uint64_t x32 = ((uint64_t)x18 & 0xfffffffffffff);
{  uint128_t x33 = (((uint128_t)0x10000000000000 * x31) + x32);
{  uint64_t x34 = (uint64_t) (x33 >> 0x34);
{  uint64_t x35 = ((uint64_t)x33 & 0xfffffffffffff);
{  uint128_t x36 = ((x29 + x24) + x34);
{  uint64_t x37 = (uint64_t) (x36 >> 0x34);
{  uint64_t x38 = ((uint64_t)x36 & 0xfffffffffffff);
{  uint128_t x39 = (x28 + x34);
{  uint64_t x40 = (uint64_t) (x39 >> 0x34);
{  uint64_t x41 = ((uint64_t)x39 & 0xfffffffffffff);
{  uint128_t x42 = (x37 + x23);
{  uint64_t x43 = (uint64_t) (x42 >> 0x34);
{  uint64_t x44 = ((uint64_t)x42 & 0xfffffffffffff);
{  uint128_t x45 = (x40 + x27);
{  uint64_t x46 = (uint64_t) (x45 >> 0x34);
{  uint64_t x47 = ((uint64_t)x45 & 0xfffffffffffff);
{  uint128_t x48 = (x43 + x22);
{  uint64_t x49 = (uint64_t) (x48 >> 0x34);
{  uint64_t x50 = ((uint64_t)x48 & 0xfffffffffffff);
{  uint128_t x51 = (x46 + x26);
{  uint64_t x52 = (uint64_t) (x51 >> 0x34);
{  uint64_t x53 = ((uint64_t)x51 & 0xfffffffffffff);
{  uint64_t x54 = (x49 + x35);
{  uint64_t x55 = (x54 >> 0x34);
{  uint64_t x56 = (x54 & 0xfffffffffffff);
{  uint64_t x57 = (x52 + x30);
{  uint64_t x58 = (x57 >> 0x34);
{  uint64_t x59 = (x57 & 0xfffffffffffff);
{  uint64_t x60 = ((0x10000000000000 * x55) + x56);
{  uint64_t x61 = (x60 >> 0x34);
{  uint64_t x62 = (x60 & 0xfffffffffffff);
{  uint64_t x63 = ((x58 + x38) + x61);
{  uint64_t x64 = (x63 >> 0x34);
{  uint64_t x65 = (x63 & 0xfffffffffffff);
{  uint64_t x66 = (x41 + x61);
{  uint64_t x67 = (x66 >> 0x34);
{  uint64_t x68 = (x66 & 0xfffffffffffff);
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
