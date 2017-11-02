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

void force_inline femul(uint64_t* out, uint64_t x16, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x30, uint64_t x31, uint64_t x29, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19)
{  uint128_t x32 = (((uint128_t)(x11 + x16) * (x25 + x30)) - ((uint128_t)x11 * x25));
{  uint128_t x33 = ((((uint128_t)(x9 + x17) * (x25 + x30)) + ((uint128_t)(x11 + x16) * (x23 + x31))) - (((uint128_t)x9 * x25) + ((uint128_t)x11 * x23)));
{  uint128_t x34 = ((((uint128_t)(x7 + x15) * (x25 + x30)) + (((uint128_t)(x9 + x17) * (x23 + x31)) + ((uint128_t)(x11 + x16) * (x21 + x29)))) - (((uint128_t)x7 * x25) + (((uint128_t)x9 * x23) + ((uint128_t)x11 * x21))));
{  uint128_t x35 = ((((uint128_t)(x5 + x13) * (x25 + x30)) + (((uint128_t)(x7 + x15) * (x23 + x31)) + (((uint128_t)(x9 + x17) * (x21 + x29)) + ((uint128_t)(x11 + x16) * (x19 + x27))))) - (((uint128_t)x5 * x25) + (((uint128_t)x7 * x23) + (((uint128_t)x9 * x21) + ((uint128_t)x11 * x19)))));
{  uint128_t x36 = ((((uint128_t)(x5 + x13) * (x23 + x31)) + (((uint128_t)(x7 + x15) * (x21 + x29)) + ((uint128_t)(x9 + x17) * (x19 + x27)))) - (((uint128_t)x5 * x23) + (((uint128_t)x7 * x21) + ((uint128_t)x9 * x19))));
{  uint128_t x37 = ((((uint128_t)(x5 + x13) * (x21 + x29)) + ((uint128_t)(x7 + x15) * (x19 + x27))) - (((uint128_t)x5 * x21) + ((uint128_t)x7 * x19)));
{  uint128_t x38 = (((uint128_t)(x5 + x13) * (x19 + x27)) - ((uint128_t)x5 * x19));
{  uint128_t x39 = (((((uint128_t)x11 * x25) + ((uint128_t)x16 * x30)) + x36) + x32);
{  uint128_t x40 = ((((((uint128_t)x9 * x25) + ((uint128_t)x11 * x23)) + (((uint128_t)x17 * x30) + ((uint128_t)x16 * x31))) + x37) + x33);
{  uint128_t x41 = ((((((uint128_t)x7 * x25) + (((uint128_t)x9 * x23) + ((uint128_t)x11 * x21))) + (((uint128_t)x15 * x30) + (((uint128_t)x17 * x31) + ((uint128_t)x16 * x29)))) + x38) + x34);
{  uint128_t x42 = ((((uint128_t)x5 * x25) + (((uint128_t)x7 * x23) + (((uint128_t)x9 * x21) + ((uint128_t)x11 * x19)))) + (((uint128_t)x13 * x30) + (((uint128_t)x15 * x31) + (((uint128_t)x17 * x29) + ((uint128_t)x16 * x27)))));
{  uint128_t x43 = (((((uint128_t)x5 * x23) + (((uint128_t)x7 * x21) + ((uint128_t)x9 * x19))) + (((uint128_t)x13 * x31) + (((uint128_t)x15 * x29) + ((uint128_t)x17 * x27)))) + x32);
{  uint128_t x44 = (((((uint128_t)x5 * x21) + ((uint128_t)x7 * x19)) + (((uint128_t)x13 * x29) + ((uint128_t)x15 * x27))) + x33);
{  uint128_t x45 = ((((uint128_t)x5 * x19) + ((uint128_t)x13 * x27)) + x34);
{  uint64_t x46 = (uint64_t) (x42 >> 0x38);
{  uint64_t x47 = ((uint64_t)x42 & 0xffffffffffffff);
{  uint64_t x48 = (uint64_t) (x35 >> 0x38);
{  uint64_t x49 = ((uint64_t)x35 & 0xffffffffffffff);
{  uint128_t x50 = (((uint128_t)0x100000000000000 * x48) + x49);
{  uint64_t x51 = (uint64_t) (x50 >> 0x38);
{  uint64_t x52 = ((uint64_t)x50 & 0xffffffffffffff);
{  uint128_t x53 = ((x46 + x41) + x51);
{  uint64_t x54 = (uint64_t) (x53 >> 0x38);
{  uint64_t x55 = ((uint64_t)x53 & 0xffffffffffffff);
{  uint128_t x56 = (x45 + x51);
{  uint64_t x57 = (uint64_t) (x56 >> 0x38);
{  uint64_t x58 = ((uint64_t)x56 & 0xffffffffffffff);
{  uint128_t x59 = (x54 + x40);
{  uint64_t x60 = (uint64_t) (x59 >> 0x38);
{  uint64_t x61 = ((uint64_t)x59 & 0xffffffffffffff);
{  uint128_t x62 = (x57 + x44);
{  uint64_t x63 = (uint64_t) (x62 >> 0x38);
{  uint64_t x64 = ((uint64_t)x62 & 0xffffffffffffff);
{  uint128_t x65 = (x60 + x39);
{  uint64_t x66 = (uint64_t) (x65 >> 0x38);
{  uint64_t x67 = ((uint64_t)x65 & 0xffffffffffffff);
{  uint128_t x68 = (x63 + x43);
{  uint64_t x69 = (uint64_t) (x68 >> 0x38);
{  uint64_t x70 = ((uint64_t)x68 & 0xffffffffffffff);
{  uint64_t x71 = (x66 + x52);
{  uint64_t x72 = (x71 >> 0x38);
{  uint64_t x73 = (x71 & 0xffffffffffffff);
{  uint64_t x74 = (x69 + x47);
{  uint64_t x75 = (x74 >> 0x38);
{  uint64_t x76 = (x74 & 0xffffffffffffff);
{  uint64_t x77 = ((0x100000000000000 * x72) + x73);
{  uint64_t x78 = (x77 >> 0x38);
{  uint64_t x79 = (x77 & 0xffffffffffffff);
{  uint64_t x80 = ((x75 + x55) + x78);
{  uint64_t x81 = (x80 >> 0x38);
{  uint64_t x82 = (x80 & 0xffffffffffffff);
{  uint64_t x83 = (x58 + x78);
{  uint64_t x84 = (x83 >> 0x38);
{  uint64_t x85 = (x83 & 0xffffffffffffff);
out[0] = x79;
out[1] = x67;
out[2] = x81 + x61;
out[3] = x82;
out[4] = x76;
out[5] = x70;
out[6] = x84 + x64;
out[7] = x85;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[8];
