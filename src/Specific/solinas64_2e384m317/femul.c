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
{  uint128_t x32 = (((uint128_t)x5 * x30) + (((uint128_t)x7 * x31) + (((uint128_t)x9 * x29) + (((uint128_t)x11 * x27) + (((uint128_t)x13 * x25) + (((uint128_t)x15 * x23) + (((uint128_t)x17 * x21) + ((uint128_t)x16 * x19))))))));
{  uint128_t x33 = ((((uint128_t)x5 * x31) + (((uint128_t)x7 * x29) + (((uint128_t)x9 * x27) + (((uint128_t)x11 * x25) + (((uint128_t)x13 * x23) + (((uint128_t)x15 * x21) + ((uint128_t)x17 * x19))))))) + (0x13d * ((uint128_t)x16 * x30)));
{  uint128_t x34 = ((((uint128_t)x5 * x29) + (((uint128_t)x7 * x27) + (((uint128_t)x9 * x25) + (((uint128_t)x11 * x23) + (((uint128_t)x13 * x21) + ((uint128_t)x15 * x19)))))) + (0x13d * (((uint128_t)x17 * x30) + ((uint128_t)x16 * x31))));
{  uint128_t x35 = ((((uint128_t)x5 * x27) + (((uint128_t)x7 * x25) + (((uint128_t)x9 * x23) + (((uint128_t)x11 * x21) + ((uint128_t)x13 * x19))))) + (0x13d * (((uint128_t)x15 * x30) + (((uint128_t)x17 * x31) + ((uint128_t)x16 * x29)))));
{  uint128_t x36 = ((((uint128_t)x5 * x25) + (((uint128_t)x7 * x23) + (((uint128_t)x9 * x21) + ((uint128_t)x11 * x19)))) + (0x13d * (((uint128_t)x13 * x30) + (((uint128_t)x15 * x31) + (((uint128_t)x17 * x29) + ((uint128_t)x16 * x27))))));
{  uint128_t x37 = ((((uint128_t)x5 * x23) + (((uint128_t)x7 * x21) + ((uint128_t)x9 * x19))) + (0x13d * (((uint128_t)x11 * x30) + (((uint128_t)x13 * x31) + (((uint128_t)x15 * x29) + (((uint128_t)x17 * x27) + ((uint128_t)x16 * x25)))))));
{  uint128_t x38 = ((((uint128_t)x5 * x21) + ((uint128_t)x7 * x19)) + (0x13d * (((uint128_t)x9 * x30) + (((uint128_t)x11 * x31) + (((uint128_t)x13 * x29) + (((uint128_t)x15 * x27) + (((uint128_t)x17 * x25) + ((uint128_t)x16 * x23))))))));
{  uint128_t x39 = (((uint128_t)x5 * x19) + (0x13d * (((uint128_t)x7 * x30) + (((uint128_t)x9 * x31) + (((uint128_t)x11 * x29) + (((uint128_t)x13 * x27) + (((uint128_t)x15 * x25) + (((uint128_t)x17 * x23) + ((uint128_t)x16 * x21)))))))));
{  uint64_t x40 = (uint64_t) (x39 >> 0x30);
{  uint64_t x41 = ((uint64_t)x39 & 0xffffffffffff);
{  uint128_t x42 = (x40 + x38);
{  uint64_t x43 = (uint64_t) (x42 >> 0x30);
{  uint64_t x44 = ((uint64_t)x42 & 0xffffffffffff);
{  uint128_t x45 = (x43 + x37);
{  uint64_t x46 = (uint64_t) (x45 >> 0x30);
{  uint64_t x47 = ((uint64_t)x45 & 0xffffffffffff);
{  uint128_t x48 = (x46 + x36);
{  uint64_t x49 = (uint64_t) (x48 >> 0x30);
{  uint64_t x50 = ((uint64_t)x48 & 0xffffffffffff);
{  uint128_t x51 = (x49 + x35);
{  uint64_t x52 = (uint64_t) (x51 >> 0x30);
{  uint64_t x53 = ((uint64_t)x51 & 0xffffffffffff);
{  uint128_t x54 = (x52 + x34);
{  uint64_t x55 = (uint64_t) (x54 >> 0x30);
{  uint64_t x56 = ((uint64_t)x54 & 0xffffffffffff);
{  uint128_t x57 = (x55 + x33);
{  uint64_t x58 = (uint64_t) (x57 >> 0x30);
{  uint64_t x59 = ((uint64_t)x57 & 0xffffffffffff);
{  uint128_t x60 = (x58 + x32);
{  uint64_t x61 = (uint64_t) (x60 >> 0x30);
{  uint64_t x62 = ((uint64_t)x60 & 0xffffffffffff);
{  uint64_t x63 = (x41 + (0x13d * x61));
{  uint64_t x64 = (x63 >> 0x30);
{  uint64_t x65 = (x63 & 0xffffffffffff);
{  uint64_t x66 = (x64 + x44);
{  uint64_t x67 = (x66 >> 0x30);
{  uint64_t x68 = (x66 & 0xffffffffffff);
out[0] = x62;
out[1] = x59;
out[2] = x56;
out[3] = x53;
out[4] = x50;
out[5] = x67 + x47;
out[6] = x68;
out[7] = x65;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[8];
