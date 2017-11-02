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

void force_inline femul(uint64_t* out, uint64_t x18, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x34, uint64_t x35, uint64_t x33, uint64_t x31, uint64_t x29, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21)
{  uint128_t x36 = (((uint128_t)x5 * x34) + (((uint128_t)x7 * x35) + (((uint128_t)x9 * x33) + (((uint128_t)x11 * x31) + (((uint128_t)x13 * x29) + (((uint128_t)x15 * x27) + (((uint128_t)x17 * x25) + (((uint128_t)x19 * x23) + ((uint128_t)x18 * x21)))))))));
{  uint128_t x37 = ((((uint128_t)x5 * x35) + (((uint128_t)x7 * x33) + (((uint128_t)x9 * x31) + (((uint128_t)x11 * x29) + (((uint128_t)x13 * x27) + (((uint128_t)x15 * x25) + (((uint128_t)x17 * x23) + ((uint128_t)x19 * x21)))))))) + (0x11 * ((uint128_t)x18 * x34)));
{  uint128_t x38 = ((((uint128_t)x5 * x33) + (((uint128_t)x7 * x31) + (((uint128_t)x9 * x29) + (((uint128_t)x11 * x27) + (((uint128_t)x13 * x25) + (((uint128_t)x15 * x23) + ((uint128_t)x17 * x21))))))) + (0x11 * (((uint128_t)x19 * x34) + ((uint128_t)x18 * x35))));
{  uint128_t x39 = ((((uint128_t)x5 * x31) + (((uint128_t)x7 * x29) + (((uint128_t)x9 * x27) + (((uint128_t)x11 * x25) + (((uint128_t)x13 * x23) + ((uint128_t)x15 * x21)))))) + (0x11 * (((uint128_t)x17 * x34) + (((uint128_t)x19 * x35) + ((uint128_t)x18 * x33)))));
{  uint128_t x40 = ((((uint128_t)x5 * x29) + (((uint128_t)x7 * x27) + (((uint128_t)x9 * x25) + (((uint128_t)x11 * x23) + ((uint128_t)x13 * x21))))) + (0x11 * (((uint128_t)x15 * x34) + (((uint128_t)x17 * x35) + (((uint128_t)x19 * x33) + ((uint128_t)x18 * x31))))));
{  uint128_t x41 = ((((uint128_t)x5 * x27) + (((uint128_t)x7 * x25) + (((uint128_t)x9 * x23) + ((uint128_t)x11 * x21)))) + (0x11 * (((uint128_t)x13 * x34) + (((uint128_t)x15 * x35) + (((uint128_t)x17 * x33) + (((uint128_t)x19 * x31) + ((uint128_t)x18 * x29)))))));
{  uint128_t x42 = ((((uint128_t)x5 * x25) + (((uint128_t)x7 * x23) + ((uint128_t)x9 * x21))) + (0x11 * (((uint128_t)x11 * x34) + (((uint128_t)x13 * x35) + (((uint128_t)x15 * x33) + (((uint128_t)x17 * x31) + (((uint128_t)x19 * x29) + ((uint128_t)x18 * x27))))))));
{  uint128_t x43 = ((((uint128_t)x5 * x23) + ((uint128_t)x7 * x21)) + (0x11 * (((uint128_t)x9 * x34) + (((uint128_t)x11 * x35) + (((uint128_t)x13 * x33) + (((uint128_t)x15 * x31) + (((uint128_t)x17 * x29) + (((uint128_t)x19 * x27) + ((uint128_t)x18 * x25)))))))));
{  uint128_t x44 = (((uint128_t)x5 * x21) + (0x11 * (((uint128_t)x7 * x34) + (((uint128_t)x9 * x35) + (((uint128_t)x11 * x33) + (((uint128_t)x13 * x31) + (((uint128_t)x15 * x29) + (((uint128_t)x17 * x27) + (((uint128_t)x19 * x25) + ((uint128_t)x18 * x23))))))))));
{  uint64_t x45 = (uint64_t) (x44 >> 0x2e);
{  uint64_t x46 = ((uint64_t)x44 & 0x3fffffffffff);
{  uint128_t x47 = (x45 + x43);
{  uint64_t x48 = (uint64_t) (x47 >> 0x2e);
{  uint64_t x49 = ((uint64_t)x47 & 0x3fffffffffff);
{  uint128_t x50 = (x48 + x42);
{  uint64_t x51 = (uint64_t) (x50 >> 0x2e);
{  uint64_t x52 = ((uint64_t)x50 & 0x3fffffffffff);
{  uint128_t x53 = (x51 + x41);
{  uint64_t x54 = (uint64_t) (x53 >> 0x2e);
{  uint64_t x55 = ((uint64_t)x53 & 0x3fffffffffff);
{  uint128_t x56 = (x54 + x40);
{  uint64_t x57 = (uint64_t) (x56 >> 0x2e);
{  uint64_t x58 = ((uint64_t)x56 & 0x3fffffffffff);
{  uint128_t x59 = (x57 + x39);
{  uint64_t x60 = (uint64_t) (x59 >> 0x2e);
{  uint64_t x61 = ((uint64_t)x59 & 0x3fffffffffff);
{  uint128_t x62 = (x60 + x38);
{  uint64_t x63 = (uint64_t) (x62 >> 0x2e);
{  uint64_t x64 = ((uint64_t)x62 & 0x3fffffffffff);
{  uint128_t x65 = (x63 + x37);
{  uint64_t x66 = (uint64_t) (x65 >> 0x2e);
{  uint64_t x67 = ((uint64_t)x65 & 0x3fffffffffff);
{  uint128_t x68 = (x66 + x36);
{  uint64_t x69 = (uint64_t) (x68 >> 0x2e);
{  uint64_t x70 = ((uint64_t)x68 & 0x3fffffffffff);
{  uint64_t x71 = (x46 + (0x11 * x69));
{  uint64_t x72 = (x71 >> 0x2e);
{  uint64_t x73 = (x71 & 0x3fffffffffff);
{  uint64_t x74 = (x72 + x49);
{  uint64_t x75 = (x74 >> 0x2e);
{  uint64_t x76 = (x74 & 0x3fffffffffff);
out[0] = x70;
out[1] = x67;
out[2] = x64;
out[3] = x61;
out[4] = x58;
out[5] = x55;
out[6] = x75 + x52;
out[7] = x76;
out[8] = x73;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[9];
