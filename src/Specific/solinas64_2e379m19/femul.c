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

void force_inline femul(uint64_t* out, uint64_t x14, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x26, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17)
{  uint128_t x28 = (((uint128_t)x5 * x26) + ((0x2 * ((uint128_t)x7 * x27)) + ((0x2 * ((uint128_t)x9 * x25)) + ((0x2 * ((uint128_t)x11 * x23)) + ((0x2 * ((uint128_t)x13 * x21)) + ((0x2 * ((uint128_t)x15 * x19)) + ((uint128_t)x14 * x17)))))));
{  uint128_t x29 = ((((uint128_t)x5 * x27) + ((0x2 * ((uint128_t)x7 * x25)) + ((0x2 * ((uint128_t)x9 * x23)) + ((0x2 * ((uint128_t)x11 * x21)) + ((0x2 * ((uint128_t)x13 * x19)) + ((uint128_t)x15 * x17)))))) + (0x13 * ((uint128_t)x14 * x26)));
{  uint128_t x30 = ((((uint128_t)x5 * x25) + ((0x2 * ((uint128_t)x7 * x23)) + ((0x2 * ((uint128_t)x9 * x21)) + ((0x2 * ((uint128_t)x11 * x19)) + ((uint128_t)x13 * x17))))) + (0x13 * (((uint128_t)x15 * x26) + ((uint128_t)x14 * x27))));
{  uint128_t x31 = ((((uint128_t)x5 * x23) + ((0x2 * ((uint128_t)x7 * x21)) + ((0x2 * ((uint128_t)x9 * x19)) + ((uint128_t)x11 * x17)))) + (0x13 * (((uint128_t)x13 * x26) + (((uint128_t)x15 * x27) + ((uint128_t)x14 * x25)))));
{  uint128_t x32 = ((((uint128_t)x5 * x21) + ((0x2 * ((uint128_t)x7 * x19)) + ((uint128_t)x9 * x17))) + (0x13 * (((uint128_t)x11 * x26) + (((uint128_t)x13 * x27) + (((uint128_t)x15 * x25) + ((uint128_t)x14 * x23))))));
{  uint128_t x33 = ((((uint128_t)x5 * x19) + ((uint128_t)x7 * x17)) + (0x13 * (((uint128_t)x9 * x26) + (((uint128_t)x11 * x27) + (((uint128_t)x13 * x25) + (((uint128_t)x15 * x23) + ((uint128_t)x14 * x21)))))));
{  uint128_t x34 = (((uint128_t)x5 * x17) + (0x13 * ((0x2 * ((uint128_t)x7 * x26)) + ((0x2 * ((uint128_t)x9 * x27)) + ((0x2 * ((uint128_t)x11 * x25)) + ((0x2 * ((uint128_t)x13 * x23)) + ((0x2 * ((uint128_t)x15 * x21)) + (0x2 * ((uint128_t)x14 * x19)))))))));
{  uint128_t x35 = (x34 >> 0x37);
{  uint64_t x36 = ((uint64_t)x34 & 0x7fffffffffffff);
{  uint128_t x37 = (x35 + x33);
{  uint128_t x38 = (x37 >> 0x36);
{  uint64_t x39 = ((uint64_t)x37 & 0x3fffffffffffff);
{  uint128_t x40 = (x38 + x32);
{  uint64_t x41 = (uint64_t) (x40 >> 0x36);
{  uint64_t x42 = ((uint64_t)x40 & 0x3fffffffffffff);
{  uint128_t x43 = (x41 + x31);
{  uint64_t x44 = (uint64_t) (x43 >> 0x36);
{  uint64_t x45 = ((uint64_t)x43 & 0x3fffffffffffff);
{  uint128_t x46 = (x44 + x30);
{  uint64_t x47 = (uint64_t) (x46 >> 0x36);
{  uint64_t x48 = ((uint64_t)x46 & 0x3fffffffffffff);
{  uint128_t x49 = (x47 + x29);
{  uint64_t x50 = (uint64_t) (x49 >> 0x36);
{  uint64_t x51 = ((uint64_t)x49 & 0x3fffffffffffff);
{  uint128_t x52 = (x50 + x28);
{  uint64_t x53 = (uint64_t) (x52 >> 0x36);
{  uint64_t x54 = ((uint64_t)x52 & 0x3fffffffffffff);
{  uint128_t x55 = (x36 + ((uint128_t)0x13 * x53));
{  uint64_t x56 = (uint64_t) (x55 >> 0x37);
{  uint64_t x57 = ((uint64_t)x55 & 0x7fffffffffffff);
{  uint64_t x58 = (x56 + x39);
{  uint64_t x59 = (x58 >> 0x36);
{  uint64_t x60 = (x58 & 0x3fffffffffffff);
out[0] = x54;
out[1] = x51;
out[2] = x48;
out[3] = x45;
out[4] = x59 + x42;
out[5] = x60;
out[6] = x57;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[7];
