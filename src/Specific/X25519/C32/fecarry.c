#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "fecarry.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline fecarry(uint32_t* out, uint32_t x17, uint32_t x18, uint32_t x16, uint32_t x14, uint32_t x12, uint32_t x10, uint32_t x8, uint32_t x6, uint32_t x4, uint32_t x2)
{  uint32_t x19 = (x2 >> 0x1a);
{  uint32_t x20 = (x2 & 0x3ffffff);
{  uint32_t x21 = (x19 + x4);
{  uint32_t x22 = (x21 >> 0x19);
{  uint32_t x23 = (x21 & 0x1ffffff);
{  uint32_t x24 = (x22 + x6);
{  uint32_t x25 = (x24 >> 0x1a);
{  uint32_t x26 = (x24 & 0x3ffffff);
{  uint32_t x27 = (x25 + x8);
{  uint32_t x28 = (x27 >> 0x19);
{  uint32_t x29 = (x27 & 0x1ffffff);
{  uint32_t x30 = (x28 + x10);
{  uint32_t x31 = (x30 >> 0x1a);
{  uint32_t x32 = (x30 & 0x3ffffff);
{  uint32_t x33 = (x31 + x12);
{  uint32_t x34 = (x33 >> 0x19);
{  uint32_t x35 = (x33 & 0x1ffffff);
{  uint32_t x36 = (x34 + x14);
{  uint32_t x37 = (x36 >> 0x1a);
{  uint32_t x38 = (x36 & 0x3ffffff);
{  uint32_t x39 = (x37 + x16);
{  uint32_t x40 = (x39 >> 0x19);
{  uint32_t x41 = (x39 & 0x1ffffff);
{  uint32_t x42 = (x40 + x18);
{  uint32_t x43 = (x42 >> 0x1a);
{  uint32_t x44 = (x42 & 0x3ffffff);
{  uint32_t x45 = (x43 + x17);
{  uint32_t x46 = (x45 >> 0x19);
{  uint32_t x47 = (x45 & 0x1ffffff);
{  uint32_t x48 = (x20 + (0x13 * x46));
{  uint32_t x49 = (x48 >> 0x1a);
{  uint32_t x50 = (x48 & 0x3ffffff);
{  uint32_t x51 = (x49 + x23);
{  uint32_t x52 = (x51 >> 0x19);
{  uint32_t x53 = (x51 & 0x1ffffff);
out[0] = x47;
out[1] = x44;
out[2] = x41;
out[3] = x38;
out[4] = x35;
out[5] = x32;
out[6] = x29;
out[7] = x52 + x26;
out[8] = x53;
out[9] = x50;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint32_t out[10];
