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

void force_inline fesquare(uint64_t* out, uint64_t x15, uint64_t x16, uint64_t x14, uint64_t x12, uint64_t x10, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint64_t x17 = (((uint64_t)x2 * x15) + (((uint64_t)x4 * x16) + (((uint64_t)x6 * x14) + (((uint64_t)x8 * x12) + (((uint64_t)x10 * x10) + (((uint64_t)x12 * x8) + (((uint64_t)x14 * x6) + (((uint64_t)x16 * x4) + ((uint64_t)x15 * x2)))))))));
{  uint64_t x18 = ((((uint64_t)x2 * x16) + (((uint64_t)x4 * x14) + (((uint64_t)x6 * x12) + (((uint64_t)x8 * x10) + (((uint64_t)x10 * x8) + (((uint64_t)x12 * x6) + (((uint64_t)x14 * x4) + ((uint64_t)x16 * x2)))))))) + (0x9 * ((uint64_t)x15 * x15)));
{  uint64_t x19 = ((((uint64_t)x2 * x14) + (((uint64_t)x4 * x12) + (((uint64_t)x6 * x10) + (((uint64_t)x8 * x8) + (((uint64_t)x10 * x6) + (((uint64_t)x12 * x4) + ((uint64_t)x14 * x2))))))) + (0x9 * (((uint64_t)x16 * x15) + ((uint64_t)x15 * x16))));
{  uint64_t x20 = ((((uint64_t)x2 * x12) + (((uint64_t)x4 * x10) + (((uint64_t)x6 * x8) + (((uint64_t)x8 * x6) + (((uint64_t)x10 * x4) + ((uint64_t)x12 * x2)))))) + (0x9 * (((uint64_t)x14 * x15) + (((uint64_t)x16 * x16) + ((uint64_t)x15 * x14)))));
{  uint64_t x21 = ((((uint64_t)x2 * x10) + (((uint64_t)x4 * x8) + (((uint64_t)x6 * x6) + (((uint64_t)x8 * x4) + ((uint64_t)x10 * x2))))) + (0x9 * (((uint64_t)x12 * x15) + (((uint64_t)x14 * x16) + (((uint64_t)x16 * x14) + ((uint64_t)x15 * x12))))));
{  uint64_t x22 = ((((uint64_t)x2 * x8) + (((uint64_t)x4 * x6) + (((uint64_t)x6 * x4) + ((uint64_t)x8 * x2)))) + (0x9 * (((uint64_t)x10 * x15) + (((uint64_t)x12 * x16) + (((uint64_t)x14 * x14) + (((uint64_t)x16 * x12) + ((uint64_t)x15 * x10)))))));
{  uint64_t x23 = ((((uint64_t)x2 * x6) + (((uint64_t)x4 * x4) + ((uint64_t)x6 * x2))) + (0x9 * (((uint64_t)x8 * x15) + (((uint64_t)x10 * x16) + (((uint64_t)x12 * x14) + (((uint64_t)x14 * x12) + (((uint64_t)x16 * x10) + ((uint64_t)x15 * x8))))))));
{  uint64_t x24 = ((((uint64_t)x2 * x4) + ((uint64_t)x4 * x2)) + (0x9 * (((uint64_t)x6 * x15) + (((uint64_t)x8 * x16) + (((uint64_t)x10 * x14) + (((uint64_t)x12 * x12) + (((uint64_t)x14 * x10) + (((uint64_t)x16 * x8) + ((uint64_t)x15 * x6)))))))));
{  uint64_t x25 = (((uint64_t)x2 * x2) + (0x9 * (((uint64_t)x4 * x15) + (((uint64_t)x6 * x16) + (((uint64_t)x8 * x14) + (((uint64_t)x10 * x12) + (((uint64_t)x12 * x10) + (((uint64_t)x14 * x8) + (((uint64_t)x16 * x6) + ((uint64_t)x15 * x4))))))))));
{  uint64_t x26 = (x25 >> 0x1b);
{  uint32_t x27 = ((uint32_t)x25 & 0x7ffffff);
{  uint64_t x28 = (x26 + x24);
{  uint64_t x29 = (x28 >> 0x1b);
{  uint32_t x30 = ((uint32_t)x28 & 0x7ffffff);
{  uint64_t x31 = (x29 + x23);
{  uint64_t x32 = (x31 >> 0x1b);
{  uint32_t x33 = ((uint32_t)x31 & 0x7ffffff);
{  uint64_t x34 = (x32 + x22);
{  uint64_t x35 = (x34 >> 0x1b);
{  uint32_t x36 = ((uint32_t)x34 & 0x7ffffff);
{  uint64_t x37 = (x35 + x21);
{  uint64_t x38 = (x37 >> 0x1b);
{  uint32_t x39 = ((uint32_t)x37 & 0x7ffffff);
{  uint64_t x40 = (x38 + x20);
{  uint64_t x41 = (x40 >> 0x1b);
{  uint32_t x42 = ((uint32_t)x40 & 0x7ffffff);
{  uint64_t x43 = (x41 + x19);
{  uint64_t x44 = (x43 >> 0x1b);
{  uint32_t x45 = ((uint32_t)x43 & 0x7ffffff);
{  uint64_t x46 = (x44 + x18);
{  uint64_t x47 = (x46 >> 0x1b);
{  uint32_t x48 = ((uint32_t)x46 & 0x7ffffff);
{  uint64_t x49 = (x47 + x17);
{  uint64_t x50 = (x49 >> 0x1b);
{  uint32_t x51 = ((uint32_t)x49 & 0x7ffffff);
{  uint64_t x52 = (x27 + (0x9 * x50));
{  uint32_t x53 = (uint32_t) (x52 >> 0x1b);
{  uint32_t x54 = ((uint32_t)x52 & 0x7ffffff);
{  uint32_t x55 = (x53 + x30);
{  uint32_t x56 = (x55 >> 0x1b);
{  uint32_t x57 = (x55 & 0x7ffffff);
out[0] = x51;
out[1] = x48;
out[2] = x45;
out[3] = x42;
out[4] = x39;
out[5] = x36;
out[6] = x56 + x33;
out[7] = x57;
out[8] = x54;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[9];
