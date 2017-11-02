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
{  ℤ x32 = ((((uint64_t)x5 * x30) + (((uint64_t)x7 * x31) + (((uint64_t)x9 * x29) + (((uint64_t)x11 * x27) + (((uint64_t)x13 * x25) + (((uint64_t)x15 * x23) + (((uint64_t)x17 * x21) + ((uint64_t)x16 * x19)))))))) +ℤ ((0x10000 *ℤ (((uint64_t)x17 * x30) + ((uint64_t)x16 * x31))) +ℤ (0x10000000000 *ℤ ((uint64_t)x16 * x30))));
{  ℤ x33 = ((((uint64_t)x5 * x31) + (((uint64_t)x7 * x29) + (((uint64_t)x9 * x27) + (((uint64_t)x11 * x25) + (((uint64_t)x13 * x23) + (((uint64_t)x15 * x21) + ((uint64_t)x17 * x19))))))) +ℤ (((uint64_t)x16 * x30) +ℤ (0x10000 *ℤ (((uint64_t)x15 * x30) + (((uint64_t)x17 * x31) + ((uint64_t)x16 * x29))))));
{  ℤ x34 = ((((uint64_t)x5 * x29) + (((uint64_t)x7 * x27) + (((uint64_t)x9 * x25) + (((uint64_t)x11 * x23) + (((uint64_t)x13 * x21) + ((uint64_t)x15 * x19)))))) +ℤ ((((uint64_t)x17 * x30) + ((uint64_t)x16 * x31)) +ℤ (0x10000 *ℤ (((uint64_t)x13 * x30) + (((uint64_t)x15 * x31) + (((uint64_t)x17 * x29) + ((uint64_t)x16 * x27)))))));
{  ℤ x35 = ((((uint64_t)x5 * x27) + (((uint64_t)x7 * x25) + (((uint64_t)x9 * x23) + (((uint64_t)x11 * x21) + ((uint64_t)x13 * x19))))) +ℤ ((((uint64_t)x15 * x30) + (((uint64_t)x17 * x31) + ((uint64_t)x16 * x29))) +ℤ (0x10000 *ℤ (((uint64_t)x11 * x30) + (((uint64_t)x13 * x31) + (((uint64_t)x15 * x29) + (((uint64_t)x17 * x27) + ((uint64_t)x16 * x25))))))));
{  ℤ x36 = ((((uint64_t)x5 * x25) + (((uint64_t)x7 * x23) + (((uint64_t)x9 * x21) + ((uint64_t)x11 * x19)))) +ℤ ((((uint64_t)x13 * x30) + (((uint64_t)x15 * x31) + (((uint64_t)x17 * x29) + ((uint64_t)x16 * x27)))) +ℤ (0x10000 *ℤ (((uint64_t)x9 * x30) + (((uint64_t)x11 * x31) + (((uint64_t)x13 * x29) + (((uint64_t)x15 * x27) + (((uint64_t)x17 * x25) + ((uint64_t)x16 * x23)))))))));
{  ℤ x37 = ((((uint64_t)x5 * x23) + (((uint64_t)x7 * x21) + ((uint64_t)x9 * x19))) +ℤ ((((uint64_t)x11 * x30) + (((uint64_t)x13 * x31) + (((uint64_t)x15 * x29) + (((uint64_t)x17 * x27) + ((uint64_t)x16 * x25))))) +ℤ (0x10000 *ℤ (((uint64_t)x7 * x30) + (((uint64_t)x9 * x31) + (((uint64_t)x11 * x29) + (((uint64_t)x13 * x27) + (((uint64_t)x15 * x25) + (((uint64_t)x17 * x23) + ((uint64_t)x16 * x21))))))))));
{  uint64_t x38 = ((((uint64_t)x5 * x21) + ((uint64_t)x7 * x19)) + (((uint64_t)x9 * x30) + (((uint64_t)x11 * x31) + (((uint64_t)x13 * x29) + (((uint64_t)x15 * x27) + (((uint64_t)x17 * x25) + ((uint64_t)x16 * x23)))))));
{  uint64_t x39 = (((uint64_t)x5 * x19) + (((uint64_t)x7 * x30) + (((uint64_t)x9 * x31) + (((uint64_t)x11 * x29) + (((uint64_t)x13 * x27) + (((uint64_t)x15 * x25) + (((uint64_t)x17 * x23) + ((uint64_t)x16 * x21))))))));
{  uint32_t x40 = (uint32_t) (x38 >> 0x18);
{  uint32_t x41 = ((uint32_t)x38 & 0xffffff);
{  ℤ x42 = (x32 >>ℤ 0x18);
{  uint32_t x43 = (x32 & 0xffffff);
{  ℤ x44 = ((0x1000000 *ℤ x42) +ℤ x43);
{  ℤ x45 = (x44 >>ℤ 0x18);
{  uint32_t x46 = (x44 & 0xffffff);
{  ℤ x47 = ((x40 +ℤ x37) +ℤ (0x10000 *ℤ x45));
{  uint64_t x48 = (x47 >> 0x18);
{  uint32_t x49 = (x47 & 0xffffff);
{  ℤ x50 = (x39 +ℤ x45);
{  uint64_t x51 = (x50 >> 0x18);
{  uint32_t x52 = (x50 & 0xffffff);
{  ℤ x53 = (x48 +ℤ x36);
{  uint64_t x54 = (x53 >> 0x18);
{  uint32_t x55 = (x53 & 0xffffff);
{  uint64_t x56 = (x51 + x41);
{  uint32_t x57 = (uint32_t) (x56 >> 0x18);
{  uint32_t x58 = ((uint32_t)x56 & 0xffffff);
{  ℤ x59 = (x54 +ℤ x35);
{  uint64_t x60 = (x59 >> 0x18);
{  uint32_t x61 = (x59 & 0xffffff);
{  ℤ x62 = (x60 +ℤ x34);
{  uint64_t x63 = (x62 >> 0x18);
{  uint32_t x64 = (x62 & 0xffffff);
{  ℤ x65 = (x63 +ℤ x33);
{  uint64_t x66 = (x65 >> 0x18);
{  uint32_t x67 = (x65 & 0xffffff);
{  uint64_t x68 = (x66 + x46);
{  uint32_t x69 = (uint32_t) (x68 >> 0x18);
{  uint32_t x70 = ((uint32_t)x68 & 0xffffff);
{  uint64_t x71 = (((uint64_t)0x1000000 * x69) + x70);
{  uint32_t x72 = (uint32_t) (x71 >> 0x18);
{  uint32_t x73 = ((uint32_t)x71 & 0xffffff);
{  uint64_t x74 = ((x57 + x49) + ((uint64_t)0x10000 * x72));
{  uint32_t x75 = (uint32_t) (x74 >> 0x18);
{  uint32_t x76 = ((uint32_t)x74 & 0xffffff);
{  uint32_t x77 = (x52 + x72);
{  uint32_t x78 = (x77 >> 0x18);
{  uint32_t x79 = (x77 & 0xffffff);
out[0] = x73;
out[1] = x67;
out[2] = x64;
out[3] = x61;
out[4] = x75 + x55;
out[5] = x76;
out[6] = x78 + x58;
out[7] = x79;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[8];
