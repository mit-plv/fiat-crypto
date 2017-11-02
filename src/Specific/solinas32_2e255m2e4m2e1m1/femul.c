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
{  uint64_t x36 = (((uint64_t)x5 * x34) + ((0x2 * ((uint64_t)x7 * x35)) + (((uint64_t)x9 * x33) + (((uint64_t)x11 * x31) + ((0x2 * ((uint64_t)x13 * x29)) + (((uint64_t)x15 * x27) + (((uint64_t)x17 * x25) + ((0x2 * ((uint64_t)x19 * x23)) + ((uint64_t)x18 * x21)))))))));
{  ℤ x37 = ((((uint64_t)x5 * x35) + (((uint64_t)x7 * x33) + (((uint64_t)x9 * x31) + (((uint64_t)x11 * x29) + (((uint64_t)x13 * x27) + (((uint64_t)x15 * x25) + (((uint64_t)x17 * x23) + ((uint64_t)x19 * x21)))))))) +ℤ (((uint64_t)x18 * x34) + ((0x2 * ((uint64_t)x18 * x34)) + (0x10 * ((uint64_t)x18 * x34)))));
{  ℤ x38 = ((((uint64_t)x5 * x33) + ((0x2 * ((uint64_t)x7 * x31)) + ((0x2 * ((uint64_t)x9 * x29)) + (((uint64_t)x11 * x27) + ((0x2 * ((uint64_t)x13 * x25)) + ((0x2 * ((uint64_t)x15 * x23)) + ((uint64_t)x17 * x21))))))) +ℤ (((0x2 * ((uint64_t)x19 * x34)) + (0x2 * ((uint64_t)x18 * x35))) +ℤ ((0x2 * ((0x2 * ((uint64_t)x19 * x34)) + (0x2 * ((uint64_t)x18 * x35)))) +ℤ (0x10 *ℤ ((0x2 * ((uint64_t)x19 * x34)) + (0x2 * ((uint64_t)x18 * x35)))))));
{  ℤ x39 = ((((uint64_t)x5 * x31) + ((0x2 * ((uint64_t)x7 * x29)) + (((uint64_t)x9 * x27) + (((uint64_t)x11 * x25) + ((0x2 * ((uint64_t)x13 * x23)) + ((uint64_t)x15 * x21)))))) +ℤ ((((uint64_t)x17 * x34) + ((0x2 * ((uint64_t)x19 * x35)) + ((uint64_t)x18 * x33))) +ℤ ((0x2 * (((uint64_t)x17 * x34) + ((0x2 * ((uint64_t)x19 * x35)) + ((uint64_t)x18 * x33)))) +ℤ (0x10 *ℤ (((uint64_t)x17 * x34) + ((0x2 * ((uint64_t)x19 * x35)) + ((uint64_t)x18 * x33)))))));
{  ℤ x40 = ((((uint64_t)x5 * x29) + (((uint64_t)x7 * x27) + (((uint64_t)x9 * x25) + (((uint64_t)x11 * x23) + ((uint64_t)x13 * x21))))) +ℤ ((((uint64_t)x15 * x34) + (((uint64_t)x17 * x35) + (((uint64_t)x19 * x33) + ((uint64_t)x18 * x31)))) +ℤ ((0x2 * (((uint64_t)x15 * x34) + (((uint64_t)x17 * x35) + (((uint64_t)x19 * x33) + ((uint64_t)x18 * x31))))) +ℤ (0x10 *ℤ (((uint64_t)x15 * x34) + (((uint64_t)x17 * x35) + (((uint64_t)x19 * x33) + ((uint64_t)x18 * x31))))))));
{  ℤ x41 = ((((uint64_t)x5 * x27) + ((0x2 * ((uint64_t)x7 * x25)) + ((0x2 * ((uint64_t)x9 * x23)) + ((uint64_t)x11 * x21)))) +ℤ (((0x2 * ((uint64_t)x13 * x34)) + ((0x2 * ((uint64_t)x15 * x35)) + (((uint64_t)x17 * x33) + ((0x2 * ((uint64_t)x19 * x31)) + (0x2 * ((uint64_t)x18 * x29)))))) +ℤ ((0x2 *ℤ ((0x2 * ((uint64_t)x13 * x34)) + ((0x2 * ((uint64_t)x15 * x35)) + (((uint64_t)x17 * x33) + ((0x2 * ((uint64_t)x19 * x31)) + (0x2 * ((uint64_t)x18 * x29))))))) +ℤ (0x10 *ℤ ((0x2 * ((uint64_t)x13 * x34)) + ((0x2 * ((uint64_t)x15 * x35)) + (((uint64_t)x17 * x33) + ((0x2 * ((uint64_t)x19 * x31)) + (0x2 * ((uint64_t)x18 * x29))))))))));
{  ℤ x42 = ((((uint64_t)x5 * x25) + ((0x2 * ((uint64_t)x7 * x23)) + ((uint64_t)x9 * x21))) +ℤ ((((uint64_t)x11 * x34) + ((0x2 * ((uint64_t)x13 * x35)) + (((uint64_t)x15 * x33) + (((uint64_t)x17 * x31) + ((0x2 * ((uint64_t)x19 * x29)) + ((uint64_t)x18 * x27)))))) +ℤ ((0x2 *ℤ (((uint64_t)x11 * x34) + ((0x2 * ((uint64_t)x13 * x35)) + (((uint64_t)x15 * x33) + (((uint64_t)x17 * x31) + ((0x2 * ((uint64_t)x19 * x29)) + ((uint64_t)x18 * x27))))))) +ℤ (0x10 *ℤ (((uint64_t)x11 * x34) + ((0x2 * ((uint64_t)x13 * x35)) + (((uint64_t)x15 * x33) + (((uint64_t)x17 * x31) + ((0x2 * ((uint64_t)x19 * x29)) + ((uint64_t)x18 * x27))))))))));
{  ℤ x43 = ((((uint64_t)x5 * x23) + ((uint64_t)x7 * x21)) +ℤ ((((uint64_t)x9 * x34) + (((uint64_t)x11 * x35) + (((uint64_t)x13 * x33) + (((uint64_t)x15 * x31) + (((uint64_t)x17 * x29) + (((uint64_t)x19 * x27) + ((uint64_t)x18 * x25))))))) +ℤ ((0x2 * (((uint64_t)x9 * x34) + (((uint64_t)x11 * x35) + (((uint64_t)x13 * x33) + (((uint64_t)x15 * x31) + (((uint64_t)x17 * x29) + (((uint64_t)x19 * x27) + ((uint64_t)x18 * x25)))))))) +ℤ (0x10 *ℤ (((uint64_t)x9 * x34) + (((uint64_t)x11 * x35) + (((uint64_t)x13 * x33) + (((uint64_t)x15 * x31) + (((uint64_t)x17 * x29) + (((uint64_t)x19 * x27) + ((uint64_t)x18 * x25)))))))))));
{  ℤ x44 = (((uint64_t)x5 * x21) +ℤ (((0x2 * ((uint64_t)x7 * x34)) + ((0x2 * ((uint64_t)x9 * x35)) + (((uint64_t)x11 * x33) + ((0x2 * ((uint64_t)x13 * x31)) + ((0x2 * ((uint64_t)x15 * x29)) + (((uint64_t)x17 * x27) + ((0x2 * ((uint64_t)x19 * x25)) + (0x2 * ((uint64_t)x18 * x23))))))))) +ℤ ((0x2 *ℤ ((0x2 * ((uint64_t)x7 * x34)) + ((0x2 * ((uint64_t)x9 * x35)) + (((uint64_t)x11 * x33) + ((0x2 * ((uint64_t)x13 * x31)) + ((0x2 * ((uint64_t)x15 * x29)) + (((uint64_t)x17 * x27) + ((0x2 * ((uint64_t)x19 * x25)) + (0x2 * ((uint64_t)x18 * x23)))))))))) +ℤ (0x10 *ℤ ((0x2 * ((uint64_t)x7 * x34)) + ((0x2 * ((uint64_t)x9 * x35)) + (((uint64_t)x11 * x33) + ((0x2 * ((uint64_t)x13 * x31)) + ((0x2 * ((uint64_t)x15 * x29)) + (((uint64_t)x17 * x27) + ((0x2 * ((uint64_t)x19 * x25)) + (0x2 * ((uint64_t)x18 * x23)))))))))))));
{  uint64_t x45 = (x36 >> 0x1c);
{  uint32_t x46 = ((uint32_t)x36 & 0xfffffff);
{  uint64_t x47 = ((0x10000000 * x45) + x46);
{  uint64_t x48 = (x47 >> 0x1c);
{  uint32_t x49 = ((uint32_t)x47 & 0xfffffff);
{  uint64_t x50 = ((0x10000000 * x48) + x49);
{  uint64_t x51 = (x50 >> 0x1c);
{  uint32_t x52 = ((uint32_t)x50 & 0xfffffff);
{  uint64_t x53 = ((0x10000000 * x51) + x52);
{  uint64_t x54 = (x53 >> 0x1c);
{  uint32_t x55 = ((uint32_t)x53 & 0xfffffff);
{  ℤ x56 = (x44 +ℤ (x54 + ((0x2 * x54) + (0x10 * x54))));
{  uint64_t x57 = (x56 >> 0x1d);
{  uint32_t x58 = (x56 & 0x1fffffff);
{  ℤ x59 = (x57 +ℤ x43);
{  uint64_t x60 = (x59 >> 0x1c);
{  uint32_t x61 = (x59 & 0xfffffff);
{  ℤ x62 = (x60 +ℤ x42);
{  uint64_t x63 = (x62 >> 0x1c);
{  uint32_t x64 = (x62 & 0xfffffff);
{  ℤ x65 = (x63 +ℤ x41);
{  uint64_t x66 = (x65 >> 0x1d);
{  uint32_t x67 = (x65 & 0x1fffffff);
{  ℤ x68 = (x66 +ℤ x40);
{  uint64_t x69 = (x68 >> 0x1c);
{  uint32_t x70 = (x68 & 0xfffffff);
{  ℤ x71 = (x69 +ℤ x39);
{  uint64_t x72 = (x71 >> 0x1c);
{  uint32_t x73 = (x71 & 0xfffffff);
{  ℤ x74 = (x72 +ℤ x38);
{  uint64_t x75 = (x74 >> 0x1d);
{  uint32_t x76 = (x74 & 0x1fffffff);
{  ℤ x77 = (x75 +ℤ x37);
{  uint64_t x78 = (x77 >> 0x1c);
{  uint32_t x79 = (x77 & 0xfffffff);
{  uint64_t x80 = (x78 + x55);
{  uint32_t x81 = (uint32_t) (x80 >> 0x1c);
{  uint32_t x82 = ((uint32_t)x80 & 0xfffffff);
{  uint32_t x83 = (x58 + (x81 + ((0x2 * x81) + (0x10 * x81))));
{  uint32_t x84 = (x83 >> 0x1d);
{  uint32_t x85 = (x83 & 0x1fffffff);
{  uint32_t x86 = (x85 >> 0x1d);
{  uint32_t x87 = (x85 & 0x1fffffff);
{  uint32_t x88 = (x87 >> 0x1d);
{  uint32_t x89 = (x87 & 0x1fffffff);
out[0] = x82;
out[1] = x79;
out[2] = x76;
out[3] = x73;
out[4] = x70;
out[5] = x67;
out[6] = x64;
out[7] = x88 + x86 + x84 + x61;
out[8] = x89;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[9];
