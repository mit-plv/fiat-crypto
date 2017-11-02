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

void force_inline femul(uint64_t* out, uint64_t x22, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x42, uint64_t x43, uint64_t x41, uint64_t x39, uint64_t x37, uint64_t x35, uint64_t x33, uint64_t x31, uint64_t x29, uint64_t x27, uint64_t x25)
{  uint64_t x44 = (((uint64_t)x5 * x42) + ((0x2 * ((uint64_t)x7 * x43)) + ((0x2 * ((uint64_t)x9 * x41)) + ((0x2 * ((uint64_t)x11 * x39)) + ((0x2 * ((uint64_t)x13 * x37)) + ((0x2 * ((uint64_t)x15 * x35)) + ((0x2 * ((uint64_t)x17 * x33)) + ((0x2 * ((uint64_t)x19 * x31)) + ((0x2 * ((uint64_t)x21 * x29)) + ((0x2 * ((uint64_t)x23 * x27)) + ((uint64_t)x22 * x25)))))))))));
{  uint64_t x45 = ((((uint64_t)x5 * x43) + ((0x2 * ((uint64_t)x7 * x41)) + ((0x2 * ((uint64_t)x9 * x39)) + ((0x2 * ((uint64_t)x11 * x37)) + ((0x2 * ((uint64_t)x13 * x35)) + ((0x2 * ((uint64_t)x15 * x33)) + ((0x2 * ((uint64_t)x17 * x31)) + ((0x2 * ((uint64_t)x19 * x29)) + ((0x2 * ((uint64_t)x21 * x27)) + ((uint64_t)x23 * x25)))))))))) + (0x5 * ((uint64_t)x22 * x42)));
{  uint64_t x46 = ((((uint64_t)x5 * x41) + ((0x2 * ((uint64_t)x7 * x39)) + ((0x2 * ((uint64_t)x9 * x37)) + ((0x2 * ((uint64_t)x11 * x35)) + ((0x2 * ((uint64_t)x13 * x33)) + ((0x2 * ((uint64_t)x15 * x31)) + ((0x2 * ((uint64_t)x17 * x29)) + ((0x2 * ((uint64_t)x19 * x27)) + ((uint64_t)x21 * x25))))))))) + (0x5 * (((uint64_t)x23 * x42) + ((uint64_t)x22 * x43))));
{  uint64_t x47 = ((((uint64_t)x5 * x39) + ((0x2 * ((uint64_t)x7 * x37)) + ((0x2 * ((uint64_t)x9 * x35)) + ((0x2 * ((uint64_t)x11 * x33)) + ((0x2 * ((uint64_t)x13 * x31)) + ((0x2 * ((uint64_t)x15 * x29)) + ((0x2 * ((uint64_t)x17 * x27)) + ((uint64_t)x19 * x25)))))))) + (0x5 * (((uint64_t)x21 * x42) + (((uint64_t)x23 * x43) + ((uint64_t)x22 * x41)))));
{  uint64_t x48 = ((((uint64_t)x5 * x37) + ((0x2 * ((uint64_t)x7 * x35)) + ((0x2 * ((uint64_t)x9 * x33)) + ((0x2 * ((uint64_t)x11 * x31)) + ((0x2 * ((uint64_t)x13 * x29)) + ((0x2 * ((uint64_t)x15 * x27)) + ((uint64_t)x17 * x25))))))) + (0x5 * (((uint64_t)x19 * x42) + (((uint64_t)x21 * x43) + (((uint64_t)x23 * x41) + ((uint64_t)x22 * x39))))));
{  uint64_t x49 = ((((uint64_t)x5 * x35) + ((0x2 * ((uint64_t)x7 * x33)) + ((0x2 * ((uint64_t)x9 * x31)) + ((0x2 * ((uint64_t)x11 * x29)) + ((0x2 * ((uint64_t)x13 * x27)) + ((uint64_t)x15 * x25)))))) + (0x5 * (((uint64_t)x17 * x42) + (((uint64_t)x19 * x43) + (((uint64_t)x21 * x41) + (((uint64_t)x23 * x39) + ((uint64_t)x22 * x37)))))));
{  uint64_t x50 = ((((uint64_t)x5 * x33) + ((0x2 * ((uint64_t)x7 * x31)) + ((0x2 * ((uint64_t)x9 * x29)) + ((0x2 * ((uint64_t)x11 * x27)) + ((uint64_t)x13 * x25))))) + (0x5 * (((uint64_t)x15 * x42) + (((uint64_t)x17 * x43) + (((uint64_t)x19 * x41) + (((uint64_t)x21 * x39) + (((uint64_t)x23 * x37) + ((uint64_t)x22 * x35))))))));
{  uint64_t x51 = ((((uint64_t)x5 * x31) + ((0x2 * ((uint64_t)x7 * x29)) + ((0x2 * ((uint64_t)x9 * x27)) + ((uint64_t)x11 * x25)))) + (0x5 * (((uint64_t)x13 * x42) + (((uint64_t)x15 * x43) + (((uint64_t)x17 * x41) + (((uint64_t)x19 * x39) + (((uint64_t)x21 * x37) + (((uint64_t)x23 * x35) + ((uint64_t)x22 * x33)))))))));
{  uint64_t x52 = ((((uint64_t)x5 * x29) + ((0x2 * ((uint64_t)x7 * x27)) + ((uint64_t)x9 * x25))) + (0x5 * (((uint64_t)x11 * x42) + (((uint64_t)x13 * x43) + (((uint64_t)x15 * x41) + (((uint64_t)x17 * x39) + (((uint64_t)x19 * x37) + (((uint64_t)x21 * x35) + (((uint64_t)x23 * x33) + ((uint64_t)x22 * x31))))))))));
{  uint64_t x53 = ((((uint64_t)x5 * x27) + ((uint64_t)x7 * x25)) + (0x5 * (((uint64_t)x9 * x42) + (((uint64_t)x11 * x43) + (((uint64_t)x13 * x41) + (((uint64_t)x15 * x39) + (((uint64_t)x17 * x37) + (((uint64_t)x19 * x35) + (((uint64_t)x21 * x33) + (((uint64_t)x23 * x31) + ((uint64_t)x22 * x29)))))))))));
{  uint64_t x54 = (((uint64_t)x5 * x25) + (0x5 * ((0x2 * ((uint64_t)x7 * x42)) + ((0x2 * ((uint64_t)x9 * x43)) + ((0x2 * ((uint64_t)x11 * x41)) + ((0x2 * ((uint64_t)x13 * x39)) + ((0x2 * ((uint64_t)x15 * x37)) + ((0x2 * ((uint64_t)x17 * x35)) + ((0x2 * ((uint64_t)x19 * x33)) + ((0x2 * ((uint64_t)x21 * x31)) + ((0x2 * ((uint64_t)x23 * x29)) + (0x2 * ((uint64_t)x22 * x27)))))))))))));
{  uint32_t x55 = (uint32_t) (x54 >> 0x10);
{  uint32_t x56 = ((uint32_t)x54 & 0xffff);
{  uint64_t x57 = (x55 + x53);
{  uint32_t x58 = (uint32_t) (x57 >> 0xf);
{  uint32_t x59 = ((uint32_t)x57 & 0x7fff);
{  uint64_t x60 = (x58 + x52);
{  uint32_t x61 = (uint32_t) (x60 >> 0xf);
{  uint32_t x62 = ((uint32_t)x60 & 0x7fff);
{  uint64_t x63 = (x61 + x51);
{  uint32_t x64 = (uint32_t) (x63 >> 0xf);
{  uint32_t x65 = ((uint32_t)x63 & 0x7fff);
{  uint64_t x66 = (x64 + x50);
{  uint32_t x67 = (uint32_t) (x66 >> 0xf);
{  uint32_t x68 = ((uint32_t)x66 & 0x7fff);
{  uint64_t x69 = (x67 + x49);
{  uint32_t x70 = (uint32_t) (x69 >> 0xf);
{  uint32_t x71 = ((uint32_t)x69 & 0x7fff);
{  uint64_t x72 = (x70 + x48);
{  uint32_t x73 = (uint32_t) (x72 >> 0xf);
{  uint32_t x74 = ((uint32_t)x72 & 0x7fff);
{  uint64_t x75 = (x73 + x47);
{  uint32_t x76 = (uint32_t) (x75 >> 0xf);
{  uint32_t x77 = ((uint32_t)x75 & 0x7fff);
{  uint64_t x78 = (x76 + x46);
{  uint32_t x79 = (uint32_t) (x78 >> 0xf);
{  uint32_t x80 = ((uint32_t)x78 & 0x7fff);
{  uint64_t x81 = (x79 + x45);
{  uint32_t x82 = (uint32_t) (x81 >> 0xf);
{  uint32_t x83 = ((uint32_t)x81 & 0x7fff);
{  uint64_t x84 = (x82 + x44);
{  uint32_t x85 = (uint32_t) (x84 >> 0xf);
{  uint32_t x86 = ((uint32_t)x84 & 0x7fff);
{  uint32_t x87 = (x56 + (0x5 * x85));
{  uint32_t x88 = (x87 >> 0x10);
{  uint32_t x89 = (x87 & 0xffff);
{  uint32_t x90 = (x88 + x59);
{  uint32_t x91 = (x90 >> 0xf);
{  uint32_t x92 = (x90 & 0x7fff);
out[0] = x86;
out[1] = x83;
out[2] = x80;
out[3] = x77;
out[4] = x74;
out[5] = x71;
out[6] = x68;
out[7] = x65;
out[8] = x91 + x62;
out[9] = x92;
out[10] = x89;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[11];
