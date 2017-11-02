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

void force_inline femul(uint64_t* out, uint64_t x26, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x50, uint64_t x51, uint64_t x49, uint64_t x47, uint64_t x45, uint64_t x43, uint64_t x41, uint64_t x39, uint64_t x37, uint64_t x35, uint64_t x33, uint64_t x31, uint64_t x29)
{  uint64_t x52 = (((uint64_t)x5 * x50) + (((uint64_t)x7 * x51) + (((uint64_t)x9 * x49) + (((uint64_t)x11 * x47) + (((uint64_t)x13 * x45) + (((uint64_t)x15 * x43) + (((uint64_t)x17 * x41) + (((uint64_t)x19 * x39) + (((uint64_t)x21 * x37) + (((uint64_t)x23 * x35) + (((uint64_t)x25 * x33) + (((uint64_t)x27 * x31) + ((uint64_t)x26 * x29)))))))))))));
{  uint64_t x53 = ((((uint64_t)x5 * x51) + (((uint64_t)x7 * x49) + (((uint64_t)x9 * x47) + (((uint64_t)x11 * x45) + (((uint64_t)x13 * x43) + (((uint64_t)x15 * x41) + (((uint64_t)x17 * x39) + (((uint64_t)x19 * x37) + (((uint64_t)x21 * x35) + (((uint64_t)x23 * x33) + (((uint64_t)x25 * x31) + ((uint64_t)x27 * x29)))))))))))) + (0xf * ((uint64_t)x26 * x50)));
{  uint64_t x54 = ((((uint64_t)x5 * x49) + (((uint64_t)x7 * x47) + (((uint64_t)x9 * x45) + (((uint64_t)x11 * x43) + (((uint64_t)x13 * x41) + (((uint64_t)x15 * x39) + (((uint64_t)x17 * x37) + (((uint64_t)x19 * x35) + (((uint64_t)x21 * x33) + (((uint64_t)x23 * x31) + ((uint64_t)x25 * x29))))))))))) + (0xf * (((uint64_t)x27 * x50) + ((uint64_t)x26 * x51))));
{  uint64_t x55 = ((((uint64_t)x5 * x47) + (((uint64_t)x7 * x45) + (((uint64_t)x9 * x43) + (((uint64_t)x11 * x41) + (((uint64_t)x13 * x39) + (((uint64_t)x15 * x37) + (((uint64_t)x17 * x35) + (((uint64_t)x19 * x33) + (((uint64_t)x21 * x31) + ((uint64_t)x23 * x29)))))))))) + (0xf * (((uint64_t)x25 * x50) + (((uint64_t)x27 * x51) + ((uint64_t)x26 * x49)))));
{  uint64_t x56 = ((((uint64_t)x5 * x45) + (((uint64_t)x7 * x43) + (((uint64_t)x9 * x41) + (((uint64_t)x11 * x39) + (((uint64_t)x13 * x37) + (((uint64_t)x15 * x35) + (((uint64_t)x17 * x33) + (((uint64_t)x19 * x31) + ((uint64_t)x21 * x29))))))))) + (0xf * (((uint64_t)x23 * x50) + (((uint64_t)x25 * x51) + (((uint64_t)x27 * x49) + ((uint64_t)x26 * x47))))));
{  uint64_t x57 = ((((uint64_t)x5 * x43) + (((uint64_t)x7 * x41) + (((uint64_t)x9 * x39) + (((uint64_t)x11 * x37) + (((uint64_t)x13 * x35) + (((uint64_t)x15 * x33) + (((uint64_t)x17 * x31) + ((uint64_t)x19 * x29)))))))) + (0xf * (((uint64_t)x21 * x50) + (((uint64_t)x23 * x51) + (((uint64_t)x25 * x49) + (((uint64_t)x27 * x47) + ((uint64_t)x26 * x45)))))));
{  uint64_t x58 = ((((uint64_t)x5 * x41) + (((uint64_t)x7 * x39) + (((uint64_t)x9 * x37) + (((uint64_t)x11 * x35) + (((uint64_t)x13 * x33) + (((uint64_t)x15 * x31) + ((uint64_t)x17 * x29))))))) + (0xf * (((uint64_t)x19 * x50) + (((uint64_t)x21 * x51) + (((uint64_t)x23 * x49) + (((uint64_t)x25 * x47) + (((uint64_t)x27 * x45) + ((uint64_t)x26 * x43))))))));
{  uint64_t x59 = ((((uint64_t)x5 * x39) + (((uint64_t)x7 * x37) + (((uint64_t)x9 * x35) + (((uint64_t)x11 * x33) + (((uint64_t)x13 * x31) + ((uint64_t)x15 * x29)))))) + (0xf * (((uint64_t)x17 * x50) + (((uint64_t)x19 * x51) + (((uint64_t)x21 * x49) + (((uint64_t)x23 * x47) + (((uint64_t)x25 * x45) + (((uint64_t)x27 * x43) + ((uint64_t)x26 * x41)))))))));
{  uint64_t x60 = ((((uint64_t)x5 * x37) + (((uint64_t)x7 * x35) + (((uint64_t)x9 * x33) + (((uint64_t)x11 * x31) + ((uint64_t)x13 * x29))))) + (0xf * (((uint64_t)x15 * x50) + (((uint64_t)x17 * x51) + (((uint64_t)x19 * x49) + (((uint64_t)x21 * x47) + (((uint64_t)x23 * x45) + (((uint64_t)x25 * x43) + (((uint64_t)x27 * x41) + ((uint64_t)x26 * x39))))))))));
{  uint64_t x61 = ((((uint64_t)x5 * x35) + (((uint64_t)x7 * x33) + (((uint64_t)x9 * x31) + ((uint64_t)x11 * x29)))) + (0xf * (((uint64_t)x13 * x50) + (((uint64_t)x15 * x51) + (((uint64_t)x17 * x49) + (((uint64_t)x19 * x47) + (((uint64_t)x21 * x45) + (((uint64_t)x23 * x43) + (((uint64_t)x25 * x41) + (((uint64_t)x27 * x39) + ((uint64_t)x26 * x37)))))))))));
{  uint64_t x62 = ((((uint64_t)x5 * x33) + (((uint64_t)x7 * x31) + ((uint64_t)x9 * x29))) + (0xf * (((uint64_t)x11 * x50) + (((uint64_t)x13 * x51) + (((uint64_t)x15 * x49) + (((uint64_t)x17 * x47) + (((uint64_t)x19 * x45) + (((uint64_t)x21 * x43) + (((uint64_t)x23 * x41) + (((uint64_t)x25 * x39) + (((uint64_t)x27 * x37) + ((uint64_t)x26 * x35))))))))))));
{  uint64_t x63 = ((((uint64_t)x5 * x31) + ((uint64_t)x7 * x29)) + (0xf * (((uint64_t)x9 * x50) + (((uint64_t)x11 * x51) + (((uint64_t)x13 * x49) + (((uint64_t)x15 * x47) + (((uint64_t)x17 * x45) + (((uint64_t)x19 * x43) + (((uint64_t)x21 * x41) + (((uint64_t)x23 * x39) + (((uint64_t)x25 * x37) + (((uint64_t)x27 * x35) + ((uint64_t)x26 * x33)))))))))))));
{  uint64_t x64 = (((uint64_t)x5 * x29) + (0xf * (((uint64_t)x7 * x50) + (((uint64_t)x9 * x51) + (((uint64_t)x11 * x49) + (((uint64_t)x13 * x47) + (((uint64_t)x15 * x45) + (((uint64_t)x17 * x43) + (((uint64_t)x19 * x41) + (((uint64_t)x21 * x39) + (((uint64_t)x23 * x37) + (((uint64_t)x25 * x35) + (((uint64_t)x27 * x33) + ((uint64_t)x26 * x31))))))))))))));
{  uint64_t x65 = (x64 >> 0x1a);
{  uint32_t x66 = ((uint32_t)x64 & 0x3ffffff);
{  uint64_t x67 = (x65 + x63);
{  uint64_t x68 = (x67 >> 0x1a);
{  uint32_t x69 = ((uint32_t)x67 & 0x3ffffff);
{  uint64_t x70 = (x68 + x62);
{  uint64_t x71 = (x70 >> 0x1a);
{  uint32_t x72 = ((uint32_t)x70 & 0x3ffffff);
{  uint64_t x73 = (x71 + x61);
{  uint64_t x74 = (x73 >> 0x1a);
{  uint32_t x75 = ((uint32_t)x73 & 0x3ffffff);
{  uint64_t x76 = (x74 + x60);
{  uint64_t x77 = (x76 >> 0x1a);
{  uint32_t x78 = ((uint32_t)x76 & 0x3ffffff);
{  uint64_t x79 = (x77 + x59);
{  uint64_t x80 = (x79 >> 0x1a);
{  uint32_t x81 = ((uint32_t)x79 & 0x3ffffff);
{  uint64_t x82 = (x80 + x58);
{  uint64_t x83 = (x82 >> 0x1a);
{  uint32_t x84 = ((uint32_t)x82 & 0x3ffffff);
{  uint64_t x85 = (x83 + x57);
{  uint64_t x86 = (x85 >> 0x1a);
{  uint32_t x87 = ((uint32_t)x85 & 0x3ffffff);
{  uint64_t x88 = (x86 + x56);
{  uint64_t x89 = (x88 >> 0x1a);
{  uint32_t x90 = ((uint32_t)x88 & 0x3ffffff);
{  uint64_t x91 = (x89 + x55);
{  uint64_t x92 = (x91 >> 0x1a);
{  uint32_t x93 = ((uint32_t)x91 & 0x3ffffff);
{  uint64_t x94 = (x92 + x54);
{  uint64_t x95 = (x94 >> 0x1a);
{  uint32_t x96 = ((uint32_t)x94 & 0x3ffffff);
{  uint64_t x97 = (x95 + x53);
{  uint64_t x98 = (x97 >> 0x1a);
{  uint32_t x99 = ((uint32_t)x97 & 0x3ffffff);
{  uint64_t x100 = (x98 + x52);
{  uint64_t x101 = (x100 >> 0x1a);
{  uint32_t x102 = ((uint32_t)x100 & 0x3ffffff);
{  uint64_t x103 = (x66 + (0xf * x101));
{  uint32_t x104 = (uint32_t) (x103 >> 0x1a);
{  uint32_t x105 = ((uint32_t)x103 & 0x3ffffff);
{  uint32_t x106 = (x104 + x69);
{  uint32_t x107 = (x106 >> 0x1a);
{  uint32_t x108 = (x106 & 0x3ffffff);
out[0] = x102;
out[1] = x99;
out[2] = x96;
out[3] = x93;
out[4] = x90;
out[5] = x87;
out[6] = x84;
out[7] = x81;
out[8] = x78;
out[9] = x75;
out[10] = x107 + x72;
out[11] = x108;
out[12] = x105;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[13];
