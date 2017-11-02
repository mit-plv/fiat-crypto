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

void force_inline femul(uint64_t* out, uint64_t x28, uint64_t x29, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x54, uint64_t x55, uint64_t x53, uint64_t x51, uint64_t x49, uint64_t x47, uint64_t x45, uint64_t x43, uint64_t x41, uint64_t x39, uint64_t x37, uint64_t x35, uint64_t x33, uint64_t x31)
{  uint64_t x56 = (((uint64_t)x5 * x54) + (((uint64_t)x7 * x55) + (((uint64_t)x9 * x53) + (((uint64_t)x11 * x51) + (((uint64_t)x13 * x49) + (((uint64_t)x15 * x47) + (((uint64_t)x17 * x45) + (((uint64_t)x19 * x43) + (((uint64_t)x21 * x41) + (((uint64_t)x23 * x39) + (((uint64_t)x25 * x37) + (((uint64_t)x27 * x35) + (((uint64_t)x29 * x33) + ((uint64_t)x28 * x31))))))))))))));
{  uint64_t x57 = ((((uint64_t)x5 * x55) + (((uint64_t)x7 * x53) + (((uint64_t)x9 * x51) + (((uint64_t)x11 * x49) + (((uint64_t)x13 * x47) + (((uint64_t)x15 * x45) + (((uint64_t)x17 * x43) + (((uint64_t)x19 * x41) + (((uint64_t)x21 * x39) + (((uint64_t)x23 * x37) + (((uint64_t)x25 * x35) + (((uint64_t)x27 * x33) + ((uint64_t)x29 * x31))))))))))))) + (0x11 * ((uint64_t)x28 * x54)));
{  uint64_t x58 = ((((uint64_t)x5 * x53) + (((uint64_t)x7 * x51) + (((uint64_t)x9 * x49) + (((uint64_t)x11 * x47) + (((uint64_t)x13 * x45) + (((uint64_t)x15 * x43) + (((uint64_t)x17 * x41) + (((uint64_t)x19 * x39) + (((uint64_t)x21 * x37) + (((uint64_t)x23 * x35) + (((uint64_t)x25 * x33) + ((uint64_t)x27 * x31)))))))))))) + (0x11 * (((uint64_t)x29 * x54) + ((uint64_t)x28 * x55))));
{  uint64_t x59 = ((((uint64_t)x5 * x51) + (((uint64_t)x7 * x49) + (((uint64_t)x9 * x47) + (((uint64_t)x11 * x45) + (((uint64_t)x13 * x43) + (((uint64_t)x15 * x41) + (((uint64_t)x17 * x39) + (((uint64_t)x19 * x37) + (((uint64_t)x21 * x35) + (((uint64_t)x23 * x33) + ((uint64_t)x25 * x31))))))))))) + (0x11 * (((uint64_t)x27 * x54) + (((uint64_t)x29 * x55) + ((uint64_t)x28 * x53)))));
{  uint64_t x60 = ((((uint64_t)x5 * x49) + (((uint64_t)x7 * x47) + (((uint64_t)x9 * x45) + (((uint64_t)x11 * x43) + (((uint64_t)x13 * x41) + (((uint64_t)x15 * x39) + (((uint64_t)x17 * x37) + (((uint64_t)x19 * x35) + (((uint64_t)x21 * x33) + ((uint64_t)x23 * x31)))))))))) + (0x11 * (((uint64_t)x25 * x54) + (((uint64_t)x27 * x55) + (((uint64_t)x29 * x53) + ((uint64_t)x28 * x51))))));
{  uint64_t x61 = ((((uint64_t)x5 * x47) + (((uint64_t)x7 * x45) + (((uint64_t)x9 * x43) + (((uint64_t)x11 * x41) + (((uint64_t)x13 * x39) + (((uint64_t)x15 * x37) + (((uint64_t)x17 * x35) + (((uint64_t)x19 * x33) + ((uint64_t)x21 * x31))))))))) + (0x11 * (((uint64_t)x23 * x54) + (((uint64_t)x25 * x55) + (((uint64_t)x27 * x53) + (((uint64_t)x29 * x51) + ((uint64_t)x28 * x49)))))));
{  uint64_t x62 = ((((uint64_t)x5 * x45) + (((uint64_t)x7 * x43) + (((uint64_t)x9 * x41) + (((uint64_t)x11 * x39) + (((uint64_t)x13 * x37) + (((uint64_t)x15 * x35) + (((uint64_t)x17 * x33) + ((uint64_t)x19 * x31)))))))) + (0x11 * (((uint64_t)x21 * x54) + (((uint64_t)x23 * x55) + (((uint64_t)x25 * x53) + (((uint64_t)x27 * x51) + (((uint64_t)x29 * x49) + ((uint64_t)x28 * x47))))))));
{  uint64_t x63 = ((((uint64_t)x5 * x43) + (((uint64_t)x7 * x41) + (((uint64_t)x9 * x39) + (((uint64_t)x11 * x37) + (((uint64_t)x13 * x35) + (((uint64_t)x15 * x33) + ((uint64_t)x17 * x31))))))) + (0x11 * (((uint64_t)x19 * x54) + (((uint64_t)x21 * x55) + (((uint64_t)x23 * x53) + (((uint64_t)x25 * x51) + (((uint64_t)x27 * x49) + (((uint64_t)x29 * x47) + ((uint64_t)x28 * x45)))))))));
{  uint64_t x64 = ((((uint64_t)x5 * x41) + (((uint64_t)x7 * x39) + (((uint64_t)x9 * x37) + (((uint64_t)x11 * x35) + (((uint64_t)x13 * x33) + ((uint64_t)x15 * x31)))))) + (0x11 * (((uint64_t)x17 * x54) + (((uint64_t)x19 * x55) + (((uint64_t)x21 * x53) + (((uint64_t)x23 * x51) + (((uint64_t)x25 * x49) + (((uint64_t)x27 * x47) + (((uint64_t)x29 * x45) + ((uint64_t)x28 * x43))))))))));
{  uint64_t x65 = ((((uint64_t)x5 * x39) + (((uint64_t)x7 * x37) + (((uint64_t)x9 * x35) + (((uint64_t)x11 * x33) + ((uint64_t)x13 * x31))))) + (0x11 * (((uint64_t)x15 * x54) + (((uint64_t)x17 * x55) + (((uint64_t)x19 * x53) + (((uint64_t)x21 * x51) + (((uint64_t)x23 * x49) + (((uint64_t)x25 * x47) + (((uint64_t)x27 * x45) + (((uint64_t)x29 * x43) + ((uint64_t)x28 * x41)))))))))));
{  uint64_t x66 = ((((uint64_t)x5 * x37) + (((uint64_t)x7 * x35) + (((uint64_t)x9 * x33) + ((uint64_t)x11 * x31)))) + (0x11 * (((uint64_t)x13 * x54) + (((uint64_t)x15 * x55) + (((uint64_t)x17 * x53) + (((uint64_t)x19 * x51) + (((uint64_t)x21 * x49) + (((uint64_t)x23 * x47) + (((uint64_t)x25 * x45) + (((uint64_t)x27 * x43) + (((uint64_t)x29 * x41) + ((uint64_t)x28 * x39))))))))))));
{  uint64_t x67 = ((((uint64_t)x5 * x35) + (((uint64_t)x7 * x33) + ((uint64_t)x9 * x31))) + (0x11 * (((uint64_t)x11 * x54) + (((uint64_t)x13 * x55) + (((uint64_t)x15 * x53) + (((uint64_t)x17 * x51) + (((uint64_t)x19 * x49) + (((uint64_t)x21 * x47) + (((uint64_t)x23 * x45) + (((uint64_t)x25 * x43) + (((uint64_t)x27 * x41) + (((uint64_t)x29 * x39) + ((uint64_t)x28 * x37)))))))))))));
{  uint64_t x68 = ((((uint64_t)x5 * x33) + ((uint64_t)x7 * x31)) + (0x11 * (((uint64_t)x9 * x54) + (((uint64_t)x11 * x55) + (((uint64_t)x13 * x53) + (((uint64_t)x15 * x51) + (((uint64_t)x17 * x49) + (((uint64_t)x19 * x47) + (((uint64_t)x21 * x45) + (((uint64_t)x23 * x43) + (((uint64_t)x25 * x41) + (((uint64_t)x27 * x39) + (((uint64_t)x29 * x37) + ((uint64_t)x28 * x35))))))))))))));
{  uint64_t x69 = (((uint64_t)x5 * x31) + (0x11 * (((uint64_t)x7 * x54) + (((uint64_t)x9 * x55) + (((uint64_t)x11 * x53) + (((uint64_t)x13 * x51) + (((uint64_t)x15 * x49) + (((uint64_t)x17 * x47) + (((uint64_t)x19 * x45) + (((uint64_t)x21 * x43) + (((uint64_t)x23 * x41) + (((uint64_t)x25 * x39) + (((uint64_t)x27 * x37) + (((uint64_t)x29 * x35) + ((uint64_t)x28 * x33)))))))))))))));
{  uint64_t x70 = (x69 >> 0x18);
{  uint32_t x71 = ((uint32_t)x69 & 0xffffff);
{  uint64_t x72 = (x70 + x68);
{  uint64_t x73 = (x72 >> 0x18);
{  uint32_t x74 = ((uint32_t)x72 & 0xffffff);
{  uint64_t x75 = (x73 + x67);
{  uint64_t x76 = (x75 >> 0x18);
{  uint32_t x77 = ((uint32_t)x75 & 0xffffff);
{  uint64_t x78 = (x76 + x66);
{  uint64_t x79 = (x78 >> 0x18);
{  uint32_t x80 = ((uint32_t)x78 & 0xffffff);
{  uint64_t x81 = (x79 + x65);
{  uint64_t x82 = (x81 >> 0x18);
{  uint32_t x83 = ((uint32_t)x81 & 0xffffff);
{  uint64_t x84 = (x82 + x64);
{  uint64_t x85 = (x84 >> 0x18);
{  uint32_t x86 = ((uint32_t)x84 & 0xffffff);
{  uint64_t x87 = (x85 + x63);
{  uint64_t x88 = (x87 >> 0x18);
{  uint32_t x89 = ((uint32_t)x87 & 0xffffff);
{  uint64_t x90 = (x88 + x62);
{  uint64_t x91 = (x90 >> 0x18);
{  uint32_t x92 = ((uint32_t)x90 & 0xffffff);
{  uint64_t x93 = (x91 + x61);
{  uint64_t x94 = (x93 >> 0x18);
{  uint32_t x95 = ((uint32_t)x93 & 0xffffff);
{  uint64_t x96 = (x94 + x60);
{  uint64_t x97 = (x96 >> 0x18);
{  uint32_t x98 = ((uint32_t)x96 & 0xffffff);
{  uint64_t x99 = (x97 + x59);
{  uint64_t x100 = (x99 >> 0x18);
{  uint32_t x101 = ((uint32_t)x99 & 0xffffff);
{  uint64_t x102 = (x100 + x58);
{  uint64_t x103 = (x102 >> 0x18);
{  uint32_t x104 = ((uint32_t)x102 & 0xffffff);
{  uint64_t x105 = (x103 + x57);
{  uint64_t x106 = (x105 >> 0x18);
{  uint32_t x107 = ((uint32_t)x105 & 0xffffff);
{  uint64_t x108 = (x106 + x56);
{  uint32_t x109 = (uint32_t) (x108 >> 0x18);
{  uint32_t x110 = ((uint32_t)x108 & 0xffffff);
{  uint64_t x111 = (x71 + ((uint64_t)0x11 * x109));
{  uint32_t x112 = (uint32_t) (x111 >> 0x18);
{  uint32_t x113 = ((uint32_t)x111 & 0xffffff);
{  uint32_t x114 = (x112 + x74);
{  uint32_t x115 = (x114 >> 0x18);
{  uint32_t x116 = (x114 & 0xffffff);
out[0] = x110;
out[1] = x107;
out[2] = x104;
out[3] = x101;
out[4] = x98;
out[5] = x95;
out[6] = x92;
out[7] = x89;
out[8] = x86;
out[9] = x83;
out[10] = x80;
out[11] = x115 + x77;
out[12] = x116;
out[13] = x113;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[14];
