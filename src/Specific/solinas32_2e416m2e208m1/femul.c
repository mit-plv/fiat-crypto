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

void force_inline femul(uint64_t* out, uint64_t x32, uint64_t x33, uint64_t x31, uint64_t x29, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x62, uint64_t x63, uint64_t x61, uint64_t x59, uint64_t x57, uint64_t x55, uint64_t x53, uint64_t x51, uint64_t x49, uint64_t x47, uint64_t x45, uint64_t x43, uint64_t x41, uint64_t x39, uint64_t x37, uint64_t x35)
{  uint64_t x64 = (((uint64_t)(x19 + x32) * (x49 + x62)) - ((uint64_t)x19 * x49));
{  uint64_t x65 = ((((uint64_t)(x17 + x33) * (x49 + x62)) + ((uint64_t)(x19 + x32) * (x47 + x63))) - (((uint64_t)x17 * x49) + ((uint64_t)x19 * x47)));
{  uint64_t x66 = ((((uint64_t)(x15 + x31) * (x49 + x62)) + (((uint64_t)(x17 + x33) * (x47 + x63)) + ((uint64_t)(x19 + x32) * (x45 + x61)))) - (((uint64_t)x15 * x49) + (((uint64_t)x17 * x47) + ((uint64_t)x19 * x45))));
{  uint64_t x67 = ((((uint64_t)(x13 + x29) * (x49 + x62)) + (((uint64_t)(x15 + x31) * (x47 + x63)) + (((uint64_t)(x17 + x33) * (x45 + x61)) + ((uint64_t)(x19 + x32) * (x43 + x59))))) - (((uint64_t)x13 * x49) + (((uint64_t)x15 * x47) + (((uint64_t)x17 * x45) + ((uint64_t)x19 * x43)))));
{  uint64_t x68 = ((((uint64_t)(x11 + x27) * (x49 + x62)) + (((uint64_t)(x13 + x29) * (x47 + x63)) + (((uint64_t)(x15 + x31) * (x45 + x61)) + (((uint64_t)(x17 + x33) * (x43 + x59)) + ((uint64_t)(x19 + x32) * (x41 + x57)))))) - (((uint64_t)x11 * x49) + (((uint64_t)x13 * x47) + (((uint64_t)x15 * x45) + (((uint64_t)x17 * x43) + ((uint64_t)x19 * x41))))));
{  uint64_t x69 = ((((uint64_t)(x9 + x25) * (x49 + x62)) + (((uint64_t)(x11 + x27) * (x47 + x63)) + (((uint64_t)(x13 + x29) * (x45 + x61)) + (((uint64_t)(x15 + x31) * (x43 + x59)) + (((uint64_t)(x17 + x33) * (x41 + x57)) + ((uint64_t)(x19 + x32) * (x39 + x55))))))) - (((uint64_t)x9 * x49) + (((uint64_t)x11 * x47) + (((uint64_t)x13 * x45) + (((uint64_t)x15 * x43) + (((uint64_t)x17 * x41) + ((uint64_t)x19 * x39)))))));
{  uint64_t x70 = ((((uint64_t)(x7 + x23) * (x49 + x62)) + (((uint64_t)(x9 + x25) * (x47 + x63)) + (((uint64_t)(x11 + x27) * (x45 + x61)) + (((uint64_t)(x13 + x29) * (x43 + x59)) + (((uint64_t)(x15 + x31) * (x41 + x57)) + (((uint64_t)(x17 + x33) * (x39 + x55)) + ((uint64_t)(x19 + x32) * (x37 + x53)))))))) - (((uint64_t)x7 * x49) + (((uint64_t)x9 * x47) + (((uint64_t)x11 * x45) + (((uint64_t)x13 * x43) + (((uint64_t)x15 * x41) + (((uint64_t)x17 * x39) + ((uint64_t)x19 * x37))))))));
{  uint64_t x71 = ((((uint64_t)(x5 + x21) * (x49 + x62)) + (((uint64_t)(x7 + x23) * (x47 + x63)) + (((uint64_t)(x9 + x25) * (x45 + x61)) + (((uint64_t)(x11 + x27) * (x43 + x59)) + (((uint64_t)(x13 + x29) * (x41 + x57)) + (((uint64_t)(x15 + x31) * (x39 + x55)) + (((uint64_t)(x17 + x33) * (x37 + x53)) + ((uint64_t)(x19 + x32) * (x35 + x51))))))))) - (((uint64_t)x5 * x49) + (((uint64_t)x7 * x47) + (((uint64_t)x9 * x45) + (((uint64_t)x11 * x43) + (((uint64_t)x13 * x41) + (((uint64_t)x15 * x39) + (((uint64_t)x17 * x37) + ((uint64_t)x19 * x35)))))))));
{  uint64_t x72 = ((((uint64_t)(x5 + x21) * (x47 + x63)) + (((uint64_t)(x7 + x23) * (x45 + x61)) + (((uint64_t)(x9 + x25) * (x43 + x59)) + (((uint64_t)(x11 + x27) * (x41 + x57)) + (((uint64_t)(x13 + x29) * (x39 + x55)) + (((uint64_t)(x15 + x31) * (x37 + x53)) + ((uint64_t)(x17 + x33) * (x35 + x51)))))))) - (((uint64_t)x5 * x47) + (((uint64_t)x7 * x45) + (((uint64_t)x9 * x43) + (((uint64_t)x11 * x41) + (((uint64_t)x13 * x39) + (((uint64_t)x15 * x37) + ((uint64_t)x17 * x35))))))));
{  uint64_t x73 = ((((uint64_t)(x5 + x21) * (x45 + x61)) + (((uint64_t)(x7 + x23) * (x43 + x59)) + (((uint64_t)(x9 + x25) * (x41 + x57)) + (((uint64_t)(x11 + x27) * (x39 + x55)) + (((uint64_t)(x13 + x29) * (x37 + x53)) + ((uint64_t)(x15 + x31) * (x35 + x51))))))) - (((uint64_t)x5 * x45) + (((uint64_t)x7 * x43) + (((uint64_t)x9 * x41) + (((uint64_t)x11 * x39) + (((uint64_t)x13 * x37) + ((uint64_t)x15 * x35)))))));
{  uint64_t x74 = ((((uint64_t)(x5 + x21) * (x43 + x59)) + (((uint64_t)(x7 + x23) * (x41 + x57)) + (((uint64_t)(x9 + x25) * (x39 + x55)) + (((uint64_t)(x11 + x27) * (x37 + x53)) + ((uint64_t)(x13 + x29) * (x35 + x51)))))) - (((uint64_t)x5 * x43) + (((uint64_t)x7 * x41) + (((uint64_t)x9 * x39) + (((uint64_t)x11 * x37) + ((uint64_t)x13 * x35))))));
{  uint64_t x75 = ((((uint64_t)(x5 + x21) * (x41 + x57)) + (((uint64_t)(x7 + x23) * (x39 + x55)) + (((uint64_t)(x9 + x25) * (x37 + x53)) + ((uint64_t)(x11 + x27) * (x35 + x51))))) - (((uint64_t)x5 * x41) + (((uint64_t)x7 * x39) + (((uint64_t)x9 * x37) + ((uint64_t)x11 * x35)))));
{  uint64_t x76 = ((((uint64_t)(x5 + x21) * (x39 + x55)) + (((uint64_t)(x7 + x23) * (x37 + x53)) + ((uint64_t)(x9 + x25) * (x35 + x51)))) - (((uint64_t)x5 * x39) + (((uint64_t)x7 * x37) + ((uint64_t)x9 * x35))));
{  uint64_t x77 = ((((uint64_t)(x5 + x21) * (x37 + x53)) + ((uint64_t)(x7 + x23) * (x35 + x51))) - (((uint64_t)x5 * x37) + ((uint64_t)x7 * x35)));
{  uint64_t x78 = (((uint64_t)(x5 + x21) * (x35 + x51)) - ((uint64_t)x5 * x35));
{  uint64_t x79 = (((((uint64_t)x19 * x49) + ((uint64_t)x32 * x62)) + x72) + x64);
{  uint64_t x80 = ((((((uint64_t)x17 * x49) + ((uint64_t)x19 * x47)) + (((uint64_t)x33 * x62) + ((uint64_t)x32 * x63))) + x73) + x65);
{  uint64_t x81 = ((((((uint64_t)x15 * x49) + (((uint64_t)x17 * x47) + ((uint64_t)x19 * x45))) + (((uint64_t)x31 * x62) + (((uint64_t)x33 * x63) + ((uint64_t)x32 * x61)))) + x74) + x66);
{  uint64_t x82 = ((((((uint64_t)x13 * x49) + (((uint64_t)x15 * x47) + (((uint64_t)x17 * x45) + ((uint64_t)x19 * x43)))) + (((uint64_t)x29 * x62) + (((uint64_t)x31 * x63) + (((uint64_t)x33 * x61) + ((uint64_t)x32 * x59))))) + x75) + x67);
{  uint64_t x83 = ((((((uint64_t)x11 * x49) + (((uint64_t)x13 * x47) + (((uint64_t)x15 * x45) + (((uint64_t)x17 * x43) + ((uint64_t)x19 * x41))))) + (((uint64_t)x27 * x62) + (((uint64_t)x29 * x63) + (((uint64_t)x31 * x61) + (((uint64_t)x33 * x59) + ((uint64_t)x32 * x57)))))) + x76) + x68);
{  uint64_t x84 = ((((((uint64_t)x9 * x49) + (((uint64_t)x11 * x47) + (((uint64_t)x13 * x45) + (((uint64_t)x15 * x43) + (((uint64_t)x17 * x41) + ((uint64_t)x19 * x39)))))) + (((uint64_t)x25 * x62) + (((uint64_t)x27 * x63) + (((uint64_t)x29 * x61) + (((uint64_t)x31 * x59) + (((uint64_t)x33 * x57) + ((uint64_t)x32 * x55))))))) + x77) + x69);
{  uint64_t x85 = ((((((uint64_t)x7 * x49) + (((uint64_t)x9 * x47) + (((uint64_t)x11 * x45) + (((uint64_t)x13 * x43) + (((uint64_t)x15 * x41) + (((uint64_t)x17 * x39) + ((uint64_t)x19 * x37))))))) + (((uint64_t)x23 * x62) + (((uint64_t)x25 * x63) + (((uint64_t)x27 * x61) + (((uint64_t)x29 * x59) + (((uint64_t)x31 * x57) + (((uint64_t)x33 * x55) + ((uint64_t)x32 * x53)))))))) + x78) + x70);
{  uint64_t x86 = ((((uint64_t)x5 * x49) + (((uint64_t)x7 * x47) + (((uint64_t)x9 * x45) + (((uint64_t)x11 * x43) + (((uint64_t)x13 * x41) + (((uint64_t)x15 * x39) + (((uint64_t)x17 * x37) + ((uint64_t)x19 * x35)))))))) + (((uint64_t)x21 * x62) + (((uint64_t)x23 * x63) + (((uint64_t)x25 * x61) + (((uint64_t)x27 * x59) + (((uint64_t)x29 * x57) + (((uint64_t)x31 * x55) + (((uint64_t)x33 * x53) + ((uint64_t)x32 * x51)))))))));
{  uint64_t x87 = (((((uint64_t)x5 * x47) + (((uint64_t)x7 * x45) + (((uint64_t)x9 * x43) + (((uint64_t)x11 * x41) + (((uint64_t)x13 * x39) + (((uint64_t)x15 * x37) + ((uint64_t)x17 * x35))))))) + (((uint64_t)x21 * x63) + (((uint64_t)x23 * x61) + (((uint64_t)x25 * x59) + (((uint64_t)x27 * x57) + (((uint64_t)x29 * x55) + (((uint64_t)x31 * x53) + ((uint64_t)x33 * x51)))))))) + x64);
{  uint64_t x88 = (((((uint64_t)x5 * x45) + (((uint64_t)x7 * x43) + (((uint64_t)x9 * x41) + (((uint64_t)x11 * x39) + (((uint64_t)x13 * x37) + ((uint64_t)x15 * x35)))))) + (((uint64_t)x21 * x61) + (((uint64_t)x23 * x59) + (((uint64_t)x25 * x57) + (((uint64_t)x27 * x55) + (((uint64_t)x29 * x53) + ((uint64_t)x31 * x51))))))) + x65);
{  uint64_t x89 = (((((uint64_t)x5 * x43) + (((uint64_t)x7 * x41) + (((uint64_t)x9 * x39) + (((uint64_t)x11 * x37) + ((uint64_t)x13 * x35))))) + (((uint64_t)x21 * x59) + (((uint64_t)x23 * x57) + (((uint64_t)x25 * x55) + (((uint64_t)x27 * x53) + ((uint64_t)x29 * x51)))))) + x66);
{  uint64_t x90 = (((((uint64_t)x5 * x41) + (((uint64_t)x7 * x39) + (((uint64_t)x9 * x37) + ((uint64_t)x11 * x35)))) + (((uint64_t)x21 * x57) + (((uint64_t)x23 * x55) + (((uint64_t)x25 * x53) + ((uint64_t)x27 * x51))))) + x67);
{  uint64_t x91 = (((((uint64_t)x5 * x39) + (((uint64_t)x7 * x37) + ((uint64_t)x9 * x35))) + (((uint64_t)x21 * x55) + (((uint64_t)x23 * x53) + ((uint64_t)x25 * x51)))) + x68);
{  uint64_t x92 = (((((uint64_t)x5 * x37) + ((uint64_t)x7 * x35)) + (((uint64_t)x21 * x53) + ((uint64_t)x23 * x51))) + x69);
{  uint64_t x93 = ((((uint64_t)x5 * x35) + ((uint64_t)x21 * x51)) + x70);
{  uint64_t x94 = (x86 >> 0x1a);
{  uint32_t x95 = ((uint32_t)x86 & 0x3ffffff);
{  uint64_t x96 = (x71 >> 0x1a);
{  uint32_t x97 = ((uint32_t)x71 & 0x3ffffff);
{  uint64_t x98 = ((0x4000000 * x96) + x97);
{  uint64_t x99 = (x98 >> 0x1a);
{  uint32_t x100 = ((uint32_t)x98 & 0x3ffffff);
{  uint64_t x101 = ((x94 + x85) + x99);
{  uint64_t x102 = (x101 >> 0x1a);
{  uint32_t x103 = ((uint32_t)x101 & 0x3ffffff);
{  uint64_t x104 = (x93 + x99);
{  uint64_t x105 = (x104 >> 0x1a);
{  uint32_t x106 = ((uint32_t)x104 & 0x3ffffff);
{  uint64_t x107 = (x102 + x84);
{  uint64_t x108 = (x107 >> 0x1a);
{  uint32_t x109 = ((uint32_t)x107 & 0x3ffffff);
{  uint64_t x110 = (x105 + x92);
{  uint64_t x111 = (x110 >> 0x1a);
{  uint32_t x112 = ((uint32_t)x110 & 0x3ffffff);
{  uint64_t x113 = (x108 + x83);
{  uint64_t x114 = (x113 >> 0x1a);
{  uint32_t x115 = ((uint32_t)x113 & 0x3ffffff);
{  uint64_t x116 = (x111 + x91);
{  uint64_t x117 = (x116 >> 0x1a);
{  uint32_t x118 = ((uint32_t)x116 & 0x3ffffff);
{  uint64_t x119 = (x114 + x82);
{  uint64_t x120 = (x119 >> 0x1a);
{  uint32_t x121 = ((uint32_t)x119 & 0x3ffffff);
{  uint64_t x122 = (x117 + x90);
{  uint64_t x123 = (x122 >> 0x1a);
{  uint32_t x124 = ((uint32_t)x122 & 0x3ffffff);
{  uint64_t x125 = (x120 + x81);
{  uint64_t x126 = (x125 >> 0x1a);
{  uint32_t x127 = ((uint32_t)x125 & 0x3ffffff);
{  uint64_t x128 = (x123 + x89);
{  uint64_t x129 = (x128 >> 0x1a);
{  uint32_t x130 = ((uint32_t)x128 & 0x3ffffff);
{  uint64_t x131 = (x126 + x80);
{  uint64_t x132 = (x131 >> 0x1a);
{  uint32_t x133 = ((uint32_t)x131 & 0x3ffffff);
{  uint64_t x134 = (x129 + x88);
{  uint64_t x135 = (x134 >> 0x1a);
{  uint32_t x136 = ((uint32_t)x134 & 0x3ffffff);
{  uint64_t x137 = (x132 + x79);
{  uint64_t x138 = (x137 >> 0x1a);
{  uint32_t x139 = ((uint32_t)x137 & 0x3ffffff);
{  uint64_t x140 = (x135 + x87);
{  uint64_t x141 = (x140 >> 0x1a);
{  uint32_t x142 = ((uint32_t)x140 & 0x3ffffff);
{  uint64_t x143 = (x138 + x100);
{  uint32_t x144 = (uint32_t) (x143 >> 0x1a);
{  uint32_t x145 = ((uint32_t)x143 & 0x3ffffff);
{  uint64_t x146 = (x141 + x95);
{  uint32_t x147 = (uint32_t) (x146 >> 0x1a);
{  uint32_t x148 = ((uint32_t)x146 & 0x3ffffff);
{  uint64_t x149 = (((uint64_t)0x4000000 * x144) + x145);
{  uint32_t x150 = (uint32_t) (x149 >> 0x1a);
{  uint32_t x151 = ((uint32_t)x149 & 0x3ffffff);
{  uint32_t x152 = ((x147 + x103) + x150);
{  uint32_t x153 = (x152 >> 0x1a);
{  uint32_t x154 = (x152 & 0x3ffffff);
{  uint32_t x155 = (x106 + x150);
{  uint32_t x156 = (x155 >> 0x1a);
{  uint32_t x157 = (x155 & 0x3ffffff);
out[0] = x151;
out[1] = x139;
out[2] = x133;
out[3] = x127;
out[4] = x121;
out[5] = x115;
out[6] = x153 + x109;
out[7] = x154;
out[8] = x148;
out[9] = x142;
out[10] = x136;
out[11] = x130;
out[12] = x124;
out[13] = x118;
out[14] = x156 + x112;
out[15] = x157;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[16];
