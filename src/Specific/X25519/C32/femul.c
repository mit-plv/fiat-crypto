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

void force_inline femul(uint32_t* out, uint32_t x20, uint32_t x21, uint32_t x19, uint32_t x17, uint32_t x15, uint32_t x13, uint32_t x11, uint32_t x9, uint32_t x7, uint32_t x5, uint32_t x38, uint32_t x39, uint32_t x37, uint32_t x35, uint32_t x33, uint32_t x31, uint32_t x29, uint32_t x27, uint32_t x25, uint32_t x23)
{  uint64_t x40 = ((uint64_t)x23 * x5);
{  uint64_t x41 = (((uint64_t)x23 * x7) + ((uint64_t)x25 * x5));
{  uint64_t x42 = ((((uint64_t)(0x2 * x25) * x7) + ((uint64_t)x23 * x9)) + ((uint64_t)x27 * x5));
{  uint64_t x43 = (((((uint64_t)x25 * x9) + ((uint64_t)x27 * x7)) + ((uint64_t)x23 * x11)) + ((uint64_t)x29 * x5));
{  uint64_t x44 = (((((uint64_t)x27 * x9) + (0x2 * (((uint64_t)x25 * x11) + ((uint64_t)x29 * x7)))) + ((uint64_t)x23 * x13)) + ((uint64_t)x31 * x5));
{  uint64_t x45 = (((((((uint64_t)x27 * x11) + ((uint64_t)x29 * x9)) + ((uint64_t)x25 * x13)) + ((uint64_t)x31 * x7)) + ((uint64_t)x23 * x15)) + ((uint64_t)x33 * x5));
{  uint64_t x46 = (((((0x2 * ((((uint64_t)x29 * x11) + ((uint64_t)x25 * x15)) + ((uint64_t)x33 * x7))) + ((uint64_t)x27 * x13)) + ((uint64_t)x31 * x9)) + ((uint64_t)x23 * x17)) + ((uint64_t)x35 * x5));
{  uint64_t x47 = (((((((((uint64_t)x29 * x13) + ((uint64_t)x31 * x11)) + ((uint64_t)x27 * x15)) + ((uint64_t)x33 * x9)) + ((uint64_t)x25 * x17)) + ((uint64_t)x35 * x7)) + ((uint64_t)x23 * x19)) + ((uint64_t)x37 * x5));
{  uint64_t x48 = (((((((uint64_t)x31 * x13) + (0x2 * (((((uint64_t)x29 * x15) + ((uint64_t)x33 * x11)) + ((uint64_t)x25 * x19)) + ((uint64_t)x37 * x7)))) + ((uint64_t)x27 * x17)) + ((uint64_t)x35 * x9)) + ((uint64_t)x23 * x21)) + ((uint64_t)x39 * x5));
{  uint64_t x49 = (((((((((((uint64_t)x31 * x15) + ((uint64_t)x33 * x13)) + ((uint64_t)x29 * x17)) + ((uint64_t)x35 * x11)) + ((uint64_t)x27 * x19)) + ((uint64_t)x37 * x9)) + ((uint64_t)x25 * x21)) + ((uint64_t)x39 * x7)) + ((uint64_t)x23 * x20)) + ((uint64_t)x38 * x5));
{  uint64_t x50 = (((((0x2 * ((((((uint64_t)x33 * x15) + ((uint64_t)x29 * x19)) + ((uint64_t)x37 * x11)) + ((uint64_t)x25 * x20)) + ((uint64_t)x38 * x7))) + ((uint64_t)x31 * x17)) + ((uint64_t)x35 * x13)) + ((uint64_t)x27 * x21)) + ((uint64_t)x39 * x9));
{  uint64_t x51 = (((((((((uint64_t)x33 * x17) + ((uint64_t)x35 * x15)) + ((uint64_t)x31 * x19)) + ((uint64_t)x37 * x13)) + ((uint64_t)x29 * x21)) + ((uint64_t)x39 * x11)) + ((uint64_t)x27 * x20)) + ((uint64_t)x38 * x9));
{  uint64_t x52 = (((((uint64_t)x35 * x17) + (0x2 * (((((uint64_t)x33 * x19) + ((uint64_t)x37 * x15)) + ((uint64_t)x29 * x20)) + ((uint64_t)x38 * x11)))) + ((uint64_t)x31 * x21)) + ((uint64_t)x39 * x13));
{  uint64_t x53 = (((((((uint64_t)x35 * x19) + ((uint64_t)x37 * x17)) + ((uint64_t)x33 * x21)) + ((uint64_t)x39 * x15)) + ((uint64_t)x31 * x20)) + ((uint64_t)x38 * x13));
{  uint64_t x54 = (((0x2 * ((((uint64_t)x37 * x19) + ((uint64_t)x33 * x20)) + ((uint64_t)x38 * x15))) + ((uint64_t)x35 * x21)) + ((uint64_t)x39 * x17));
{  uint64_t x55 = (((((uint64_t)x37 * x21) + ((uint64_t)x39 * x19)) + ((uint64_t)x35 * x20)) + ((uint64_t)x38 * x17));
{  uint64_t x56 = (((uint64_t)x39 * x21) + (0x2 * (((uint64_t)x37 * x20) + ((uint64_t)x38 * x19))));
{  uint64_t x57 = (((uint64_t)x39 * x20) + ((uint64_t)x38 * x21));
{  uint64_t x58 = ((uint64_t)(0x2 * x38) * x20);
{  uint64_t x59 = (x48 + (x58 << 0x4));
{  uint64_t x60 = (x59 + (x58 << 0x1));
{  uint64_t x61 = (x60 + x58);
{  uint64_t x62 = (x47 + (x57 << 0x4));
{  uint64_t x63 = (x62 + (x57 << 0x1));
{  uint64_t x64 = (x63 + x57);
{  uint64_t x65 = (x46 + (x56 << 0x4));
{  uint64_t x66 = (x65 + (x56 << 0x1));
{  uint64_t x67 = (x66 + x56);
{  uint64_t x68 = (x45 + (x55 << 0x4));
{  uint64_t x69 = (x68 + (x55 << 0x1));
{  uint64_t x70 = (x69 + x55);
{  uint64_t x71 = (x44 + (x54 << 0x4));
{  uint64_t x72 = (x71 + (x54 << 0x1));
{  uint64_t x73 = (x72 + x54);
{  uint64_t x74 = (x43 + (x53 << 0x4));
{  uint64_t x75 = (x74 + (x53 << 0x1));
{  uint64_t x76 = (x75 + x53);
{  uint64_t x77 = (x42 + (x52 << 0x4));
{  uint64_t x78 = (x77 + (x52 << 0x1));
{  uint64_t x79 = (x78 + x52);
{  uint64_t x80 = (x41 + (x51 << 0x4));
{  uint64_t x81 = (x80 + (x51 << 0x1));
{  uint64_t x82 = (x81 + x51);
{  uint64_t x83 = (x40 + (x50 << 0x4));
{  uint64_t x84 = (x83 + (x50 << 0x1));
{  uint64_t x85 = (x84 + x50);
{  uint64_t x86 = (x85 >> 0x1a);
{  uint32_t x87 = ((uint32_t)x85 & 0x3ffffff);
{  uint64_t x88 = (x86 + x82);
{  uint64_t x89 = (x88 >> 0x19);
{  uint32_t x90 = ((uint32_t)x88 & 0x1ffffff);
{  uint64_t x91 = (x89 + x79);
{  uint64_t x92 = (x91 >> 0x1a);
{  uint32_t x93 = ((uint32_t)x91 & 0x3ffffff);
{  uint64_t x94 = (x92 + x76);
{  uint64_t x95 = (x94 >> 0x19);
{  uint32_t x96 = ((uint32_t)x94 & 0x1ffffff);
{  uint64_t x97 = (x95 + x73);
{  uint64_t x98 = (x97 >> 0x1a);
{  uint32_t x99 = ((uint32_t)x97 & 0x3ffffff);
{  uint64_t x100 = (x98 + x70);
{  uint64_t x101 = (x100 >> 0x19);
{  uint32_t x102 = ((uint32_t)x100 & 0x1ffffff);
{  uint64_t x103 = (x101 + x67);
{  uint64_t x104 = (x103 >> 0x1a);
{  uint32_t x105 = ((uint32_t)x103 & 0x3ffffff);
{  uint64_t x106 = (x104 + x64);
{  uint64_t x107 = (x106 >> 0x19);
{  uint32_t x108 = ((uint32_t)x106 & 0x1ffffff);
{  uint64_t x109 = (x107 + x61);
{  uint64_t x110 = (x109 >> 0x1a);
{  uint32_t x111 = ((uint32_t)x109 & 0x3ffffff);
{  uint64_t x112 = (x110 + x49);
{  uint64_t x113 = (x112 >> 0x19);
{  uint32_t x114 = ((uint32_t)x112 & 0x1ffffff);
{  uint64_t x115 = (x87 + (0x13 * x113));
{  uint32_t x116 = (uint32_t) (x115 >> 0x1a);
{  uint32_t x117 = ((uint32_t)x115 & 0x3ffffff);
{  uint32_t x118 = (x116 + x90);
{  uint32_t x119 = (x118 >> 0x19);
{  uint32_t x120 = (x118 & 0x1ffffff);
out[0] = x114;
out[1] = x111;
out[2] = x108;
out[3] = x105;
out[4] = x102;
out[5] = x99;
out[6] = x96;
out[7] = x119 + x93;
out[8] = x120;
out[9] = x117;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint32_t out[10];
