#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "freeze.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline freeze(uint32_t* out, uint32_t x17, uint32_t x18, uint32_t x16, uint32_t x14, uint32_t x12, uint32_t x10, uint32_t x8, uint32_t x6, uint32_t x4, uint32_t x2)
{  uint32_t x20; uint8_t/*bool*/ x21 = _subborrow_u26(0x0, x2, 0x3ffffed, &x20);
{  uint32_t x23; uint8_t/*bool*/ x24 = _subborrow_u25(x21, x4, 0x1ffffff, &x23);
{  uint32_t x26; uint8_t/*bool*/ x27 = _subborrow_u26(x24, x6, 0x3ffffff, &x26);
{  uint32_t x29; uint8_t/*bool*/ x30 = _subborrow_u25(x27, x8, 0x1ffffff, &x29);
{  uint32_t x32; uint8_t/*bool*/ x33 = _subborrow_u26(x30, x10, 0x3ffffff, &x32);
{  uint32_t x35; uint8_t/*bool*/ x36 = _subborrow_u25(x33, x12, 0x1ffffff, &x35);
{  uint32_t x38; uint8_t/*bool*/ x39 = _subborrow_u26(x36, x14, 0x3ffffff, &x38);
{  uint32_t x41; uint8_t/*bool*/ x42 = _subborrow_u25(x39, x16, 0x1ffffff, &x41);
{  uint32_t x44; uint8_t/*bool*/ x45 = _subborrow_u26(x42, x18, 0x3ffffff, &x44);
{  uint32_t x47; uint8_t/*bool*/ x48 = _subborrow_u25(x45, x17, 0x1ffffff, &x47);
{  uint32_t x49 = cmovznz32(x48, 0x0, 0xffffffff);
{  uint32_t x50 = (x49 & 0x3ffffed);
{  uint32_t x52; uint8_t/*bool*/ x53 = _addcarryx_u26(0x0, x20, x50, &x52);
{  uint32_t x54 = (x49 & 0x1ffffff);
{  uint32_t x56; uint8_t/*bool*/ x57 = _addcarryx_u25(x53, x23, x54, &x56);
{  uint32_t x58 = (x49 & 0x3ffffff);
{  uint32_t x60; uint8_t/*bool*/ x61 = _addcarryx_u26(x57, x26, x58, &x60);
{  uint32_t x62 = (x49 & 0x1ffffff);
{  uint32_t x64; uint8_t/*bool*/ x65 = _addcarryx_u25(x61, x29, x62, &x64);
{  uint32_t x66 = (x49 & 0x3ffffff);
{  uint32_t x68; uint8_t/*bool*/ x69 = _addcarryx_u26(x65, x32, x66, &x68);
{  uint32_t x70 = (x49 & 0x1ffffff);
{  uint32_t x72; uint8_t/*bool*/ x73 = _addcarryx_u25(x69, x35, x70, &x72);
{  uint32_t x74 = (x49 & 0x3ffffff);
{  uint32_t x76; uint8_t/*bool*/ x77 = _addcarryx_u26(x73, x38, x74, &x76);
{  uint32_t x78 = (x49 & 0x1ffffff);
{  uint32_t x80; uint8_t/*bool*/ x81 = _addcarryx_u25(x77, x41, x78, &x80);
{  uint32_t x82 = (x49 & 0x3ffffff);
{  uint32_t x84; uint8_t/*bool*/ x85 = _addcarryx_u26(x81, x44, x82, &x84);
{  uint32_t x86 = (x49 & 0x1ffffff);
{  uint32_t x88; uint8_t/*bool*/ _ = _addcarryx_u25(x85, x47, x86, &x88);
out[0] = x88;
out[1] = x84;
out[2] = x80;
out[3] = x76;
out[4] = x72;
out[5] = x68;
out[6] = x64;
out[7] = x60;
out[8] = x56;
out[9] = x52;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint32_t out[10];
