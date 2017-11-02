#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "feadd.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline feadd(uint64_t* out, uint64_t x18, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x34, uint64_t x35, uint64_t x33, uint64_t x31, uint64_t x29, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21)
{  uint64_t x37; uint8_t x38 = _addcarryx_u64(0x0, x5, x21, &x37);
{  uint64_t x40; uint8_t x41 = _addcarryx_u64(x38, x7, x23, &x40);
{  uint64_t x43; uint8_t x44 = _addcarryx_u64(x41, x9, x25, &x43);
{  uint64_t x46; uint8_t x47 = _addcarryx_u64(x44, x11, x27, &x46);
{  uint64_t x49; uint8_t x50 = _addcarryx_u64(x47, x13, x29, &x49);
{  uint64_t x52; uint8_t x53 = _addcarryx_u64(x50, x15, x31, &x52);
{  uint64_t x55; uint8_t x56 = _addcarryx_u64(x53, x17, x33, &x55);
{  uint64_t x58; uint8_t x59 = _addcarryx_u64(x56, x19, x35, &x58);
{  uint64_t x61; uint8_t x62 = _addcarryx_u64(x59, x18, x34, &x61);
{  uint64_t x64; uint8_t x65 = _subborrow_u64(0x0, x37, 0xffffffffffffffffL, &x64);
{  uint64_t x67; uint8_t x68 = _subborrow_u64(x65, x40, 0xffffffffffffffffL, &x67);
{  uint64_t x70; uint8_t x71 = _subborrow_u64(x68, x43, 0xffffffffffffffffL, &x70);
{  uint64_t x73; uint8_t x74 = _subborrow_u64(x71, x46, 0xffffffffffffffffL, &x73);
{  uint64_t x76; uint8_t x77 = _subborrow_u64(x74, x49, 0xffffffffffffffffL, &x76);
{  uint64_t x79; uint8_t x80 = _subborrow_u64(x77, x52, 0xffffffffffffffffL, &x79);
{  uint64_t x82; uint8_t x83 = _subborrow_u64(x80, x55, 0xffffffffffffffffL, &x82);
{  uint64_t x85; uint8_t x86 = _subborrow_u64(x83, x58, 0xffffffffffffffffL, &x85);
{  uint64_t x88; uint8_t x89 = _subborrow_u64(x86, x61, 0x1ff, &x88);
{  uint64_t _; uint8_t x92 = _subborrow_u64(x89, x62, 0x0, &_);
{  uint64_t x93 = cmovznz(x92, x88, x61);
{  uint64_t x94 = cmovznz(x92, x85, x58);
{  uint64_t x95 = cmovznz(x92, x82, x55);
{  uint64_t x96 = cmovznz(x92, x79, x52);
{  uint64_t x97 = cmovznz(x92, x76, x49);
{  uint64_t x98 = cmovznz(x92, x73, x46);
{  uint64_t x99 = cmovznz(x92, x70, x43);
{  uint64_t x100 = cmovznz(x92, x67, x40);
{  uint64_t x101 = cmovznz(x92, x64, x37);
out[0] = x93;
out[1] = x94;
out[2] = x95;
out[3] = x96;
out[4] = x97;
out[5] = x98;
out[6] = x99;
out[7] = x100;
out[8] = x101;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[9];
