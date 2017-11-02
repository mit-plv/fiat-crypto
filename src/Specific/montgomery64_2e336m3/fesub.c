#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "fesub.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline fesub(uint64_t* out, uint64_t x12, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x22, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15)
{  uint64_t x25; uint8_t x26 = _subborrow_u64(0x0, x5, x15, &x25);
{  uint64_t x28; uint8_t x29 = _subborrow_u64(x26, x7, x17, &x28);
{  uint64_t x31; uint8_t x32 = _subborrow_u64(x29, x9, x19, &x31);
{  uint64_t x34; uint8_t x35 = _subborrow_u64(x32, x11, x21, &x34);
{  uint64_t x37; uint8_t x38 = _subborrow_u64(x35, x13, x23, &x37);
{  uint64_t x40; uint8_t x41 = _subborrow_u64(x38, x12, x22, &x40);
{  uint64_t x42 = (uint64_t)cmovznz(x41, 0x0, 0xffffffffffffffffL);
{  uint64_t x43 = (x42 & 0xfffffffffffffffdL);
{  uint64_t x45; uint8_t x46 = _addcarryx_u64(0x0, x25, x43, &x45);
{  uint64_t x47 = (x42 & 0xffffffffffffffffL);
{  uint64_t x49; uint8_t x50 = _addcarryx_u64(x46, x28, x47, &x49);
{  uint64_t x51 = (x42 & 0xffffffffffffffffL);
{  uint64_t x53; uint8_t x54 = _addcarryx_u64(x50, x31, x51, &x53);
{  uint64_t x55 = (x42 & 0xffffffffffffffffL);
{  uint64_t x57; uint8_t x58 = _addcarryx_u64(x54, x34, x55, &x57);
{  uint64_t x59 = (x42 & 0xffffffffffffffffL);
{  uint64_t x61; uint8_t x62 = _addcarryx_u64(x58, x37, x59, &x61);
{  uint64_t x63 = (x42 & 0xffff);
{  uint64_t x65; uint8_t _ = _addcarryx_u64(x62, x40, x63, &x65);
out[0] = x65;
out[1] = x61;
out[2] = x57;
out[3] = x53;
out[4] = x49;
out[5] = x45;
}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[6];
