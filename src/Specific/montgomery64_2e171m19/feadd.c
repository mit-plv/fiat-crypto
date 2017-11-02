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

void force_inline feadd(uint64_t* out, uint64_t x6, uint64_t x7, uint64_t x5, uint64_t x10, uint64_t x11, uint64_t x9)
{  uint64_t x13; uint8_t x14 = _addcarryx_u64(0x0, x5, x9, &x13);
{  uint64_t x16; uint8_t x17 = _addcarryx_u64(x14, x7, x11, &x16);
{  uint64_t x19; uint8_t x20 = _addcarryx_u64(x17, x6, x10, &x19);
{  uint64_t x22; uint8_t x23 = _subborrow_u64(0x0, x13, 0xffffffffffffffedL, &x22);
{  uint64_t x25; uint8_t x26 = _subborrow_u64(x23, x16, 0xffffffffffffffffL, &x25);
{  uint64_t x28; uint8_t x29 = _subborrow_u64(x26, x19, 0x7ffffffffff, &x28);
{  uint64_t _; uint8_t x32 = _subborrow_u64(x29, x20, 0x0, &_);
{  uint64_t x33 = cmovznz(x32, x28, x19);
{  uint64_t x34 = cmovznz(x32, x25, x16);
{  uint64_t x35 = cmovznz(x32, x22, x13);
out[0] = x33;
out[1] = x34;
out[2] = x35;
}}}}}}}}}}
// caller: uint64_t out[3];
