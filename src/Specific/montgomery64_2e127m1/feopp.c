#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "feopp.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline feopp(uint64_t* out, uint64_t x1, uint64_t x2)
{  uint64_t x4; uint8_t x5 = _subborrow_u64(0x0, 0x0, x2, &x4);
{  uint64_t x7; uint8_t x8 = _subborrow_u64(x5, 0x0, x1, &x7);
{  uint64_t x9 = (uint64_t)cmovznz(x8, 0x0, 0xffffffffffffffffL);
{  uint64_t x10 = (x9 & 0xffffffffffffffffL);
{  uint64_t x12; uint8_t x13 = _addcarryx_u64(0x0, x4, x10, &x12);
{  uint64_t x14 = (x9 & 0x7fffffffffffffffL);
{  uint64_t x16; uint8_t _ = _addcarryx_u64(x13, x7, x14, &x16);
out[0] = x16;
out[1] = x12;
}}}}}}}
// caller: uint64_t out[2];
