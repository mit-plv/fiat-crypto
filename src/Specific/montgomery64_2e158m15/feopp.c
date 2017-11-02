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

void force_inline feopp(uint64_t* out, uint64_t x3, uint64_t x4, uint64_t x2)
{  uint64_t x6; uint8_t x7 = _subborrow_u64(0x0, 0x0, x2, &x6);
{  uint64_t x9; uint8_t x10 = _subborrow_u64(x7, 0x0, x4, &x9);
{  uint64_t x12; uint8_t x13 = _subborrow_u64(x10, 0x0, x3, &x12);
{  uint64_t x14 = (uint64_t)cmovznz(x13, 0x0, 0xffffffffffffffffL);
{  uint64_t x15 = (x14 & 0xfffffffffffffff1L);
{  uint64_t x17; uint8_t x18 = _addcarryx_u64(0x0, x6, x15, &x17);
{  uint64_t x19 = (x14 & 0xffffffffffffffffL);
{  uint64_t x21; uint8_t x22 = _addcarryx_u64(x18, x9, x19, &x21);
{  uint64_t x23 = (x14 & 0x3fffffff);
{  uint64_t x25; uint8_t _ = _addcarryx_u64(x22, x12, x23, &x25);
out[0] = x25;
out[1] = x21;
out[2] = x17;
}}}}}}}}}}
// caller: uint64_t out[3];
