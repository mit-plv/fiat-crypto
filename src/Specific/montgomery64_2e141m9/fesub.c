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

void force_inline fesub(uint64_t* out, uint64_t x6, uint64_t x7, uint64_t x5, uint64_t x10, uint64_t x11, uint64_t x9)
{  uint64_t x13; uint8_t x14 = _subborrow_u64(0x0, x5, x9, &x13);
{  uint64_t x16; uint8_t x17 = _subborrow_u64(x14, x7, x11, &x16);
{  uint64_t x19; uint8_t x20 = _subborrow_u64(x17, x6, x10, &x19);
{  uint64_t x21 = (uint64_t)cmovznz(x20, 0x0, 0xffffffffffffffffL);
{  uint64_t x22 = (x21 & 0xfffffffffffffff7L);
{  uint64_t x24; uint8_t x25 = _addcarryx_u64(0x0, x13, x22, &x24);
{  uint64_t x26 = (x21 & 0xffffffffffffffffL);
{  uint64_t x28; uint8_t x29 = _addcarryx_u64(x25, x16, x26, &x28);
{  uint64_t x30 = (x21 & 0x1fff);
{  uint64_t x32; uint8_t _ = _addcarryx_u64(x29, x19, x30, &x32);
out[0] = x32;
out[1] = x28;
out[2] = x24;
}}}}}}}}}}
// caller: uint64_t out[3];
