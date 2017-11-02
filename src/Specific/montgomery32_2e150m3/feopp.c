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

void force_inline feopp(uint64_t* out, uint64_t x7, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint32_t x10; uint8_t x11 = _subborrow_u32(0x0, 0x0, x2, &x10);
{  uint32_t x13; uint8_t x14 = _subborrow_u32(x11, 0x0, x4, &x13);
{  uint32_t x16; uint8_t x17 = _subborrow_u32(x14, 0x0, x6, &x16);
{  uint32_t x19; uint8_t x20 = _subborrow_u32(x17, 0x0, x8, &x19);
{  uint32_t x22; uint8_t x23 = _subborrow_u32(x20, 0x0, x7, &x22);
{  uint32_t x24 = (uint32_t)cmovznz(x23, 0x0, 0xffffffff);
{  uint32_t x25 = (x24 & 0xfffffffd);
{  uint32_t x27; uint8_t x28 = _addcarryx_u32(0x0, x10, x25, &x27);
{  uint32_t x29 = (x24 & 0xffffffff);
{  uint32_t x31; uint8_t x32 = _addcarryx_u32(x28, x13, x29, &x31);
{  uint32_t x33 = (x24 & 0xffffffff);
{  uint32_t x35; uint8_t x36 = _addcarryx_u32(x32, x16, x33, &x35);
{  uint32_t x37 = (x24 & 0xffffffff);
{  uint32_t x39; uint8_t x40 = _addcarryx_u32(x36, x19, x37, &x39);
{  uint32_t x41 = (x24 & 0x3fffff);
{  uint32_t x43; uint8_t _ = _addcarryx_u32(x40, x22, x41, &x43);
out[0] = x43;
out[1] = x39;
out[2] = x35;
out[3] = x31;
out[4] = x27;
}}}}}}}}}}}}}}}}
// caller: uint64_t out[5];
