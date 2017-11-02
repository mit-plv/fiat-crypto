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

void force_inline feopp(uint64_t* out, uint64_t x9, uint64_t x10, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint32_t x12; uint8_t x13 = _subborrow_u32(0x0, 0x0, x2, &x12);
{  uint32_t x15; uint8_t x16 = _subborrow_u32(x13, 0x0, x4, &x15);
{  uint32_t x18; uint8_t x19 = _subborrow_u32(x16, 0x0, x6, &x18);
{  uint32_t x21; uint8_t x22 = _subborrow_u32(x19, 0x0, x8, &x21);
{  uint32_t x24; uint8_t x25 = _subborrow_u32(x22, 0x0, x10, &x24);
{  uint32_t x27; uint8_t x28 = _subborrow_u32(x25, 0x0, x9, &x27);
{  uint32_t x29 = (uint32_t)cmovznz(x28, 0x0, 0xffffffff);
{  uint32_t x30 = (x29 & 0xfffffffd);
{  uint32_t x32; uint8_t x33 = _addcarryx_u32(0x0, x12, x30, &x32);
{  uint32_t x34 = (x29 & 0xffffffff);
{  uint32_t x36; uint8_t x37 = _addcarryx_u32(x33, x15, x34, &x36);
{  uint32_t x38 = (x29 & 0xffffffff);
{  uint32_t x40; uint8_t x41 = _addcarryx_u32(x37, x18, x38, &x40);
{  uint32_t x42 = (x29 & 0xffffffff);
{  uint32_t x44; uint8_t x45 = _addcarryx_u32(x41, x21, x42, &x44);
{  uint32_t x46 = (x29 & 0xffffffff);
{  uint32_t x48; uint8_t x49 = _addcarryx_u32(x45, x24, x46, &x48);
{  uint32_t x50 = (x29 & 0x3fff);
{  uint32_t x52; uint8_t _ = _addcarryx_u32(x49, x27, x50, &x52);
out[0] = x52;
out[1] = x48;
out[2] = x44;
out[3] = x40;
out[4] = x36;
out[5] = x32;
}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[6];
