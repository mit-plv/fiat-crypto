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

void force_inline feadd(uint64_t* out, uint64_t x8, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x14, uint64_t x15, uint64_t x13, uint64_t x11)
{  uint32_t x17; uint8_t x18 = _addcarryx_u32(0x0, x5, x11, &x17);
{  uint32_t x20; uint8_t x21 = _addcarryx_u32(x18, x7, x13, &x20);
{  uint32_t x23; uint8_t x24 = _addcarryx_u32(x21, x9, x15, &x23);
{  uint32_t x26; uint8_t x27 = _addcarryx_u32(x24, x8, x14, &x26);
{  uint32_t x29; uint8_t x30 = _subborrow_u32(0x0, x17, 0xffffffff, &x29);
{  uint32_t x32; uint8_t x33 = _subborrow_u32(x30, x20, 0xffffffff, &x32);
{  uint32_t x35; uint8_t x36 = _subborrow_u32(x33, x23, 0xffffffff, &x35);
{  uint32_t x38; uint8_t x39 = _subborrow_u32(x36, x26, 0x7fffffff, &x38);
{  uint32_t _; uint8_t x42 = _subborrow_u32(x39, x27, 0x0, &_);
{  uint32_t x43 = cmovznz(x42, x38, x26);
{  uint32_t x44 = cmovznz(x42, x35, x23);
{  uint32_t x45 = cmovznz(x42, x32, x20);
{  uint32_t x46 = cmovznz(x42, x29, x17);
out[0] = x43;
out[1] = x44;
out[2] = x45;
out[3] = x46;
}}}}}}}}}}}}}
// caller: uint64_t out[4];
