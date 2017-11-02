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

void force_inline fesub(uint64_t* out, uint64_t x8, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x14, uint64_t x15, uint64_t x13, uint64_t x11)
{  uint64_t x17; uint8_t x18 = _subborrow_u64(0x0, x5, x11, &x17);
{  uint64_t x20; uint8_t x21 = _subborrow_u64(x18, x7, x13, &x20);
{  uint64_t x23; uint8_t x24 = _subborrow_u64(x21, x9, x15, &x23);
{  uint64_t x26; uint8_t x27 = _subborrow_u64(x24, x8, x14, &x26);
{  uint64_t x28 = (uint64_t)cmovznz(x27, 0x0, 0xffffffffffffffffL);
{  uint64_t x29 = (x28 & 0xffffffffffffffffL);
{  uint64_t x31; uint8_t x32 = _addcarryx_u64(0x0, x17, x29, &x31);
{  uint64_t x33 = (x28 & 0xffffffff);
{  uint64_t x35; uint8_t x36 = _addcarryx_u64(x32, x20, x33, &x35);
{  uint64_t x38; uint8_t x39 = _addcarryx_u64(x36, x23, 0x0, &x38);
{  uint64_t x40 = (x28 & 0xffffffff00000001L);
{  uint64_t x42; uint8_t _ = _addcarryx_u64(x39, x26, x40, &x42);
out[0] = x42;
out[1] = x38;
out[2] = x35;
out[3] = x31;
}}}}}}}}}}}}
// caller: uint64_t out[4];
