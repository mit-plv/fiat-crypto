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
{  uint64_t x33 = (x28 & 0xffffffffffffffffL);
{  uint64_t x35; uint8_t x36 = _addcarryx_u64(x32, x20, x33, &x35);
{  uint64_t x37 = (x28 & 0xffffffffffffffffL);
{  uint64_t x39; uint8_t x40 = _addcarryx_u64(x36, x23, x37, &x39);
{  uint64_t x41 = (x28 & 0x14bf);
{  uint64_t x43; uint8_t _ = _addcarryx_u64(x40, x26, x41, &x43);
out[0] = x43;
out[1] = x39;
out[2] = x35;
out[3] = x31;
}}}}}}}}}}}}}
// caller: uint64_t out[4];
