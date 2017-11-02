#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "femul.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline femul(uint64_t* out, uint64_t x6, uint64_t x7, uint64_t x5, uint64_t x10, uint64_t x11, uint64_t x9)
{  uint64_t x14;  uint64_t x13 = _mulx_u64(x5, x9, &x14);
{  uint64_t x17;  uint64_t x16 = _mulx_u64(x5, x11, &x17);
{  uint64_t x20;  uint64_t x19 = _mulx_u64(x5, x10, &x20);
{  uint64_t x22; uint8_t x23 = _addcarryx_u64(0x0, x14, x16, &x22);
{  uint64_t x25; uint8_t x26 = _addcarryx_u64(x23, x17, x19, &x25);
{  uint64_t x28; uint8_t _ = _addcarryx_u64(0x0, x26, x20, &x28);
{  uint64_t _;  uint64_t x31 = _mulx_u64(x13, 0xcccccccccccccccdL, &_);
{  uint64_t x35;  uint64_t x34 = _mulx_u64(x31, 0xfffffffffffffffbL, &x35);
{  uint64_t x38;  uint64_t x37 = _mulx_u64(x31, 0xffffffffffffffffL, &x38);
out[0] = uint64_t x40;
out[1] = uint8_t x41 = Op Syntax.MulSplit 64 Syntax.TWord 6 Syntax.TWord 3 Syntax.TWord 6 Syntax.TWord 3  x31;
out[2] = 0x3;;
}}}}}}}}}
// caller: uint64_t out[3];
