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

void force_inline femul(uint64_t* out, uint64_t x8, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x14, uint64_t x15, uint64_t x13, uint64_t x11)
{  uint64_t x18;  uint64_t x17 = _mulx_u64(x5, x11, &x18);
{  uint64_t x21;  uint64_t x20 = _mulx_u64(x5, x13, &x21);
{  uint64_t x24;  uint64_t x23 = _mulx_u64(x5, x15, &x24);
{  uint64_t x27;  uint64_t x26 = _mulx_u64(x5, x14, &x27);
{  uint64_t x29; uint8_t x30 = _addcarryx_u64(0x0, x18, x20, &x29);
{  uint64_t x32; uint8_t x33 = _addcarryx_u64(x30, x21, x23, &x32);
{  uint64_t x35; uint8_t x36 = _addcarryx_u64(x33, x24, x26, &x35);
{  uint64_t x38; uint8_t _ = _addcarryx_u64(0x0, x36, x27, &x38);
{  uint64_t _;  uint64_t x41 = _mulx_u64(x17, 0xf83e0f83e0f83e1, &_);
{  uint64_t x45;  uint64_t x44 = _mulx_u64(x41, 0xffffffffffffffdfL, &x45);
{  uint64_t x48;  uint64_t x47 = _mulx_u64(x41, 0xffffffffffffffffL, &x48);
{  uint64_t x51;  uint64_t x50 = _mulx_u64(x41, 0xffffffffffffffffL, &x51);
out[0] = uint64_t x53;
out[1] = uint8_t x54 = Op Syntax.MulSplit 64 Syntax.TWord 6 Syntax.TWord 3 Syntax.TWord 6 Syntax.TWord 3  x41;
out[2] = 0x3;;
}}}}}}}}}}}}
// caller: uint64_t out[3];
