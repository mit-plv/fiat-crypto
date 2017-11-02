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

void force_inline femul(uint64_t* out, uint64_t x10, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x18, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13)
{  uint32_t x22;  uint32_t x21 = _mulx_u32(x5, x13, &x22);
{  uint32_t x25;  uint32_t x24 = _mulx_u32(x5, x15, &x25);
{  uint32_t x28;  uint32_t x27 = _mulx_u32(x5, x17, &x28);
{  uint32_t x31;  uint32_t x30 = _mulx_u32(x5, x19, &x31);
{  uint32_t x34;  uint32_t x33 = _mulx_u32(x5, x18, &x34);
{  uint32_t x36; uint8_t x37 = _addcarryx_u32(0x0, x22, x24, &x36);
{  uint32_t x39; uint8_t x40 = _addcarryx_u32(x37, x25, x27, &x39);
{  uint32_t x42; uint8_t x43 = _addcarryx_u32(x40, x28, x30, &x42);
{  uint32_t x45; uint8_t x46 = _addcarryx_u32(x43, x31, x33, &x45);
{  uint32_t x48; uint8_t _ = _addcarryx_u32(0x0, x46, x34, &x48);
{  uint32_t _;  uint32_t x51 = _mulx_u32(x21, 0xcccccccd, &_);
{  uint32_t x55;  uint32_t x54 = _mulx_u32(x51, 0xfffffffb, &x55);
{  uint32_t x58;  uint32_t x57 = _mulx_u32(x51, 0xffffffff, &x58);
{  uint32_t x61;  uint32_t x60 = _mulx_u32(x51, 0xffffffff, &x61);
{  uint32_t x64;  uint32_t x63 = _mulx_u32(x51, 0xffffffff, &x64);
out[0] = uint32_t x66;
out[1] = uint8_t x67 = Op Syntax.MulSplit 32 Syntax.TWord 5 Syntax.TWord 3 Syntax.TWord 5 Syntax.TWord 3  x51;
out[2] = 0x3;;
}}}}}}}}}}}}}}}
// caller: uint64_t out[3];
