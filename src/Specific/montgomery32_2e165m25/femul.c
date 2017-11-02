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

void force_inline femul(uint64_t* out, uint64_t x12, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x22, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15)
{  uint32_t x26;  uint32_t x25 = _mulx_u32(x5, x15, &x26);
{  uint32_t x29;  uint32_t x28 = _mulx_u32(x5, x17, &x29);
{  uint32_t x32;  uint32_t x31 = _mulx_u32(x5, x19, &x32);
{  uint32_t x35;  uint32_t x34 = _mulx_u32(x5, x21, &x35);
{  uint32_t x38;  uint32_t x37 = _mulx_u32(x5, x23, &x38);
{  uint32_t x41;  uint32_t x40 = _mulx_u32(x5, x22, &x41);
{  uint32_t x43; uint8_t x44 = _addcarryx_u32(0x0, x26, x28, &x43);
{  uint32_t x46; uint8_t x47 = _addcarryx_u32(x44, x29, x31, &x46);
{  uint32_t x49; uint8_t x50 = _addcarryx_u32(x47, x32, x34, &x49);
{  uint32_t x52; uint8_t x53 = _addcarryx_u32(x50, x35, x37, &x52);
{  uint32_t x55; uint8_t x56 = _addcarryx_u32(x53, x38, x40, &x55);
{  uint32_t x58; uint8_t _ = _addcarryx_u32(0x0, x56, x41, &x58);
{  uint32_t _;  uint32_t x61 = _mulx_u32(x25, 0xc28f5c29, &_);
{  uint32_t x65;  uint32_t x64 = _mulx_u32(x61, 0xffffffe7, &x65);
{  uint32_t x68;  uint32_t x67 = _mulx_u32(x61, 0xffffffff, &x68);
{  uint32_t x71;  uint32_t x70 = _mulx_u32(x61, 0xffffffff, &x71);
{  uint32_t x74;  uint32_t x73 = _mulx_u32(x61, 0xffffffff, &x74);
{  uint32_t x77;  uint32_t x76 = _mulx_u32(x61, 0xffffffff, &x77);
out[0] = uint32_t x79;
out[1] = uint8_t x80 = Op Syntax.MulSplit 32 Syntax.TWord 5 Syntax.TWord 3 Syntax.TWord 5 Syntax.TWord 3  x61;
out[2] = 0x1f;;
}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[3];
