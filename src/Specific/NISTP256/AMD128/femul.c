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

void force_inline femul(uint64_t* out, uint64_t x4, uint64_t x5, uint64_t x6, uint64_t x7)
{  uint128_t x10;  uint128_t x9 = _mulx_u128(x5, x7, &x10);
{  uint128_t x13;  uint128_t x12 = _mulx_u128(x5, x6, &x13);
{  uint128_t x15; uint8_t/*bool*/ x16 = _addcarryx_u128(0x0, x10, x12, &x15);
{  uint128_t x18; uint8_t/*bool*/ _ = _addcarryx_u128(0x0, x16, x13, &x18);
{  uint128_t _;  uint128_t x21 = _mulx_u128(x9, 0x1000000000000000000000001L, &_);
{  uint128_t x25;  uint128_t x24 = _mulx_u128(x21, 0xffffffffffffffffffffffffL, &x25);
{  uint128_t x28;  uint128_t x27 = _mulx_u128(x21, 0xffffffff000000010000000000000000L, &x28);
{  uint128_t x30; uint8_t/*bool*/ x31 = _addcarryx_u128(0x0, x25, x27, &x30);
{  uint128_t x33; uint8_t/*bool*/ _ = _addcarryx_u128(0x0, x31, x28, &x33);
{  uint128_t _; uint8_t/*bool*/ x37 = _addcarryx_u128(0x0, x9, x24, &_);
{  uint128_t x39; uint8_t/*bool*/ x40 = _addcarryx_u128(x37, x15, x30, &x39);
{  uint128_t x42; uint8_t/*bool*/ x43 = _addcarryx_u128(x40, x18, x33, &x42);
{  uint128_t x46;  uint128_t x45 = _mulx_u128(x4, x7, &x46);
{  uint128_t x49;  uint128_t x48 = _mulx_u128(x4, x6, &x49);
{  uint128_t x51; uint8_t/*bool*/ x52 = _addcarryx_u128(0x0, x46, x48, &x51);
{  uint128_t x54; uint8_t/*bool*/ _ = _addcarryx_u128(0x0, x52, x49, &x54);
{  uint128_t x57; uint8_t/*bool*/ x58 = _addcarryx_u128(0x0, x39, x45, &x57);
{  uint128_t x60; uint8_t/*bool*/ x61 = _addcarryx_u128(x58, x42, x51, &x60);
{  uint128_t x63; uint8_t/*bool*/ x64 = _addcarryx_u128(x61, x43, x54, &x63);
{  uint128_t _;  uint128_t x66 = _mulx_u128(x57, 0x1000000000000000000000001L, &_);
{  uint128_t x70;  uint128_t x69 = _mulx_u128(x66, 0xffffffffffffffffffffffffL, &x70);
{  uint128_t x73;  uint128_t x72 = _mulx_u128(x66, 0xffffffff000000010000000000000000L, &x73);
{  uint128_t x75; uint8_t/*bool*/ x76 = _addcarryx_u128(0x0, x70, x72, &x75);
{  uint128_t x78; uint8_t/*bool*/ _ = _addcarryx_u128(0x0, x76, x73, &x78);
{  uint128_t _; uint8_t/*bool*/ x82 = _addcarryx_u128(0x0, x57, x69, &_);
{  uint128_t x84; uint8_t/*bool*/ x85 = _addcarryx_u128(x82, x60, x75, &x84);
{  uint128_t x87; uint8_t/*bool*/ x88 = _addcarryx_u128(x85, x63, x78, &x87);
{  uint8_t x89 = ((uint8_t)x88 + x64);
{  uint128_t x91; uint8_t/*bool*/ x92 = _subborrow_u128(0x0, x84, 0xffffffffffffffffffffffffL, &x91);
{  uint128_t x94; uint8_t/*bool*/ x95 = _subborrow_u128(x92, x87, 0xffffffff000000010000000000000000L, &x94);
{  uint128_t _; uint8_t/*bool*/ x98 = _subborrow_u128(x95, x89, 0x0, &_);
{  uint128_t x99 = cmovznz128(x98, x94, x87);
{  uint128_t x100 = cmovznz128(x98, x91, x84);
out[0] = x99;
out[1] = x100;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[2];
