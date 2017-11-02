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
{  uint64_t x10;  uint64_t x9 = _mulx_u64(x5, x7, &x10);
{  uint64_t x13;  uint64_t x12 = _mulx_u64(x5, x6, &x13);
{  uint64_t x15; uint8_t x16 = _addcarryx_u64(0x0, x10, x12, &x15);
{  uint64_t x18; uint8_t _ = _addcarryx_u64(0x0, x16, x13, &x18);
{  uint64_t x22;  uint64_t x21 = _mulx_u64(x9, 0xffffffffffffffffL, &x22);
{  uint64_t x25;  uint64_t x24 = _mulx_u64(x9, 0x7fffffffffffffffL, &x25);
{  uint64_t x27; uint8_t x28 = _addcarryx_u64(0x0, x22, x24, &x27);
{  uint64_t x30; uint8_t _ = _addcarryx_u64(0x0, x28, x25, &x30);
{  uint64_t _; uint8_t x34 = _addcarryx_u64(0x0, x9, x21, &_);
{  uint64_t x36; uint8_t x37 = _addcarryx_u64(x34, x15, x27, &x36);
{  uint64_t x39; uint8_t x40 = _addcarryx_u64(x37, x18, x30, &x39);
{  uint64_t x43;  uint64_t x42 = _mulx_u64(x4, x7, &x43);
{  uint64_t x46;  uint64_t x45 = _mulx_u64(x4, x6, &x46);
{  uint64_t x48; uint8_t x49 = _addcarryx_u64(0x0, x43, x45, &x48);
{  uint64_t x51; uint8_t _ = _addcarryx_u64(0x0, x49, x46, &x51);
{  uint64_t x54; uint8_t x55 = _addcarryx_u64(0x0, x36, x42, &x54);
{  uint64_t x57; uint8_t x58 = _addcarryx_u64(x55, x39, x48, &x57);
{  uint64_t x60; uint8_t x61 = _addcarryx_u64(x58, x40, x51, &x60);
{  uint64_t x64;  uint64_t x63 = _mulx_u64(x54, 0xffffffffffffffffL, &x64);
{  uint64_t x67;  uint64_t x66 = _mulx_u64(x54, 0x7fffffffffffffffL, &x67);
{  uint64_t x69; uint8_t x70 = _addcarryx_u64(0x0, x64, x66, &x69);
{  uint64_t x72; uint8_t _ = _addcarryx_u64(0x0, x70, x67, &x72);
{  uint64_t _; uint8_t x76 = _addcarryx_u64(0x0, x54, x63, &_);
{  uint64_t x78; uint8_t x79 = _addcarryx_u64(x76, x57, x69, &x78);
{  uint64_t x81; uint8_t x82 = _addcarryx_u64(x79, x60, x72, &x81);
{  uint8_t x83 = (x82 + x61);
{  uint64_t x85; uint8_t x86 = _subborrow_u64(0x0, x78, 0xffffffffffffffffL, &x85);
{  uint64_t x88; uint8_t x89 = _subborrow_u64(x86, x81, 0x7fffffffffffffffL, &x88);
{  uint64_t _; uint8_t x92 = _subborrow_u64(x89, x83, 0x0, &_);
{  uint64_t x93 = cmovznz(x92, x88, x81);
{  uint64_t x94 = cmovznz(x92, x85, x78);
out[0] = x93;
out[1] = x94;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[2];
