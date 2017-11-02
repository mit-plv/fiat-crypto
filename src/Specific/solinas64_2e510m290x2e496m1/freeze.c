#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "freeze.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline freeze(uint64_t* out, uint64_t x17, uint64_t x18, uint64_t x16, uint64_t x14, uint64_t x12, uint64_t x10, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint64_t x20; uint8_t x21 = _subborrow_u51(0x0, x2, 0x7ffffffffffff, &x20);
{  uint64_t x23; uint8_t x24 = _subborrow_u51(x21, x4, 0x7ffffffffffff, &x23);
{  uint64_t x26; uint8_t x27 = _subborrow_u51(x24, x6, 0x7ffffffffffff, &x26);
{  uint64_t x29; uint8_t x30 = _subborrow_u51(x27, x8, 0x7ffffffffffff, &x29);
{  uint64_t x32; uint8_t x33 = _subborrow_u51(x30, x10, 0x7ffffffffffff, &x32);
{  uint64_t x35; uint8_t x36 = _subborrow_u51(x33, x12, 0x7ffffffffffff, &x35);
{  uint64_t x38; uint8_t x39 = _subborrow_u51(x36, x14, 0x7ffffffffffff, &x38);
{  uint64_t x41; uint8_t x42 = _subborrow_u51(x39, x16, 0x7ffffffffffff, &x41);
{  uint64_t x44; uint8_t x45 = _subborrow_u51(x42, x18, 0x7ffffffffffff, &x44);
{  uint64_t x47; uint8_t x48 = _subborrow_u51(x45, x17, 0x7dbbfffffffff, &x47);
{  uint64_t x49 = (uint64_t)cmovznz(x48, 0x0, 0xffffffffffffffffL);
{  uint64_t x50 = (x49 & 0x7ffffffffffff);
{  uint64_t x52; uint8_t x53 = _addcarryx_u51(0x0, x20, x50, &x52);
{  uint64_t x54 = (x49 & 0x7ffffffffffff);
{  uint64_t x56; uint8_t x57 = _addcarryx_u51(x53, x23, x54, &x56);
{  uint64_t x58 = (x49 & 0x7ffffffffffff);
{  uint64_t x60; uint8_t x61 = _addcarryx_u51(x57, x26, x58, &x60);
{  uint64_t x62 = (x49 & 0x7ffffffffffff);
{  uint64_t x64; uint8_t x65 = _addcarryx_u51(x61, x29, x62, &x64);
{  uint64_t x66 = (x49 & 0x7ffffffffffff);
{  uint64_t x68; uint8_t x69 = _addcarryx_u51(x65, x32, x66, &x68);
{  uint64_t x70 = (x49 & 0x7ffffffffffff);
{  uint64_t x72; uint8_t x73 = _addcarryx_u51(x69, x35, x70, &x72);
{  uint64_t x74 = (x49 & 0x7ffffffffffff);
{  uint64_t x76; uint8_t x77 = _addcarryx_u51(x73, x38, x74, &x76);
{  uint64_t x78 = (x49 & 0x7ffffffffffff);
{  uint64_t x80; uint8_t x81 = _addcarryx_u51(x77, x41, x78, &x80);
{  uint64_t x82 = (x49 & 0x7ffffffffffff);
{  uint64_t x84; uint8_t x85 = _addcarryx_u51(x81, x44, x82, &x84);
{  uint64_t x86 = (x49 & 0x7dbbfffffffff);
{  uint64_t x88; uint8_t _ = _addcarryx_u51(x85, x47, x86, &x88);
out[0] = x88;
out[1] = x84;
out[2] = x80;
out[3] = x76;
out[4] = x72;
out[5] = x68;
out[6] = x64;
out[7] = x60;
out[8] = x56;
out[9] = x52;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[10];
