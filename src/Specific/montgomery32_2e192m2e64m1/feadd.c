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

void force_inline feadd(uint64_t* out, uint64_t x12, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x22, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15)
{  uint32_t x25; uint8_t x26 = _addcarryx_u32(0x0, x5, x15, &x25);
{  uint32_t x28; uint8_t x29 = _addcarryx_u32(x26, x7, x17, &x28);
{  uint32_t x31; uint8_t x32 = _addcarryx_u32(x29, x9, x19, &x31);
{  uint32_t x34; uint8_t x35 = _addcarryx_u32(x32, x11, x21, &x34);
{  uint32_t x37; uint8_t x38 = _addcarryx_u32(x35, x13, x23, &x37);
{  uint32_t x40; uint8_t x41 = _addcarryx_u32(x38, x12, x22, &x40);
{  uint32_t x43; uint8_t x44 = _subborrow_u32(0x0, x25, 0xffffffff, &x43);
{  uint32_t x46; uint8_t x47 = _subborrow_u32(x44, x28, 0xffffffff, &x46);
{  uint32_t x49; uint8_t x50 = _subborrow_u32(x47, x31, 0xfffffffe, &x49);
{  uint32_t x52; uint8_t x53 = _subborrow_u32(x50, x34, 0xffffffff, &x52);
{  uint32_t x55; uint8_t x56 = _subborrow_u32(x53, x37, 0xffffffff, &x55);
{  uint32_t x58; uint8_t x59 = _subborrow_u32(x56, x40, 0xffffffff, &x58);
{  uint32_t _; uint8_t x62 = _subborrow_u32(x59, x41, 0x0, &_);
{  uint32_t x63 = cmovznz(x62, x58, x40);
{  uint32_t x64 = cmovznz(x62, x55, x37);
{  uint32_t x65 = cmovznz(x62, x52, x34);
{  uint32_t x66 = cmovznz(x62, x49, x31);
{  uint32_t x67 = cmovznz(x62, x46, x28);
{  uint32_t x68 = cmovznz(x62, x43, x25);
out[0] = x63;
out[1] = x64;
out[2] = x65;
out[3] = x66;
out[4] = x67;
out[5] = x68;
}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[6];
