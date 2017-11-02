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

void force_inline feadd(uint64_t* out, uint64_t x14, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x26, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17)
{  uint64_t x29; uint8_t x30 = _addcarryx_u64(0x0, x5, x17, &x29);
{  uint64_t x32; uint8_t x33 = _addcarryx_u64(x30, x7, x19, &x32);
{  uint64_t x35; uint8_t x36 = _addcarryx_u64(x33, x9, x21, &x35);
{  uint64_t x38; uint8_t x39 = _addcarryx_u64(x36, x11, x23, &x38);
{  uint64_t x41; uint8_t x42 = _addcarryx_u64(x39, x13, x25, &x41);
{  uint64_t x44; uint8_t x45 = _addcarryx_u64(x42, x15, x27, &x44);
{  uint64_t x47; uint8_t x48 = _addcarryx_u64(x45, x14, x26, &x47);
{  uint64_t x50; uint8_t x51 = _subborrow_u64(0x0, x29, 0xffffffffffffffffL, &x50);
{  uint64_t x53; uint8_t x54 = _subborrow_u64(x51, x32, 0xffffffffffffffffL, &x53);
{  uint64_t x56; uint8_t x57 = _subborrow_u64(x54, x35, 0xffffffffffffffffL, &x56);
{  uint64_t x59; uint8_t x60 = _subborrow_u64(x57, x38, 0xfffffffeffffffffL, &x59);
{  uint64_t x62; uint8_t x63 = _subborrow_u64(x60, x41, 0xffffffffffffffffL, &x62);
{  uint64_t x65; uint8_t x66 = _subborrow_u64(x63, x44, 0xffffffffffffffffL, &x65);
{  uint64_t x68; uint8_t x69 = _subborrow_u64(x66, x47, 0xffffffffffffffffL, &x68);
{  uint64_t _; uint8_t x72 = _subborrow_u64(x69, x48, 0x0, &_);
{  uint64_t x73 = cmovznz(x72, x68, x47);
{  uint64_t x74 = cmovznz(x72, x65, x44);
{  uint64_t x75 = cmovznz(x72, x62, x41);
{  uint64_t x76 = cmovznz(x72, x59, x38);
{  uint64_t x77 = cmovznz(x72, x56, x35);
{  uint64_t x78 = cmovznz(x72, x53, x32);
{  uint64_t x79 = cmovznz(x72, x50, x29);
out[0] = x73;
out[1] = x74;
out[2] = x75;
out[3] = x76;
out[4] = x77;
out[5] = x78;
out[6] = x79;
}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[7];
