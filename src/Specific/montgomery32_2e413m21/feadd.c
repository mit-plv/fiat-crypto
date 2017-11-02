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

void force_inline feadd(uint64_t* out, uint64_t x26, uint64_t x27, uint64_t x25, uint64_t x23, uint64_t x21, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x50, uint64_t x51, uint64_t x49, uint64_t x47, uint64_t x45, uint64_t x43, uint64_t x41, uint64_t x39, uint64_t x37, uint64_t x35, uint64_t x33, uint64_t x31, uint64_t x29)
{  uint32_t x53; uint8_t x54 = _addcarryx_u32(0x0, x5, x29, &x53);
{  uint32_t x56; uint8_t x57 = _addcarryx_u32(x54, x7, x31, &x56);
{  uint32_t x59; uint8_t x60 = _addcarryx_u32(x57, x9, x33, &x59);
{  uint32_t x62; uint8_t x63 = _addcarryx_u32(x60, x11, x35, &x62);
{  uint32_t x65; uint8_t x66 = _addcarryx_u32(x63, x13, x37, &x65);
{  uint32_t x68; uint8_t x69 = _addcarryx_u32(x66, x15, x39, &x68);
{  uint32_t x71; uint8_t x72 = _addcarryx_u32(x69, x17, x41, &x71);
{  uint32_t x74; uint8_t x75 = _addcarryx_u32(x72, x19, x43, &x74);
{  uint32_t x77; uint8_t x78 = _addcarryx_u32(x75, x21, x45, &x77);
{  uint32_t x80; uint8_t x81 = _addcarryx_u32(x78, x23, x47, &x80);
{  uint32_t x83; uint8_t x84 = _addcarryx_u32(x81, x25, x49, &x83);
{  uint32_t x86; uint8_t x87 = _addcarryx_u32(x84, x27, x51, &x86);
{  uint32_t x89; uint8_t x90 = _addcarryx_u32(x87, x26, x50, &x89);
{  uint32_t x92; uint8_t x93 = _subborrow_u32(0x0, x53, 0xffffffeb, &x92);
{  uint32_t x95; uint8_t x96 = _subborrow_u32(x93, x56, 0xffffffff, &x95);
{  uint32_t x98; uint8_t x99 = _subborrow_u32(x96, x59, 0xffffffff, &x98);
{  uint32_t x101; uint8_t x102 = _subborrow_u32(x99, x62, 0xffffffff, &x101);
{  uint32_t x104; uint8_t x105 = _subborrow_u32(x102, x65, 0xffffffff, &x104);
{  uint32_t x107; uint8_t x108 = _subborrow_u32(x105, x68, 0xffffffff, &x107);
{  uint32_t x110; uint8_t x111 = _subborrow_u32(x108, x71, 0xffffffff, &x110);
{  uint32_t x113; uint8_t x114 = _subborrow_u32(x111, x74, 0xffffffff, &x113);
{  uint32_t x116; uint8_t x117 = _subborrow_u32(x114, x77, 0xffffffff, &x116);
{  uint32_t x119; uint8_t x120 = _subborrow_u32(x117, x80, 0xffffffff, &x119);
{  uint32_t x122; uint8_t x123 = _subborrow_u32(x120, x83, 0xffffffff, &x122);
{  uint32_t x125; uint8_t x126 = _subborrow_u32(x123, x86, 0xffffffff, &x125);
{  uint32_t x128; uint8_t x129 = _subborrow_u32(x126, x89, 0x1fffffff, &x128);
{  uint32_t _; uint8_t x132 = _subborrow_u32(x129, x90, 0x0, &_);
{  uint32_t x133 = cmovznz(x132, x128, x89);
{  uint32_t x134 = cmovznz(x132, x125, x86);
{  uint32_t x135 = cmovznz(x132, x122, x83);
{  uint32_t x136 = cmovznz(x132, x119, x80);
{  uint32_t x137 = cmovznz(x132, x116, x77);
{  uint32_t x138 = cmovznz(x132, x113, x74);
{  uint32_t x139 = cmovznz(x132, x110, x71);
{  uint32_t x140 = cmovznz(x132, x107, x68);
{  uint32_t x141 = cmovznz(x132, x104, x65);
{  uint32_t x142 = cmovznz(x132, x101, x62);
{  uint32_t x143 = cmovznz(x132, x98, x59);
{  uint32_t x144 = cmovznz(x132, x95, x56);
{  uint32_t x145 = cmovznz(x132, x92, x53);
out[0] = x133;
out[1] = x134;
out[2] = x135;
out[3] = x136;
out[4] = x137;
out[5] = x138;
out[6] = x139;
out[7] = x140;
out[8] = x141;
out[9] = x142;
out[10] = x143;
out[11] = x144;
out[12] = x145;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[13];
