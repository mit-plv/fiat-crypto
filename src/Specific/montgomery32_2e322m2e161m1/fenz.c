#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "fenz.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline fenz(uint64_t* out, uint64_t x19, uint64_t x20, uint64_t x18, uint64_t x16, uint64_t x14, uint64_t x12, uint64_t x10, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint32_t x21 = (x20 | x19);
{  uint32_t x22 = (x18 | x21);
{  uint32_t x23 = (x16 | x22);
{  uint32_t x24 = (x14 | x23);
{  uint32_t x25 = (x12 | x24);
{  uint32_t x26 = (x10 | x25);
{  uint32_t x27 = (x8 | x26);
{  uint32_t x28 = (x6 | x27);
{  uint32_t x29 = (x4 | x28);
{  uint32_t x30 = (x2 | x29);
out[0] = x30;
}}}}}}}}}}
// caller: uint64_t out[1];
