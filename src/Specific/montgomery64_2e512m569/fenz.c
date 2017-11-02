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

void force_inline fenz(uint64_t* out, uint64_t x13, uint64_t x14, uint64_t x12, uint64_t x10, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint64_t x15 = (x14 | x13);
{  uint64_t x16 = (x12 | x15);
{  uint64_t x17 = (x10 | x16);
{  uint64_t x18 = (x8 | x17);
{  uint64_t x19 = (x6 | x18);
{  uint64_t x20 = (x4 | x19);
{  uint64_t x21 = (x2 | x20);
out[0] = x21;
}}}}}}}
// caller: uint64_t out[1];
