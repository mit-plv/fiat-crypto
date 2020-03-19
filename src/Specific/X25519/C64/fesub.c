#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "fesub.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline fesub(uint64_t* out, uint64_t x10, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x18, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13)
{  (((0xffffffffffffe + x10) - x18), ((0xffffffffffffe + x11) - x19), ((0xffffffffffffe + x9) - x17), ((0xffffffffffffe + x7) - x15), ((0xfffffffffffda + x5) - x13)))
{ (x, x0)%core
{      : word64 * word64 * word64 * word64 * word64 → word64 * word64 * word64 * word64 * word64 → ReturnType (uint64_t * uint64_t * uint64_t * uint64_t * uint64_t)
