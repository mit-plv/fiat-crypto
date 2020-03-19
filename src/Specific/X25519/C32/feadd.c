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

void force_inline feadd(uint32_t* out, uint32_t x20, uint32_t x21, uint32_t x19, uint32_t x17, uint32_t x15, uint32_t x13, uint32_t x11, uint32_t x9, uint32_t x7, uint32_t x5, uint32_t x38, uint32_t x39, uint32_t x37, uint32_t x35, uint32_t x33, uint32_t x31, uint32_t x29, uint32_t x27, uint32_t x25, uint32_t x23)
{  ((x20 + x38), (x21 + x39), (x19 + x37), (x17 + x35), (x15 + x33), (x13 + x31), (x11 + x29), (x9 + x27), (x7 + x25), (x5 + x23)))
{ (x, x0)%core
{      : word32 * word32 * word32 * word32 * word32 * word32 * word32 * word32 * word32 * word32 → word32 * word32 * word32 * word32 * word32 * word32 * word32 * word32 * word32 * word32 → ReturnType (uint32_t * uint32_t * uint32_t * uint32_t * uint32_t * uint32_t * uint32_t * uint32_t * uint32_t * uint32_t)
