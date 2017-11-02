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

void force_inline freeze(uint64_t* out, uint64_t x25, uint64_t x26, uint64_t x24, uint64_t x22, uint64_t x20, uint64_t x18, uint64_t x16, uint64_t x14, uint64_t x12, uint64_t x10, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
out[0] = uint32_t x28;
out[1] = uint8_t x29 = Op Syntax.SubWithGetBorrow 24 Syntax.TWord 3 Syntax.TWord 5 Syntax.TWord 5 Syntax.TWord 5 Syntax.TWord 3 0x0;
out[2] = x2;
out[3] = 0xffffef;;
}
// caller: uint64_t out[4];
