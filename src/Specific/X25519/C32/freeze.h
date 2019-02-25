#include <stdint.h>

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline freeze(uint32_t* out, uint32_t x17, uint32_t x18, uint32_t x16, uint32_t x14, uint32_t x12, uint32_t x10, uint32_t x8, uint32_t x6, uint32_t x4, uint32_t x2);
