#include <stdint.h>

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline fenz(uint64_t* out, uint64_t x1, uint64_t x2);
