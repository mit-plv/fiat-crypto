#include <stdint.h>

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline feadd(uint64_t* out, uint64_t x6, uint64_t x7, uint64_t x5, uint64_t x10, uint64_t x11, uint64_t x9);
