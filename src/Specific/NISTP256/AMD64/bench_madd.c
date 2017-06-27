#include <stdint.h>
#include "p256.h"

void bench_madd(unsigned char* buf) {
  uint64_t* r = (uint64_t*) buf;
  p256_jacobian_add_affine(r, r, r+12);
}
