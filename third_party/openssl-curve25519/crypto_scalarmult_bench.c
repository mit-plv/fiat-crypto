#include "ec_curve25519.h"

void crypto_scalarmult_bench(unsigned char* buf) {
  x25519_scalar_mult(buf, buf+32, buf+64);
}
