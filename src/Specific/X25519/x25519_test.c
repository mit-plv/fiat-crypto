#include <stdio.h>
#include <stdint.h>

void crypto_scalarmult(uint8_t *out, const uint8_t *secret, const uint8_t *basepoint);

const uint8_t expected[32] = {0x89, 0x16, 0x1f, 0xde, 0x88, 0x7b, 0x2b, 0x53, 0xde, 0x54, 0x9a, 0xf4, 0x83, 0x94, 0x01, 0x06, 0xec, 0xc1, 0x14, 0xd6, 0x98, 0x2d, 0xaa, 0x98, 0x25, 0x6d, 0xe2, 0x3b, 0xdf, 0x77, 0x66, 0x1a};
const uint8_t basepoint[32] = {9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

int main() {
	uint8_t a[32] = {0}, b[32] = {0};
	uint8_t* in = a;
	uint8_t* out = b;
	a[0] = 1;

	for (int i = 0; i < 200; i++) {
		crypto_scalarmult(out, in, basepoint);
    uint8_t* t = out;
    out = in;
    in = t;
	}

  for (int i = 0; i < 32; i++) {
    if (in[i] != expected[i]) {
      return (i+1);
    }
  }
  return 0;
}
