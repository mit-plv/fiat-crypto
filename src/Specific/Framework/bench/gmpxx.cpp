#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <gmpxx.h>

#ifndef q_mpz
#define q_mpz ((1_mpz<<255)-19)
#endif

#ifndef modulus_bytes_val
#define modulus_bytes_val 32
#endif

#ifndef a24_hex
#define a24_hex 0x01db41
#endif

static const mpz_class q = q_mpz;
static const size_t modulus_bytes = modulus_bytes_val;
static const unsigned int a24 = a24_hex;

static void fe_print(const mpz_class &x) {
	printf("0x"); for (size_t i = modulus_bytes-1; i<modulus_bytes; --i) { printf("%02lx", mpz_class(x>>(8*i)).get_ui()&0xff); }
}

static void fe_print_frac(mpz_class x, mpz_class z) {
	// remainder -> modulo
	if (z < 0) { z += q; }
	if (mpz_invert(z.get_mpz_t(), z.get_mpz_t(), q.get_mpz_t())) {
		// remainder -> modulo
		if (x < 0) { x += q; }
		x = x*z % q;
		fe_print(x);
	} else {
		printf("inf                               ");
	}
}

using std::pair;
using std::make_pair;
static const pair<pair<mpz_class,mpz_class>, pair<mpz_class,mpz_class>>
ladderstep(const mpz_class &x1, const mpz_class &x, const mpz_class &z, const mpz_class &x_p, const mpz_class &z_p) {
	mpz_class t;
	{ t = x;			mpz_class origx = t;
	{ t = (x + z)%q;		mpz_class x = t;
	{ t = (origx - z)%q;		mpz_class z = t;
	{ t = x_p;			mpz_class origx_p = t;
	{ t = (x_p + z_p)%q;		mpz_class x_p = t;
	{ t = (origx_p - z_p)%q;	mpz_class z_p = t;
	{ t = (x_p * z)%q;		mpz_class xx_p = t;
	{ t = (x * z_p)%q;		mpz_class zz_p = t;
	{ t = xx_p;			mpz_class origx_p = t;
	{ t = (xx_p + zz_p)%q;		mpz_class xx_p = t;
	{ t = (origx_p - zz_p)%q;	mpz_class zz_p = t;
	{ t = (xx_p*xx_p)%q;		mpz_class x3 = t;
	{ t = (zz_p*zz_p)%q;		mpz_class zzz_p = t;
	{ t = (zzz_p * x1)%q;		mpz_class z3 = t;
	{ t = (x*x)%q;			mpz_class xx = t;
	{ t = (z*z)%q;			mpz_class zz = t;
	{ t = (xx * zz)%q;		mpz_class x2 = t;
	{ t = (xx - zz)%q;		mpz_class zz = t;
	{ t = (zz * a24)%q;		mpz_class zzz = t;
	{ t = (zzz + xx)%q;		mpz_class zzz = t;
	{ t = (zz * zzz)%q;		mpz_class z2 = t;

	return make_pair(make_pair(x2, z2), make_pair(x3, z3));
	}}}}}}}}}}}}}}}}}}}}}
}

static void crypto_scalarmult(uint8_t *out, const uint8_t *secret, size_t secretbits, const uint8_t *point) {
	mpz_class x1; for (size_t i = 0; i<modulus_bytes; i++) { x1 |= mpz_class(point[i]) << (8*i); }
	mpz_class x = 1, z = 0, x_p = x1, z_p = 1;

	bool swap = false;
	for (size_t i = secretbits-1; i < secretbits; --i) {
		bool bit = (secret[i/8] >> (i%8))&1;
		// printf("%d ", bit); fe_print_frac(x, z); printf(" "); fe_print_frac(x_p, z_p); printf("\n");
		if (swap ^ bit) { std::swap(x, x_p); std::swap(z, z_p); }
		swap = bit;

		auto pp = ladderstep(x1, x, z, x_p, z_p);
		x = pp.first.first;
		z = pp.first.second;
		x_p = pp.second.first;
		z_p = pp.second.second;
	}
	if (swap) { std::swap(x, x_p); std::swap(z, z_p); }

	// remainder -> modulo
	if (z < 0) { z += q; }

	// if (mpz_invert(z.get_mpz_t(), z.get_mpz_t(), q.get_mpz_t())) {
	// 	x = x*z % q;
	// } else {
	// 	x = 0;
	// }

	// // remainder -> modulo
	// if (x < 0) { x += q; }

	for (size_t i = 0; i<modulus_bytes; i++) { out[i] = mpz_class(x>>(8*i)).get_ui()&0xff; }
	for (size_t i = 0; i<modulus_bytes; i++) { out[i] ^= mpz_class(z>>(8*i)).get_ui()&0xff; }
}

int main() {
	// {
	// 	uint8_t out[modulus_bytes] = {0};
	// 	uint8_t point[modulus_bytes] = {9};
	// 	uint8_t secret[modulus_bytes] = {1};
	// 	crypto_scalarmult(out, secret, 256, point);
	// 	// printf("0x"); for (int i = 31; i>=0; --i) { printf("%02x", out[i]); }; printf("\n");
	// }
	// {
	// 	const uint8_t expected[32] = {0x89, 0x16, 0x1f, 0xde, 0x88, 0x7b, 0x2b, 0x53, 0xde, 0x54, 0x9a, 0xf4, 0x83, 0x94, 0x01, 0x06, 0xec, 0xc1, 0x14, 0xd6, 0x98, 0x2d, 0xaa, 0x98, 0x25, 0x6d, 0xe2, 0x3b, 0xdf, 0x77, 0x66, 0x1a};
	// 	const uint8_t basepoint[32] = {9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};


	// 	uint8_t a[32] = {0}, b[32] = {0};
	// 	uint8_t* in = a;
	// 	uint8_t* out = b;
	// 	a[0] = 1;

	// 	for (int i = 0; i < 200; i++) {
	// 		in[0] &= 248;
	// 		in[31] &= 127;
	// 		in[31] |= 64;

	// 		crypto_scalarmult(out, in, 256, basepoint);
	// 		uint8_t* t = out;
	// 		out = in;
	// 		in = t;
	// 	}

	// 	for (int i = 0; i < 32; i++) {
	// 		if (in[i] != expected[i]) {
	// 			return (i+1);
	// 		}
	// 	}
	// 	return 0;
	// }
  uint8_t secret[32];
  uint8_t point[modulus_bytes];

  for (int i = 0; i < modulus_bytes; i++) { point[modulus_bytes-i] = i; }

  for (int i = 0; i < 1000; i++) {
      for (int j = 0; j<modulus_bytes; j++) {
          secret[j%32] ^= point[j];
      }
      crypto_scalarmult(point, secret, 32*8, point);
  }
  return 0;
}
