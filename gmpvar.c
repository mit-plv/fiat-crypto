#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <gmp.h>

// modulus, encoded as big-endian bytes
static const unsigned char modulus[] = {0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xed};
static const unsigned char a_minus_two_over_four[] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01,0xdb,0x41};
#define modulus_bytes (sizeof(modulus))
#define modulus_limbs ((8*sizeof(modulus) + GMP_LIMB_BITS-1)/GMP_LIMB_BITS)


static void fe_print(mp_limb_t* fe) {
	printf("0x");
	for (size_t i = modulus_limbs-1; i > 0; --i) { printf("%016lx", fe[i]); }
	printf("%016lx", fe[0]);
}

static void crypto_scalarmult(uint8_t *out, const uint8_t *secret, size_t secretbits, const uint8_t *point) {
	// curve constants
	mp_limb_t m[modulus_limbs+1];
	mp_limb_t a24[modulus_limbs+1];
	assert(mpn_set_str(m, modulus, modulus_bytes, 256) == (mp_size_t)modulus_limbs);
	assert(mpn_set_str(a24, a_minus_two_over_four, sizeof(a_minus_two_over_four), 256) <= (mp_size_t)modulus_limbs);

	// allocate scratch space for internal use by GMP.
	// as GMP _itch are documented as functions, not macros, we use a
	// variable-size stack allocation. hopefully the compiler will inline _itch
	// functions and figure out the correct stack frame size statically through
	// constant propagation.
	mp_size_t invscratch_sz = mpn_sec_invert_itch(modulus_limbs);
	mp_size_t scratch_sz = invscratch_sz;
	          scratch_sz = (modulus_limbs > scratch_sz) ? modulus_limbs : scratch_sz;
	mp_limb_t scratch[scratch_sz];
	for (size_t i = 0; i<scratch_sz; ++i) { scratch[i] = 0; }

	// allocate scratch space for use by the field operation macros.
	mp_limb_t _product_tmp[modulus_limbs+modulus_limbs];
	
	#define fe_mul(out, x, y) do { \
		mpn_mul(_product_tmp, x, modulus_limbs, y, modulus_limbs); \
		mpn_tdiv_qr(scratch, _product_tmp, 0, _product_tmp, modulus_limbs+modulus_limbs, m, modulus_limbs); \
		for (size_t i = 0; i<modulus_limbs; i++) { out[i] = _product_tmp[i]; } \
	} while (0)
	
	#define fe_sqr(out, x) do { \
		mpn_sqr(_product_tmp, x, modulus_limbs); \
		mpn_tdiv_qr(scratch, _product_tmp, 0, _product_tmp, modulus_limbs+modulus_limbs, m, modulus_limbs); \
		for (size_t i = 0; i<modulus_limbs; i++) { out[i] = _product_tmp[i]; } \
	} while (0)
	
	#define fe_add(out, x, y) do { \
		if (mpn_add_n(out, x, y, modulus_limbs)) { \
			mpn_sub_n(out, out, m, modulus_limbs); \
		} \
	} while (0)
	
	#define fe_sub(out, x, y) do { \
		if (mpn_sub_n(out, x, y, modulus_limbs)) { \
			mpn_add_n(out, out, m, modulus_limbs); \
		} \
	} while (0)
	
	#define fe_inv(out, x) do { \
		for (size_t i = 0; i<modulus_limbs; i++) { _product_tmp[i] = x[i]; } \
		mp_size_t invertible = mpn_sec_invert(out, _product_tmp, m, modulus_limbs, 2*modulus_limbs*GMP_NUMB_BITS, scratch); \
		mpn_cnd_sub_n(1-invertible, out, out, out, modulus_limbs); \
	} while (0)

	mp_limb_t a[modulus_limbs] = {0}; mp_limb_t *nqpqx = a;
	mp_limb_t b[modulus_limbs] = {1}; mp_limb_t *nqpqz = b;
	mp_limb_t c[modulus_limbs] ={1}; mp_limb_t *nqx = c;
	mp_limb_t d[modulus_limbs] = {0}; mp_limb_t *nqz = d;
	mp_limb_t e[modulus_limbs] = {0}; mp_limb_t *nqpqx2 = e;
	mp_limb_t f[modulus_limbs] = {1}; mp_limb_t *nqpqz2 = f;
	mp_limb_t g[modulus_limbs] = {0}; mp_limb_t *nqx2 = g;
	mp_limb_t h[modulus_limbs] = {1}; mp_limb_t *nqz2 = h;
	mp_limb_t *t;

	uint8_t revpoint[modulus_bytes];
	for (size_t i = 0; i<modulus_bytes; i++) { revpoint[i] = point[modulus_bytes-1-i]; }
	for (size_t i = 0; i<modulus_limbs; i++) { nqpqx[i] = 0; }
	assert(mpn_set_str(nqpqx, revpoint, modulus_bytes, 256) <= (mp_size_t)modulus_limbs);

	mp_limb_t qmqp[modulus_limbs];
	for (size_t i = 0; i<modulus_limbs; i++) { qmqp[i] = nqpqx[i]; }

	for (size_t i = secretbits-1; i < secretbits; --i) {
		mp_limb_t bit = (secret[i/8] >> (i%8))&1;
		// printf("%01d ", bit);

		mpn_cnd_swap(bit, nqx, nqpqx, modulus_limbs);
		mpn_cnd_swap(bit, nqz, nqpqz, modulus_limbs);

		mp_limb_t *x2 = nqx2;
		mp_limb_t *z2 = nqz2;
		mp_limb_t *x3 = nqpqx2;
		mp_limb_t *z3 = nqpqz2;
		mp_limb_t *x = nqx;
		mp_limb_t *z = nqz;
		mp_limb_t *xprime = nqpqx;
		mp_limb_t *zprime = nqpqz;
		// fmonty(mp_limb_t *x2, mp_limb_t 0*z2, /* output 2Q */
		//        mp_limb_t *x3, mp_limb_t *z3, /* output Q + Q' */
		//        mp_limb_t *x, mp_limb_t *z,   /* input Q */
		//        mp_limb_t *xprime, mp_limb_t *zprime, /* input Q' */
		//        const mp_limb_t *qmqp /* input Q - Q' */) {

		mp_limb_t origx[modulus_limbs], origxprime[modulus_limbs], zzz[modulus_limbs], xx[modulus_limbs], zz[modulus_limbs], xxprime[modulus_limbs], zzprime[modulus_limbs], zzzprime[modulus_limbs];

		for (size_t i = 0; i<modulus_limbs; i++) { origx[i] = x[i]; }
		fe_add(x, x, z);
		fe_sub(z, origx, z);

		for (size_t i = 0; i<modulus_limbs; i++) { origxprime[i] = xprime[i]; }
		fe_add(xprime, xprime, zprime);
		fe_sub(zprime, origxprime, zprime);
		fe_mul(xxprime, xprime, z);
		fe_mul(zzprime, x, zprime);
		for (size_t i = 0; i<modulus_limbs; i++) { origxprime[i] = xxprime[i]; }
		fe_add(xxprime, xxprime, zzprime);
		fe_sub(zzprime, origxprime, zzprime);
		fe_sqr(x3, xxprime);
		fe_sqr(zzzprime, zzprime);
		fe_mul(z3, zzzprime, qmqp);

		fe_sqr(xx, x);
		fe_sqr(zz, z);
		fe_mul(x2, xx, zz);
		fe_sub(zz, xx, zz);
		fe_mul(zzz, zz, a24);
		fe_add(zzz, zzz, xx);
		fe_mul(z2, zz, zzz);

		// } fmonty

		mpn_cnd_swap(bit, nqx2, nqpqx2, modulus_limbs);
		mpn_cnd_swap(bit, nqz2, nqpqz2, modulus_limbs);

		t = nqx;
		nqx = nqx2;
		nqx2 = t;
		t = nqz;
		nqz = nqz2;
		nqz2 = t;
		t = nqpqx;
		nqpqx = nqpqx2;
		nqpqx2 = t;
		t = nqpqz;
		nqpqz = nqpqz2;
		nqpqz2 = t;

		// { mp_limb_t pr[modulus_limbs]; fe_inv(pr, nqz); fe_mul(pr, pr, nqx); fe_print(pr); }
		// printf(" "); 
		// { mp_limb_t pr[modulus_limbs]; fe_inv(pr, nqpqz); fe_mul(pr, pr, nqpqx); fe_print(pr); }
		// printf("\n");

	}

	fe_inv(nqz, nqz);
	fe_mul(nqx, nqx, nqz);

	for (size_t i = 0; i < modulus_bytes; i++) { out[i] = 0; }
	for (size_t i = 0; i < 8*modulus_bytes; i++) {
		mp_limb_t bit = (nqx[i/GMP_LIMB_BITS] >> (i%GMP_LIMB_BITS))&1;
		out [i/8] |= bit<<(i%8);
	}
}


int main() {
	// {
	// 	uint8_t out[sizeof(modulus)] = {0};
	// 	uint8_t point[sizeof(modulus)] = {9};
	// 	uint8_t secret[sizeof(modulus)] = {1};
	// 	crypto_scalarmult(out, point, secret, 256);
	// 	printf("0x"); for (int i = 31; i>=0; --i) { printf("%02x", out[i]); }; printf("\n");
	// }

	{
		const uint8_t expected[32] = {0x89, 0x16, 0x1f, 0xde, 0x88, 0x7b, 0x2b, 0x53, 0xde, 0x54, 0x9a, 0xf4, 0x83, 0x94, 0x01, 0x06, 0xec, 0xc1, 0x14, 0xd6, 0x98, 0x2d, 0xaa, 0x98, 0x25, 0x6d, 0xe2, 0x3b, 0xdf, 0x77, 0x66, 0x1a};
		const uint8_t basepoint[32] = {9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};


		uint8_t a[32] = {0}, b[32] = {0};
		uint8_t* in = a;
		uint8_t* out = b;
		a[0] = 1;

		for (int i = 0; i < 200; i++) {
			in[0] &= 248;
			in[31] &= 127;
			in[31] |= 64;

			crypto_scalarmult(out, in, 256, basepoint);
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
}
