#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <gmp.h>

// modulus, encoded as big-endian bytes
static const unsigned char modulus[] = {0xec,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff};
static const size_t modulus_bytes = sizeof(modulus);
static const size_t modulus_limbs = (8*sizeof(modulus) + GMP_LIMB_BITS-1)/GMP_LIMB_BITS;

static void print_limbs(mp_limb_t* fe) {
	for (size_t i = 0; i<modulus_limbs; i++) { printf("0x%016lx ", fe[i]); } printf("\n");
}

int main() {
	mp_limb_t m[modulus_limbs+1];
	assert(mpn_set_str(m, modulus, modulus_bytes, 256) == (mp_size_t)modulus_limbs);

	// allocate scratch space for internal use by GMP.
	// as GMP _itch are documented as functions, not macros, we use a
	// variable-size stack allocation. hopefully the compiler will inline _itch
	// functions and figure out the correct stack frame size statically through
	// constant propagation.
	mp_size_t mulscratch_sz = mpn_sec_mul_itch(modulus_limbs, modulus_limbs);
	mp_size_t sqrscratch_sz = mpn_sec_sqr_itch(modulus_limbs);
	mp_size_t modscratch_sz = mpn_sec_div_r_itch(modulus_limbs+modulus_limbs, modulus_limbs);
	mp_size_t invscratch_sz = mpn_sec_invert_itch(modulus_limbs);
	mp_size_t scratch_sz = mulscratch_sz;
	          scratch_sz = (sqrscratch_sz > scratch_sz) ? sqrscratch_sz : scratch_sz;
	          scratch_sz = (modscratch_sz > scratch_sz) ? modscratch_sz : scratch_sz;
	          scratch_sz = (invscratch_sz > scratch_sz) ? invscratch_sz : scratch_sz;
	mp_limb_t scratch[scratch_sz];

	// allocate scratch space for use by the following macros.
	mp_limb_t _product_tmp[modulus_limbs+modulus_limbs];

	#define fe_mul(out, x, y) do { \
		mpn_sec_mul(_product_tmp, x, modulus_limbs, y, modulus_limbs, scratch); \
		mpn_sec_div_r(_product_tmp, modulus_limbs+modulus_limbs, m, modulus_limbs, scratch); \
		for (size_t i = 0; i<modulus_limbs; i++) { out[i] = _product_tmp[i]; } \
	} while (0)
	
	#define fe_sqr(out, x) do { \
		mpn_sec_sqr(_product_tmp, x, modulus_limbs, scratch); \
		mpn_sec_div_r(_product_tmp, modulus_limbs+modulus_limbs, m, modulus_limbs, scratch); \
		for (size_t i = 0; i<modulus_limbs; i++) { out[i] = _product_tmp[i]; } \
	} while (0)
	
	#define fe_add(out, x, y) do { \
		mpn_cnd_sub_n(mpn_add_n(out, x, y, modulus_limbs), out, out, m, modulus_limbs); \
	} while (0)
	
	#define fe_sub(out, x, y) do { \
		mpn_cnd_add_n(mpn_sub_n(out, x, y, modulus_limbs), out, out, m, modulus_limbs); \
	} while (0)
	
	#define fe_inv(out, x) do { \
		for (size_t i = 0; i<modulus_limbs; i++) { _product_tmp[i] = x[i]; } \
		mp_size_t invertible = mpn_sec_invert(out, _product_tmp, m, modulus_limbs, 2*modulus_limbs*GMP_NUMB_BITS, scratch); \
		mpn_cnd_sub_n(1-invertible, out, out, out, modulus_limbs); \
	} while (0)

	mp_limb_t x[modulus_limbs]; mpn_zero(x, modulus_limbs);
	x[3] = 7;
	print_limbs(x);
	mp_limb_t y[modulus_limbs]; mpn_zero(y, modulus_limbs);
	y[3] = 5;
	print_limbs(y);

	mp_limb_t xy[modulus_limbs];

	fe_mul(xy, x,y);
	print_limbs(xy);

	fe_sqr(xy, xy);
	print_limbs(xy);

	fe_add(xy, xy, xy);
	print_limbs(xy);

	fe_sub(xy, xy, m);
	print_limbs(xy);

	print_limbs(y);
	fe_inv(x, y);
	print_limbs(x);

	fe_mul(xy, x, y);
	print_limbs(xy);

	fe_inv(x, m);
	print_limbs(x);
}
