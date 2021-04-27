#include "../../fiat-c/src/p384_32.c"

#define LIMBS 12 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint32_t
#define WORDSIZE 32 /* wordsize */
#define LEN_PRIME 384 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_p384

#include "inversion_template.c"
