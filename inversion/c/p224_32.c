#include "../../fiat-c/src/p224_32.c"

#define LIMBS 7 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint32_t
#define WORDSIZE 32 /* wordsize */
#define LEN_PRIME 224 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_p224

#include "inversion_template.c"

