#include "../../fiat-c/src/p434_64.c"

#define LIMBS 7 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint64_t
#define WORDSIZE 64 /* wordsize */
#define LEN_PRIME 434 /* length of the prime in bits */
#define CURVE_DESCRIPTION fiat_p434

#include "inversion_template.c"
