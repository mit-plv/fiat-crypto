/*
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)
*/

#include "gmp.h"
#include "certif.h"

#ifndef __FACTORIZE_H__

void set_verbose();
pock_certif_t mersenne_certif (mpz_t t, unsigned long int p);
pock_certif_t pock_certif (mpz_t t);
void extend_lc (certif_t lc, pock_certif_t c, unsigned long int min,
		unsigned long int max );
#define  __FACTORIZE_H__
#endif  /* __FACTORIZE_H__ */
