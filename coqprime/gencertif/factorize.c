/*
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "gmp.h"
#include "ecm.h" 
#include "certif.h"

#if  defined (__STDC__)                                 \
  || defined (__cplusplus)                              \
  || defined (_AIX)                                     \
  || defined (__DECC)                                   \
  || (defined (__mips) && defined (_SYSTYPE_SVR4))      \
  || defined (_MSC_VER)                                 \
  || defined (_WIN32)
#define __ECM_HAVE_TOKEN_PASTE  1
#else
#define __ECM_HAVE_TOKEN_PASTE  0
#endif

#ifndef __ECM
#if __ECM_HAVE_TOKEN_PASTE
#define __ECM(x) __ecm_##x
#else
#define __ECM(x) __ecm_/**/x
#endif
#endif

#define pp1_random_seed __ECM(pp1_random_seed)
void pp1_random_seed  (mpz_t, mpz_t, gmp_randstate_t);
#define pm1_random_seed __ECM(pm1_random_seed)
void pm1_random_seed  (mpz_t, mpz_t, gmp_randstate_t);
#define get_random_ul   __ECM(get_random_ul)
unsigned long get_random_ul (void);


static unsigned add[] = {4, 2, 4, 2, 4, 6, 2, 6};
 
void
factor_using_division (mpz_t t, pock_certif_t c)
{
  mpz_t q, r;
  unsigned long int f;
  int ai;
  unsigned *addv = add;
  unsigned int failures;
  unsigned int limit;

  /* Set the trial division limit according the size of n.  */
  limit = mpz_sizeinbase (t, 2);
  if (limit > 1000) 
    limit = 1000 * 1000;
  else 
    limit = limit * limit;


  if (flag_verbose)
    {
      printf ("[using trivial division (%u)] ", limit);
      fflush (stdout);
    }

  mpz_init (q);
  mpz_init (r);

  f = mpz_scan1 (t, 0);
  mpz_div_2exp (t, t, f);     
  while (f)
    {
      if (flag_verbose) { printf ("2 "); fflush (stdout);}
      dec_add_ui(c, 2); 
      f--;
    }

  for (;;)
    {
      mpz_tdiv_qr_ui (q, r, t, 3);
      if (mpz_cmp_ui (r, 0) != 0) break;
      mpz_set (t, q);
      if (flag_verbose) { printf ("3 "); fflush (stdout); }
      dec_add_ui(c,3);
   }

  for (;;)
    {
      mpz_tdiv_qr_ui (q, r, t, 5);
      if (mpz_cmp_ui (r, 0) != 0) break; 
      mpz_set (t, q);
      if (flag_verbose) { printf ("5 "); fflush (stdout); }
      dec_add_ui(c,5);
    }

  failures = 0;
  f = 7;
  ai = 0;
  while (mpz_cmp_ui (t, 1) != 0)
    {
      mpz_tdiv_qr_ui (q, r, t, f);

      if (mpz_cmp_ui (r, 0) != 0)
	{
	  f += addv[ai];
	  if (mpz_cmp_ui (q, f) < 0) break;
	  ai = (ai + 1) & 7;
	  failures++;
	  if (failures > limit)  break;
	}
      else
	{ 
	  mpz_swap (t, q);
	  if (flag_verbose) { printf ("%lu ", f); fflush (stdout); }
	  dec_add_ui(c,f);
	  failures = 0;
	}
    }

  if (flag_verbose) fprintf(stdout,"\n");
	 
  mpz_clear (q);
  mpz_clear (r);
  return;
}

void out_factor(mpz_t f,pock_certif_t c) 
{
  mpz_out_str (stdout, 10, f);
  fprintf(stdout," (%lu digits, F1 %lu digits) \n", mpz_sizeinbase(f,10),
	  mpz_sizeinbase(c->_F1,10));
  fflush(stdout);
  return;
}


int
factor_using_pollard_rho (mpz_t n, int a_int, unsigned long p, 
			  pock_certif_t pc)
{
  mpz_t x, x1, y, P;
  mpz_t a;
  mpz_t g;
  mpz_t t1, t2;
  int k, l, c, i, res;

  if (flag_verbose)
    {
      printf ("[pollard-rho (%d)] ", a_int);
      fflush (stdout);
    }

  mpz_init (g);
  mpz_init (t1);
  mpz_init (t2);

  mpz_init_set_si (a, a_int);
  mpz_init_set_si (y, 2);
  mpz_init_set_si (x, 2);
  mpz_init_set_si (x1, 2);
  k = 1;
  l = 1;
  mpz_init_set_ui (P, 1);
  c = 0;

  res = 0;

  while (!res)
    {
S2:
      if (p != 0)
	{
	  mpz_powm_ui (x, x, p, n); mpz_add (x, x, a);
	}
      else
	{
	  mpz_mul (x, x, x); mpz_add (x, x, a); mpz_mod (x, x, n);
	}
      mpz_sub (t1, x1, x); mpz_mul (t2, P, t1); mpz_mod (P, t2, n);
      c++;
      if (c == 20)
	{
	  c = 0;
	  mpz_gcd (g, P, n);
	  if (mpz_cmp_ui (g, 1) != 0)
	    goto S4;
	  mpz_set (y, x);
	}
      /*S3: */
      k--;
      if (k > 0)
	goto S2;

      mpz_gcd (g, P, n);
      if (mpz_cmp_ui (g, 1) != 0)
	goto S4;

      mpz_set (x1, x);
      k = l;
      l = 2 * l;
      for (i = 0; i < k; i++)
	{
	  if (p != 0)
	    {
	      mpz_powm_ui (x, x, p, n); mpz_add (x, x, a);
	    }
	  else
	    {
	      mpz_mul (x, x, x); mpz_add (x, x, a); mpz_mod (x, x, n);
	    }
	}
      mpz_set (y, x);
      c = 0;
      goto S2;
S4:
      do
	{
	  if (p != 0)
	    {
	      mpz_powm_ui (y, y, p, n); mpz_add (y, y, a); 
	    }
	  else
	    {
	      mpz_mul (y, y, y); mpz_add (y, y, a); mpz_mod (y, y, n);
	    }
	  mpz_sub (t1, x1, y); mpz_gcd (g, t1, n);
	}
      while (mpz_cmp_ui (g, 1) == 0);

      if (!mpz_probab_prime_p (g, 3))
	{
	  do
            {
              mp_limb_t a_limb;
              mpn_random (&a_limb, (mp_size_t) 1);
              a_int = (int) a_limb;
            }
	  while (a_int == -2 || a_int == 0);

	  if (flag_verbose)
	    {
	      printf ("[composite factor--restarting pollard-rho] ");
	      fflush (stdout);
	    }
	  res = factor_using_pollard_rho (g, a_int, p, pc);
	  break;
	}
      else
	{
          dec_add_mpz(pc, g);
	  if (flag_verbose) out_factor(g,pc);
	  res = check_pock (pc);
	  if (res) break; 
	}
      mpz_div (n, n, g);
      mpz_mod (x, x, n);
      mpz_mod (x1, x1, n);
      mpz_mod (y, y, n);
      if (mpz_probab_prime_p (n, 3))
	{
          dec_add_mpz(pc, n); 
	  if (flag_verbose) out_factor(n,pc);
	  res = check_pock (pc);
	  break;
	}
    }

  mpz_clear (g);
  mpz_clear (P);
  mpz_clear (t2);
  mpz_clear (t1);
  mpz_clear (a);
  mpz_clear (x1);
  mpz_clear (x);
  mpz_clear (y);

  return res;
}

static double B1_table[] = 
  { 11000, 50000, 250000, 1000000, 3000000,
    11000000, 43000000, 110000000, 260000000, 850000000 };

static int it_table[] =
 { 200, 214, 422, 30, 30,
   20, 20, 20, 20, 20}; 

static int size_table[] =
  { 20, 25, 30, 35, 40,
    45, 50, 55, 60, 65 };

int ecm_factorize(mpz_t n, pock_certif_t c);

int my_ecm_factor(mpz_t n, pock_certif_t c, double B1, int iterate) 
{
  int i, res, found;
  mpz_t f;
  gmp_randstate_t randstate;
  ecm_params params;

  mpz_init(f);
  ecm_init(params);
  /* if (flag_verbose) params->verbose = 1; */
  gmp_randinit_default (randstate);
  gmp_randseed_ui (randstate, get_random_ul ());
  if (B1 > 11000) params->B1done = 11000;
  
  res = 0;
  i = 0;
  iterate += 5;
  while (i < iterate && !res && mpz_cmp_ui (n, 1) != 0) {
    if (i == 0) { /* start with pm1 */
      if (flag_verbose) {
	printf("using pm1 with B1 = %1.0f ", B1); 
	fflush(stdout);
      }

      params->method = ECM_PM1;
      pm1_random_seed (params->x, n, randstate);
      found = ecm_factor(f, n, B1, params);
      if (found) {
	mpz_tdiv_q(n, n, f);
	if (mpz_probab_prime_p (f, 3)) 
	  {
	    dec_add_mpz(c,f);
	    if (flag_verbose) out_factor(f,c);
	    res = check_pock(c);
	  } 
	else 
	  {
	    if (flag_verbose) 
	      {
		fprintf(stdout,"composite factor ");
		mpz_out_str (stdout, 10, f);
		fprintf(stdout,"(%lu digits)\n",mpz_sizeinbase(f,10));
		fflush(stdout);	
	    }
	    if (B1 == 11000) res = factor_using_pollard_rho(f, 1, 0,c);
	    else res = ecm_factorize(f, c);
	  }

	if (!res && mpz_cmp_ui (n, 1) != 0 && mpz_probab_prime_p (n, 3)) {
	  dec_add_mpz(c,n);
	  if (flag_verbose) out_factor(n,c);
	  mpz_tdiv_q(n, n, n);
	  res = check_pock(c); 
	}
      } else i++;
      if (flag_verbose) printf("\n");
    } else if (0 < i && i <= 3) {
      /* do 3 time pp1 */
      params->method = ECM_PP1;
      mpz_set_ui (params->x, 0);
      if (flag_verbose && i == 1) 
	{ printf("using pp1 with B1 = %1.0f ", B1); 
	  fflush(stdout);
	}
      pp1_random_seed (params->x, n, randstate);
      found = ecm_factor(f, n, B1, params);
      if (found) {
	mpz_tdiv_q(n, n, f);
	if (mpz_probab_prime_p (f, 3)) 
	  {
	    dec_add_mpz(c,f);
	    if (flag_verbose) out_factor(f,c);
	    res = check_pock(c);
	  } 
	else 
	  {
	    if (flag_verbose) 
	      {
		fprintf(stdout,"composite factor ");
		mpz_out_str (stdout, 10, f);
		fprintf(stdout,"(%lu digits)\n",mpz_sizeinbase(f,10));
		fflush(stdout);	
	      }
	    if (B1 == 11000) res = factor_using_pollard_rho(f, 1, 0,c);
	    else res = ecm_factorize(f, c);
	  }

	if (!res && mpz_cmp_ui (n, 1) != 0 && mpz_probab_prime_p (n, 3)) {
	  dec_add_mpz(c,n);
	  if (flag_verbose) out_factor(n,c);
	  mpz_tdiv_q(n, n, n);
	  res = check_pock(c); 
	}
	i = 0; /* restarting to factorize */
      } else i++;
      if (flag_verbose && i == 3) printf("\n");
    } else { /* continue with ecm */
      params->method = ECM_ECM;
      mpz_set_ui (params->x, 0);
      if (flag_verbose && i == 4) {
	printf("using ecm with B1 = %1.0f ", B1); 
	fflush(stdout);
      } else {printf("#%i ", i-4); fflush(stdout);}

      mpz_urandomb (params->sigma, randstate, 32);
      mpz_add_ui (params->sigma, params->sigma, 6);

      found = ecm_factor (f, n, B1, params);
     
      if (found > 0) { /* found a factor */
	mpz_tdiv_q(n, n, f);
	if (mpz_probab_prime_p (f, 3)) 
	  {
	    dec_add_mpz(c,f);
	    if (flag_verbose) out_factor(f,c);
	    res = check_pock(c);
	  } 
	else 
	  {
	    if (flag_verbose) 
	      {
		fprintf(stdout,"composite factor ");
		mpz_out_str (stdout, 10, f);
		fprintf(stdout,"(%lu digits)\n",mpz_sizeinbase(f,10));
		fflush(stdout);	
	      }
	    if (B1 == 11000) res = factor_using_pollard_rho(f, 1, 0,c);
	    else res = ecm_factorize(f, c);
	  }
	if (!res && mpz_cmp_ui (n, 1) != 0 && mpz_probab_prime_p (n, 3)) {
	  dec_add_mpz(c,n);
	  if (flag_verbose)  out_factor(n,c);
	  mpz_tdiv_q(n, n, n);
	  res = check_pock(c); 
	}
	i = 0; /* restarting to factorize */
      } else i++;  
    }
  }
  if (flag_verbose) printf("\n"); 
    
  ecm_clear(params);
  mpz_clear(f);
  return res;
}


int ecm_factorize(mpz_t n, pock_certif_t c) 
{
  
  int iB1, res = 0;

  /*res = my_ecm_factor(n, c, B1_table[0], 4);
  if (!res) res = my_ecm_factor(n, c, B1_table[1], 4);
  if (!res) res = my_ecm_factor(n, c, B1_table[2], 4);
  if (!res) res = my_ecm_factor(n, c, B1_table[3], 3);
  if (!res) res = my_ecm_factor(n, c, B1_table[4], 2); */

  for (iB1 = 0; !res && iB1 < 10 &&  mpz_cmp_ui (n, 1) != 0; iB1++) 
    {
      if (flag_verbose) 
	printf("Searching factor of %i digits\n", size_table[iB1]);
      res = my_ecm_factor(n, c, B1_table[iB1], it_table[iB1]);
    }

  return res;
}

int factorize_no_small(mpz_t n, pock_certif_t c)
{
  int res;
 
  if (mpz_probab_prime_p (n, 3))
    {
      if (flag_verbose) mpz_out_str (stdout, 10, n);
      dec_add_mpz(c,n);
      res = check_pock(c);
    }
  else
    res = ecm_factorize (n, c);
  
  if (flag_verbose) { fprintf(stdout,"\n");fflush(stdout); }
 
  return res;
}

int factorize(mpz_t n, pock_certif_t c) 
{ 
  int res;

  /* compute the factorization */
  if (flag_verbose) { 
    fprintf(stdout,"   factorize "); 
    mpz_out_str (stdout, 10, n);fflush(stdout);
    fprintf(stdout,"\n     ");
    fprintf(stdout,"   of %lu digits\n", mpz_sizeinbase(n,10));
    fflush(stdout);
  }

  factor_using_division (n, c);

  res = check_pock(c);
   
  if (!res) res = factorize_no_small(n, c);

  if (flag_verbose) { fprintf(stdout,"\n");fflush(stdout); }

  return res;
}

int factorize_mersenne (unsigned long int p, pock_certif_t c)
{
  unsigned long int q; 
  int i,iB1,res,used;
  mpz_t n;
  __mpz_struct dec[100];

  if (flag_verbose) { 
    fprintf(stdout, "\nfactorize mersenne %lu\n", p); 
    fflush(stdout);
  }

  used = 0;
  q = p;
  mpz_init (n);

  while (q > 3) {

    if (q % 2 == 0) 
      {
	q = q / 2;

	mpz_set_ui(n, 1);         /* n = 1                */
	mpz_mul_2exp(n, n, q);    /* n = 2^q              */
	mpz_add_ui(n, n, 1);      /* n = 2^q + 1          */

	factor_using_division(n,c);
	
	mpz_init_set(&(dec[used]), n);
	used++;
      } 
    else if (q % 3 == 0 )
      {
	q = q /3;

	mpz_set_ui (n,1);     /* n = 1                */
	mpz_mul_2exp (n, n, q);    /* n = 2^q              */
	mpz_add_ui (n, n, 1);      /* n = 2^q + 1          */
	mpz_mul_2exp (n, n, q);    /* n = 2^(2q) + 2^q     */
	mpz_add_ui (n, n, 1);      /* n = 2^(2q) + 2^q + 1 */
      
	factor_using_division (n,c);
	mpz_init_set(&(dec[used]), n);
	used++;
      }
    else break;
      
  }
     
  switch (q) {
  case 1: 
    break;
  case 2: 
    dec_add_ui(c,3);
    break;
  case 3:
    dec_add_ui(c,7);
    break;
  default: 
    mpz_set_ui(n, 1); 
    mpz_mul_2exp(n, n, q); 
    mpz_sub_ui(n, n, 1); 
    factor_using_division (n,c);
    mpz_init_set(&(dec[used]), n);
    used++;
    break;
  }
  
  res = check_pock(c);
  iB1 = 0;
  while (!res && iB1 < 10) {
    for (i = 0; i < used && !res; i++) {
      if (mpz_cmp_ui (&(dec[i]), 1) != 0) 
	res = my_ecm_factor(&(dec[i]), c, B1_table[iB1], it_table[iB1]);
    }
    iB1++;
  }

  mpz_clear(n);
  return res;
}


pock_certif_t mersenne_certif (mpz_t t, unsigned long int p)
{
  pock_certif_t c;
  c = pock_init(t);
  dec_add_ui(c, 2);
  factorize_mersenne (p-1, c);
  finalize_pock(c);  
  return c;
}



pock_certif_t pock_certif (mpz_t t)
{
 
  mpz_t tm1;

  pock_certif_t c;

  if (flag_verbose) {
    fprintf(stdout,"pocklington ");
    mpz_out_str (stdout, 10, t);fflush(stdout);
    fprintf(stdout,"\n");fflush(stdout);
  }

  /* initialize the decompostion */
  c = pock_init(t); 
  
  /* compute t - 1 */
  mpz_init_set (tm1, c->_R1);
 
  /* compute the factorisation */
  factorize(tm1, c);

  mpz_clear(tm1);

  finalize_pock(c);

  return c;
}



int MAXPROOFPRIMES = 48611;  /* 5000 first ones */

pre_certif_t certif_2;

void extend_lc (certif_t lc, pock_certif_t c, unsigned long int min,
                 unsigned long int max )
{
  int i, size;
  mpz_ptr *ptr;
  mpz_t t;
  mpz_init (t);

  ptr = c->_dec;
  size = c->_used;

  if (c->_pow2 > 0 && !_2_is_in(lc)) {
    mpz_t t2;
    pre_certif_t ct;
    mpz_init_set_ui (t2, 2);
    ct = mk_proof_certif(t2);
    add_pre(ct, lc);
    mpz_clear(t2); 
  }

  for(i = size - 1; i >= 0; i--)
    { 
      mpz_set(t, ptr[i]);
      if (!is_in(t, lc)) {
	pre_certif_t ct;
   	if (mpz_cmp_ui(t, MAXPROOFPRIMES) <= 0 || 
            (mpz_cmp_ui (t, min) >= 0 && (mpz_cmp_ui (t, max) <= 0)))
	    ct = mk_proof_certif(t);
        else {
	  ct = mk_pock_certif (pock_certif(t));
	  extend_lc(lc, ct->_certif._pock, min, max);
	}
	add_pre(ct, lc);
      }
    }
  return;
}
