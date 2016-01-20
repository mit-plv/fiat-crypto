/*
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)
*/

#include <stdio.h>
#include "gmp.h"

#ifndef __CERTIF_H__

extern int flag_verbose;
void my_set_verbose();

/**********************************************/
/*        Pocklington certificate             */
/**********************************************/


typedef struct
{
  mpz_ptr _N;             /* the prime number to prove                */
  mpz_ptr _F1;            /* product of the pseudo factorization      */
  mpz_ptr _R1;            /* R1 = (N - 1)/F1                          */
  unsigned long int _a;   /* the witness                              */
  mpz_ptr _sqrt;          /* The sqrt root needed by the certif ...   */
  int     _pow2;          /* Number of power of 2 in F1               */
  int     _allocated;     /* allocated size in words of _dec          */ 
  int     _used;          /* used words in _dec                       */
  mpz_ptr *_dec;          /* pseudo factorization of N-1              */
                          /* increasing first                         */
                          /* F1 = 2^pow2 * PROD dec                   */
} __pock_struct;

typedef __pock_struct *pock_certif_t;

pock_certif_t pock_init (mpz_t N);
void dec_add_ui  (pock_certif_t c, unsigned long int ui);
void dec_add_mpz (pock_certif_t c, mpz_t n);
int  check_pock  (pock_certif_t c);

void finalize_pock(pock_certif_t c);

/**********************************************/
/*            Proof certificate               */
/**********************************************/

typedef struct
{
  mpz_ptr _N;             /* The prime number to prove                */
  char *_lemma;           /* The name of the lemma                    */
} __proof_struct;

typedef __proof_struct *proof_certif_t;

/**********************************************/
/*            Lucas certificate               */
/**********************************************/

typedef struct
{
  mpz_ptr _N;             /* The prime number to prove                */
  unsigned long int _n;   /* N = 2^n - 1                              */
} __lucas_struct;

typedef __lucas_struct *lucas_certif_t;



/**********************************************/
/*            Pre certificate                 */
/**********************************************/


typedef struct
{
  int _kind;               /* kind of certificate:                     */
                           /*       0 : proof; 1 : pock_cerif; 
                                    2: lucas_certif         */
  union {
    pock_certif_t   _pock; 
    proof_certif_t _proof; 
    lucas_certif_t _lucas;
  } _certif;
} __pre_struct;

typedef __pre_struct *pre_certif_t;

pre_certif_t mk_proof_certif(mpz_t N);
pre_certif_t mk_pock_certif(pock_certif_t c);
pre_certif_t mk_lucas_certif(mpz_t N, unsigned long int n);



/**********************************************/
/*              Certificate                   */
/**********************************************/


typedef struct
{
  int _allocated; 
  int _used;
  pre_certif_t *_list;
} __certif_struct;

typedef __certif_struct *certif_t;

void set_proof_limit (unsigned int max);

certif_t init_certif();
int _2_is_in (certif_t lc);
int is_in (mpz_t t, certif_t lc);
void add_pre(pre_certif_t, certif_t lc);


void print_pock_certif(FILE *out, pock_certif_t c);
void print_file(char *filename, char *name, pre_certif_t c, certif_t lc);
pock_certif_t read_file(char * filename, certif_t lc);

void print_lemma(FILE *out, char* name, pre_certif_t p, certif_t lc);
void print_prelude(FILE *out);
#define  __CERTIF_H__
#endif /* __CERTIF_H__ */

