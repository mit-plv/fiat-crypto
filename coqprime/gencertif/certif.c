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
#include <unistd.h>
#include "gmp.h"
#include "certif.h"

#define ALLOCSIZE 20

int flag_verbose = 0;

void my_set_verbose ()
{
  flag_verbose = 1;
}

pock_certif_t pock_init (mpz_t N)
{
  pock_certif_t res;
  
  res = (pock_certif_t)malloc(sizeof(__pock_struct));
  res->_N = malloc(sizeof(mpz_t));
  mpz_init_set (res->_N, N);
  res->_F1 = malloc(sizeof(mpz_t));
  mpz_init_set_ui (res->_F1, 1);
  res->_R1 = malloc(sizeof(mpz_t));
  mpz_init_set (res->_R1, N);
  mpz_sub_ui (res->_R1, res->_R1, 1);
  res->_sqrt = malloc(sizeof(mpz_t));
  mpz_init_set_ui (res->_sqrt, 1);
  res->_a = 0;
  res->_pow2 = 0;
  res->_allocated = ALLOCSIZE;
  res->_used = 0;
  res->_dec = (mpz_ptr *)malloc(sizeof(mpz_ptr) * ALLOCSIZE);
  return res;
}

void realloc_dec (pock_certif_t c)
{
  mpz_ptr *ndec;
  mpz_ptr *odec;
  int i, alloc,used;

  used = c->_used;
  alloc = 2 * c->_allocated;
  odec = c->_dec;
  ndec = (mpz_ptr *)malloc(sizeof(mpz_ptr) * alloc);
  
  for(i=0; i<used; i++) ndec[i] = odec[i];
  
  c->_allocated = alloc;
  c->_dec = ndec;
  return;
}

void dec_add_ui (pock_certif_t c, unsigned long int ui)
{
  mpz_ptr mpz_ui;
  int i,j, used;
  mpz_ptr * p; 

  if (ui == 2) {
    c->_pow2 ++;
    mpz_mul_ui(c->_F1, c->_F1, 2);
    mpz_tdiv_q_ui(c->_R1, c->_R1, 2);

    return;
  }

  used = c->_used; 
    
  /* realloc if necessary */
  if (c->_allocated <= used) realloc_dec(c);
  
  /* Add ui in the dec, smaller elements first */
  p = c->_dec;
  i = 0;
  while( (i < used) && (mpz_cmp_ui (p[i], ui) <= 0)) i++;
  for(j = used - 1; i <= j; j --) p[j+1]=p[j];
  mpz_ui = malloc(sizeof(mpz_t));
  mpz_init_set_ui(mpz_ui, ui);
  p[i] = mpz_ui;
  c->_used = used+1;

  /* Update the value of F1 and R1 */
  mpz_mul_ui(c->_F1, c->_F1, ui);
  mpz_tdiv_q_ui(c->_R1, c->_R1, ui);

  return;
}


void dec_add_mpz (pock_certif_t c, mpz_t n)
{
  mpz_ptr new_n;
  int i,j, used;
  mpz_ptr * p; 

  if (mpz_cmp_ui(n, 2) == 0) {
    c->_pow2 ++;
    mpz_mul_ui(c->_F1, c->_F1, 2);
    mpz_tdiv_q_ui(c->_R1, c->_R1, 2);

    return;
  }

  used = c->_used; 
    
  /* realloc if necessary */
  if (c->_allocated <= used) realloc_dec(c);
  
  /* Add n in the dec, smaller elements first */
  p = c->_dec;
  i = 0;
  while( (i < used) && (mpz_cmp (p[i], n) <= 0)) i++;
  for(j = used - 1; i <= j; j --) p[j+1]=p[j];
  new_n = malloc(sizeof(mpz_t));
  mpz_init_set(new_n, n);
  p[i] = new_n;
  c->_used = used+1;

  /* Update the value of F1 and R1 */
  mpz_mul(c->_F1, c->_F1, n);
  mpz_tdiv_q(c->_R1, c->_R1, n);

  return;
}

int check_mpz(mpz_t N, mpz_t F1, mpz_t R1)
{
  mpz_t r,sum;
  int res;

  mpz_init (r);
  mpz_init_set (sum, F1);      /* sum = F1                             */
  mpz_mul_ui (sum, sum, 2);    /* sum = 2 * F1                         */
  mpz_mod (r, R1, sum);        /* r = R1 mod (2 * F1)                  */
  mpz_add (sum, sum, r);       /* sum = 2*F1 + r                       */
  mpz_add_ui (sum, sum, 1);    /* sum = 2*F1 + r + 1                   */
  mpz_mul (sum, sum, F1);      /* sum = 2*F1^2 + (r+1)*F1              */
  mpz_add (sum, sum, r);       /* sum = 2*F1^2 + (r+1)*F1 + r          */
  mpz_mul (sum, sum, F1);      /* sum = 2*F1^3 + (r+1)*F1^2 + r*F1     */
  mpz_add_ui (sum, sum, 1);    /* sum = 2*F1^3 + (r+1)*F1^2 + r*F1 + 1 */
                               /*     = (F1+1)(2F1^2+(r-1)F1 + 1       */
 
  res = mpz_cmp (N, sum) <= 0;

  mpz_clear(r);
  mpz_clear(sum);

  return res;
}


int check_pock (pock_certif_t c)
{
  return (check_mpz (c->_N, c->_F1, c->_R1));
}


void simplify_certif(pock_certif_t c)
{
  mpz_t N, F1, R1, pi;
  int used, i, j;
  mpz_ptr * ptr; 


  mpz_init(pi);
  mpz_init_set(N,c->_N);
  mpz_init_set(F1,c->_F1);
  mpz_init_set(R1,c->_R1);
  
  used = c->_used;
  i = used - 1;
  ptr = c->_dec;

  while (i >= 0){
    mpz_set (pi, ptr[i]);
    mpz_tdiv_q (F1, F1, pi);
    mpz_mul (R1, R1, pi);

    if (check_mpz (N, F1, R1)) 
      {  
	mpz_set(c->_F1, F1);
	mpz_set(c->_R1, R1);
	for(j = i + 1; j < used ; j++) ptr[j-1] = ptr[j];
	used--;
	c->_used = used;
      }
    else 
      {	
	mpz_set (F1, c->_F1);
	mpz_set (R1, c->_R1);
	while(i > 0 && (mpz_cmp(ptr[i-1], ptr[i]) == 0)) i--;
      }
    i--;
  }


  mpz_clear (N);
  mpz_clear (F1);
  mpz_clear (R1);
  
  return;
} 

void simplify_small_certif(pock_certif_t c)
{
  mpz_t N, F1, R1, pi;
  int used, j;
  mpz_ptr * ptr; 


  mpz_init(pi);
  mpz_init_set(N,c->_N);
  mpz_init_set(F1,c->_F1);
  mpz_init_set(R1,c->_R1);
  
  used = c->_used;
 
  ptr = c->_dec;

  while (0 <used){
    mpz_set (pi, ptr[0]);
    mpz_tdiv_q (F1, F1, pi);
    mpz_mul (R1, R1, pi);

    if (check_mpz (N, F1, R1)) 
      {  /* remove pi */
	mpz_set(c->_F1, F1);
	mpz_set(c->_R1, R1);
	for(j = 1; j < used ; j++) ptr[j-1] = ptr[j];
	used--;
	c->_used = used;
      }
    else break;
    
  }


  mpz_clear (N);
  mpz_clear (F1);
  mpz_clear (R1);
  simplify_certif(c);
  
  return;
}
 

int is_witness(unsigned long int a, pock_certif_t c)
{
  int i, size, res;
  mpz_t N, N1, exp, aux, mpza;
  mpz_ptr * ptr;

  /*  if (flag_verbose) printf("is witness a = %lu ",a); */
  mpz_init(exp);
  mpz_init(aux);
  mpz_init (N1);

  mpz_init_set (N, c->_N);
  mpz_init_set_ui (mpza, a);
  mpz_sub_ui (N1, N, 1);

  mpz_powm (aux, mpza, N1, N);
  
  if (mpz_cmp_ui (aux, 1) != 0) {
    mpz_clear(exp);
    mpz_clear(aux);
    mpz_clear(N);
    mpz_clear(N1);
    mpz_clear(mpza);
    return 0;
  }

  ptr = c->_dec;
  size = c->_used;
  res = 1;
  
  if (c->_pow2 > 0) {
    mpz_tdiv_q_ui(exp, N1, 2);
    mpz_powm (aux, mpza, exp, N);
    mpz_sub_ui(aux, aux, 1);
    mpz_gcd (aux, aux, N);
    if  (mpz_cmp_ui(aux, 1) != 0) res = 0;
  }
  
  i = 0;
  
  while (i < size && res) {
    if (flag_verbose) {
      mpz_out_str (stdout, 10,ptr[i]);
      printf(" ");
    }
    mpz_tdiv_q(exp, N1, ptr[i]);
    mpz_powm (aux, mpza, exp, N);
    mpz_sub_ui(aux, aux, 1);
    mpz_gcd (aux, aux, N);
    if  (mpz_cmp_ui(aux, 1) != 0) res = 0;
    while ((i < size - 1) && (mpz_cmp (ptr[i], ptr[i+1]) == 0)) i++;
    i++;
  }

  mpz_clear(exp);
  mpz_clear(aux);
  mpz_clear(N);
  mpz_clear(N1);
  mpz_clear(mpza);

  if (flag_verbose) printf("\n");
    
  return res;
}


void set_witness(pock_certif_t c)
{
  unsigned long int a = 2;

  while (!is_witness(a,c)) a++;
  
  c->_a = a;

  return;
}
 
void set_sqrt(pock_certif_t c)
{
  mpz_t s;
  mpz_t r;
  mpz_t aux;

  mpz_init (s);
  mpz_init (r);
  mpz_init_set (aux, c->_F1);
  mpz_mul_ui(aux, aux, 2);
  mpz_tdiv_qr (s, r, c->_R1, aux);
  if (mpz_cmp_ui (s, 0) != 0) {
    mpz_mul(r, r, r);
    mpz_mul_ui(s, s, 8);
    mpz_sub(aux, r, s);
    if (mpz_cmp_ui (aux, 0) > 0) mpz_sqrt(c->_sqrt, aux);
  }

  mpz_clear (s);
  mpz_clear (r);
  mpz_clear (aux);
  return;
}


void finalize_pock(pock_certif_t c)
{
  simplify_certif(c);
  set_witness(c);
  set_sqrt(c);

  return;
}
/**********************************************/
/*            Pre certificate                 */
/**********************************************/

char* mk_name(mpz_t t) 
{
  int size;
  int filedes[2];
  char * name;
  FILE *fnin;
  FILE *fnout;
  pipe(filedes);
  fnout = fdopen(filedes[1],"w");
  fnin = fdopen(filedes[0], "r");
  fprintf(fnout,"prime");
  size = 5;
  size += mpz_out_str (fnout, 10, t);
  fflush(fnout);
  name = (char *)malloc(size+1);
  fread(name, 1, size, fnin);
  name[size] = '\0';
  fclose(fnin);
  fclose(fnout);
  return name;
}


pre_certif_t mk_proof_certif(mpz_t N)
{
  proof_certif_t proof;
  pre_certif_t pre;

  proof = (proof_certif_t)malloc(sizeof(__proof_struct));
  proof->_N = malloc(sizeof(mpz_t));
  mpz_init_set (proof->_N, N);
  proof->_lemma = (char *)mk_name(N);

  pre = (pre_certif_t)malloc(sizeof(__pre_struct));
  pre->_kind = 0;
  pre->_certif._proof = proof;

  return pre;
}
  
pre_certif_t mk_lucas_certif(mpz_t N, unsigned long int n)
{
  lucas_certif_t lucas;
  pre_certif_t pre;

  lucas = (lucas_certif_t)malloc(sizeof(__lucas_struct));
  lucas->_N = malloc(sizeof(mpz_t));
  mpz_init_set (lucas->_N, N);
  lucas->_n = n;

  pre = (pre_certif_t)malloc(sizeof(__pre_struct));
  pre->_kind = 2;
  pre->_certif._lucas = lucas;

  return pre;
}
  
  
pre_certif_t mk_pock_certif(pock_certif_t c) 
{
  pre_certif_t pre;

  pre = (pre_certif_t)malloc(sizeof(__pre_struct));
  pre->_kind = 1;
  pre->_certif._pock = c;
  return pre;
}

mpz_ptr get_N (pre_certif_t pre)
{
  switch (pre->_kind) {
  case 0 : return (pre->_certif._proof->_N);
  case 1 : return (pre->_certif._pock->_N);
  case 2 : return (pre->_certif._lucas->_N);
  default : exit (1);
  }
}



/**********************************************/
/*              Certificate                   */
/**********************************************/


certif_t init_certif()
{
  certif_t res;

  res = malloc(sizeof(__certif_struct));
  res->_allocated = ALLOCSIZE;
  res->_used = 0;
  res->_list = (pre_certif_t *)malloc(sizeof(pre_certif_t)*ALLOCSIZE);
 
  return res;
}


void realloc_list(certif_t  lc)
{
  int i, size;
  pre_certif_t * nlist, * olist;

  size = lc->_allocated;
  olist = lc->_list;
  nlist = (pre_certif_t *)malloc(sizeof(pre_certif_t)*2*size);

  for(i = 0; i < size; i++) nlist[i] = olist[i];

  lc->_allocated = 2*size;
  lc->_list = nlist;

  return;
}

int _2_is_in (certif_t lc)
{
   
  if (lc->_used == 0) return 0; 

  return (mpz_cmp_ui(get_N(lc->_list[0]), 2) == 0);

}
  
int is_in (mpz_t t, certif_t lc)
{
  pre_certif_t * ptr;
  int i, test;

  ptr = lc->_list;

  for(i = lc->_used - 1; i >= 0; i--) {
    test = mpz_cmp(t, get_N(ptr[i]));
    if (test == 0) return 1;
    if (test > 0) break;
  }

  return 0;
}

  
void add_pre(pre_certif_t pre, certif_t lc)
{
  int i, j, used;
  mpz_ptr N;
  pre_certif_t * ptr;

  if (lc->_used == lc->_allocated) realloc_list(lc);

  i = 0;
  ptr = lc->_list;
  N = get_N(pre);
  used = lc->_used;

  while(i < used && mpz_cmp(get_N(ptr[i]), N) <= 0 ) i++;

  for (j = used-1;j >= i; j--) ptr[j+1] = ptr[j];

  ptr[i] = pre;
  lc->_used = used + 1;

  return;
}



/**********************************************/
/*              I/O on file                   */
/**********************************************/

void print_pock_certif(FILE *out, pock_certif_t c)
{
  int i, pow, size;
  mpz_ptr *p;
  mpz_t last;
  
  size = c->_used;
  p = c->_dec;

  fprintf(out, "(Pock_certif "); mpz_out_str (out, 10, c->_N);
  fprintf(out, " %lu ", c->_a);

  fprintf(out, "("); 
    
  if (size > 0) {
    mpz_init_set(last,p[size-1]);
    pow = 1;
    
    for(i = size - 2; i >= 0; i--) {
      if (mpz_cmp(last,p[i]) == 0) pow++;
      else {
	fprintf(out,"(");
	mpz_out_str (out, 10, last);
	fprintf(out,", %i)::", pow);
	mpz_set(last,p[i]);
	pow = 1;
      }
    }
    fprintf(out,"(");
    mpz_out_str (out, 10, last);
    fprintf(out,", %i)::", pow);
  } 
    
  fprintf(out,"(2,%i)::nil) ", c->_pow2);
  mpz_out_str (out, 10, c->_sqrt);
  fprintf(out,")");
  
}


void print_pre_certif(FILE *out, pre_certif_t pre)
{
  mpz_ptr N;
  N = get_N(pre);

  switch (pre->_kind) 
    {
    case 0 :
      fprintf(out, "(Proof_certif ");mpz_out_str (out, 10, N);
      fprintf(out, " %s)", pre->_certif._proof->_lemma);
      break;
    case 1: 
      print_pock_certif(out, pre->_certif._pock);
      break;
    case 2:
      fprintf(out, "(Lucas_certif ");mpz_out_str (out, 10, N);
      fprintf(out, " %lu)", pre->_certif._lucas->_n); 
    default : break;
    }
  return;
}

void print_lc(FILE *out, certif_t lc)
{
  int i,size;
  pre_certif_t *p;

  size = lc->_used;
  p = lc->_list;
 
  fprintf(out, "    (");
  for(i=size-1; i >= 0; i--) {
    print_pre_certif(out, p[i]);
    fprintf(out, " ::\n         ");
  }
  fprintf(out, " nil)");
 
}

void print_lemma(FILE *out, char *name, pre_certif_t p, certif_t lc)
{

  fprintf(out, "Lemma %s", name); 
  fprintf(out, " : prime ");mpz_out_str (out, 10, get_N(p));
  fprintf(out, ".\n");
  fprintf(out, "Proof.\n");
  fprintf(out, " apply (Pocklington_refl\n         ");

  print_pre_certif(out, p);
  fprintf(out, "\n    ");
 

  print_lc(out, lc);
  fprintf(out, ").\n");
  fprintf(out," exact_no_check (refl_equal true).\n");
  fprintf(out,"Qed.\n\n");
}


void print_prelude(FILE *out)
{
  fprintf(out,"Require Import List.\n");
  fprintf(out,"Require Import ZArith.\n");
  fprintf(out,"Require Import ZAux.\n\n");
  fprintf(out,"Require Import PocklingtonCertificat.\n\n");

  fprintf(out,"Open Local Scope positive_scope.\n\n");

  fprintf(out,"Set Virtual Machine.\n");
}


void print_file(char *filename, char *name, pre_certif_t p, certif_t lc)
{
  FILE * out; 

  out = fopen(filename,"w+");

  fprintf(out, "Require Import PocklingtonRefl.\n\n"); 

  fprintf(out,"Set Virtual Machine.\n");
  
  fprintf(out,"Open Local Scope positive_scope.\n\n");

  print_lemma(out, name, p, lc);

  fclose(out);

  return;
}

pock_certif_t read_file(char * filename, certif_t lc)
{
  FILE * in;
  pock_certif_t c;
  mpz_t n, q, r;
  int i;

  in = fopen(filename, "r");

  if (in == NULL) {
    fprintf(stdout,"Invalid file name\n");
    fflush(stdout);
    exit(2);
  }

  mpz_init(n);
  mpz_init(q);
  mpz_init(r);

  mpz_inp_str(n,in,10);
  c = pock_init(n);
  mpz_set(q, n);
  mpz_sub_ui (q, q, 1);

  
  while(fgetc(in) != EOF){
    if (mpz_inp_str(n,in,10)){
      mpz_out_str (stdout, 10, n);
      fprintf(stdout, "\n"); 
	
      mpz_tdiv_qr(q, r, q, n);

      if (mpz_cmp_ui (r, 0) != 0) {
	mpz_out_str (stdout, 10, n);
	fprintf(stdout, " is not a divisor\n"); 
	fflush(stdout);
	exit(1);
      }

      if (!mpz_probab_prime_p (n, 3)) {
	mpz_out_str (stdout, 10, n);
	fprintf(stdout, " is not prime \n"); 
	fflush(stdout);
	exit(1);
      }
	
	
      dec_add_mpz(c, n);
      i = getc(in);
      if (i=='*') add_pre(mk_proof_certif(n),lc);
      else ungetc(i, in);
    } else { break;
      
      fprintf(stdout,"\nSyntax error\n");
      fflush(stdout);
      exit(1);
    }
  }

  if (!check_pock(c)) {
    fprintf(stdout, "Decomposition to small \n"); 
    fflush(stdout);
    exit (1);
    
  }

  fclose(in); 

  return c;
}


