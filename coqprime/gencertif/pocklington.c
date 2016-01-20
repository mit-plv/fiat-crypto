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
#include "ecm.h" 
#include "certif.h"
#include "factorize.h"


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

void usage ()
{
  fprintf(stdout,"usage ; pocklington [-v] [-o file] [-n name] numspec\n");
  fprintf(stdout,"numspec = prime | -next number\n");
  fprintf(stdout,"        = -size number | -proth k n | -lucas number \n");
  fprintf(stdout,"        | -mersenne number | -dec filename\n");
  fflush(stdout);
  exit (-1);    
}

int
main (int argc, char *argv[])
{
  mpz_t t;
  pre_certif_t p;
  pock_certif_t c;
  certif_t lc;
  char *filename;
  int defaultname = 1;
  char *lemmaname;
  lemmaname = "myPrime";
  c = NULL;

  if (argc < 2) {
	usage();
  }

  while (1) { 
    
    if (!strcmp (argv[1], "-v")) {
      my_set_verbose();
      argv++;
      argc--;
    } else if (!strcmp (argv[1], "-o")) {
      if (argc == 2) usage();
      filename = argv[2];
      defaultname = 0;
      argv += 2;
      argc -= 2;
    } else if (!strcmp (argv[1], "-n")) {
      if (argc == 2) usage();
      lemmaname = argv[2];
      argv += 2;
      argc -= 2;
    } else

break;
  }

  mpz_init (t);
  lc = init_certif();
 
  switch (argc) {
  case 2:  
    mpz_set_str (t, argv[1], 0);
    if (!mpz_probab_prime_p (t, 3)) {
      mpz_out_str (stdout, 10, t);
      fprintf(stdout," is not a prime number\n");
      fflush(stdout);
      exit (-1);
    }
    c = pock_certif(t);
    break;

  case 3: 
    if (!strcmp(argv[1], "-size"))
      {
	unsigned long int size;
        gmp_randstate_t randstate;

	size = atoi(argv[2]);
	gmp_randinit_default (randstate);
	gmp_randseed_ui (randstate, get_random_ul ()); 
	mpz_urandomb (t, randstate, 4*size);
	while ( mpz_sizeinbase(t,10) <= size)
	  mpz_urandomb (t, randstate, 4*size);

	while (mpz_sizeinbase(t,10) > size) mpz_tdiv_q_2exp(t,t,1);
	
	mpz_nextprime (t, t);    
	c = pock_certif(t);
	break;
      }

    if (!strcmp (argv[1], "-next"))
      {
	mpz_set_str (t, argv[2], 0);
	mpz_nextprime (t, t);    
	c = pock_certif(t);
	break;
      }

    if (!strcmp(argv[1], "-lucas"))
      {
	unsigned long int n;
        n = atoi(argv[2]);
        /* compute the mersenne number */
	mpz_set_ui(t, 1);mpz_mul_2exp(t, t, n);mpz_sub_ui(t, t, 1);
	fprintf(stdout,"mersenne %lu = ", n);
	mpz_out_str (stdout, 10, t);
	fprintf(stdout, "\n");
        /* Check primality */ 
	if (!mpz_probab_prime_p (t, 3)) {
	  fprintf(stdout,"is not a prime number\n"); fflush(stdout);
	  exit (-1);
	}
        /* build the filename */ 
	if (defaultname) 
	  {
	    int size;
	    size = /*mersenne.v*/ 7 + strlen (argv[2])+1;
	    filename = (char *)malloc(size);
	    strcpy(filename,"lucas");
	    strcat(filename,argv[2]);
	    strncat(filename,".v",2);
	    defaultname = 0;
	  }
	p = mk_lucas_certif(t, n);
	break;
      }

    if (!strcmp(argv[1], "-mersenne"))
      {
	unsigned long int n;
        n = atoi(argv[2]);
        /* compute the mersenne number */
	mpz_set_ui(t, 1);mpz_mul_2exp(t, t, n);mpz_sub_ui(t, t, 1);
	fprintf(stdout,"mersenne %lu = ", n);
	mpz_out_str (stdout, 10, t);
	fprintf(stdout, "\n");
        /* Check primality */ 
	if (!mpz_probab_prime_p (t, 3)) {
	  fprintf(stdout,"is not a prime number\n"); fflush(stdout);
	  exit (-1);
	}
        /* build the filename */ 
	if (defaultname) 
	  {
	    int size;
	    size = /*mersenne.v*/ 10 + strlen (argv[2])+1;
	    filename = (char *)malloc(size);
	    strcpy(filename,"mersenne");
	    strcat(filename,argv[2]);
	    strncat(filename,".v",2);
	    defaultname = 0;
	  }
	c = mersenne_certif(t, n);
	break;
      }

    if (!strcmp(argv[1], "-dec"))
      { 
	c = read_file(argv[2], lc);
	
	if (defaultname)  
	  { 
	    int size;
	    size = strlen (argv[2])+3;
	    filename = (char *)malloc(size);
	    strcpy(filename,argv[2]);
	    strncat(filename,".v",2);
	    defaultname = 0;
	  } 
	fprintf(stdout, "build certificate for\n");
 	mpz_out_str (stdout, 10, c->_N);
 	fprintf(stdout, "\n"); fflush(stdout);
        finalize_pock(c);
	p = mk_pock_certif(c);
 	break;
      }
    else usage();

  case 4:
    if (!strcmp(argv[1], "-proth"))
      {
	unsigned long int n, k;
        k = atoi(argv[2]);
	n = atoi(argv[3]);
	mpz_set_ui (t, k);
	mpz_mul_2exp (t, t, n);
	mpz_add_ui (t, t, 1);
	if (!mpz_probab_prime_p (t, 3)) {
	  mpz_out_str (stdout, 10, t);
	  fprintf(stdout," is not a prime number\n");
	  fflush(stdout);
	  exit (-1);
	}
	c = pock_certif(t);
	break;
      }
	
  default:
    usage();
  }

 if (defaultname) {
   int size, len;
   int filedes[2];
   FILE *fnin;
   FILE *fnout;
   filename = "Prime.v";
   pipe(filedes);
   fnout = fdopen(filedes[1],"w");
   fnin = fdopen(filedes[0], "r");
   fprintf(fnout,"prime");
   size = 5;
   len = mpz_out_str (fnout, 10, t);
   size += len;
   fprintf(fnout,".v"); fflush(fnout);
   size += 2;
   if (size > FILENAME_MAX-1) filename = "Prime.v";
   else {
     filename = (char *)malloc(size+1);
     fread(filename, 1, size, fnin);
     filename[size] = '\0';
   }
   fclose(fnin);
   fclose(fnout); 
 }
 
 if (c != NULL) {
   p = mk_pock_certif(c); 
   extend_lc (lc, c, 0, 0);  
 } 

 print_file(filename, lemmaname, p, lc);

 fprintf(stdout,"\n");fflush(stdout);
 mpz_clear(t); 
 exit (0);
}
