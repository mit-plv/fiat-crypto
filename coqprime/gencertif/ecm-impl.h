/* ecm-impl.h - header file for libecm
 
  Copyright 2001, 2002, 2003, 2004, 2005 Paul Zimmermann and Alexander Kruppa.
 
  This program is free software; you can redistribute it and/or modify it
  under the terms of the GNU General Public License as published by the
  Free Software Foundation; either version 2 of the License, or (at your
  option) any later version.
 
  This program is distributed in the hope that it will be useful, but WITHOUT
  ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
  more details.
 
  You should have received a copy of the GNU General Public License along
  with this program; see the file COPYING.  If not, write to the Free
  Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
  02111-1307, USA.
*/

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

#define ECM_STDOUT __ecm_stdout
#define ECM_STDERR __ecm_stderr
extern FILE *ECM_STDOUT, *ECM_STDERR;

/* Warnings about unused parameters by gcc can be suppressed by prefixing 
   parameter with ATTRIBUTE_UNUSED when parameter can't be removed, i.e. 
   for interface consistency reasons */
#ifdef __GNUC__
#define ATTRIBUTE_UNUSED __attribute__ ((unused))
#define ATTRIBUTE_CONST __attribute__ ((const))
#else
#define ATTRIBUTE_UNUSED
#define ATTRIBUTE_CONST
#endif

#ifdef __GNUC__
#define INLINE inline
#else
#define INLINE
#endif

/* if POLYEVALTELLEGEN is defined, use polyeval_tellegen(),
   otherwise use polyeval() */
#define POLYEVALTELLEGEN

/* use Kronecker-Scho"nhage's multiplication */
#define KS_MULTIPLY

/* define top-level multiplication */
#define KARA 2
#define TOOM3 3
#define TOOM4 4
#define KS 5

/* compile with -DMULT=2 to override default */
#ifndef MULT
#ifdef KS_MULTIPLY
#define MULT KS
#else
#define MULT TOOM4
#endif
#endif

#ifdef POLYEVALTELLEGEN
#define USE_SHORT_PRODUCT
#endif

/* Use George Woltman's GWNUM library */
/* Should be defined via -DHAVE_GWNUM by Makefile
#define HAVE_GWNUM
*/

#ifdef HAVE_GWNUM
/* Only Fermat numbers with exponent >= GWTHRESHOLD are multiplied with 
   Woltman's DWT */
#define GWTHRESHOLD 1024
#endif

#if WANT_ASSERT
#include <assert.h>
#define ASSERT(expr)   assert (expr)
#else
#define ASSERT(expr)   do {} while (0)
#endif

/* thresholds */
#ifndef MUL_KARATSUBA_THRESHOLD
#define MUL_KARATSUBA_THRESHOLD 32
#endif

#ifndef DIV_DC_THRESHOLD
#define DIV_DC_THRESHOLD    (3 * MUL_KARATSUBA_THRESHOLD)
#endif

#define MPZMOD_THRESHOLD_DEFAULT (3 * DIV_DC_THRESHOLD / 2)
#define REDC_THRESHOLD_DEFAULT   (2 * DIV_DC_THRESHOLD)

/* base2mod is used when size(2^n+/-1) <= BASE2_THRESHOLD * size(cofactor) */
#define BASE2_THRESHOLD 1.4

/* default number of probable prime tests */
#define PROBAB_PRIME_TESTS 1

/* kronecker_schonhage() is used instead of toomcook4()
   when bitsize(poly) >= KS_MUL_THRESHOLD */
#define KS_MUL_THRESHOLD  1e6
/* same for median product */
#define KS_TMUL_THRESHOLD 8e5

#define ABS(x) ((x) >= 0 ? (x) : -(x))

/* getprime */
#define WANT_FREE_PRIME_TABLE(p) (p < 0.0)
#define FREE_PRIME_TABLE -1.0

#define MOD_PLAIN 0
#define MOD_BASE2 1
#define MOD_MODMULN 2
#define MOD_REDC 3

/* Various logging levels */
/* OUTPUT_ALWAYS means print always, regardless of verbose value */
#define OUTPUT_ALWAYS 0
/* OUTPUT_NORMAL means print during normal program execution */
#define OUTPUT_NORMAL 1
/* OUTPUT_VERBOSE means print if the user requested more verbosity */
#define OUTPUT_VERBOSE 2
/* OUTPUT_RESVERBOSE is for printing residues (after stage 1 etc) */
#define OUTPUT_RESVERBOSE 3
/* OUTPUT_DEVVERBOSE is for printing internal parameters (for developers) */
#define OUTPUT_DEVVERBOSE 4
/* OUTPUT_TRACE is for printing trace data, produces lots of output */
#define OUTPUT_TRACE 5
/* OUTPUT_ERROR is for printing error messages */
#define OUTPUT_ERROR -1

typedef mpz_t mpres_t;

typedef mpz_t* listz_t;

typedef struct
{
  mpres_t x;
  mpres_t y;
} __point_struct;
typedef __point_struct point;

typedef struct
{
  mpres_t x;
  mpres_t y;
  mpres_t A;
} __curve_struct;
typedef __curve_struct curve;

typedef struct
{
  unsigned int size_fd; /* How many entries .fd has, always nr * (S+1) */
  unsigned int nr;     /* How many separate progressions there are */
  unsigned int next;   /* From which progression to take the next root */
  unsigned int S;      /* Degree of the polynomials */
  unsigned int dsieve; /* Values not coprime to dsieve are skipped */
  unsigned int rsieve; /* Which residue mod dsieve current .next belongs to */
  int dickson_a;       /* Parameter for Dickson polynomials */
  point *fd;
  mpres_t *T;          /* For temp values. FIXME: should go! */
  curve *X;            /* The curve the points are on */
} __ecm_roots_state;
typedef __ecm_roots_state ecm_roots_state;

/* WARNING: it is important that the order of fields matches that
   of ecm_roots_state. See comment in pm1.c:pm1_rootsF. */
typedef struct
{
  unsigned int size_fd; /* How many entries .fd has, always nr * (S+1) */
  unsigned int nr;     /* How many separate progressions there are */
  unsigned int next;   /* From which progression to take the next root */
  unsigned int S;      /* Degree of the polynomials */
  unsigned int dsieve; /* Values not coprime to dsieve are skipped */
  unsigned int rsieve; /* Which residue mod dsieve current .next belongs to */
  int dickson_a;       /* Parameter for Dickson polynomials */
  mpres_t *fd;
  int invtrick;
} __pm1_roots_state;
typedef __pm1_roots_state pm1_roots_state;

typedef struct
{
  unsigned int size_fd; /* How many entries .fd has, always nr * (S+1) */
  unsigned int nr;     /* How many separate progressions there are */
  unsigned int next;   /* From which progression to take the next root */
  unsigned int S;      /* Degree of the polynomials */
  unsigned int dsieve; /* Values not coprime to dsieve are skipped */
  unsigned int rsieve; /* Which residue mod dsieve current .next belongs to */
  point *fd;           /* for S != 1 */
  mpres_t tmp[4];      /* for S=1 */
  unsigned int d;      /* Step size for computing roots of G */
} __pp1_roots_state;
typedef __pp1_roots_state pp1_roots_state;

typedef struct
{
  int alloc;
  int degree;
  listz_t coeff;
} __polyz_struct;
typedef __polyz_struct polyz_t[1];

typedef struct 
{
  int repr;           /* 0: plain modulus, possibly normalized
                         1: base 2 number
                         2: MODMULN
                         3: REDC representation */
  int bits;           /* in case of a base 2 number, 2^k[+-]1, bits = [+-]k
                         in case of MODMULN or REDC representation, nr. of 
                         bits b so that 2^b > orig_modulus and 
                         mp_bits_per_limb | b */
  int Fermat;         /* If repr = 1 (base 2 number): If modulus is 2^(2^m)+1, 
                         i.e. bits = 2^m, then Fermat = 2^m, 0 otherwise.
                         If repr != 1, undefined */
  mp_limb_t Nprim;    /* For MODMULN */
  mpz_t orig_modulus; /* The original modulus */
  mpz_t aux_modulus;  /* The auxiliary modulus value (i.e. normalized 
                         modulus, or -1/N (mod 2^bits) for REDC */
  mpz_t multiple;     /* The smallest multiple of N that is larger or
			 equal to 2^bits for REDC/MODMULN */
  mpz_t R2, R3;       /* For MODMULN and REDC, R^2 and R^3 (mod orig_modulus), 
                         where R = 2^bits. */
  mpz_t temp1, temp2; /* Temp values used during multiplication etc. */
} __mpmod_struct;
typedef __mpmod_struct mpmod_t[1];

#if defined (__cplusplus)
extern "C" {
#endif  

/* getprime.c */
#define getprime __ECM(getprime)
double   getprime       (double);

/* pm1.c */
#define pm1_rootsF __ECM(pm1_rootsF)
int     pm1_rootsF       (mpz_t, listz_t, unsigned int, unsigned int,
			  unsigned int, mpres_t *, listz_t, int, mpmod_t);
#define pm1_rootsG_init __ECM(pm1_rootsG_init)
pm1_roots_state* pm1_rootsG_init  (mpres_t *, mpz_t, unsigned int,
				   unsigned int, int, mpmod_t);
#define pm1_rootsG __ECM(pm1_rootsG)
int     pm1_rootsG       (mpz_t, listz_t, unsigned int, pm1_roots_state *, 
                          listz_t, mpmod_t);
#define pm1_rootsG_clear __ECM(pm1_rootsG_clear)
void    pm1_rootsG_clear (pm1_roots_state *, mpmod_t);

/* bestd.c */
#define phi __ECM(phi)
unsigned long phi (unsigned long);
#define bestD __ECM(bestD)
int     bestD (mpz_t, mpz_t, int, unsigned int *, unsigned int *, 
               unsigned int *, unsigned int *, mpz_t);

/* ecm.c */
#define choose_S __ECM(choose_S)
int choose_S (mpz_t);

/* ecm2.c */
#define ecm_rootsF __ECM(ecm_rootsF)
int     ecm_rootsF       (mpz_t, listz_t, unsigned int, unsigned int,
			  unsigned int, curve *, int, mpmod_t);
#define ecm_rootsG_init __ECM(ecm_rootsG_init)
ecm_roots_state* ecm_rootsG_init (mpz_t, curve *, mpz_t, unsigned int,
		  unsigned int, unsigned int, unsigned int, int, mpmod_t);
#define ecm_rootsG __ECM(ecm_rootsG)
int     ecm_rootsG       (mpz_t, listz_t, unsigned int, ecm_roots_state *, 
                          mpmod_t);
#define ecm_rootsG_clear __ECM(ecm_rootsG_clear)
void    ecm_rootsG_clear (ecm_roots_state *, int, mpmod_t);
void init_roots_state   (ecm_roots_state *, int, unsigned int, unsigned int, 
                         double);

/* lucas.c */
#define pp1_mul_prac __ECM(pp1_mul_prac)
void  pp1_mul_prac     (mpres_t, unsigned long, mpmod_t, mpres_t, mpres_t,
                        mpres_t, mpres_t, mpres_t);

/* pp1.c */
#define pp1_rootsF __ECM(pp1_rootsF)
int   pp1_rootsF       (listz_t, unsigned int, unsigned int, unsigned int,
                        mpres_t *, listz_t, int, mpmod_t);
#define pp1_rootsG __ECM(pp1_rootsG)
int   pp1_rootsG   (listz_t, unsigned int, pp1_roots_state *, mpmod_t, mpres_t*);
#define pp1_rootsG_init __ECM(pp1_rootsG_init)
pp1_roots_state* pp1_rootsG_init (mpres_t*, mpz_t, unsigned int,
                                  unsigned int, int, mpmod_t);
#define pp1_rootsG_clear __ECM(pp1_rootsG_clear)
void  pp1_rootsG_clear (pp1_roots_state *, mpmod_t);

/* stage2.c */
#define stage2 __ECM(stage2)
int          stage2     (mpz_t, void *, mpmod_t, mpz_t, mpz_t, unsigned int,
                         int, int, int, char *);
#define init_progression_coeffs __ECM(init_progression_coeffs)
listz_t init_progression_coeffs (mpz_t, unsigned int, unsigned int,
                         unsigned int, unsigned int, unsigned int, int);

/* listz.c */
#define list_mul_mem __ECM(list_mul_mem)
int          list_mul_mem (unsigned int);
#define init_list __ECM(init_list)
listz_t      init_list  (unsigned int);
#define clear_list __ECM(clear_list)
void         clear_list (listz_t, unsigned int);
#define list_inp_raw __ECM(list_inp_raw)
int          list_inp_raw (listz_t, FILE *, unsigned int);
#define list_out_raw __ECM(list_out_raw)
int          list_out_raw (FILE *, listz_t, unsigned int);
#define print_list __ECM(print_list)
void         print_list (listz_t, unsigned int);
#define list_set __ECM(list_set)
void         list_set   (listz_t, listz_t, unsigned int);
#define list_revert __ECM(list_revert)
void         list_revert (listz_t, unsigned int);
#define list_swap __ECM(list_swap)
void         list_swap  (listz_t, listz_t, unsigned int);
#define list_mod __ECM(list_mod)
void         list_mod   (listz_t, listz_t, unsigned int, mpz_t);
#define list_add __ECM(list_add)
void         list_add   (listz_t, listz_t, listz_t, unsigned int);
#define list_sub __ECM(list_sub)
void         list_sub   (listz_t, listz_t, listz_t, unsigned int);
#define list_mul_z __ECM(list_mul_z)
void         list_mul_z (listz_t, listz_t, mpz_t, unsigned int, mpz_t);
#define list_gcd __ECM(list_gcd)
int          list_gcd   (mpz_t, listz_t, unsigned int, mpz_t);
#define list_zero __ECM(list_zero)
void         list_zero  (listz_t, unsigned int);
#define list_mul_high __ECM(list_mul_high)
void      list_mul_high (listz_t, listz_t, listz_t, unsigned int, listz_t);
#define karatsuba __ECM(karatsuba)
void         karatsuba  (listz_t, listz_t, listz_t, unsigned int, listz_t);
#define list_mulmod __ECM(list_mulmod)
void        list_mulmod (listz_t, listz_t, listz_t, listz_t, unsigned int,
                         listz_t, mpz_t);
#define list_invert __ECM(list_invert)
int         list_invert (listz_t, listz_t, unsigned int, mpz_t, mpmod_t);
#define PolyFromRoots __ECM(PolyFromRoots)
void      PolyFromRoots (listz_t, listz_t, unsigned int, listz_t, mpz_t);
#define PolyFromRoots_Tree __ECM(PolyFromRoots_Tree)
int       PolyFromRoots_Tree (listz_t, listz_t, unsigned int, listz_t, int, 
                         mpz_t, listz_t*, FILE*, unsigned int);
#define PrerevertDivision __ECM(PrerevertDivision)
int   PrerevertDivision (listz_t, listz_t, listz_t, unsigned int, listz_t,
			 mpz_t);
#define PolyInvert __ECM(PolyInvert)
void         PolyInvert (listz_t, listz_t, unsigned int, listz_t, mpz_t);
#define RecursiveDivision __ECM(RecursiveDivision)
void  RecursiveDivision (listz_t, listz_t, listz_t, unsigned int,
                         listz_t, mpz_t, int);

/* polyeval.c */
#define polyeval __ECM(polyeval)
void polyeval (listz_t, unsigned int, listz_t*, listz_t, mpz_t, unsigned int);
#define polyeval_tellegen __ECM(polyeval_tellegen)
int polyeval_tellegen (listz_t, unsigned int, listz_t*, listz_t,
		       unsigned int, listz_t, mpz_t, char *);

/* toomcook.c */
#define toomcook3 __ECM(toomcook3)
void          toomcook3 (listz_t, listz_t, listz_t, unsigned int, listz_t);
#define toomcook4 __ECM(toomcook4)
void          toomcook4 (listz_t, listz_t, listz_t, unsigned int, listz_t);

/* ks-multiply.c */
#define kronecker_schonhage __ECM(kronecker_schonhage)
int kronecker_schonhage (listz_t, listz_t, listz_t, unsigned int, listz_t);
#define TMulKS __ECM(TMulKS)
int TMulKS     (listz_t, unsigned int, listz_t, unsigned int, listz_t,
                unsigned int, mpz_t, int);
#define ks_wrapmul_m __ECM(ks_wrapmul_m)
unsigned int ks_wrapmul_m (unsigned int, unsigned int, mpz_t);
#define ks_wrapmul __ECM(ks_wrapmul)
unsigned int ks_wrapmul (listz_t, unsigned int, listz_t, unsigned int,
                         listz_t, unsigned int, mpz_t);

/* mpmod.c */
#define isbase2 __ECM(isbase2)
int isbase2 (mpz_t, double);
#define mpmod_init __ECM(mpmod_init)
void mpmod_init (mpmod_t, mpz_t, int);
#define mpmod_init_MPZ __ECM(mpmod_init_MPZ)
void mpmod_init_MPZ (mpmod_t, mpz_t);
#define mpmod_init_BASE2 __ECM(mpmod_init_BASE2)
int mpmod_init_BASE2 (mpmod_t, int, mpz_t);
#define mpmod_init_MODMULN __ECM(mpmod_init_MODMULN)
void mpmod_init_MODMULN (mpmod_t, mpz_t);
#define mpmod_init_REDC __ECM(mpmod_init_REDC)
void mpmod_init_REDC (mpmod_t, mpz_t);
#define mpmod_clear __ECM(mpmod_clear)
void mpmod_clear (mpmod_t);
#define mpres_pow __ECM(mpres_pow)
void mpres_pow (mpres_t, mpres_t, mpres_t, mpmod_t);
#define mpres_ui_pow __ECM(mpres_ui_pow)
void mpres_ui_pow (mpres_t, unsigned int, mpres_t, mpmod_t);
#define mpres_mul __ECM(mpres_mul)
void mpres_mul (mpres_t, mpres_t, mpres_t, mpmod_t);
#define mpres_div_2exp __ECM(mpres_div_2exp)
void mpres_div_2exp (mpres_t, mpres_t, unsigned int, mpmod_t);
#define mpres_add_ui __ECM(mpres_add_ui)
void mpres_add_ui (mpres_t, mpres_t, unsigned int, mpmod_t);
#define mpres_add __ECM(mpres_add)
void mpres_add (mpres_t, mpres_t, mpres_t, mpmod_t);
#define mpres_sub_ui __ECM(mpres_sub_ui)
void mpres_sub_ui (mpres_t, mpres_t, unsigned int, mpmod_t);
#define mpres_sub __ECM(mpres_sub)
void mpres_sub (mpres_t, mpres_t, mpres_t, mpmod_t);
#define mpres_set_z __ECM(mpres_set_z)
void mpres_set_z (mpres_t, mpz_t, mpmod_t);
#define mpres_get_z __ECM(mpres_get_z)
void mpres_get_z (mpz_t, mpres_t, mpmod_t);
#define mpres_set_ui __ECM(mpres_set_ui)
void mpres_set_ui (mpres_t, unsigned int, mpmod_t);
#define mpres_init __ECM(mpres_init)
void mpres_init (mpres_t, mpmod_t);
#define mpres_realloc __ECM(mpres_realloc)
void mpres_realloc (mpres_t, mpmod_t);
#define mpres_mul_ui __ECM(mpres_mul_ui)
void mpres_mul_ui (mpres_t, mpres_t, unsigned int, mpmod_t);
#define mpres_neg __ECM(mpres_neg)
void mpres_neg (mpres_t, mpres_t, mpmod_t);
#define mpres_invert __ECM(mpres_invert)
int  mpres_invert (mpres_t, mpres_t, mpmod_t);
#define mpres_gcd __ECM(mpres_gcd)
void mpres_gcd (mpz_t, mpres_t, mpmod_t);
#define mpres_out_str __ECM(mpres_out_str)
void mpres_out_str (FILE *, unsigned int, mpres_t, mpmod_t);
#define mpres_is_zero __ECM(mpres_is_zero)
int  mpres_is_zero (mpres_t, mpmod_t);
#define mpres_clear(a,n) mpz_clear (a)
#define mpres_set(a,b,n) mpz_set (a, b)
#define mpres_swap(a,b,n) mpz_swap (a, b)

/* mul_lo.c */
#define ecm_mul_lo_n __ECM(ecm_mul_lo_n)
void ecm_mul_lo_n (mp_ptr, mp_srcptr, mp_srcptr, mp_size_t);

/* median.c */
#define TMulGen __ECM(TMulGen)
unsigned int
TMulGen (listz_t, unsigned int, listz_t, unsigned int, listz_t, 
         unsigned int, listz_t, mpz_t);
#define TMulGen_space __ECM(TMulGen_space)
unsigned int TMulGen_space (unsigned int, unsigned int, unsigned int);

/* schoen_strass.c */
#define DEFAULT 0
#define MONIC 1
#define NOPAD 2
#define F_mul __ECM(F_mul)
unsigned int F_mul (mpz_t *, mpz_t *, mpz_t *, unsigned int, int,
                    unsigned int, mpz_t *);
#define F_mul_trans __ECM(F_mul_trans)
unsigned int F_mul_trans (mpz_t *, mpz_t *, mpz_t *, unsigned int,
                          unsigned int, mpz_t *);

/* rho.c */
#define rhoinit __ECM(rhoinit)
void   rhoinit (int, int);
#define ecmprob __ECM(ecmprob)
double ecmprob (double, double, double, double, int);

/* auxlib.c */
#define gcd __ECM(gcd)
unsigned int gcd (unsigned int, unsigned int);
#define mpz_sub_si __ECM(mpz_sub_si)
void         mpz_sub_si (mpz_t, mpz_t, int);
#define mpz_divby3_1op __ECM(mpz_divby3_1op)
void         mpz_divby3_1op (mpz_t);
#define ceil_log2 __ECM(ceil_log2)
unsigned int ceil_log2  (unsigned int);
#define cputime __ECM(cputime)
unsigned int cputime    (void);
#define elltime __ECM(elltime)
unsigned int elltime    (unsigned int, unsigned int);
#define test_verbose __ECM(test_verbose)
int          test_verbose (int);
#define get_verbose __ECM(get_verbose)
int          get_verbose (void);
#define set_verbose __ECM(set_verbose)
void         set_verbose (int);
#define inc_verbose __ECM(inc_verbose)
int          inc_verbose (void);
#define outputf __ECM(outputf)
int          outputf (int, char *, ...);

/* random.c */
#define pp1_random_seed __ECM(pp1_random_seed)
void pp1_random_seed  (mpz_t, mpz_t, gmp_randstate_t);
#define pm1_random_seed __ECM(pm1_random_seed)
void pm1_random_seed  (mpz_t, mpz_t, gmp_randstate_t);
#define get_random_ui   __ECM(get_random_ui)
unsigned int get_random_ui (void);

/* Fgw.c */
#ifdef HAVE_GWNUM
void Fgwinit (int);
void Fgwclear (void);
void Fgwmul (mpz_t, mpz_t, mpz_t);
#endif


#if defined (__cplusplus)
}
#endif

#define TWO53 9007199254740992.0 /* 2^53 */

/* a <- b * c where a and b are mpz, c is a double, and t an auxiliary mpz */
#if (BITS_PER_MP_LIMB >= 53)
#define mpz_mul_d(a, b, c, t) \
   mpz_mul_ui (a, b, (unsigned long int) c);
#else
#if (BITS_PER_MP_LIMB >= 32)
#define mpz_mul_d(a, b, c, t) \
   if (c < 4294967296.0) \
      mpz_mul_ui (a, b, (unsigned long int) c); \
   else { \
   mpz_set_d (t, c); \
   mpz_mul (a, b, t); }
#else
#define mpz_mul_d(a, b, c, t) \
   mpz_set_d (t, c); \
   mpz_mul (a, b, t);
#endif
#endif
