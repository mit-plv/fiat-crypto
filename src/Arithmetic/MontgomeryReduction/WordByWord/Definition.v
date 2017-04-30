(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on [tuple ℤ].  We follow "Fast Prime
    Field Elliptic Curve Cryptography with 256 Bit Primes",
    https://eprint.iacr.org/2013/816.pdf. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.

(** Quoting from page 7 of "Fast Prime
    Field Elliptic Curve Cryptography with 256 Bit Primes",
    https://eprint.iacr.org/2013/816.pdf: *)
(** * Algorithm 1: Word-by-Word Montgomery Multiplication (WW-MM) *)
(** Input: [p < 2ˡ] (odd modulus),
           [0 ≤ a, b < p], [l = s×k]
    Output: [a×b×2⁻ˡ mod p]
    Pre-computed: [k0 = -p⁻¹ mod 2ˢ]
    Flow
<<
1. T = a×b
 For i = 1 to k do
   2. T1 = T mod 2ˢ
   3. Y = T1 × k0 mod 2ˢ
   4. T2 = Y × p
   5. T3 = (T + T2)
   6. T = T3 / 2ˢ
 End For
7. If T ≥ p then X = T – p;
      else X = T
Return X
>> *)
Local Open Scope Z_scope.
Section positional.
  Local Notation "ts {{ i }}" := (@nth_default Z _ 0%Z i ts).
  Context (k : nat)
          (weight : nat -> Z)
          (p : tuple Z k) (* the prime *)
          (p' : Z) (* [-p⁻¹] *)
          (modulo div : Z -> Z -> Z).
  Local Notation encode := (@B.Positional.encode weight modulo div k).
  Local Notation mul a b := (@B.Positional.mul_cps weight k k a b _ id).
  Local Notation add a b := (@B.Positional.add_cps weight k a b _ id).

  Section body.
    Context (T : tuple Z k)
            (i : nat).
    Let N := weight (S i) / weight i.
    Let k0 := p' mod N.

    Let T1 := T{{i}} mod N.
    Let Y := (T1 * k0) mod N.
    Let T2 := mul p (encode Y).
    Let T3 := add T T2.
    Definition redc_body := T3.
  End body.

  Fixpoint redc_from (T : tuple Z k) (count : nat) : tuple Z k
    := match count with
       | O => T
       | S count' => redc_from (redc_body T (k - count)) count'
       end.

  Definition redc (T : tuple Z k) : tuple Z k
    := redc_from T k.
End positional.
