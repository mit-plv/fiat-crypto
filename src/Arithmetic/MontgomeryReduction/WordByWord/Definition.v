(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on [tuple ℤ].  We follow "Fast Prime
    Field Elliptic Curve Cryptography with 256 Bit Primes",
    https://eprint.iacr.org/2013/816.pdf. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Saturated.
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
Section columns.
  (** TODO(jadep): implement these *)
  Context (Columns_add_cps : forall (weight : nat -> Z)
                                    (n : nat)
                                    (a b : tuple (list Z) n)
                                    T
                                    (f : tuple (list Z) n -> T),
              T)
          (Columns_mul_cps : forall (weight : nat -> Z)
                                    (n m : nat)
                                    (a b : tuple (list Z) n)
                                    T
                                    (f : tuple (list Z) m -> T),
              T).
  Context (modulo div : Z -> Z -> Z)
          (add_get_carry : Z -> Z -> Z -> Z * Z)
          (k' : nat)
          (s : Z).
  Let k := S k'.
  Context (p : tuple (list Z) k)
          (p' : Z) (* [-p⁻¹] *).
  Local Notation weight := (fun i : nat => 2^(Z.of_nat i * s))%Z.
  Section body.
    Context (T : tuple Z k).
    Local Notation Pos2Col t
      := (@Columns.from_associational
            weight k
            (@B.Positional.to_associational
               weight k t)).
    Local Notation encode z
      := (Pos2Col (@B.Positional.encode weight modulo div k z)).
    Local Notation compact := (@Columns.compact weight add_get_carry div modulo k).
    Local Notation mul a b := (@Columns_mul_cps weight k k a b _ id).
    Local Notation add a b := (@Columns_add_cps weight k a b _ id).

    Let N := 2^s.
    Let k0 := p' mod N.

    Let T1 := (hd T) mod N.
    Let Y := (T1 * k0) mod N.
    Let T2 := mul p (encode Y).
    Let T3 := add (Pos2Col T) T2.
    Definition carry_to_highest_and_drop_lowest (ts : tuple Z k) (c : Z) : tuple Z k
      := Tuple.left_append c (tl ts).
    Definition redc_body : tuple Z k
      := let '(c, ts) := compact T3 in carry_to_highest_and_drop_lowest ts c.
  End body.

  Fixpoint redc_for (T : tuple Z k) (count : nat) : tuple Z k
    := match count with
       | O => T
       | S count' => redc_for (redc_body T) count'
       end.

  Definition redc (T : tuple Z k) : tuple Z k
    := redc_for T k.
End columns.
