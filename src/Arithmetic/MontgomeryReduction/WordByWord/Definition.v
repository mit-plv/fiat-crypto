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
  Context {T : Type} {length : T -> nat}
          {divmod : T -> T * Z} (* returns lowest limb and all-but-lowest-limb *)
          {scmul : Z -> T -> T} (* uses double-output multiply *)
          {add : T -> T -> T * Z} (* produces carry *)
          {join : T * Z -> T}
          {zero : nat -> T}
          (A B : T)
          (bound : Z)
          (N : T)
          (k : Z) (* [(-1 mod N) mod bound] *).
  Definition redc_body : T * T -> T * T
    := fun '(A, S')
       => let '(A, a) := divmod A in
          let '(S', _) := add S' (scmul a B) in
          let '(_, q) := divmod (scmul k S') in
          let '(S', _) := divmod (join (add S' (scmul q N))) in
          (A, S').

  Fixpoint redc_loop (count : nat) : T * T -> T * T
    := match count with
       | O => fun A_S => A_S
       | S count' => fun A_S => redc_loop count' (redc_body A_S)
       end.

  Definition redc : T
    := snd (redc_loop (length A) (A, zero (1 + length B))).
End columns.
