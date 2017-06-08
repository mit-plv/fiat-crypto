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
  Context {t : Type} {length : t -> nat}
          {divmod : t -> t * Z} (* returns lowest limb and all-but-lowest-limb *)
          {scmul : Z -> t -> t} (* uses double-output multiply *)
          {add : t -> t -> t * Z} (* produces carry *)
          {join : t * Z -> t}
          (p : t)
          (s : Z)
          (k0 : Z) (* [(-p⁻¹) mod 2ˢ] *).
  Definition redc_body (T : t) : t
    := let '(_, T1) := divmod T in
       let Y := (T1 * k0) mod (2^s) in
       let T2 := scmul Y p in
       let T3 := join (add T T2) in
       let '(T, _) := divmod T3 in
       T.

  Fixpoint redc (count : nat) : t -> t
    := match count with
       | O => fun T => T
       | S count' => fun T => redc count' (redc_body T)
       end.
End columns.
