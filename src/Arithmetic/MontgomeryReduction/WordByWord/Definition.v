(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on an abstract [T].  We follow "Fast Prime
    Field Elliptic Curve Cryptography with 256 Bit Primes",
    https://eprint.iacr.org/2013/816.pdf. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.

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

Section WordByWordMontgomery.
  Local Coercion Z.pos : positive >-> Z.
  Context
    {T : Type}
    {eval : T -> Z}
    {numlimbs : T -> nat}
    {zero : nat -> T}
    {divmod : T -> T * Z} (* returns lowest limb and all-but-lowest-limb *)
    {r : positive}
    {scmul : Z -> T -> T} (* uses double-output multiply *)
    {R : positive}
    {add : T -> T -> T} (* joins carry *)
    (N : T).

  (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
  Section Iteration.
    Context (B : T) (k : Z).
    Context (A S : T).
    (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)
    Local Definition A_a := dlet p := divmod A in p. Local Definition A' := fst A_a. Local Definition a := snd A_a.
    Local Definition S1 := add S (scmul a B).
    Local Definition s := snd (divmod S1).
    Local Definition q := s * k mod r.
    Local Definition cS2 := add S1 (scmul q N).
    Local Definition S3 := fst (divmod cS2).
  End Iteration.

  Section loop.
    Context (A B : T) (k : Z) (S' : T).

    Definition redc_body : T * T -> T * T
      := fun '(A, S') => (A' A, S3 B k A S').

    Fixpoint redc_loop (count : nat) : T * T -> T * T
      := match count with
         | O => fun A_S => A_S
         | S count' => fun A_S => redc_loop count' (redc_body A_S)
         end.

    Definition redc : T
      := snd (redc_loop (numlimbs A) (A, zero (1 + numlimbs B))).
  End loop.
End WordByWordMontgomery.

Create HintDb word_by_word_montgomery.
Hint Unfold S3 cS2 q s S1 a A' A_a Let_In : word_by_word_montgomery.
