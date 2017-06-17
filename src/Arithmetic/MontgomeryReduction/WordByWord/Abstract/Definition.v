(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on an abstract [T].  See
    https://github.com/mit-plv/fiat-crypto/issues/157 for a discussion
    of the algorithm; note that it may be that none of the algorithms
    there exactly match what we're doing here. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.Definitions.

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
    {drop_high : T -> T} (* drops the highest limb *)
    (N : T).

  (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
  Section Iteration.
    Context (B : T) (k : Z).
    Context (A S : T).
    (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)
    Local Definition A_a := dlet p := divmod A in p. Local Definition A' := fst A_a. Local Definition a := snd A_a.
    Local Definition S1 := add S (scmul a B).
    Local Definition s := snd (divmod S1).
    Local Definition q := fst (Z.mul_split r s k).
    Local Definition S2 := add S1 (scmul q N).
    Local Definition S3 := fst (divmod S2).
    Local Definition S4 := drop_high S3.
  End Iteration.

  Section loop.
    Context (A B : T) (k : Z) (S' : T).

    Definition redc_body : T * T -> T * T
      := fun '(A, S') => (A' A, S4 B k A S').

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
Hint Unfold S4 S3 S2 q s S1 a A' A_a Let_In : word_by_word_montgomery.
