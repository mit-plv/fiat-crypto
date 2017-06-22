(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on an abstract [T : ℕ → Type].  See
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
    {T : nat -> Type}
    {eval : forall {n}, T n -> Z}
    {zero : forall {n}, T n}
    {divmod : forall {n}, T (S n) -> T n * Z} (* returns lowest limb and all-but-lowest-limb *)
    {r : positive}
    {R : positive}
    {R_numlimbs : nat}
    {scmul : forall {n}, Z -> T n -> T (S n)} (* uses double-output multiply *)
    {addT : forall {n}, T n -> T n -> T (S n)} (* joins carry *)
    {addT' : forall {n}, T (S n) -> T n -> T (S (S n))} (* joins carry *)
    {drop_high : T (S (S R_numlimbs)) -> T (S R_numlimbs)} (* drops the highest limb *)
    {conditional_sub : T (S R_numlimbs) -> T R_numlimbs} (* computes [arg - N] if [N <= arg], and drops high bit *)
    {sub_then_maybe_add : T R_numlimbs -> T R_numlimbs -> T R_numlimbs} (* computes [a - b + if (a - b) <? 0 then N else 0] *)
    (N : T R_numlimbs).

  (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
  Section Iteration.
    Context (pred_A_numlimbs : nat)
            (B : T R_numlimbs) (k : Z)
            (A : T (S pred_A_numlimbs))
            (S : T (S R_numlimbs)).
    (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)
    Local Definition A_a := dlet p := divmod _ A in p. Local Definition A' := fst A_a. Local Definition a := snd A_a.
    Local Definition S1 := addT _ S (scmul _ a B).
    Local Definition s := snd (divmod _ S1).
    Local Definition q := fst (Z.mul_split r s k).
    Local Definition S2 := addT' _ S1 (scmul _ q N).
    Local Definition S3 := fst (divmod _ S2).
    Local Definition S4 := drop_high S3.
  End Iteration.

  Section loop.
    Context (A_numlimbs : nat)
            (A : T A_numlimbs)
            (B : T R_numlimbs)
            (k : Z)
            (S' : T (S R_numlimbs)).

    Definition redc_body {pred_A_numlimbs} : T (S pred_A_numlimbs) * T (S R_numlimbs)
                                             -> T pred_A_numlimbs * T (S R_numlimbs)
      := fun '(A, S') => (A' _ A, S4 _ B k A S').

    Fixpoint redc_loop (count : nat) : T count * T (S R_numlimbs) -> T O * T (S R_numlimbs)
      := match count return T count * _ -> _ with
         | O => fun A_S => A_S
         | S count' => fun A_S => redc_loop count' (redc_body A_S)
         end.

    Definition pre_redc : T (S R_numlimbs)
      := snd (redc_loop A_numlimbs (A, zero (1 + R_numlimbs))).

    Definition redc : T R_numlimbs
      := conditional_sub pre_redc.
  End loop.

  Definition add (A B : T R_numlimbs) : T R_numlimbs
    := conditional_sub (addT _ A B).
  Definition sub (A B : T R_numlimbs) : T R_numlimbs
    := sub_then_maybe_add A B.
  Definition opp (A : T R_numlimbs) : T R_numlimbs
    := sub (zero _) A.
End WordByWordMontgomery.

Create HintDb word_by_word_montgomery.
Hint Unfold S4 S3 S2 q s S1 a A' A_a Let_In : word_by_word_montgomery.
