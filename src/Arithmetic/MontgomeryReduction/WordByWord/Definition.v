(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on an abstract [ℤⁿ].  See
    https://github.com/mit-plv/fiat-crypto/issues/157 for a discussion
    of the algorithm; note that it may be that none of the algorithms
    there exactly match what we're doing here. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Dependent.Definition.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.Definitions.

Local Open Scope Z_scope.

Section WordByWordMontgomery.
  Local Coercion Z.pos : positive >-> Z.
  (** TODO: pick better names for the arguments to this definition. *)
  Context
    {r : positive}
    {R_numlimbs : nat}
    (N : T R_numlimbs).

  Local Notation scmul := (@scmul (Z.pos r)).
  Local Notation addT' := (@MontgomeryAPI.add_S1 (Z.pos r)).
  Local Notation addT := (@MontgomeryAPI.add (Z.pos r)).
  Local Notation conditional_sub_cps := (fun V => @conditional_sub_cps (Z.pos r) _ V N _).
  Local Notation conditional_sub := (fun V => @conditional_sub (Z.pos r) _ V N).
  Local Notation sub_then_maybe_add_cps :=
    (fun V1 V2 => @sub_then_maybe_add_cps (Z.pos r) R_numlimbs (Z.pos r - 1) V1 V2 N).
  Local Notation sub_then_maybe_add := (fun V1 V2 => @sub_then_maybe_add (Z.pos r) R_numlimbs (Z.pos r - 1) V1 V2 N).

  Definition redc_body_no_cps (B : T R_numlimbs) (k : Z) {pred_A_numlimbs} (A_S : T (S pred_A_numlimbs) * T (S R_numlimbs))
    : T pred_A_numlimbs * T (S R_numlimbs)
    := @redc_body T (@divmod) r R_numlimbs (@scmul) (@addT) (@addT') (@drop_high (S R_numlimbs)) N B k _ A_S.
  Definition redc_loop_no_cps (B : T R_numlimbs) (k : Z) (count : nat) (A_S : T count * T (S R_numlimbs))
    : T 0 * T (S R_numlimbs)
    := @redc_loop T (@divmod) r R_numlimbs (@scmul) (@addT) (@addT') (@drop_high (S R_numlimbs)) N B k count A_S.
  Definition pre_redc_no_cps {A_numlimbs} (A : T A_numlimbs) (B : T R_numlimbs) (k : Z) : T (S R_numlimbs)
    := @pre_redc T (@zero) (@divmod) r R_numlimbs (@scmul) (@addT) (@addT') (@drop_high (S R_numlimbs)) N _ A B k.
  Definition redc_no_cps {A_numlimbs} (A : T A_numlimbs) (B : T R_numlimbs) (k : Z) : T R_numlimbs
    := @redc T (@zero) (@divmod) r R_numlimbs (@scmul) (@addT) (@addT') (@drop_high (S R_numlimbs)) conditional_sub N _ A B k.

  Definition redc_body_cps {pred_A_numlimbs} (A : T (S pred_A_numlimbs)) (B : T R_numlimbs) (k : Z) (S' : T (S R_numlimbs))
             {cpsT} (rest : T pred_A_numlimbs * T (S R_numlimbs) -> cpsT)
    : cpsT
    := divmod_cps A (fun '(A, a) =>
       @scmul_cps r _ a B _ (fun aB => @add_cps r _ S' aB _ (fun S1 =>
       divmod_cps S1 (fun '(_, s) =>
       dlet q := fst (Z.mul_split r s k) in
       @scmul_cps r _ q N _ (fun qN => @add_S1_cps r _ S1 qN _ (fun S2 =>
       divmod_cps S2 (fun '(S3, _) =>
       @drop_high_cps (S R_numlimbs) S3 _ (fun S4 => rest (A, S4))))))))).

  Section loop.
    Context {A_numlimbs} (A : T A_numlimbs) (B : T R_numlimbs) (k : Z) {cpsT : Type}.
    Fixpoint redc_loop_cps (count : nat) (rest : T 0 * T (S R_numlimbs) -> cpsT) : T count * T (S R_numlimbs) -> cpsT
      := match count with
         | O => rest
         | S count' => fun '(A, S') => redc_body_cps A B k S' (redc_loop_cps count' rest)
         end.

    Definition pre_redc_cps (rest : T (S R_numlimbs) -> cpsT) : cpsT
      := redc_loop_cps A_numlimbs (fun '(A, S') => rest S') (A, zero).

    Definition redc_cps (rest : T R_numlimbs -> cpsT) : cpsT
      := pre_redc_cps (fun v => conditional_sub_cps v rest).
  End loop.

  Definition redc_body {pred_A_numlimbs} (A : T (S pred_A_numlimbs)) (B : T R_numlimbs) (k : Z) (S' : T (S R_numlimbs))
    : T pred_A_numlimbs * T (S R_numlimbs)
    := redc_body_cps A B k S' id.
  Definition redc_loop (B : T R_numlimbs) (k : Z) (count : nat) : T count * T (S R_numlimbs) -> T 0 * T (S R_numlimbs)
    := redc_loop_cps B k count id.
  Definition pre_redc {A_numlimbs} (A : T A_numlimbs) (B : T R_numlimbs) (k : Z) : T (S R_numlimbs)
    := pre_redc_cps A B k id.
  Definition redc {A_numlimbs} (A : T A_numlimbs) (B : T R_numlimbs) (k : Z) : T R_numlimbs
    := redc_cps A B k id.

  Definition add_no_cps (A B : T R_numlimbs) : T R_numlimbs
    := @add T R_numlimbs (@addT) (@conditional_sub) A B.
  Definition sub_no_cps (A B : T R_numlimbs) : T R_numlimbs
    := @sub T R_numlimbs (@sub_then_maybe_add) A B.
  Definition opp_no_cps (A : T R_numlimbs) : T R_numlimbs
    := @opp T (@zero) R_numlimbs (@sub_then_maybe_add) A.

  Definition add_cps (A B : T R_numlimbs) {cpsT} (rest : T R_numlimbs -> cpsT) : cpsT
    := @add_cps r _ A B
                _ (fun v => conditional_sub_cps v rest).
  Definition add (A B : T R_numlimbs) : T R_numlimbs
    := add_cps A B id.
  Definition sub_cps (A B : T R_numlimbs) {cpsT} (rest : T R_numlimbs -> cpsT) : cpsT
    := @sub_then_maybe_add_cps A B _ rest.
  Definition sub (A B : T R_numlimbs) : T R_numlimbs
    := sub_cps A B id.
  Definition opp_cps (A : T R_numlimbs) {cpsT} (rest : T R_numlimbs -> cpsT) : cpsT
    := sub_cps zero A rest.
  Definition opp (A : T R_numlimbs) : T R_numlimbs
    := opp_cps A id.
  Definition nonzero_cps (A : T R_numlimbs) {cpsT} (f : Z -> cpsT) : cpsT
    := @nonzero_cps R_numlimbs A cpsT f.
  Definition nonzero (A : T R_numlimbs) : Z
    := nonzero_cps A id.
End WordByWordMontgomery.

Hint Opaque redc pre_redc redc_body redc_loop add sub opp nonzero : uncps.
