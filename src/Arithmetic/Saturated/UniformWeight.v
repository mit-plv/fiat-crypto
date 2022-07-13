Require Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Saturated.Core.
Require Import Crypto.Util.ZUtil.Le.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.LetIn Crypto.Util.Tuple.
Local Notation "A ^ n" := (tuple A n) : type_scope.

Section UniformWeight.
  Context (bound : Z) {bound_pos : bound > 0}.

  Definition uweight : nat -> Z := fun i => bound ^ Z.of_nat i.
  Lemma uweight_0 : uweight 0%nat = 1. Proof. reflexivity. Qed.
  Lemma uweight_positive i : uweight i > 0.
  Proof. apply Z.lt_gt, Z.pow_pos_nonneg; lia. Qed.
  Lemma uweight_nonzero i : uweight i <> 0.
  Proof. auto using Z.positive_is_nonzero, uweight_positive. Qed.
  Lemma uweight_multiples i : uweight (S i) mod uweight i = 0.
  Proof. apply Z.mod_same_pow; rewrite Nat2Z.inj_succ; lia. Qed.
  Lemma uweight_divides i : uweight (S i) / uweight i > 0.
  Proof.
    cbv [uweight]. rewrite <-Z.pow_sub_r by (rewrite ?Nat2Z.inj_succ; lia).
    apply Z.lt_gt, Z.pow_pos_nonneg; rewrite ?Nat2Z.inj_succ; lia.
  Qed.

  (* TODO : move to Positional *)
  Lemma eval_from_eq {n} (p:Z^n) wt offset :
    (forall i, wt i = uweight (i + offset)) ->
    B.Positional.eval wt p = B.Positional.eval_from uweight offset p.
  Proof. cbv [B.Positional.eval_from]. auto using B.Positional.eval_wt_equiv. Qed.

  Lemma uweight_eval_from {n} (p:Z^n): forall offset,
    B.Positional.eval_from uweight offset p = uweight offset * B.Positional.eval uweight p.
  Proof.
    induction n; intros; cbv [B.Positional.eval_from];
      [|rewrite (subst_append p)];
    repeat match goal with
           | _ => destruct p
           | _ => rewrite B.Positional.eval_unit; [ ]
           | _ => rewrite B.Positional.eval_step; [ ]
           | _ => rewrite IHn; [ ]
           | _ => rewrite @eval_from_eq with (offset:=S offset)
               by (intros; f_equal; lia)
           | _ => rewrite @eval_from_eq with
                  (wt:=fun i => uweight (S i)) (offset:=1%nat)
               by (intros; f_equal; lia)
           | _ => ring
           end.
    repeat match goal with
           | _ => cbv [uweight]; progress autorewrite with natsimplify
           | _ => progress (rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_0, ?Z.pow_0_r)
           | _ => rewrite !Z.pow_succ_r by (try apply Nat2Z.is_nonneg; lia)
           | _ => ring
           end.
  Qed.

  Lemma uweight_eval_step {n} (p:Z^S n):
    B.Positional.eval uweight p = hd p + bound * B.Positional.eval uweight (tl p).
  Proof.
    rewrite (subst_append p) at 1; rewrite B.Positional.eval_step.
    rewrite eval_from_eq with (offset := 1%nat) by (intros; f_equal; lia).
    rewrite uweight_eval_from. cbv [uweight]; rewrite Z.pow_0_r, Z.pow_1_r.
    ring.
  Qed.

  Lemma uweight_le_mono n m : (n <= m)%nat ->
    uweight n <= uweight m.
  Proof.
    unfold uweight; intro; Z.peel_le; lia.
  Qed.

  Lemma uweight_lt_mono (bound_gt_1 : bound > 1) n m : (n < m)%nat ->
    uweight n < uweight m.
  Proof.
    clear bound_pos.
    unfold uweight; intro; apply Z.pow_lt_mono_r; lia.
  Qed.

  Lemma uweight_succ n : uweight (S n) = bound * uweight n.
  Proof.
    unfold uweight.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by auto using Nat2Z.is_nonneg; reflexivity.
  Qed.


  Definition small {n} (p : Z^n) : Prop :=
    forall x, In x (to_list _ p) -> 0 <= x < bound.

End UniformWeight.

Module Export Hints.
  Export Crypto.Arithmetic.Core.Hints.
  Export Crypto.Arithmetic.Saturated.Core.Hints.
  Export Crypto.Util.ZUtil.Le.Hints.
  Export Crypto.Util.ZUtil.Modulo.Hints.
  Export Crypto.Util.ZUtil.Tactics.PeelLe.Hints.
  Export Crypto.Util.LetIn.Hints Crypto.Util.Tuple.Hints.
End Hints.
