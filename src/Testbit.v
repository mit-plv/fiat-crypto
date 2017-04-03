Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil.
Require Import Crypto.BaseSystem Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.Pow2Base Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Util.Tactics.UniquePose.
Require Coq.Arith.Arith.
Import Nat.
Local Open Scope Z.

Section Testbit.
  Context {width : Z} (limb_width_pos : 0 < width).
  Context (limb_widths : list Z) (limb_widths_nonnil : limb_widths <> nil)
    (limb_widths_uniform : forall w, In w limb_widths -> w = width).
  Local Notation base := (base_from_limb_widths limb_widths).

  Definition testbit (us : list Z) (n : nat) :=
    Z.testbit (nth_default 0 us (n / (Z.to_nat width))) (Z.of_nat (n mod Z.to_nat width)%nat).

  Ltac zify_nat_hyp :=
    repeat match goal with
           | H : ~ (_ < _)%nat |- _ => rewrite nlt_ge in H
           | H : ~ (_ <= _)%nat |- _ => rewrite nle_gt in H
           | H : ~ (_ > _)%nat |- _ => apply not_gt in H
           | H : ~ (_ >= _)%nat |- _ => apply not_ge in H
           | H : (_ < _)%nat |- _ => unique pose proof (proj1 (Nat2Z.inj_lt _ _) H)
           | H : (_ <= _)%nat |- _ => unique pose proof (proj1 (Nat2Z.inj_le _ _) H)
           | H : (_ > _)%nat |- _ => unique pose proof (proj1 (Nat2Z.inj_gt _ _) H)
           | H : (_ >= _)%nat |- _ => unique pose proof (proj1 (Nat2Z.inj_ge _ _) H)
           | H : ~ (_ = _ :> nat) |- _ => unique pose proof (fun x => H (Nat2Z.inj _ _ x))
           | H : (_ = _ :> nat) |- _ => unique pose proof (proj2 (Nat2Z.inj_iff _ _) H)
           end.

  Lemma testbit_spec' : forall a b us, (0 <= b < width) ->
    bounded limb_widths us -> (length us = length limb_widths)%nat ->
    Z.testbit (nth_default 0 us a) b = Z.testbit (decode base us) (Z.of_nat a * width + b).
  Proof.
      repeat match goal with
             | |- _ => progress intros
             | |- _ => progress autorewrite with push_nth_default Ztestbit zsimplify in *
             | |- _ => progress change (Z.of_nat 0) with 0 in *
             | [ H : In ?x ?ls, H' : forall x', In x' ?ls -> x' = _ |- _ ]
               => is_var x; apply H' in H
             | |- _ => rewrite Nat2Z.inj_succ, Z.mul_succ_l
             | |- _ => rewrite nth_default_out_of_bounds by omega
             | |- _ => rewrite nth_default_uniform_base by omega
             | |- false = Z.testbit (decode _ _) _ => rewrite testbit_decode_high
             | |- _ => rewrite (@sum_firstn_uniform_base width) by (eassumption || omega)
             | |- _ => rewrite sum_firstn_succ_default
             | |- Z.testbit (nth_default _ _ ?x) _ = Z.testbit (decode _ _) _ =>
                destruct (lt_dec x (length limb_widths));
                  [ erewrite testbit_decode_digit_select with (i := x); eauto | ]
             | |- _ => reflexivity
             | |- _ => assumption
             | |- _ => zify_nat_hyp; omega
             | |- ?a * ?b <= ?c * ?b + ?d => transitivity (c * b); [ | omega ]
             | |- ?a * ?b <= ?c * ?b => apply Z.mul_le_mono_pos_r
             | |- _ => solve [auto]
             | |- _ => solve [eapply uniform_limb_widths_nonneg; eauto]
             end.
  Qed.

  Hint Rewrite div_add_l' mod_add_l mod_add_l' mod_div_eq0 add_0_r mod_mod : nat_mod_div.

  Lemma testbit_spec : forall n us, (length us = length limb_widths)%nat ->
    bounded limb_widths us ->
    testbit us n = Z.testbit (BaseSystem.decode base us) (Z.of_nat n).
  Proof.
    cbv [testbit]; intros.
    pose proof limb_width_pos as limb_width_pos_nat.
    rewrite Z2Nat.inj_lt in limb_width_pos_nat by omega.
    rewrite (Nat.div_mod n (Z.to_nat width)) by omega.
    autorewrite with nat_mod_div; try omega.
    rewrite testbit_spec' by (rewrite ?mod_Zmod, ?Z2Nat.id; try apply Z.mod_pos_bound; omega || auto).
    f_equal.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id; ring || omega.
  Qed.

End Testbit.
