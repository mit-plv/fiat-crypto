From Coq Require Import ZArith QArith Qround.
From Coq Require Import Lia.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Morphisms.
Require Import Crypto.Util.Bool.Reflect.

Local Open Scope Z_scope.

Lemma Qfloor_le_add a b :  Qfloor a + Qfloor b <= Qfloor (a + b).
  destruct a as [x y], b as [a b]; cbv [Qceiling Qfloor Qplus Qopp QArith_base.Qden QArith_base.Qnum].
  Z.div_mod_to_quot_rem_in_goal; nia.
Qed.

Lemma Qceiling_le_add a b : Qceiling (a + b) <= Qceiling a + Qceiling b.
  destruct a as [x y], b as [a b]; cbv [Qceiling Qfloor Qplus Qopp QArith_base.Qden QArith_base.Qnum].
  Z.div_mod_to_quot_rem_in_goal. nia.
Qed.

Lemma add_floor_l_le_ceiling a b : Qfloor a + Qceiling b <= Qceiling (a + b).
  destruct a as [x y], b as [a b]; cbv [Qceiling Qfloor Qplus Qopp QArith_base.Qden QArith_base.Qnum].
  Z.div_mod_to_quot_rem_in_goal; nia.
Qed.

Lemma Zle_floor_ceiling  a : Z.le (Qfloor a) (Qceiling a).
  pose proof Qle_floor_ceiling.
  destruct a as [x y]; cbv [Qceiling Qfloor Qplus Qopp QArith_base.Qden QArith_base.Qnum].
  Z.div_mod_to_quot_rem_in_goal; nia.
Qed.

Section pow_ceil_mul_nat.
  Context b f (b_nz:0 <> b) (f_pos:(0 <= f)%Q).
  Local Notation wt i := (b^Qceiling (f * inject_Z (Z.of_nat i))) (only parsing).

  Lemma zero_le_ceil_mul_nat i :
    0 <= Qceiling (f * inject_Z (Z.of_nat i))%Q.
  Proof.
    rewrite Zle_Qle.
    eapply Qle_trans; [|eapply Qle_ceiling].
    eapply Qle_trans; [|eapply (Qmult_le_compat_r 0)]; trivial.
    cbv; discriminate.
    apply (Qle_trans _ (inject_Z 0)); [vm_decide|].
    change 0%Q with (inject_Z 0).
    rewrite <-Zle_Qle.
    eapply Zle_0_nat.
  Qed.

  Lemma pow_ceil_mul_nat_nonzero
    : forall i, wt i <> 0.
  Proof.
    intros.
    eapply Z.pow_nonzero; try lia.
    eapply zero_le_ceil_mul_nat.
  Qed.

  Lemma pow_ceil_mul_nat_nonneg (Hb : 0 <= b)
    : forall i, 0 <= wt i.
  Proof.
    intros.
    apply Z.pow_nonneg; assumption.
  Qed.

  Lemma pow_ceil_mul_S i :
    wt (S i) =
    (b ^ (Qceiling (f + f * inject_Z (Z.of_nat i)) - Qceiling (f * inject_Z (Z.of_nat i))) * wt i).
  Proof.
    rewrite Nat2Z.inj_succ.
    rewrite <-Z.add_1_l.
    rewrite inject_Z_plus.
    change (inject_Z 1) with 1%Q.
    rewrite Qmult_plus_distr_r, Qmult_1_r.
    let g := constr:((f * inject_Z (Z.of_nat i))%Q) in
    replace (Qceiling (f+g)) with ((Qceiling (f+g)-Qceiling g)+Qceiling g) at 1 by lia.
    rewrite Z.pow_add_r; [reflexivity|eapply Zle_minus_le_0|apply zero_le_ceil_mul_nat].
    eapply Qceiling_resp_le.
    rewrite <-Qplus_0_l at 1.
    eapply Qplus_le_compat;
      auto with qarith.
  Qed.

  Lemma pow_ceil_mul_nat_multiples i :
    wt (S i) mod (wt i) = 0.
  Proof.
    rewrite pow_ceil_mul_S, Z_mod_mult; reflexivity.
  Qed.
End pow_ceil_mul_nat.

Section pow_ceil_mul_nat2.
  Context b f (b_pos:0 < b) (f_ge_1:(1 <= f)%Q).
  Local Notation wt i := (b^Qceiling (f * inject_Z (Z.of_nat i))) (only parsing).

  Lemma pow_ceil_mul_nat_pos
    : forall i, wt i > 0.
  Proof.
    intros.
    eapply Z.gt_lt_iff.
    eapply Z.pow_pos_nonneg; [assumption|].
    eapply zero_le_ceil_mul_nat.
    eapply (Qle_trans _ 1 _); [vm_decide|assumption].
  Qed.

  Lemma pow_ceil_mul_nat_divide i :
    wt (S i) / (wt i) > 0.
  Proof.
    rewrite pow_ceil_mul_S.
    rewrite Z_div_mult_full; [|apply pow_ceil_mul_nat_nonzero].
    rewrite Z.gt_lt_iff.
    eapply Z.pow_pos_nonneg; [assumption|].
    etransitivity; [|eapply Z.sub_le_ge_Proper].
    2:eapply add_floor_l_le_ceiling.
    2:eapply Z.ge_le_iff; reflexivity.
    assert (1 <= Qfloor f); [|lia].
    change 1%Z with (Qfloor 1).
    eapply Qfloor_resp_le.
    all: trivial; try lia; (eapply (Qle_trans _ 1 _); [vm_decide|assumption]).
  Qed.

  Lemma pow_ceil_mul_nat_divide_nonzero i :
    wt (S i) / (wt i) <> 0.
  Proof.
    pose proof (pow_ceil_mul_nat_divide i).
    lia.
  Qed.

  Lemma pow_ceil_mul_nat_divide_upperbound i :
    wt (S i) / (wt i) <= b^Qceiling f.
  Proof.
    rewrite pow_ceil_mul_S.
    rewrite Z_div_mult_full; [|apply pow_ceil_mul_nat_nonzero].
    all:[ > | lia | eapply (Qle_trans _ 1 _); [vm_decide|assumption].. ].
    apply Z.pow_le_mono_r; [ assumption | ].
    rewrite Z.le_sub_le_add_l, Z.add_comm.
    etransitivity; [ | apply Qceiling_le_add ].
    reflexivity.
  Qed.
End pow_ceil_mul_nat2.

Scheme Equality for Q.
Scheme Induction for Q Sort Prop.
Scheme Induction for Q Sort Set.
Scheme Induction for Q Sort Type.
Scheme Minimality for Q Sort Prop.
Scheme Minimality for Q Sort Set.
Scheme Minimality for Q Sort Type.

Global Instance reflect_eq_Q : reflect_rel (@eq Q) Q_beq | 10
  := reflect_of_brel internal_Q_dec_bl internal_Q_dec_lb.

Global Instance Q_rect_Proper {P}
  : Proper (forall_relation (fun _ => forall_relation (fun _ => eq)) ==> forall_relation (fun _ => eq)) (Q_rect P).
Proof.
  intros f g Hfg [? ?]; cbn; apply Hfg.
Qed.

Global Instance Q_rect_Proper_nondep {T}
  : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq) (Q_rect (fun _ => T)).
Proof.
  intros f g Hfg [? ?] y ?; subst y; cbn; apply Hfg.
Qed.

Global Instance Q_rect_Proper_nondep_gen {P} (R : relation P) : Proper ((eq ==> eq ==> R) ==> eq ==> R) (@Q_rect (fun _ => P)) | 100.
Proof.
  intros f g Hfg [? ?] y ?; subst y; cbn; now apply Hfg.
Qed.
