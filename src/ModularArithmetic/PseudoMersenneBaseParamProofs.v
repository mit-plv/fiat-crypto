Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import VerdiTactics.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Section PseudoMersenneBaseParamProofs.
  Context `{prm : PseudoMersenneBaseParams}.

  Fixpoint base_from_limb_widths limb_widths :=
    match limb_widths with
    | nil => nil
    | w :: lw => 1 :: map (Z.mul (two_p w)) (base_from_limb_widths lw)
    end.

  Definition base := base_from_limb_widths limb_widths.

  Lemma base_length : length base = length limb_widths.
  Proof.
    unfold base.
    induction limb_widths; try reflexivity.
    simpl; rewrite map_length; auto.
  Qed.

  Lemma nth_error_first : forall {T} (a b : T) l, nth_error (a :: l) 0 = Some b ->
  a = b.
  Proof.
    intros; simpl in *.
    unfold value in *.
    congruence.
  Qed.
  
  Lemma base_from_limb_widths_step : forall i b w, (S i < length base)%nat ->
    nth_error base i = Some b ->
    nth_error limb_widths i = Some w ->
    nth_error base (S i) = Some (two_p w * b).
  Proof.
    unfold base; induction limb_widths; intros ? ? ? ? nth_err_w nth_err_b;
      unfold base_from_limb_widths in *; fold base_from_limb_widths in *;
      [rewrite (@nil_length0 Z) in *; omega | ].
    simpl in *; rewrite map_length in *.
    case_eq i; intros; subst.
    + subst; apply nth_error_first in nth_err_w.
      apply nth_error_first in nth_err_b; subst.
      apply map_nth_error. 
      case_eq l; intros; subst; [simpl in *; omega | ].
      unfold base_from_limb_widths; fold base_from_limb_widths.
      reflexivity.
    + simpl in nth_err_w.
      apply nth_error_map in nth_err_w.
      destruct nth_err_w as [x [A B]].
      subst.
      replace (two_p w * (two_p a * x)) with (two_p a * (two_p w * x)) by ring.
      apply map_nth_error.
      apply IHl; auto; omega.
  Qed.

  Lemma nth_error_exists_first : forall {T} l (x : T) (H : nth_error l 0 = Some x),
    exists l', l = x :: l'.
  Proof.
    induction l; try discriminate; eexists.
    apply nth_error_first in H.
    subst; eauto.
  Qed.
  
  Lemma sum_firstn_succ : forall l i x,
    nth_error l i = Some x ->
    sum_firstn l (S i) = x + sum_firstn l i.
  Proof.
    unfold sum_firstn; induction l;
      [intros; rewrite (@nth_error_nil_error Z) in *; congruence | ].
    intros ? x nth_err_x; destruct (NPeano.Nat.eq_dec i 0).
    + subst; simpl in *; unfold value in *.
      congruence.
    + rewrite <- (NPeano.Nat.succ_pred i) at 2 by auto.
      rewrite <- (NPeano.Nat.succ_pred i) in nth_err_x by auto.
      simpl. simpl in nth_err_x.
      specialize (IHl (pred i) x).
      rewrite NPeano.Nat.succ_pred in IHl by auto.
      destruct (NPeano.Nat.eq_dec (pred i) 0).
      - replace i with 1%nat in * by omega.
        simpl. replace (pred 1) with 0%nat in * by auto.
        apply nth_error_exists_first in nth_err_x.
        destruct nth_err_x as [l' ?].
        subst; simpl; ring.
      - rewrite IHl by auto; ring.
  Qed.

  Lemma limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w.
  Proof.
    intros.
    apply Z.lt_le_incl.
    auto using limb_widths_pos.
  Qed.

  Lemma sum_firstn_limb_widths_nonneg : forall n, 0 <= sum_firstn limb_widths n.
  Proof.
    unfold sum_firstn; intros.
    apply fold_right_invariant; try omega.
    intros y In_y_lw ? ?.
    apply Z.add_nonneg_nonneg; try assumption.
    apply limb_widths_nonneg.
    eapply In_firstn; eauto.
  Qed.

  Lemma k_nonneg : 0 <= k.
  Proof.
    apply sum_firstn_limb_widths_nonneg.
  Qed.

  Lemma nth_error_base : forall i, (i < length base)%nat ->
    nth_error base i = Some (two_p (sum_firstn limb_widths i)).
  Proof.
    induction i; intros.
    + unfold base, sum_firstn, base_from_limb_widths in *; case_eq limb_widths; try reflexivity.
      intro lw_nil; rewrite lw_nil, (@nil_length0 Z) in *; omega.
    + 
      assert (i < length base)%nat as lt_i_length by omega.
      specialize (IHi lt_i_length).
      rewrite base_length in lt_i_length.
      destruct (nth_error_length_exists_value _ _ lt_i_length) as [w nth_err_w].
      erewrite base_from_limb_widths_step; eauto.
      f_equal.
      simpl.
      destruct (NPeano.Nat.eq_dec i 0).
      - subst; unfold sum_firstn; simpl.
        apply nth_error_exists_first in nth_err_w.
        destruct nth_err_w as [l' lw_destruct]; subst.
        rewrite lw_destruct.
        ring_simplify.
        f_equal; simpl; ring.
      - erewrite sum_firstn_succ; eauto.
        symmetry.
        apply two_p_is_exp; auto using sum_firstn_limb_widths_nonneg.
        apply limb_widths_nonneg.
        eapply nth_error_value_In; eauto.
  Qed.
  
  Lemma nth_default_base : forall d i, (i < length base)%nat ->
    nth_default d base i = 2 ^ (sum_firstn limb_widths i).
  Proof.
    intros ? ? i_lt_length.
    destruct (nth_error_length_exists_value _ _ i_lt_length) as [x nth_err_x].
    unfold nth_default.
    rewrite nth_err_x.
    rewrite nth_error_base in nth_err_x by assumption.
    rewrite two_p_correct in nth_err_x.
    congruence.
  Qed.

  Lemma base_matches_modulus: forall i j,
    (i   <  length base)%nat ->
    (j   <  length base)%nat ->
    (i+j >= length base)%nat->
    let b := nth_default 0 base in
    let r := (b i * b j)  /   (2^k * b (i+j-length base)%nat) in
              b i * b j = r * (2^k * b (i+j-length base)%nat).
  Proof.
    intros.
    rewrite (Z.mul_comm r).
    subst r.
    assert (i + j - length base < length base)%nat by omega.
    rewrite mul_div_eq by (apply gt_lt_symmetry; apply Z.mul_pos_pos;
      [ | subst b; rewrite nth_default_base; try assumption ];
      apply Z.pow_pos_nonneg; omega || apply k_nonneg || apply sum_firstn_limb_widths_nonneg).
    rewrite (Zminus_0_l_reverse (b i * b j)) at 1.
    f_equal.
    subst b.
    repeat rewrite nth_default_base by assumption.
    do 2 rewrite <- Z.pow_add_r by (apply sum_firstn_limb_widths_nonneg || apply k_nonneg).
    symmetry.
    apply mod_same_pow.
    split.
    + apply Z.add_nonneg_nonneg; apply sum_firstn_limb_widths_nonneg || apply k_nonneg.
    + rewrite base_length in *; apply limb_widths_match_modulus; assumption.
  Qed.

  Lemma base_succ : forall i, ((S i) < length base)%nat -> 
    nth_default 0 base (S i) mod nth_default 0 base i = 0.
  Proof.
    intros.
    repeat rewrite nth_default_base by omega.
    apply mod_same_pow.
    split; [apply sum_firstn_limb_widths_nonneg | ].
    destruct (NPeano.Nat.eq_dec i 0); subst.
      + case_eq limb_widths; intro; unfold sum_firstn; simpl; try omega; intros l' lw_eq.
        apply Z.add_nonneg_nonneg; try omega.
        apply limb_widths_nonneg.
        rewrite lw_eq.
        apply in_eq.
      + assert (i < length base)%nat as i_lt_length by omega.
        rewrite base_length in *.
        apply nth_error_length_exists_value in i_lt_length.
        destruct i_lt_length as [x nth_err_x].
        erewrite sum_firstn_succ; eauto.
        apply nth_error_value_In in nth_err_x.
        apply limb_widths_nonneg in nth_err_x.
        omega.
   Qed.

   Lemma nth_error_subst : forall i b, nth_error base i = Some b ->
     b = 2 ^ (sum_firstn limb_widths i).
   Proof.
     intros i b nth_err_b.
     pose proof (nth_error_value_length _ _ _ _ nth_err_b).
     rewrite nth_error_base in nth_err_b by assumption.
     rewrite two_p_correct in nth_err_b.
     congruence.
   Qed.

   Lemma base_positive : forall b : Z, In b base -> b > 0.
   Proof.
     intros b In_b_base.
     apply In_nth_error_value in In_b_base.
     destruct In_b_base as [i nth_err_b].
     apply nth_error_subst in nth_err_b.
     rewrite nth_err_b.
     apply gt_lt_symmetry.
     apply Z.pow_pos_nonneg; omega || apply sum_firstn_limb_widths_nonneg.
   Qed.

   Lemma b0_1 : forall x : Z, nth_default x base 0 = 1.
   Proof.
     unfold base; case_eq limb_widths; intros; [pose proof limb_widths_nonnil; congruence | reflexivity].
   Qed.
 
   Lemma base_good : forall i j : nat,
                (i + j < length base)%nat ->
                let b := nth_default 0 base in
                let r := b i * b j / b (i + j)%nat in
                b i * b j = r * b (i + j)%nat.
   Proof.
     intros; subst b r.
     repeat rewrite nth_default_base by omega.
     rewrite (Z.mul_comm _ (2 ^ (sum_firstn limb_widths (i+j)))).
     rewrite mul_div_eq by (apply gt_lt_symmetry; apply Z.pow_pos_nonneg; omega || apply sum_firstn_limb_widths_nonneg).
     rewrite <- Z.pow_add_r by apply sum_firstn_limb_widths_nonneg.
     rewrite mod_same_pow; try ring.
     split; [ apply sum_firstn_limb_widths_nonneg | ].
     apply limb_widths_good.
     rewrite <- base_length; assumption.
   Qed.

  Global Instance bv : BaseSystem.BaseVector base := {
    base_positive := base_positive;
    b0_1 := b0_1;
    base_good := base_good
  }.

End PseudoMersenneBaseParamProofs.
