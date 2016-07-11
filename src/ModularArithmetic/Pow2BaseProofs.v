Require Import Zpower ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.Pow2Base Crypto.BaseSystemProofs.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Section Pow2BaseProofs.
  Context {limb_widths} (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Notation "{base}" := (base_from_limb_widths limb_widths).

  Lemma base_from_limb_widths_length : length {base} = length limb_widths.
  Proof.
    induction limb_widths; try reflexivity.
    simpl; rewrite map_length.
    simpl in limb_widths_nonneg.
    rewrite IHl; auto.
  Qed.

  Lemma sum_firstn_limb_widths_nonneg : forall n, 0 <= sum_firstn limb_widths n.
  Proof.
    unfold sum_firstn; intros.
    apply fold_right_invariant; try omega.
    intros y In_y_lw ? ?.
    apply Z.add_nonneg_nonneg; try assumption.
    apply limb_widths_nonneg.
    eapply In_firstn; eauto.
  Qed. Hint Resolve sum_firstn_limb_widths_nonneg.

  Lemma base_from_limb_widths_step : forall i b w, (S i < length {base})%nat ->
    nth_error {base} i = Some b ->
    nth_error limb_widths i = Some w ->
    nth_error {base} (S i) = Some (two_p w * b).
  Proof.
    induction limb_widths; intros ? ? ? ? nth_err_w nth_err_b;
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
      apply IHl; auto. omega.
  Qed.


  Lemma nth_error_base : forall i, (i < length {base})%nat ->
    nth_error {base} i = Some (two_p (sum_firstn limb_widths i)).
  Proof.
    induction i; intros.
    + unfold sum_firstn, base_from_limb_widths in *; case_eq limb_widths; try reflexivity.
      intro lw_nil; rewrite lw_nil, (@nil_length0 Z) in *; omega.
    + assert (i < length {base})%nat as lt_i_length by omega.
      specialize (IHi lt_i_length).
      rewrite base_from_limb_widths_length in lt_i_length.
      destruct (nth_error_length_exists_value _ _ lt_i_length) as [w nth_err_w].
      erewrite base_from_limb_widths_step; eauto.
      f_equal.
      simpl.
      destruct (NPeano.Nat.eq_dec i 0).
      - subst; unfold sum_firstn; simpl.
        apply nth_error_exists_first in nth_err_w.
        destruct nth_err_w as [l' lw_destruct]; subst.
        simpl; ring_simplify.
        f_equal; ring.
      - erewrite sum_firstn_succ; eauto.
        symmetry.
        apply two_p_is_exp; auto using sum_firstn_limb_widths_nonneg.
        apply limb_widths_nonneg.
        eapply nth_error_value_In; eauto.
  Qed.

  Lemma nth_default_base : forall d i, (i < length {base})%nat ->
    nth_default d {base} i = 2 ^ (sum_firstn limb_widths i).
  Proof.
    intros ? ? i_lt_length.
    destruct (nth_error_length_exists_value _ _ i_lt_length) as [x nth_err_x].
    unfold nth_default.
    rewrite nth_err_x.
    rewrite nth_error_base in nth_err_x by assumption.
    rewrite two_p_correct in nth_err_x.
    congruence.
  Qed.

  Lemma base_succ : forall i, ((S i) < length {base})%nat ->
    nth_default 0 {base} (S i) mod nth_default 0 {base} i = 0.
  Proof.
    intros.
    repeat rewrite nth_default_base by omega.
    apply Z.mod_same_pow.
    split; [apply sum_firstn_limb_widths_nonneg | ].
    destruct (NPeano.Nat.eq_dec i 0); subst.
      + case_eq limb_widths; intro; unfold sum_firstn; simpl; try omega; intros l' lw_eq.
        apply Z.add_nonneg_nonneg; try omega.
        apply limb_widths_nonneg.
        rewrite lw_eq.
        apply in_eq.
      + assert (i < length {base})%nat as i_lt_length by omega.
        rewrite base_from_limb_widths_length in *.
        apply nth_error_length_exists_value in i_lt_length.
        destruct i_lt_length as [x nth_err_x].
        erewrite sum_firstn_succ; eauto.
        apply nth_error_value_In in nth_err_x.
        apply limb_widths_nonneg in nth_err_x.
        omega.
   Qed.

   Lemma nth_error_subst : forall i b, nth_error {base} i = Some b ->
     b = 2 ^ (sum_firstn limb_widths i).
   Proof.
     intros i b nth_err_b.
     pose proof (nth_error_value_length _ _ _ _ nth_err_b).
     rewrite nth_error_base in nth_err_b by assumption.
     rewrite two_p_correct in nth_err_b.
     congruence.
   Qed.

End Pow2BaseProofs.

Section BitwiseDecodeEncode.
  Context {limb_widths} (bv : BaseSystem.BaseVector (base_from_limb_widths limb_widths))
          (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Hint Resolve limb_widths_nonneg.
  Local Notation "w[ i ]" := (nth_default 0 limb_widths i).
  Local Notation "{base}" := (base_from_limb_widths limb_widths).
  Local Notation "{max}" := (upper_bound limb_widths).

  Lemma encode'_spec : forall x i, (i <= length {base})%nat ->
    encode' limb_widths x i = BaseSystem.encode' {base} x {max} i.
  Proof.
    induction i; intros.
    + rewrite encode'_zero. reflexivity.
    + rewrite encode'_succ, <-IHi by omega.
      simpl; do 2 f_equal.
      rewrite Z.land_ones, Z.shiftr_div_pow2 by auto using sum_firstn_limb_widths_nonneg.
      match goal with H : (S _ <= length {base})%nat |- _ =>
        apply le_lt_or_eq in H; destruct H end.
      - repeat f_equal; rewrite nth_default_base by (omega || auto); reflexivity.
      - repeat f_equal; try solve [rewrite nth_default_base by (omega || auto); reflexivity].
        rewrite nth_default_out_of_bounds by omega.
        unfold upper_bound.
        rewrite <-base_from_limb_widths_length by auto.
        congruence.
  Qed.

  Lemma nth_default_limb_widths_nonneg : forall i, 0 <= w[i].
  Proof.
    intros; apply nth_default_preserves_properties; auto; omega.
  Qed. Hint Resolve nth_default_limb_widths_nonneg.

  Lemma base_upper_bound_compatible : @base_max_succ_divide {base} {max}.
  Proof.
    unfold base_max_succ_divide; intros i lt_Si_length.
    rewrite Nat.lt_eq_cases in lt_Si_length; destruct lt_Si_length;
      rewrite !nth_default_base by (omega || auto).
    + erewrite sum_firstn_succ by (eapply nth_error_Some_nth_default with (x := 0); 
         rewrite <-base_from_limb_widths_length by auto; omega).
      rewrite Z.pow_add_r; auto using sum_firstn_limb_widths_nonneg.
      apply Z.divide_factor_r.
    + rewrite nth_default_out_of_bounds by omega.
      unfold upper_bound.
      replace (length limb_widths) with (S (pred (length limb_widths))) by
        (rewrite base_from_limb_widths_length in H by auto; omega).
      replace i with (pred (length limb_widths)) by
        (rewrite base_from_limb_widths_length in H by auto; omega).
      erewrite sum_firstn_succ by (eapply nth_error_Some_nth_default with (x := 0); 
         rewrite <-base_from_limb_widths_length by auto; omega).
      rewrite Z.pow_add_r; auto using sum_firstn_limb_widths_nonneg.
      apply Z.divide_factor_r. 
  Qed.
  Hint Resolve base_upper_bound_compatible.

  Lemma encodeZ_spec : forall x,
    BaseSystem.decode {base} (encodeZ limb_widths x) = x mod {max}.
  Proof.
    intros.
    assert (length {base} = length limb_widths) by auto using base_from_limb_widths_length.
    unfold encodeZ; rewrite encode'_spec by omega.
    rewrite BaseSystemProofs.encode'_spec; unfold upper_bound; try zero_bounds;
      auto using sum_firstn_limb_widths_nonneg.
    rewrite nth_default_out_of_bounds by omega.
    reflexivity.
  Qed.

  Lemma decode_bitwise'_succ : forall us i acc, bounded limb_widths us ->
    decode_bitwise' limb_widths us (S i) acc =
    decode_bitwise' limb_widths us i (acc * (2 ^ w[i]) + nth_default 0 us i).
  Proof.
    intros.
    simpl; f_equal.
    match goal with H : bounded _ _ |- _ => 
      rewrite Z.lor_shiftl by (auto; unfold bounded in H; specialize (H i); assumption) end.
    rewrite Z.shiftl_mul_pow2 by auto.
    ring.
  Qed.

  (* c is a counter, allows i to count up rather than down *)
  Fixpoint partial_decode us i c :=
    match c with
    | O => 0
    | S c' => (partial_decode us (S i) c' *  2 ^ w[i]) + nth_default 0 us i
    end.

  Lemma partial_decode_counter_over : forall c us i, (c >= length us - i)%nat ->
    partial_decode us i c = partial_decode us i (length us - i).
  Proof.
    induction c; intros.
    + f_equal. omega.
    + simpl. rewrite IHc by omega.
      case_eq (length us - i)%nat; intros.
      - rewrite nth_default_out_of_bounds with (us0 := us) by omega.
        replace (length us - S i)%nat with 0%nat by omega.
        reflexivity.
      - simpl. repeat f_equal. omega.
  Qed.

  Lemma partial_decode_counter_subst : forall c c' us i,
    (c >= length us - i)%nat -> (c' >= length us - i)%nat ->
    partial_decode us i c = partial_decode us i c'.
  Proof.
    intros.
    rewrite partial_decode_counter_over by assumption.
    symmetry.
    auto using partial_decode_counter_over.
  Qed.

  Lemma partial_decode_succ : forall c us i, (c >= length us - i)%nat ->
    partial_decode us (S i) c * 2 ^ w[i] + nth_default 0 us i =
    partial_decode us i c.
  Proof.
    intros.
    rewrite partial_decode_counter_subst with (i := i) (c' := S c) by omega.
    reflexivity.
  Qed.

  Lemma partial_decode_intermediate : forall c us i, length us = length limb_widths ->
    (c >= length us - i)%nat ->
    partial_decode us i c = BaseSystem.decode' (base_from_limb_widths (skipn i limb_widths)) (skipn i us).
  Proof.
    induction c; intros.
    + simpl. rewrite skipn_all by omega.
      symmetry; apply decode_base_nil.
    + simpl.
      destruct (lt_dec i (length limb_widths)).
      - rewrite IHc by omega.
        do 2 (rewrite skipn_nth_default with (n := i) (d := 0) by (rewrite <-?base_length; omega)).
        unfold base_from_limb_widths; fold base_from_limb_widths.
        rewrite peel_decode.
        fold (BaseSystem.mul_each (two_p w[i])).
        rewrite <-mul_each_base, mul_each_rep, two_p_correct.
        ring_simplify.
        f_equal; ring.
     - rewrite <- IHc by omega.
       apply partial_decode_succ; omega.
  Qed.


  Lemma decode_bitwise'_succ_partial_decode : forall us i c,
    bounded limb_widths us -> length us = length limb_widths ->
    decode_bitwise' limb_widths us (S i) (partial_decode us (S i) c) =
    decode_bitwise' limb_widths us i (partial_decode us i (S c)).
  Proof.
    intros.
    rewrite decode_bitwise'_succ by auto.
    f_equal.
  Qed.

  Lemma decode_bitwise'_spec : forall us i, (i <= length limb_widths)%nat ->
    bounded limb_widths us -> length us = length limb_widths ->
    decode_bitwise' limb_widths us i (partial_decode us i (length us - i)) =
    BaseSystem.decode {base} us.
  Proof.
    induction i; intros.
    + rewrite partial_decode_intermediate by auto.
      reflexivity.
    + rewrite decode_bitwise'_succ_partial_decode by auto.
      replace (S (length us - S i)) with (length us - i)%nat by omega.
      apply IHi; auto; omega.
  Qed.

  Lemma decode_bitwise_spec : forall us, bounded limb_widths us ->
    length us = length limb_widths ->
    decode_bitwise limb_widths us = BaseSystem.decode {base} us.
  Proof.
    unfold decode_bitwise; intros.
    replace 0 with (partial_decode us (length us) (length us - length us)) by
      (rewrite Nat.sub_diag; reflexivity).
    apply decode_bitwise'_spec; auto; omega.
  Qed.

End BitwiseDecodeEncode.

Section Conversion.
  Context {limb_widthsA} (limb_widthsA_nonneg : forall w, In w limb_widthsA -> 0 <= w)
          {limb_widthsB} (limb_widthsB_nonneg : forall w, In w limb_widthsB -> 0 <= w).
  Local Notation "{baseA}" := (base_from_limb_widths limb_widthsA).
  Local Notation "{baseB}" := (base_from_limb_widths limb_widthsB).
  Context (bvB : BaseSystem.BaseVector {baseB}).

  Definition convert xs := @encodeZ limb_widthsB (@decode_bitwise limb_widthsA xs).

  Lemma convert_spec : forall xs, @bounded limb_widthsA xs -> length xs = length limb_widthsA ->
    BaseSystem.decode {baseA} xs mod (@upper_bound limb_widthsB) = BaseSystem.decode {baseB} (convert xs).
  Proof.
    unfold convert; intros.
    rewrite encodeZ_spec, decode_bitwise_spec by auto.
    reflexivity.
  Qed.

End Conversion.