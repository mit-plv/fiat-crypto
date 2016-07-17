Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.ModularArithmetic.Pow2Base Crypto.BaseSystemProofs.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Create HintDb simpl_add_to_nth discriminated.

Section Pow2BaseProofs.
  Context {limb_widths} (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Notation base := (base_from_limb_widths limb_widths).

  Lemma base_from_limb_widths_length : length base = length limb_widths.
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

  Lemma base_from_limb_widths_step : forall i b w, (S i < length base)%nat ->
    nth_error base i = Some b ->
    nth_error limb_widths i = Some w ->
    nth_error base (S i) = Some (two_p w * b).
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


  Lemma nth_error_base : forall i, (i < length base)%nat ->
    nth_error base i = Some (two_p (sum_firstn limb_widths i)).
  Proof.
    induction i; intros.
    + unfold sum_firstn, base_from_limb_widths in *; case_eq limb_widths; try reflexivity.
      intro lw_nil; rewrite lw_nil, (@nil_length0 Z) in *; omega.
    + assert (i < length base)%nat as lt_i_length by omega.
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

  Lemma base_succ : forall i, ((S i) < length base)%nat ->
    nth_default 0 base (S i) mod nth_default 0 base i = 0.
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
      + assert (i < length base)%nat as i_lt_length by omega.
        rewrite base_from_limb_widths_length in *.
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
     apply Z.gt_lt_iff.
     apply Z.pow_pos_nonneg; omega || auto using sum_firstn_limb_widths_nonneg.
   Qed.

   Lemma b0_1 : forall x : Z, limb_widths <> nil -> nth_default x base 0 = 1.
   Proof.
     case_eq limb_widths; intros; [congruence | reflexivity].
   Qed.

  Lemma base_from_limb_widths_cons : forall l0 l,
    base_from_limb_widths (l0 :: l) = 1 :: map (Z.mul (two_p l0)) (base_from_limb_widths l).
  Proof.
    reflexivity.
  Qed.

End Pow2BaseProofs.

Section BitwiseDecodeEncode.
  Context {limb_widths} (bv : BaseSystem.BaseVector (base_from_limb_widths limb_widths))
          (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Hint Resolve limb_widths_nonneg.
  Local Notation "w[ i ]" := (nth_default 0 limb_widths i).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation max := (upper_bound limb_widths).

  Lemma encode'_spec : forall x i, (i <= length base)%nat ->
    encode' limb_widths x i = BaseSystem.encode' base x max i.
  Proof.
    induction i; intros.
    + rewrite encode'_zero. reflexivity.
    + rewrite encode'_succ, <-IHi by omega.
      simpl; do 2 f_equal.
      rewrite Z.land_ones, Z.shiftr_div_pow2 by auto using sum_firstn_limb_widths_nonneg.
      match goal with H : (S _ <= length base)%nat |- _ =>
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

  Lemma base_upper_bound_compatible : @base_max_succ_divide base max.
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
    BaseSystem.decode base (encodeZ limb_widths x) = x mod max.
  Proof.
    intros.
    assert (length base = length limb_widths) by auto using base_from_limb_widths_length.
    unfold encodeZ; rewrite encode'_spec by omega.
    rewrite BaseSystemProofs.encode'_spec; unfold upper_bound; try zero_bounds;
      auto using sum_firstn_limb_widths_nonneg.
    rewrite nth_default_out_of_bounds by omega.
    reflexivity.
  Qed.

  Lemma decode_bitwise'_nil : forall i,
    decode_bitwise' limb_widths nil i 0 = 0.
  Proof.
    induction i; intros.
    + reflexivity.
    + cbv [decode_bitwise'].
      rewrite nth_default_nil, Z.shiftl_0_l.
      apply IHi.
  Qed.

  Lemma decode_bitwise_nil : decode_bitwise limb_widths nil = 0.
  Proof.
    cbv [decode_bitwise].
    apply decode_bitwise'_nil.
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
        do 2 (rewrite skipn_nth_default with (n := i) (d := 0) by omega).
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
    BaseSystem.decode base us.
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
    decode_bitwise limb_widths us = BaseSystem.decode base us.
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

Section UniformBase.
  Context {width : Z} (limb_width_pos : 0 < width).
  Context (limb_widths : list Z) (limb_widths_nonnil : limb_widths <> nil)
    (limb_widths_uniform : forall w, In w limb_widths -> w = width).
  Local Notation base := (base_from_limb_widths limb_widths).

   Lemma bounded_uniform : forall us, (length us <= length limb_widths)%nat ->
     (bounded limb_widths us <-> (forall u, In u us -> 0 <= u < 2 ^ width)).
   Proof.
     cbv [bounded]; split; intro A; intros.
     + let G := fresh "G" in
       match goal with H : In _ us |- _ =>
         eapply In_nth in H; destruct H as [? G]; destruct G as [? G];
         rewrite <-nth_default_eq in G; rewrite <-G end.
       specialize (A x).
       split; try eapply A.
       eapply Z.lt_le_trans; try apply A.
       apply nth_default_preserves_properties; [ | apply Z.pow_le_mono_r; omega ] .
       intros; apply Z.eq_le_incl.
       f_equal; auto.
     + apply nth_default_preserves_properties_length_dep;
         try solve [apply nth_default_preserves_properties; split; zero_bounds; rewrite limb_widths_uniform; auto || omega].
      intros; apply nth_default_preserves_properties_length_dep; try solve [intros; omega].
       let x := fresh "x" in intro x; intros;
         replace x with width; try symmetry; auto.
   Qed.

  Lemma decode'_tl_base_shift' : forall us lw,
    (forall w, In w lw -> w = width) ->
    (length us <= length lw)%nat ->
    BaseSystem.decode' (map (Z.mul (2 ^ width)) (base_from_limb_widths lw)) us =
    (BaseSystem.decode' (1 :: map (Z.mul (2 ^ width)) (base_from_limb_widths lw)) us) << width.
  Proof.
    induction us; intros ? Hin Hlength.
    + rewrite !decode_nil, Z.shiftl_0_l; reflexivity.
    + edestruct (destruct_repeat lw) as [? | [tl_lw [Heq_lw tl_lw_uniform]]]; eauto.
      - subst lw; rewrite !length_cons, nil_length0 in Hlength; omega.
      - rewrite Heq_lw in Hlength |- *.
        rewrite base_from_limb_widths_cons, decode'_cons, two_p_correct.
        cbv [tl].
        fold (BaseSystem.mul_each (2 ^ width)).
        rewrite <-!mul_each_base, !mul_each_rep.
        rewrite decode'_cons, Z.mul_add_distr_l.
        rewrite Z.shiftl_mul_pow2 by omega. rewrite Z.mul_add_distr_r.
        f_equal; try ring.
        rewrite <-Z.mul_assoc. f_equal; try ring.
        rewrite IHus by (simpl in Hlength; auto || omega).
        rewrite Z.shiftl_mul_pow2 by omega.
        reflexivity.
  Qed.

  Lemma decode_tl_base_shift : forall us, (length us < length limb_widths)%nat ->
    BaseSystem.decode (tl base) us = BaseSystem.decode base us << width.
  Proof.
    intros ? Hlength.
    edestruct (destruct_repeat limb_widths) as [? | [tl_lw [Heq_lw tl_lw_uniform]]];
        eauto; try congruence.
    rewrite Heq_lw in Hlength |- *.
    rewrite base_from_limb_widths_cons, two_p_correct.
    cbv [tl].
    apply decode'_tl_base_shift';
      auto; simpl in *; omega.
  Qed.

  Lemma decode_shift : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode base us) << width).
  Proof.
    intros.
    rewrite <-decode_tl_base_shift by (simpl in *; omega).
    case_eq limb_widths; try congruence; intros.
    rewrite base_from_limb_widths_cons, decode'_cons.
    cbv [tl].
    f_equal; ring.
  Qed.

  Lemma uniform_limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w.
  Proof.
    intros.
    apply Z.lt_le_incl.
    replace w with width by (symmetry; auto).
    assumption.
  Qed.
End UniformBase.

Section carrying_helper.
  Context {limb_widths} (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).

  Lemma update_nth_sum : forall n f us, (n < length us \/ n >= length base)%nat ->
    BaseSystem.decode base (update_nth n f us) =
    (let v := nth_default 0 us n in f v - v) * nth_default 0 base n + BaseSystem.decode base us.
  Proof.
    intros.
    unfold BaseSystem.decode.
    destruct H as [H|H].
    { nth_inbounds; auto. (* TODO(andreser): nth_inbounds should do this auto*)
      rewrite_strat topdown hints simpl_nth_default.
      unfold splice_nth.
      rewrite <- (firstn_skipn n us) at 3.
      do 2 rewrite decode'_splice.
      remember (length (firstn n us)) as n0.
      ring_simplify.
      remember (BaseSystem.decode' (firstn n0 base) (firstn n us)).
      rewrite (skipn_nth_default n us 0) by omega.
      rewrite_strat topdown hints simpl_nth_default.
      rewrite firstn_length in Heqn0.
      rewrite Min.min_l in Heqn0 by omega; subst n0.
      destruct (le_lt_dec (length base) n). {
        rewrite (@nth_default_out_of_bounds _ _ base) by auto.
        rewrite skipn_all by omega.
        do 2 rewrite decode_base_nil.
        ring_simplify; auto.
      } {
        rewrite (skipn_nth_default n base 0) by omega.
        do 2 rewrite decode'_cons.
        ring_simplify; ring.
      } }
    { rewrite (nth_default_out_of_bounds _ base) by omega; ring_simplify.
      etransitivity; rewrite BaseSystem.decode'_truncate; [ reflexivity | ].
      apply f_equal.
      autorewrite with push_firstn simpl_update_nth.
      rewrite update_nth_out_of_bounds by (distr_length; omega * ).
      reflexivity. }
  Qed.

  Lemma unfold_add_to_nth n x
    : forall xs,
      add_to_nth n x xs
      = match n with
        | O => match xs with
	       | nil => nil
	       | x'::xs' => x + x'::xs'
	       end
        | S n' =>  match xs with
		   | nil => nil
		   | x'::xs' => x'::add_to_nth n' x xs'
		   end
        end.
  Proof.
    induction n; destruct xs; reflexivity.
  Qed.

  Lemma simpl_add_to_nth_0 x
    : forall xs,
      add_to_nth 0 x xs
      = match xs with
        | nil => nil
        | x'::xs' => x + x'::xs'
        end.
  Proof. intro; rewrite unfold_add_to_nth; reflexivity. Qed.

  Lemma simpl_add_to_nth_S x n
    : forall xs,
      add_to_nth (S n) x xs
      = match xs with
        | nil => nil
        | x'::xs' => x'::add_to_nth n x xs'
        end.
  Proof. intro; rewrite unfold_add_to_nth; reflexivity. Qed.

  Hint Rewrite @simpl_set_nth_S @simpl_set_nth_0 : simpl_add_to_nth.

  Lemma add_to_nth_cons : forall x u0 us, add_to_nth 0 x (u0 :: us) = x + u0 :: us.
  Proof. reflexivity. Qed.

  Hint Rewrite @add_to_nth_cons : simpl_add_to_nth.

  Lemma cons_add_to_nth : forall n f y us,
      y :: add_to_nth n f us = add_to_nth (S n) f (y :: us).
  Proof.
    induction n; boring.
  Qed.

  Hint Rewrite <- @cons_add_to_nth : simpl_add_to_nth.

  Lemma add_to_nth_nil : forall n f, add_to_nth n f nil = nil.
  Proof.
    induction n; boring.
  Qed.

  Hint Rewrite @add_to_nth_nil : simpl_add_to_nth.

  Lemma add_to_nth_set_nth n x xs
    : add_to_nth n x xs
      = set_nth n (x + nth_default 0 xs n) xs.
  Proof.
    revert xs; induction n; destruct xs;
      autorewrite with simpl_set_nth simpl_add_to_nth;
      try rewrite IHn;
      reflexivity.
  Qed.
  Lemma add_to_nth_update_nth n x xs
    : add_to_nth n x xs
      = update_nth n (fun y => x + y) xs.
  Proof.
    revert xs; induction n; destruct xs;
      autorewrite with simpl_update_nth simpl_add_to_nth;
      try rewrite IHn;
      reflexivity.
  Qed.

  Lemma length_add_to_nth i x xs : length (add_to_nth i x xs) = length xs.
  Proof. unfold add_to_nth; distr_length; reflexivity. Qed.

  Hint Rewrite @length_add_to_nth : distr_length.

  Lemma set_nth_sum : forall n x us, (n < length us \/ n >= length base)%nat ->
    BaseSystem.decode base (set_nth n x us) =
    (x - nth_default 0 us n) * nth_default 0 base n + BaseSystem.decode base us.
  Proof. intros; unfold set_nth; rewrite update_nth_sum by assumption; reflexivity. Qed.

  Lemma add_to_nth_sum : forall n x us, (n < length us \/ n >= length base)%nat ->
    BaseSystem.decode base (add_to_nth n x us) =
    x * nth_default 0 base n + BaseSystem.decode base us.
  Proof. unfold add_to_nth; intros; rewrite set_nth_sum; try ring_simplify; auto. Qed.

  Lemma add_to_nth_nth_default_full : forall n x l i d,
    nth_default d (add_to_nth n x l) i =
    if lt_dec i (length l) then
      if (eq_nat_dec i n) then x + nth_default d l i
      else nth_default d l i
    else d.
  Proof. intros; rewrite add_to_nth_update_nth; apply update_nth_nth_default_full; assumption. Qed.
  Hint Rewrite @add_to_nth_nth_default_full : push_nth_default.

  Lemma add_to_nth_nth_default : forall n x l i, (0 <= i < length l)%nat ->
    nth_default 0 (add_to_nth n x l) i =
    if (eq_nat_dec i n) then x + nth_default 0 l i else nth_default 0 l i.
  Proof. intros; rewrite add_to_nth_update_nth; apply update_nth_nth_default; assumption. Qed.
  Hint Rewrite @add_to_nth_nth_default using omega : push_nth_default.

  Lemma log_cap_nonneg : forall i, 0 <= log_cap i.
  Proof.
    unfold log_cap, nth_default; intros.
    case_eq (nth_error limb_widths i); intros; try omega.
    apply limb_widths_nonneg.
    eapply nth_error_value_In; eauto.
  Qed. Local Hint Resolve log_cap_nonneg.
End carrying_helper.

Hint Rewrite @simpl_set_nth_S @simpl_set_nth_0 : simpl_add_to_nth.
Hint Rewrite @add_to_nth_cons : simpl_add_to_nth.
Hint Rewrite <- @cons_add_to_nth : simpl_add_to_nth.
Hint Rewrite @add_to_nth_nil : simpl_add_to_nth.
Hint Rewrite @length_add_to_nth : distr_length.
Hint Rewrite @add_to_nth_nth_default_full : push_nth_default.
Hint Rewrite @add_to_nth_nth_default using (omega || distr_length; omega) : push_nth_default.

Section carrying.
  Context {limb_widths} (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).
  Local Hint Resolve limb_widths_nonneg sum_firstn_limb_widths_nonneg.

  (*
  Lemma length_carry_gen : forall f i us, length (carry_gen limb_widths f i us) = length us.
  Proof. intros; unfold carry_gen, carry_and_reduce_single; distr_length; reflexivity. Qed.

  Hint Rewrite @length_carry_gen : distr_length.
  *)

  Lemma length_carry_simple : forall i us, length (carry_simple limb_widths i us) = length us.
  Proof. intros; unfold carry_simple; distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry_simple : distr_length.

  Lemma nth_default_base_succ : forall i, (S i < length base)%nat ->
    nth_default 0 base (S i) = 2 ^ log_cap i * nth_default 0 base i.
  Proof.
    intros.
    rewrite !nth_default_base, <- Z.pow_add_r by (omega || eauto using log_cap_nonneg).
    autorewrite with simpl_sum_firstn; reflexivity.
  Qed.

  (*
  Lemma carry_gen_decode_eq : forall f i' us (i := (i' mod length base)%nat),
    (length us = length base) ->
    BaseSystem.decode base (carry_gen limb_widths f i' us)
    = ((f (nth_default 0 us i / 2 ^ log_cap i))
         * (if eq_nat_dec (S i mod length base) 0
            then nth_default 0 base 0
            else (2 ^ log_cap i) * (nth_default 0 base i))
       - (nth_default 0 us i / 2 ^ log_cap i) * 2 ^ log_cap i * nth_default 0 base i
      )
      + BaseSystem.decode base us.
  Proof.
    intros f i' us i H; intros.
    destruct (eq_nat_dec 0 (length base));
      [ destruct limb_widths, us, i; simpl in *; try congruence;
        unfold carry_gen, carry_and_reduce_single, add_to_nth;
        autorewrite with zsimplify simpl_nth_default simpl_set_nth simpl_update_nth distr_length;
        reflexivity
      | ].
    assert (0 <= i < length base)%nat by (subst i; auto with arith).
    assert (0 <= log_cap i) by auto using log_cap_nonneg.
    assert (2 ^ log_cap i <> 0) by (apply Z.pow_nonzero; lia).
    unfold carry_gen, carry_and_reduce_single.
    rewrite H; change (i' mod length base)%nat with i.
    rewrite add_to_nth_sum by (rewrite length_set_nth; omega).
    rewrite set_nth_sum by omega.
    unfold Z.pow2_mod.
    rewrite Z.land_ones by auto using log_cap_nonneg.
    rewrite Z.shiftr_div_pow2 by auto using log_cap_nonneg.
    destruct (eq_nat_dec (S i mod length base) 0);
      repeat first [ ring
                   | congruence
                   | match goal with H : _ = _ |- _ => rewrite !H in * end
                   | rewrite nth_default_base_succ by omega
                   | rewrite !(nth_default_out_of_bounds _ base) by omega
                   | rewrite !(nth_default_out_of_bounds _ us) by omega
                   | rewrite Z.mod_eq by assumption
                   | progress distr_length
                   | progress autorewrite with natsimplify zsimplify in *
                   | progress break_match ].
  Qed.

  Lemma carry_simple_decode_eq : forall i us,
    (length us = length base) ->
    (i < (pred (length base)))%nat ->
    BaseSystem.decode base (carry_simple limb_widths i us) = BaseSystem.decode base us.
  Proof.
    unfold carry_simple; intros; rewrite carry_gen_decode_eq by assumption.
    autorewrite with natsimplify.
    break_match; lia.
  Qed.
*)

  Lemma carry_simple_decode_eq : forall i us,
    (length us = length base) ->
    (i < (pred (length base)))%nat ->
    BaseSystem.decode base (carry_simple limb_widths i us) = BaseSystem.decode base us.
  Proof.
    unfold carry_simple. intros.
    rewrite add_to_nth_sum by (rewrite length_set_nth; omega).
    rewrite set_nth_sum by omega.
    unfold Z.pow2_mod.
    rewrite Z.land_ones by eauto using log_cap_nonneg.
    rewrite Z.shiftr_div_pow2 by eauto using log_cap_nonneg.
    rewrite nth_default_base_succ by omega.
    rewrite Z.mul_assoc.
    rewrite (Z.mul_comm _ (2 ^ log_cap i)).
    rewrite Z.mul_div_eq; try ring.
    apply Z.gt_lt_iff.
    apply Z.pow_pos_nonneg; omega || eauto using log_cap_nonneg.
  Qed.

  Lemma length_carry_simple_sequence : forall is us, length (carry_simple_sequence limb_widths is us) = length us.
  Proof.
    unfold carry_simple_sequence.
    induction is; [ reflexivity | simpl; intros ].
    distr_length.
    congruence.
  Qed.
  Hint Rewrite @length_carry_simple_sequence : distr_length.

  Lemma length_make_chain : forall i, length (make_chain i) = i.
  Proof. induction i; simpl; congruence. Qed.
  Hint Rewrite @length_make_chain : distr_length.

  Lemma length_full_carry_chain : length (full_carry_chain limb_widths) = length limb_widths.
  Proof. unfold full_carry_chain; distr_length; reflexivity. Qed.
  Hint Rewrite @length_full_carry_chain : distr_length.

  Lemma length_carry_simple_full us : length (carry_simple_full limb_widths us) = length us.
  Proof. unfold carry_simple_full; distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry_simple_full : distr_length.

  (* TODO : move? *)
  Lemma make_chain_lt : forall x i : nat, In i (make_chain x) -> (i < x)%nat.
  Proof.
    induction x; simpl; intuition.
  Qed.
(*
  Lemma nth_default_carry_gen_full : forall f d i n us,
      nth_default d (carry_gen limb_widths f i us) n
      = if lt_dec n (length us)
        then if eq_nat_dec n (i mod length us)
             then (if eq_nat_dec (S n) (length us)
                   then (if eq_nat_dec n 0
                         then f ((nth_default 0 us n) >> log_cap n)
                         else 0)
                   else 0)
                  + Z.pow2_mod (nth_default 0 us n) (log_cap n)
             else (if eq_nat_dec n (if eq_nat_dec (S (i mod length us)) (length us) then 0%nat else S (i mod length us))
                   then f (nth_default 0 us (i mod length us) >> log_cap (i mod length us))
                   else 0)
                  + nth_default d us n
        else d.
  Proof.
    unfold carry_gen, carry_and_reduce_single.
    intros; autorewrite with push_nth_default natsimplify distr_length.
    edestruct lt_dec; [ | reflexivity ].
    change (S ?x) with (1 + x)%nat.
    rewrite (Nat.add_mod_idemp_r 1 i (length us)) by omega.
    autorewrite with natsimplify.
    change (1 + ?x)%nat with (S x).
    destruct (eq_nat_dec n (i mod length us));
      subst; repeat break_match; omega.
  Qed.

  Hint Rewrite @nth_default_carry_gen_full : push_nth_default.

  Lemma nth_default_carry_simple_full : forall d i n us,
      nth_default d (carry_simple limb_widths i us) n
      = if lt_dec n (length us)
        then if eq_nat_dec n (i mod length us)
             then (if eq_nat_dec (S n) (length us)
                   then (if eq_nat_dec n 0
                         then (nth_default 0 us n >> log_cap n + Z.pow2_mod (nth_default 0 us n) (log_cap n))
                         (* FIXME: The above is just [nth_default 0 us n], but do we really care about the case of [n = 0], [length us = 1]? *)
                         else Z.pow2_mod (nth_default 0 us n) (log_cap n))
                   else Z.pow2_mod (nth_default 0 us n) (log_cap n))
             else (if eq_nat_dec n (if eq_nat_dec (S (i mod length us)) (length us) then 0%nat else S (i mod length us))
                   then nth_default 0 us (i mod length us) >> log_cap (i mod length us)
                   else 0)
                  + nth_default d us n
        else d.
  Proof.
    intros; unfold carry_simple; autorewrite with push_nth_default;
      repeat break_match; reflexivity.
  Qed.

  Hint Rewrite @nth_default_carry_simple_full : push_nth_default.

  Lemma nth_default_carry_gen
    : forall f i us,
      (0 <= i < length us)%nat
      -> nth_default 0 (carry_gen limb_widths f i us) i
         = (if PeanoNat.Nat.eq_dec i (if PeanoNat.Nat.eq_dec (S i) (length us) then 0%nat else S i)
            then f (nth_default 0 us i >> log_cap i) + Z.pow2_mod (nth_default 0 us i) (log_cap i)
            else Z.pow2_mod (nth_default 0 us i) (log_cap i)).
  Proof.
    unfold carry_gen, carry_and_reduce_single.
    intros; autorewrite with push_nth_default natsimplify; reflexivity.
  Qed.
  Hint Rewrite @nth_default_carry_gen using (omega || distr_length; omega) : push_nth_default.

  Lemma nth_default_carry_simple
    : forall f i us,
      (0 <= i < length us)%nat
      -> nth_default 0 (carry_gen limb_widths f i us) i
         = (if PeanoNat.Nat.eq_dec i (if PeanoNat.Nat.eq_dec (S i) (length us) then 0%nat else S i)
            then f (nth_default 0 us i >> log_cap i) + Z.pow2_mod (nth_default 0 us i) (log_cap i)
            else Z.pow2_mod (nth_default 0 us i) (log_cap i)).
  Proof.
    unfold carry_gen, carry_and_reduce_single.
    intros; autorewrite with push_nth_default natsimplify; reflexivity.
  Qed.
  Hint Rewrite @nth_default_carry_gen using (omega || distr_length; omega) : push_nth_default.


  Lemma nth_default_carry_gen
    : forall f i us,
      (0 <= i < length us)%nat
      -> nth_default 0 (carry_gen limb_widths f i us) i
         = (if PeanoNat.Nat.eq_dec i (if PeanoNat.Nat.eq_dec (S i) (length us) then 0%nat else S i)
            then f (nth_default 0 us i >> log_cap i) + Z.pow2_mod (nth_default 0 us i) (log_cap i)
            else Z.pow2_mod (nth_default 0 us i) (log_cap i)).
  Proof.
    unfold carry_gen, carry_and_reduce_single.
    intros; autorewrite with push_nth_default natsimplify; reflexivity.
  Qed.
  Hint Rewrite @nth_default_carry_gen using (omega || distr_length; omega) : push_nth_default.
*)
End carrying.

(*
Hint Rewrite @length_carry_gen : distr_length.
*)
Hint Rewrite @length_carry_simple @length_carry_simple_sequence @length_make_chain @length_full_carry_chain @length_carry_simple_full : distr_length.
(*
Hint Rewrite @nth_default_carry_gen_full : push_nth_default.
Hint Rewrite @nth_default_carry_gen using (omega || distr_length; omega) : push_nth_default.
*)
