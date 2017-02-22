Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.BaseSystem.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.Conversion.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.

Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.ModularArithmetic.ModularBaseSystemList.
Local Open Scope Z_scope.

Section LengthProofs.
  Context `{prm :PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).

  Lemma length_encode {x} : length (encode x) = length limb_widths.
  Proof.
    cbv [encode encodeZ]; intros.
    rewrite encode'_spec;
      auto using encode'_length, limb_widths_nonneg, Nat.eq_le_incl, base_from_limb_widths_length.
  Qed.

  Lemma length_reduce : forall us,
      (length limb_widths <= length us <= length (ext_base limb_widths))%nat ->
      (length (reduce us) = length limb_widths)%nat.
  Proof.
    rewrite extended_base_length.
    unfold reduce; intros.
    rewrite add_length_exact.
    pose proof (@base_from_limb_widths_length limb_widths).
    rewrite map_length, firstn_length, skipn_length, Min.min_l, Max.max_l;
      omega.
  Qed.

  Lemma length_mul {u v} :
      length u = length limb_widths
      -> length v = length limb_widths
      -> length (mul u v) = length limb_widths.
  Proof.
    cbv [mul]; intros.
    apply length_reduce.
    destruct u; try congruence.
    + rewrite @nil_length0 in *; omega.
    + rewrite mul_length_exact, extended_base_length, base_from_limb_widths_length; try omega;
        repeat match goal with
               | |- _ => progress intros
               | |- nth_default _ (ext_base _) 0 = 1 => apply b0_1
               | x := nth_default _ (ext_base _) |- _ => apply ext_base_good
               | x := nth_default _ base |- _ => apply base_good
               | x := nth_default _ base |- _ => apply limb_widths_good
               | |- 2 ^ _ <> 0 => apply Z.pow_nonzero
               | |- _ => solve [apply BaseSystem.b0_1]
               | |- _ => solve [auto using limb_widths_nonneg, sum_firstn_limb_widths_nonneg, limb_widths_match_modulus]
               | |- _ => omega
               | |- _ => congruence
               end.
  Qed.

  Section Sub.
  Context {mm : list Z} (mm_length : length mm = length limb_widths).

  Lemma length_sub {u v} :
      length u = length limb_widths
      -> length v = length limb_widths
      -> length (sub mm u v) = length limb_widths.
  Proof.
    cbv [sub]; intros.
    rewrite sub_length, add_length_exact.
    repeat rewrite Max.max_r; omega.
  Qed.
  End Sub.

  Lemma length_carry_and_reduce {us}: forall i, length (carry_and_reduce i us) = length us.
  Proof. intros; unfold carry_and_reduce; autorewrite with distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry_and_reduce : distr_length.

  Lemma length_carry {u i} :
    length u = length limb_widths
    -> length (carry i u) = length limb_widths.
  Proof. intros; unfold carry; break_if; autorewrite with distr_length; omega. Qed.
  Hint Rewrite @length_carry : distr_length.

  Lemma length_carry_sequence {u i} :
    length u = length limb_widths
    -> length (carry_sequence i u) = length limb_widths.
  Proof.
   induction i; intros; unfold carry_sequence;
     simpl; autorewrite with distr_length; auto. Qed.
  Hint Rewrite @length_carry_sequence : distr_length.

  Lemma length_carry_full {u} :
    length u = length limb_widths
    -> length (carry_full u) = length limb_widths.
  Proof. intros; unfold carry_full; autorewrite with distr_length; congruence. Qed.
  Hint Rewrite @length_carry_full : distr_length.

  Lemma length_modulus_digits : length modulus_digits = length limb_widths.
  Proof.
    intros; unfold modulus_digits, encodeZ.
    rewrite encode'_spec, encode'_length;
      auto using encode'_length, limb_widths_nonneg, Nat.eq_le_incl, base_from_limb_widths_length.
  Qed.
  Hint Rewrite @length_modulus_digits : distr_length.

  Lemma length_conditional_subtract_modulus {int_width u cond} :
    length u = length limb_widths
    -> length (conditional_subtract_modulus int_width u cond) = length limb_widths.
  Proof.
    intros; unfold conditional_subtract_modulus.
    rewrite map2_length, map_length, length_modulus_digits.
    apply Min.min_case; omega.
  Qed.
  Hint Rewrite @length_conditional_subtract_modulus : distr_length.

  Lemma length_freeze {int_width u} :
    length u = length limb_widths
    -> length (freeze int_width u) = length limb_widths.
  Proof.
    intros; unfold freeze; repeat autorewrite with distr_length; congruence.
  Qed.

  Lemma length_pack : forall {target_widths}
                             {target_widths_nonneg : forall x, In x target_widths -> 0 <= x}
                             {pf us},
      length (pack target_widths_nonneg pf us) = length target_widths.
  Proof.
    cbv [pack]; intros.
    apply length_convert.
  Qed.

  Lemma length_unpack : forall {target_widths}
                             {target_widths_nonneg : forall x, In x target_widths -> 0 <= x}
                             {pf us},
      length (unpack target_widths_nonneg pf us) = length limb_widths.
  Proof.
    cbv [pack]; intros.
    apply length_convert.
  Qed.

End LengthProofs.

Section ModulusDigitsProofs.
  Context `{prm :PseudoMersenneBaseParams}
          (c_upper_bound : c - 1 < 2 ^ nth_default 0 limb_widths 0).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Hint Resolve sum_firstn_limb_widths_nonneg.
  Local Hint Resolve limb_widths_nonneg.

  Lemma decode_modulus_digits : decode' base modulus_digits = modulus.
  Proof.
    cbv [modulus_digits].
    pose proof c_pos. pose proof modulus_pos.
    rewrite encodeZ_spec by eauto using limb_widths_nonnil, limb_widths_good.
    apply Z.mod_small.
    cbv [upper_bound]. fold k.
    assert (Z.pos modulus = 2 ^ k - c) by (cbv [c]; ring).
    omega.
  Qed.

  Lemma bounded_modulus_digits : bounded limb_widths modulus_digits.
  Proof.
    apply bounded_encodeZ; auto using limb_widths_nonneg.
    pose proof modulus_pos; omega.
  Qed.

  Lemma modulus_digits_ones : forall i, (0 < i < length limb_widths)%nat ->
    nth_default 0 modulus_digits i = Z.ones (nth_default 0 limb_widths i).
  Proof.
    repeat match goal with
           | |- _ => progress (cbv [BaseSystem.decode]; intros)
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => unique pose proof c_pos
           | |- _ => unique pose proof modulus_pos
           | |- _ => unique assert (Z.pos modulus = 2 ^ k - c) by (cbv [c]; ring)
           | |- _ => break_if
           | |- _ => rewrite decode_modulus_digits
           | |- _ => rewrite Z.testbit_pow2_mod
                       by eauto using nth_default_limb_widths_nonneg
           | |- _ => rewrite Z.ones_spec by eauto using nth_default_limb_widths_nonneg
           | |- _ => erewrite digit_select
                        by (eauto; apply bounded_encodeZ; eauto; omega)
           | |- Z.testbit (2 ^ k - c) _ = _ =>
             rewrite Z.testbit_sub_pow2 by (try omega; cbv [k];
               pose proof (sum_firstn_prefix_le limb_widths (S i) (length limb_widths));
               specialize_by (eauto || omega);
               rewrite sum_firstn_succ_default in *; split; zero_bounds; eauto)
           | |- Z.pow2_mod _ _ = Z.ones _ => apply Z.bits_inj'
           | |- Z.testbit (Z.pos modulus) ?i = true => transitivity (Z.testbit (2 ^ k - c) i)
           | |- _ => congruence
           end.

    replace (c - 1) with ((c - 1) mod 2 ^ nth_default 0 limb_widths 0) by (apply Z.mod_small; omega).
    rewrite Z.mod_pow2_bits_high; auto.
    pose proof (sum_firstn_prefix_le limb_widths 1 i).
    specialize_by (eauto ||  omega).
    rewrite !sum_firstn_succ_default, !sum_firstn_0 in *.
    split; zero_bounds; eauto using nth_default_limb_widths_nonneg.
  Qed.

  Lemma bounded_le_modulus_digits : forall us i, length us = length limb_widths ->
    bounded limb_widths us -> (0 < i < length limb_widths)%nat ->
    nth_default 0 us i <= nth_default 0 modulus_digits i.
  Proof.
    intros until 0; rewrite bounded_iff; intros.
    rewrite modulus_digits_ones by omega.
    specialize (H0 i).
    rewrite Z.ones_equiv.
    omega.
  Qed.

End ModulusDigitsProofs.

Section ModulusComparisonProofs.
  Context `{prm :PseudoMersenneBaseParams}
          (c_upper_bound : c - 1 < 2 ^ nth_default 0 limb_widths 0).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Hint Resolve sum_firstn_limb_widths_nonneg.
  Local Hint Resolve limb_widths_nonneg.

  Fixpoint compare' us vs i :=
    match i with
    | O => Eq
    | S i' => if Z_eq_dec (nth_default 0 us i') (nth_default 0 vs i')
              then compare' us vs i'
              else Z.compare (nth_default 0 us i') (nth_default 0 vs i')
    end.

  (* Lexicographically compare two vectors of equal length, starting from the END of the list
     (in our context, this is the most significant end). NOT constant time. *)
  Definition compare us vs := compare' us vs (length us).

  Lemma decode_firstn_compare' : forall us vs i,
    (i <= length limb_widths)%nat ->
    length us = length limb_widths -> bounded limb_widths us ->
    length vs = length limb_widths -> bounded limb_widths vs ->
    (Z.compare (decode' base (firstn i us)) (decode' base (firstn i vs))
     = compare' us vs i).
  Proof.
    induction i;
      repeat match goal with
             | |- _ => progress intros
             | |- _ => progress (simpl compare')
             | |- _ => progress specialize_by (assumption || omega)
             | |- _ => rewrite sum_firstn_0
             | |- _ => rewrite set_higher
             | |- _ => rewrite nth_default_base by eauto
             | |- _ => rewrite firstn_length, Min.min_l by omega
             | |- _ => rewrite firstn_O
             | |- _ => rewrite firstn_succ with (d := 0) by omega
             | |- _ => rewrite Z.compare_add_shiftl by
               (eauto || (rewrite decode_firstn_pow2_mod, Z.pow2_mod_pow2_mod, Z.min_id by
                  (eauto || omega); reflexivity))
             | |- appcontext[2 ^ ?x * ?y] => replace (2 ^ x * y) with (y << x) by
               (rewrite (Z.mul_comm (2 ^ x)); apply Z.shiftl_mul_pow2; eauto)
             | |- _ => tauto
             | |- _ => split
             | |- _ => break_if
             end.
  Qed.

  Lemma decode_compare' : forall us vs,
    length us = length limb_widths -> bounded limb_widths us ->
    length vs = length limb_widths -> bounded limb_widths vs ->
    (Z.compare (decode' base us) (decode' base vs)
     = compare' us vs (length limb_widths)).
  Proof.
    intros.
    rewrite <-decode_firstn_compare' by (auto || omega).
    rewrite !firstn_all by auto.
    reflexivity.
  Qed.

  Lemma ge_modulus'_0 : forall {A} f us i,
    ge_modulus' (A := A) f us 0 i = f 0.
  Proof.
    induction i; intros; simpl; cbv [cmovne cmovl]; break_if; auto.
  Qed.

  Lemma ge_modulus'_01 : forall {A} f us i b,
    (b = 0 \/ b = 1) ->
    (ge_modulus' (A := A) f us b i = f 0 \/ ge_modulus' (A := A) f us b i = f 1).
  Proof.
    induction i; intros;
      try intuition (subst; cbv [ge_modulus' LetIn.Let_In cmovl cmovne]; break_if; tauto).
    simpl; cbv [LetIn.Let_In cmovl cmovne].
    break_if; apply IHi; tauto.
  Qed.

  Lemma ge_modulus_01 : forall us,
    (ge_modulus us = 0 \/ ge_modulus us = 1).
  Proof.
    cbv [ge_modulus]; intros; apply ge_modulus'_01; tauto.
  Qed.

  Lemma ge_modulus'_true_digitwise : forall us,
    length us = length limb_widths ->
    forall i, (i < length us)%nat -> ge_modulus' id us 1 i = 1 ->
              forall j, (j <= i)%nat ->
                        nth_default 0 modulus_digits j <= nth_default 0 us j.
  Proof.
    induction i;
      repeat match goal with
             | |- _ => progress intros; simpl in *
             | |- _ => progress cbv [LetIn.Let_In cmovne cmovl] in *
             | |- _ =>erewrite (ge_modulus'_0 (@id Z)) in *
             | H : (?x <= 0)%nat |- _ => progress replace x with 0%nat in * by omega
             | |- _ => break_if
             | |- _ => discriminate
             | |- _ => solve [rewrite ?Z.leb_le, ?Z.eqb_eq in *; omega]
             end.
    destruct (le_dec j i).
    + apply IHi; auto; omega.
    + replace j with (S i) in * by omega; rewrite Z.eqb_eq in *; try omega.
  Qed.

  Lemma ge_modulus'_compare' : forall us, length us = length limb_widths -> bounded limb_widths us ->
    forall i, (i < length limb_widths)%nat ->
    (ge_modulus' id us 1 i = 0 <-> compare' us modulus_digits (S i) = Lt).
  Proof.
    induction i;
      repeat match goal with
             | |- _ => progress (intros; cbv [LetIn.Let_In id cmovne cmovl])
             | |- _ => progress (simpl compare' in * )
             | |- _ => progress specialize_by omega
             | |- _ => (progress rewrite ?Z.compare_eq_iff,
                       ?Z.compare_gt_iff, ?Z.compare_lt_iff in * )
             | |- appcontext[ge_modulus' _  _ _ 0] =>
               cbv [ge_modulus']
             | |- appcontext[ge_modulus' _ _ _ (S _)] =>
               unfold ge_modulus'; fold (ge_modulus' (@id Z))
             | |- _ => break_if
             | |- _ => rewrite Nat.sub_0_r
             | |- _ => rewrite (ge_modulus'_0 (@id Z))
             | |- _ => rewrite Bool.andb_true_r
             | |- _ => rewrite Z.leb_compare; break_match
             | |- _ => rewrite Z.eqb_compare; break_match
             | |- _ => (rewrite Z.leb_le in * )
             | |- _ => (rewrite Z.leb_gt in * )
             | |- _ => (rewrite Z.eqb_eq in * )
             | |- _ => (rewrite Z.eqb_neq in * )
             | |- _ => split; (congruence || omega)
             | |- _ => assumption
             end;
       pose proof (bounded_le_modulus_digits c_upper_bound us (S i));
         specialize_by (auto || omega); split; (congruence || omega).
  Qed.

   Lemma ge_modulus_spec : forall u, length u = length limb_widths ->
     bounded limb_widths u ->
    (ge_modulus u = 0 <-> 0 <= BaseSystem.decode base u < modulus).
  Proof.
    cbv [ge_modulus]; intros.
    assert (0 < length limb_widths)%nat
      by (pose proof limb_widths_nonnil; destruct limb_widths;
          distr_length; omega || congruence).
    rewrite ge_modulus'_compare' by (auto || omega).
    replace (S (length limb_widths - 1)) with (length limb_widths) by omega.
    rewrite <-decode_compare'
      by (try (apply length_modulus_digits || apply bounded_encodeZ); eauto;
          pose proof modulus_pos; omega).
    rewrite Z.compare_lt_iff.
    rewrite decode_modulus_digits.
    repeat (split; intros; eauto using decode_nonneg).
    cbv [BaseSystem.decode] in *. omega.
  Qed.

End ModulusComparisonProofs.

Section ConditionalSubtractModulusProofs.
  Context `{prm :PseudoMersenneBaseParams}
          (* B is machine integer width (e.g. 32, 64) *)
          {B} (B_pos : 0 < B) (B_compat : forall w, In w limb_widths -> w <= B)
          (c_upper_bound : c - 1 < 2 ^ nth_default 0 limb_widths 0)
          (lt_1_length_limb_widths : (1 < length limb_widths)%nat).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Hint Resolve sum_firstn_limb_widths_nonneg.
  Local Hint Resolve limb_widths_nonneg.
  Local Hint Resolve length_modulus_digits.

  Lemma map2_sub_eq : forall us vs, length us = length vs ->
    map2 (fun x y => x - y) us vs = BaseSystem.sub us vs.
  Proof.
    induction us; destruct vs; boring; try omega.
  Qed.

  (* TODO : ListUtil *)
  Lemma map_id_strong : forall {A} f (xs : list A),
    (forall x, In x xs -> f x = x) -> map f xs = xs.
  Proof.
    induction xs; intros; auto.
    simpl; f_equal; auto using in_eq, in_cons.
  Qed.

  Lemma bounded_digit_fits : forall us,
    length us = length limb_widths -> bounded limb_widths us ->
    forall x, In x us -> 0 <= x < 2 ^ B.
  Proof.
    intros.
    let i := fresh "i" in
    match goal with H : In ?x ?us, Hb : bounded _ _ |- _ =>
                    apply In_nth with (d := 0) in H; destruct H as [i [? ?] ];
                      rewrite bounded_iff in Hb; specialize (Hb i);
                        assert (2 ^ nth i limb_widths 0 <= 2 ^ B) by
                          (apply Z.pow_le_mono_r; try apply B_compat, nth_In; omega) end.
    rewrite !nth_default_eq in *.
    omega.
  Qed.

  Lemma map_land_max_ones : forall us,
    length us = length limb_widths ->
    bounded limb_widths us -> map (Z.land (Z.ones B)) us = us.
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => apply map_id_strong
           | |- appcontext[Z.ones ?n &' ?x] => rewrite (Z.land_comm _ x);
                                                 rewrite Z.land_ones by omega
           | |- _ => apply Z.mod_small
           | |- _ => solve [eauto using bounded_digit_fits]
           end.
  Qed.

  Lemma map_land_zero : forall us, map (Z.land 0) us = zeros (length us).
  Proof.
    induction us; boring.
  Qed.

  Hint Rewrite @length_modulus_digits @length_zeros : distr_length.
  Lemma conditional_subtract_modulus_spec : forall u cond
    (cond_01 : cond = 0 \/ cond = 1),
    length u = length limb_widths ->
    BaseSystem.decode base (conditional_subtract_modulus B u cond) =
    BaseSystem.decode base u - cond * modulus.
  Proof.
    repeat match goal with
           | |- _ => progress (cbv [conditional_subtract_modulus neg]; intros)
           | |- _ => destruct cond_01; subst
           | |- _ => break_if
           | |- _ => rewrite map_land_max_ones by auto using bounded_modulus_digits
           | |- _ => rewrite map_land_zero
           | |- _ => rewrite map2_sub_eq by distr_length
           | |- _ => rewrite sub_rep by auto
           | |- _ => rewrite zeros_rep
           | |- _ => rewrite decode_modulus_digits by auto
           | |- _ => f_equal; ring
           | |- _ => discriminate
           end.
  Qed.

  Lemma conditional_subtract_modulus_preserves_bounded : forall u,
      length u = length limb_widths ->
      bounded limb_widths u ->
      bounded limb_widths (conditional_subtract_modulus B u (ge_modulus u)).
  Proof.
    repeat match goal with
           | |- _ => progress (cbv [conditional_subtract_modulus neg]; intros)
           | |- _ => unique pose proof bounded_modulus_digits
           | |- _ => rewrite map_land_max_ones by auto using bounded_modulus_digits
           | |- _ => rewrite map_land_zero
           | |- _ => rewrite length_modulus_digits in *
           | |- _ => rewrite length_zeros in *
           | |- _ => rewrite Min.min_l in * by omega
           | |- _ => rewrite nth_default_zeros
           | |- _ => rewrite nth_default_map2 with (d1 := 0) (d2 := 0)
           | |- _ => break_if
           | |- bounded _ _ => apply bounded_iff
           | |- 0 <= 0 < _ => split; zero_bounds; eauto using nth_default_limb_widths_nonneg
           end;
    repeat match goal with
           | H : bounded _ ?x |- appcontext[nth_default 0 ?x ?i] =>
             rewrite bounded_iff in H; specialize (H i)
           | |- _ => omega
           end.
    cbv [ge_modulus] in Heqb.
    rewrite Z.eqb_eq in *.
    apply ge_modulus'_true_digitwise with (j := i) in Heqb; auto; omega.
  Qed.

  Lemma bounded_mul2_modulus : forall u, length u = length limb_widths ->
    bounded limb_widths u -> ge_modulus u = 1 ->
    modulus <= BaseSystem.decode base u < 2 * modulus.
  Proof.
    intros.
    pose proof (@decode_upper_bound _ limb_widths_nonneg u).
    specialize_by auto.
    cbv [upper_bound] in *.
    fold k in *.
    assert (Z.pos modulus = 2 ^ k - c) by (cbv [c]; ring).
    destruct (Z_le_dec modulus (BaseSystem.decode base u)).
    + split; try omega.
      apply Z.lt_le_trans with (m := 2 ^ k); try omega.
      assert (2 * c <= 2 ^ k); try omega.
      transitivity (2 ^ (nth_default 0 limb_widths 0 + 1));
        try (rewrite Z.pow_add_r, ?Z.pow_1_r;
             eauto using nth_default_limb_widths_nonneg; omega).
      apply Z.pow_le_mono_r; try omega.
      unfold k.
      pose proof (sum_firstn_prefix_le limb_widths 2 (length limb_widths)).
      specialize_by (eauto || omega).
      etransitivity; try eassumption.
      rewrite !sum_firstn_succ_default, sum_firstn_0.
      assert (0 < nth_default 0 limb_widths 1); try omega.
      apply limb_widths_pos.
      rewrite nth_default_eq.
      apply nth_In.
      omega.
    + assert (0 <= BaseSystem.decode base u < modulus) as Hlt_modulus by omega.
      apply ge_modulus_spec in Hlt_modulus; auto.
      congruence.
  Qed.

  Lemma conditional_subtract_lt_modulus : forall u,
    length u = length limb_widths ->
    bounded limb_widths u ->
    ge_modulus (conditional_subtract_modulus B u (ge_modulus u)) = 0.
  Proof.
    intros.
    rewrite ge_modulus_spec by auto using length_conditional_subtract_modulus, conditional_subtract_modulus_preserves_bounded.
    pose proof (ge_modulus_01 u) as Hgm01.
    rewrite conditional_subtract_modulus_spec by auto.
    destruct Hgm01 as [Hgm0 | Hgm1]; rewrite ?Hgm0, ?Hgm1.
    + apply ge_modulus_spec in Hgm0; auto.
      omega.
    + pose proof (bounded_mul2_modulus u); specialize_by auto.
      omega.
  Qed.
End ConditionalSubtractModulusProofs.
