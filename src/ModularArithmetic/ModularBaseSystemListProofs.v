Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.BaseSystem.
Require Import Crypto.BaseSystemProofs.
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

  Lemma length_conditional_subtract_modulus {u cond} :
    length u = length limb_widths
    -> length (conditional_subtract_modulus u cond) = length limb_widths.
  Proof.
    intros; unfold conditional_subtract_modulus.
    rewrite map2_length, map_length, length_modulus_digits.
    apply Min.min_case; omega.
  Qed.
  Hint Rewrite @length_conditional_subtract_modulus : distr_length.

  Lemma length_freeze {u} :
    length u = length limb_widths
    -> length (freeze u) = length limb_widths.
  Proof.
    intros; unfold freeze; repeat autorewrite with distr_length; congruence.
  Qed.

  Lemma length_pack : forall {target_widths}
                             {target_widths_nonneg : forall x, In x target_widths -> 0 <= x}
                             {pf us},
      length (pack target_widths_nonneg pf us) = length target_widths.
  Proof.
    cbv [pack]; intros.
    apply Pow2BaseProofs.length_convert.
  Qed.

  Lemma length_unpack : forall {target_widths}
                             {target_widths_nonneg : forall x, In x target_widths -> 0 <= x}
                             {pf us},
      length (unpack target_widths_nonneg pf us) = length limb_widths.
  Proof.
    cbv [pack]; intros.
    apply Pow2BaseProofs.length_convert.
  Qed.

End LengthProofs.

Section ConditionalSubtractModulusProofs.
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
  
  (* TODO : move to ZUtil *)
  Lemma add_compare_mono_r: forall n m p, (n + p ?= m + p) = (n ?= m).
  Proof.
    intros.
    rewrite <-!(Z.add_comm p).
    apply Z.add_compare_mono_l.
  Qed.

  (* TODO : move to ZUtil *)
  Lemma pow2_mod_id_iff : forall a n, 0 <= n ->
                                      Z.pow2_mod a n = a <-> 0 <= a < 2 ^ n.
  Proof.
    intros.
    rewrite Z.pow2_mod_spec by assumption.
    assert (0 < 2 ^ n) by zero_bounds.
    rewrite Z.mod_small_iff by omega.
    split; intros; intuition omega.
  Qed.

  (* TODO : move to ZUtil *)
  Lemma compare_add_shiftl : forall x1 y1 x2 y2 n, 0 <= n ->
    Z.pow2_mod x1 n = x1 -> Z.pow2_mod x2 n = x2  -> 
    x1 + (y1 << n) ?= x2 + (y2 << n) =
      if Z_eq_dec y1 y2
      then x1 ?= x2
      else y1 ?= y2.
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress subst y1
           | |- _ => rewrite Z.shiftl_mul_pow2 by omega
           | |- _ => rewrite add_compare_mono_r
           | |- _ => rewrite <-Z.mul_sub_distr_r 
           | |- _ => break_if
           | H : Z.pow2_mod _ _ = _ |- _ => rewrite pow2_mod_id_iff in H by omega
           | H : ?a <> ?b |- _ = (?a ?= ?b) => 
             case_eq (a ?= b); rewrite ?Z.compare_eq_iff, ?Z.compare_gt_iff, ?Z.compare_lt_iff
           | |- _ + (_ * _) > _ + (_ * _) => cbv [Z.gt] 
           | |- _ + (_ * ?x) < _ + (_ * ?x) =>
             apply Z.lt_sub_lt_add; apply Z.lt_le_trans with (m := 1 * x); [omega|]
           | |- _ => apply Z.mul_le_mono_nonneg_r; omega
           | |- _ => reflexivity
           | |- _ => congruence 
           end.
  Qed.

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
             | |- _ => rewrite compare_add_shiftl by
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

  Lemma ge_modulus'_false : forall us i,
    ge_modulus' us false i = false.
  Proof.
    induction i; intros; simpl; rewrite Bool.andb_false_r; auto.
  Qed.

  (* TODO : ZUtil *)
  Lemma add_pow_mod_l : forall a b c, a <> 0 -> 0 < b ->
                                      ((a ^ b) + c) mod a = c mod a.
  Proof.
    intros.
    replace b with (b - 1 + 1) by ring.
    rewrite Z.pow_add_r, Z.pow_1_r by omega.
    auto using Z.mod_add_l.
  Qed.

  (* TODO : ZUtil *)
  Lemma testbit_sub_pow2 : forall n i x, 0 <= i < n -> 0 < x < 2 ^ n ->
    Z.testbit (2 ^ n - x) i = negb (Z.testbit (x - 1)  i).
  Proof.
  Admitted.

  Lemma decode_modulus_digits : decode' base modulus_digits = modulus.
  Proof.
    cbv [modulus_digits].
    pose proof c_pos. pose proof modulus_pos.
    rewrite encodeZ_spec by eauto using limb_widths_nonnil, limb_widths_good.
    apply Z.mod_small.
    cbv [upper_bound]. fold k.
    assert (modulus = 2 ^ k - c) by (cbv [c]; ring).
    omega.
  Qed.

  Lemma modulus_digits_ones : forall i, (0 < i < length limb_widths)%nat ->
    nth_default 0 modulus_digits i = Z.ones (nth_default 0 limb_widths i).
  Proof.
    repeat match goal with
           | |- _ => progress (cbv [BaseSystem.decode]; intros)
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => unique pose proof c_pos
           | |- _ => unique pose proof modulus_pos
           | |- _ => unique assert (modulus = 2 ^ k - c) by (cbv [c]; ring)
           | |- _ => break_if
           | |- _ => rewrite decode_modulus_digits 
           | |- _ => rewrite Z.testbit_pow2_mod
                       by eauto using nth_default_limb_widths_nonneg
           | |- _ => rewrite Z.ones_spec by eauto using nth_default_limb_widths_nonneg
           | |- _ => erewrite digit_select
                        by (eauto; apply bounded_encodeZ; eauto; omega)
           | |- Z.testbit (2 ^ k - c) _ = _ =>
             rewrite testbit_sub_pow2 by (try omega; cbv [k];
               pose proof (sum_firstn_prefix_le limb_widths (S i) (length limb_widths));
               specialize_by (eauto || omega);
               rewrite sum_firstn_succ_default in *; split; zero_bounds; eauto)
           | |- Z.pow2_mod _ _ = Z.ones _ => apply Z.bits_inj'
           | |- Z.testbit modulus ?i = true => transitivity (Z.testbit (2 ^ k - c) i)
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
        
  Lemma ge_modulus'_compare' : forall us, length us = length limb_widths -> bounded limb_widths us ->
    forall i, (i < length limb_widths)%nat ->
    (ge_modulus' us true i = false <-> compare' us modulus_digits (S i) = Lt).
  Proof.
    induction i;
      repeat match goal with
             | |- _ => progress intros
             | |- _ => progress (simpl ge_modulus'; simpl compare' in *)
             | |- _ => progress specialize_by omega
             | |- _ => progress rewrite ?Z.compare_eq_iff,
                       ?Z.compare_gt_iff, ?Z.compare_lt_iff in *
             | |- _ => break_if
             | |- _ => rewrite Nat.sub_0_r
             | |- _ => rewrite ge_modulus'_false 
             | |- _ => rewrite Bool.andb_true_r
             | |- _ => rewrite Z.leb_compare; break_match
             | |- _ => rewrite Z.eqb_compare; break_match
             | |- _ => split; (congruence || omega)
             | |- _ => assumption
             end;
      pose proof (bounded_le_modulus_digits us (S i));
      specialize_by (auto || omega); omega.
  Qed.

   Lemma ge_modulus_spec : forall u, length u = length limb_widths ->
     bounded limb_widths u ->
    (ge_modulus u = false <-> 0 <= BaseSystem.decode base u < modulus).
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

  Lemma conditional_subtract_modulus_spec : forall u cond,
    length u = length limb_widths ->
    BaseSystem.decode base (conditional_subtract_modulus u cond) =
    BaseSystem.decode base u - (if cond then 1 else 0) * modulus.
  Proof.
  Admitted.

  Lemma conditional_subtract_modulus_preserves_bounded : forall u,
      bounded limb_widths u ->
      bounded limb_widths (conditional_subtract_modulus u (ge_modulus u)).
  Proof.
  Admitted.

  Lemma conditional_subtract_lt_modulus : forall u,
    bounded limb_widths u ->
    ge_modulus (conditional_subtract_modulus u (ge_modulus u)) = false.
  Proof.
  Admitted.
End ConditionalSubtractModulusProofs.