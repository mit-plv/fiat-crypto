Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Coq.funind.Recdef.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SubstLet.
Require Import Crypto.Util.Tactics.Forward.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs Crypto.BaseSystemProofs.
Require Import Crypto.Util.Notations.
Require Export Crypto.Util.FixCoqMistakes.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Section ConversionHelper.
  Local Hint Resolve in_eq in_cons.

  (* concatenates first n bits of a with all bits of b *)
  Definition concat_bits n a b := Z.lor (Z.pow2_mod a n) (b << n).

  Lemma concat_bits_spec : forall a b n i, 0 <= n ->
                                           Z.testbit (concat_bits n a b) i =
                                           if Z_lt_dec i n then Z.testbit a i else Z.testbit b (i - n).
  Proof.
    repeat match goal with
           | |- _ => progress cbv [concat_bits]; intros
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => rewrite Z.testbit_pow2_mod by omega
           | |- _ => rewrite Z.testbit_neg_r by omega
           | |- _ => break_if
           | |- appcontext [Z.testbit (?a << ?b) ?i] => destruct (Z_le_dec 0 i)
           | |- (?a || ?b)%bool = ?a => replace b with false
           | |- _ => reflexivity
           end.
  Qed.

  Definition update_by_concat_bits num_low_bits bits x := concat_bits num_low_bits x bits.

End ConversionHelper.

Section Conversion.
  Context {limb_widthsA} (limb_widthsA_nonneg : forall w, In w limb_widthsA -> 0 <= w)
          {limb_widthsB} (limb_widthsB_nonneg : forall w, In w limb_widthsB -> 0 <= w).
  Local Notation bitsIn lw := (sum_firstn lw (length lw)).
  Context (bits_fit : bitsIn limb_widthsA <=  bitsIn limb_widthsB).
  Local Notation decodeA := (BaseSystem.decode (base_from_limb_widths limb_widthsA)).
  Local Notation decodeB := (BaseSystem.decode (base_from_limb_widths limb_widthsB)).
  Local Notation "u # i" := (nth_default 0 u i).
  Local Hint Resolve in_eq in_cons nth_default_limb_widths_nonneg sum_firstn_limb_widths_nonneg Nat2Z.is_nonneg.
  Local Opaque bounded.

  Function convert' inp i out
           {measure (fun x => Z.to_nat ((bitsIn limb_widthsA) - Z.of_nat x)) i}:=
    if Z_le_dec (bitsIn limb_widthsA) (Z.of_nat i)
    then out
    else
      let digitA := digit_index limb_widthsA (Z.of_nat i) in
      let digitB := digit_index limb_widthsB (Z.of_nat i) in
      let indexA :=   bit_index limb_widthsA (Z.of_nat i) in
      let indexB :=   bit_index limb_widthsB (Z.of_nat i) in
      let dist := Z.min ((limb_widthsA # digitA) - indexA) ((limb_widthsB # digitB) - indexB) in
      let bitsA := Z.pow2_mod ((inp # digitA) >> indexA) dist in
      convert' inp (i + Z.to_nat dist)%nat (update_nth digitB (update_by_concat_bits indexB bitsA) out).
  Proof.
    generalize limb_widthsA_nonneg; intros _. (* don't drop this from the proof in 8.4 *)
    generalize limb_widthsB_nonneg; intros _. (* don't drop this from the proof in 8.4 *)
    repeat match goal with
           | |- _ => progress intros
           | |- appcontext [bit_index (Z.of_nat ?i)] =>
             unique pose proof (Nat2Z.is_nonneg i)
           | H : forall x : Z, In x ?lw -> 0 <= x |- appcontext [bit_index ?lw ?i] =>
             unique pose proof (bit_index_not_done lw i)
           | H : forall x : Z, In x ?lw -> 0 <= x |- appcontext [bit_index ?lw ?i] =>
             unique assert (0 <= i < bitsIn lw -> i + ((lw # digit_index lw i) - bit_index lw i) <= bitsIn lw) by auto using rem_bits_in_digit_le_rem_bits
           | |- _ => rewrite Z2Nat.id
           | |- _ => rewrite Nat2Z.inj_add
           | |- (Z.to_nat _ < Z.to_nat _)%nat => apply Z2Nat.inj_lt
           | |- (?a - _ < ?a - _) => apply Z.sub_lt_mono_l
           | |- appcontext [Z.min ?a ?b] => unique assert (0 < Z.min a b) by (specialize_by lia; lia)
           | |- _ => lia
           end.
  Defined.

  Definition convert'_invariant inp i out :=
    length out = length limb_widthsB
    /\ bounded limb_widthsB out
    /\ Z.of_nat i <= bitsIn limb_widthsA
    /\ forall n, Z.testbit (decodeB out) n = if Z_lt_dec n (Z.of_nat i) then Z.testbit (decodeA inp) n else false.

  Ltac subst_lia := subst_let; subst; lia.

  Lemma convert'_bounded_step : forall inp i out,
    bounded limb_widthsB out ->
    let digitA := digit_index limb_widthsA (Z.of_nat i) in
    let digitB := digit_index limb_widthsB (Z.of_nat i) in
    let indexA :=   bit_index limb_widthsA (Z.of_nat i) in
    let indexB :=   bit_index limb_widthsB (Z.of_nat i) in
    let dist := Z.min ((limb_widthsA # digitA) - indexA)
                      ((limb_widthsB # digitB) - indexB) in
    let bitsA := Z.pow2_mod ((inp # digitA) >> indexA) dist in
    0 < dist ->
    bounded limb_widthsB (update_nth digitB (update_by_concat_bits indexB bitsA) out).
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => rewrite update_nth_nth_default_full
           | |- _ => rewrite Z.testbit_pow2_mod
           | |- _ => break_if
           | |- _ =>  progress cbv [update_by_concat_bits];
                        rewrite concat_bits_spec by (apply bit_index_nonneg; auto using Nat2Z.is_nonneg)
           | |- bounded _ _ => apply pow2_mod_bounded_iff
           | |- Z.pow2_mod _ _ = _ => apply Z.bits_inj'
           | |- false = Z.testbit _ _ => symmetry
           | x := _ |- Z.testbit ?x _ = _ => subst x
           | |- Z.testbit _ _ = false => eapply testbit_bounded_high; eauto; lia
           | |- _ => solve [auto]
           | |- _ => subst_lia
    end.
  Qed.

  Lemma convert'_index_step : forall inp i out,
    bounded limb_widthsB out ->
    let digitA := digit_index limb_widthsA (Z.of_nat i) in
    let digitB := digit_index limb_widthsB (Z.of_nat i) in
    let indexA :=   bit_index limb_widthsA (Z.of_nat i) in
    let indexB :=   bit_index limb_widthsB (Z.of_nat i) in
    let dist := Z.min ((limb_widthsA # digitA) - indexA)
                      ((limb_widthsB # digitB) - indexB) in
    let bitsA := Z.pow2_mod ((inp # digitA) >> indexA) dist in
    0 < dist ->
    Z.of_nat i < bitsIn limb_widthsA ->
    Z.of_nat i + dist <= bitsIn limb_widthsA.
  Proof.
    pose proof (rem_bits_in_digit_le_rem_bits limb_widthsA).
    pose proof (rem_bits_in_digit_le_rem_bits limb_widthsA).
    repeat match goal with
           | |- _ => progress intros
           | H : forall x : Z, In x ?lw -> x = ?y, H0 : 0 < ?y |- _ =>
              unique pose proof (uniform_limb_widths_nonneg H0 lw H)
           | |- _ => progress specialize_by assumption
           | H : _ /\ _ |- _ => destruct H
           | |- _ => break_if
           | |- _ => split
           | a := digit_index _ ?i, H : forall x, 0 <= x < bitsIn _ -> _ |- _ => specialize (H i); forward H
           | |- _ => subst_lia
           | |- _ => apply bit_index_pos_iff; auto
           | |- _ => apply Nat2Z.is_nonneg
    end.
  Qed.

  Lemma convert'_invariant_step : forall inp i out,
    length inp = length limb_widthsA ->
    bounded limb_widthsA inp ->
    convert'_invariant inp i out ->
    let digitA := digit_index limb_widthsA (Z.of_nat i) in
    let digitB := digit_index limb_widthsB (Z.of_nat i) in
    let indexA :=   bit_index limb_widthsA (Z.of_nat i) in
    let indexB :=   bit_index limb_widthsB (Z.of_nat i) in
    let dist := Z.min ((limb_widthsA # digitA) - indexA)
                      ((limb_widthsB # digitB) - indexB) in
    let bitsA := Z.pow2_mod ((inp # digitA) >> indexA) dist in
    0 < dist ->
    Z.of_nat i < bitsIn limb_widthsA ->
    convert'_invariant inp (i + Z.to_nat dist)%nat
                       (update_nth digitB (update_by_concat_bits indexB bitsA) out).
  Proof.
    Time
    repeat match goal with
           | |- _ => progress intros; cbv [convert'_invariant] in *
           | |- _ => progress autorewrite with Ztestbit
           | H : forall x, In x ?lw -> 0 <= x |- appcontext[digit_index ?lw ?i]  =>
              unique pose proof (digit_index_lt_length lw H i)
           | |- _ => rewrite Nat2Z.inj_add
           | |- _ => rewrite Z2Nat.id in *
           | H : forall n, Z.testbit (decodeB _) n = _ |- Z.testbit (decodeB _) ?n = _ =>
             specialize (H n)
           | H0 : ?n < ?i, H1 : ?n < ?i + ?d,
             H : Z.testbit (decodeB _) ?n = Z.testbit (decodeA _) ?n |- _ = Z.testbit (decodeA _) ?n =>
             rewrite <-H
           | H : _ /\ _ |- _ => destruct H
           | |- _ => break_if
           | |- _ => split
           | |- _ => rewrite testbit_decode_full
           | |- _ => rewrite update_nth_nth_default_full
           | |- _ => rewrite nth_default_out_of_bounds by omega
           | H : ~ (0 <= ?n ) |- appcontext[Z.testbit ?a ?n] => rewrite (Z.testbit_neg_r a n) by omega
           | |- _ =>  progress cbv [update_by_concat_bits];
                        rewrite concat_bits_spec by (apply bit_index_nonneg; auto using Nat2Z.is_nonneg)
           | |- _ => solve [distr_length]
           | |- _ => eapply convert'_bounded_step; solve [auto]
           | |- _ => etransitivity; [ | eapply convert'_index_step]; subst_let; eauto; lia
           | H : digit_index limb_widthsB ?i = digit_index limb_widthsB ?j |- _ =>
             unique assert (digit_index limb_widthsA i = digit_index limb_widthsA j) by
               (symmetry; apply same_digit; assumption || lia);
                  pose proof (same_digit_bit_index_sub limb_widthsA j i) as X;
                     forward X; [  | lia | lia | lia ]
           | d := digit_index ?lw ?j,
               H : digit_index ?lw ?i <> ?d |- _ =>
               exfalso; apply H; symmetry; apply same_digit; assumption || subst_lia
           | d := digit_index ?lw ?j,
              H : digit_index ?lw ?i = ?d |- _ =>
                let X := fresh "H" in
                  ((pose proof (same_digit_bit_index_sub lw i j) as X;
                      forward X; [ subst_let | subst_lia | lia | lia ]) ||
                   (pose proof (same_digit_bit_index_sub lw j i) as X;
                      forward X; [ subst_let | subst_lia | lia | lia ]))
           | |- Z.testbit _ (bit_index ?lw _ - bit_index ?lw ?i + _) = false =>
           apply (@testbit_bounded_high limb_widthsA); auto;
               rewrite (same_digit_bit_index_sub) by subst_lia;
               rewrite <-(split_index_eqn limb_widthsA i) at 2 by lia
           | |- ?lw # ?b <= ?a - ((sum_firstn ?lw ?b) + ?c) + ?c => replace (a - (sum_firstn lw b + c) + c) with (a - sum_firstn lw b) by ring; apply Z.le_add_le_sub_r
           | |- (?lw # ?n) + sum_firstn ?lw ?n <= _ =>
            rewrite <-sum_firstn_succ_default; transitivity (bitsIn lw); [ | lia];
            apply sum_firstn_prefix_le; auto; lia
           | |- _ => lia
           | |- _ => assumption
           | |- _ => solve [auto]
           | |- _ => rewrite <-testbit_decode by (assumption || lia || auto); assumption
           | |- _ => repeat (f_equal; try congruence); lia
           end.
  Qed.

  Lemma convert'_invariant_holds : forall inp i out,
    length inp = length limb_widthsA ->
    bounded limb_widthsA inp ->
    convert'_invariant inp i out ->
    convert'_invariant inp (Z.to_nat (bitsIn limb_widthsA)) (convert' inp i out).
  Proof.
    intros until 2; functional induction (convert' inp i out);
      repeat match goal with
           | |- _ => progress intros
           | H : forall x : Z, In x ?lw -> 0 <= x |- appcontext [bit_index ?lw ?i] =>
              unique pose proof (bit_index_not_done lw i)
           | H : convert'_invariant _ _ _ |- convert'_invariant _ _ (convert' _ _ _) =>
             eapply convert'_invariant_step in H; solve [auto; specialize_by lia; lia]
           | H : convert'_invariant _ _ ?out |- convert'_invariant _ _ ?out => progress cbv [convert'_invariant] in *
           | H : _ /\ _ |- _ => destruct H
           | |- _ => rewrite Z2Nat.id
           | |- _ => split
           | |- _ => assumption
           | |- _ => lia
           | |- _ => solve [eauto]
           | |- _ => replace (bitsIn limb_widthsA) with (Z.of_nat i) by (apply Z.le_antisymm; assumption)
             end.
  Qed.

  Definition convert us := convert' us 0 (BaseSystem.zeros (length limb_widthsB)).

  Lemma convert_correct : forall us, length us = length limb_widthsA ->
                                     bounded limb_widthsA us ->
                                     decodeA us = decodeB (convert us).
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress cbv [convert convert'_invariant] in *
           | |- _ => progress change (Z.of_nat 0) with 0 in *
           | |- _ => progress rewrite ?length_zeros, ?zeros_rep, ?Z.testbit_0_l
           | H : length _ = length limb_widthsA |- _ => rewrite H
           | |- _ => rewrite Z.testbit_neg_r by omega
           | |- _ => rewrite nth_default_zeros
           | |- _ => break_if
           | |- _ => split
           | H : _ /\ _ |- _ => destruct H
           | H : forall n, Z.testbit ?x n = _ |- _ = ?x => apply Z.bits_inj'; intros; rewrite H
           | |- _ = decodeB (convert' ?a ?b ?c) => edestruct (convert'_invariant_holds a b c)
           | |- _ => apply testbit_decode_high
           | |- _ => assumption
           | |- _ => reflexivity
           | |- _ => lia
           | |- _ => solve [auto using sum_firstn_limb_widths_nonneg]
           | |- _ => solve [apply nth_default_preserves_properties; auto; lia]
           | |- _ => rewrite Z2Nat.id in *
           | |- bounded _ _ => apply bounded_iff
           | |- 0 < 2 ^ _ => zero_bounds
           end.
  Qed.

  (* This is part of convert'_invariant, but proving it separately strips preconditions *)
  Lemma convert'_bounded : forall inp i out,
    bounded limb_widthsB out ->
    bounded limb_widthsB (convert' inp i out).
  Proof.
    intros; functional induction (convert' inp i out); auto.
    apply IHl.
    apply convert'_bounded_step; auto.
    clear IHl.
    pose proof (bit_index_not_done limb_widthsA (Z.of_nat i)).
    pose proof (bit_index_not_done limb_widthsB (Z.of_nat i)).
    specialize_by lia.
    lia.
  Qed.

  Lemma convert_bounded : forall us, bounded limb_widthsB (convert us).
  Proof.
    intros; apply convert'_bounded.
    apply bounded_iff; intros.
    rewrite nth_default_zeros.
    split; zero_bounds.
  Qed.

  (* This is part of convert'_invariant, but proving it separately strips preconditions *)
  Lemma length_convert' : forall inp i out,
    length (convert' inp i out) = length out.
  Proof.
    intros; functional induction (convert' inp i out); distr_length.
  Qed.

  Lemma length_convert : forall us, length (convert us) = length limb_widthsB.
  Proof.
    cbv [convert]; intros.
    rewrite length_convert', length_zeros.
    reflexivity.
  Qed.
End Conversion.
