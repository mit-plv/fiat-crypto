Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Algebra.
Require Import Crypto.BaseSystem.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemList.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil Crypto.Util.NatUtil.
Require Import Crypto.Util.AdditionChainExponentiation.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Export Crypto.Util.FixCoqMistakes.
Local Open Scope Z_scope.

Local Opaque add_to_nth carry_simple.

Class CarryChain (limb_widths : list Z) :=
  {
    carry_chain : list nat;
    carry_chain_valid : forall i, In i carry_chain -> (i < length limb_widths)%nat
  }.

  Class SubtractionCoefficient {m : positive} {prm : PseudoMersenneBaseParams m} := {
    coeff : tuple Z (length limb_widths);
    coeff_mod: decode coeff = 0%F
  }.

  Class ExponentiationChain {m : positive} {prm : PseudoMersenneBaseParams m} (exp : Z) := {
    chain : list (nat * nat);
    chain_correct : fold_chain 0%N N.add chain (1%N :: nil) = Z.to_N exp
  }.


Section FieldOperationProofs.
  Context `{prm :PseudoMersenneBaseParams}.

  Local Arguments to_list {_ _} _.
  Local Arguments from_list {_ _} _ _.

  Local Hint Unfold decode.
  Local Notation "u ~= x" := (rep u x).
  Local Notation digits := (tuple Z (length limb_widths)).
  Local Hint Resolve (@limb_widths_nonneg _ prm) sum_firstn_limb_widths_nonneg.

  Local Hint Resolve log_cap_nonneg.
  Local Hint Resolve base_from_limb_widths_length.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).

  Local Hint Unfold rep decode ModularBaseSystemList.decode.

  Lemma rep_decode : forall us x, us ~= x -> decode us = x.
  Proof.
    autounfold; intuition.
  Qed.

  Lemma decode_rep : forall us, rep us (decode us).
  Proof.
    cbv [rep]; auto.
  Qed.

  Lemma encode_eq : forall x : F modulus,
    ModularBaseSystemList.encode x = BaseSystem.encode base (F.to_Z x) (2 ^ k).
  Proof.
    cbv [ModularBaseSystemList.encode BaseSystem.encode encodeZ]; intros.
    rewrite base_from_limb_widths_length.
    apply encode'_spec; auto using Nat.eq_le_incl.
  Qed.

  Lemma encode_rep : forall x : F modulus, encode x ~= x.
  Proof.
    autounfold; cbv [encode]; intros.
    rewrite to_list_from_list; autounfold.
    rewrite encode_eq, encode_rep.
    + apply F.of_Z_to_Z.
    + apply bv.
    + rewrite <-F.mod_to_Z.
      match goal with |- appcontext [?a mod (Z.pos modulus)] =>
                      pose proof (Z.mod_pos_bound a modulus modulus_pos) end.
      pose proof lt_modulus_2k.
      omega.
    + eauto using base_upper_bound_compatible, limb_widths_nonneg.
  Qed.

  Lemma bounded_encode : forall x, bounded limb_widths (to_list (encode x)).
  Proof.
    intros.
    cbv [encode]; rewrite to_list_from_list.
    cbv [ModularBaseSystemList.encode].
    apply bounded_encodeZ; auto.
    apply F.to_Z_range.
    pose proof prime_modulus; prime_bound.
  Qed.

  Lemma encode_range : forall x,
    0 <= BaseSystem.decode base (to_list (encode x)) < modulus.
  Proof.
    cbv [encode]; intros.
    rewrite to_list_from_list.
    rewrite encode_eq.
    rewrite BaseSystemProofs.encode_rep; auto using F.to_Z_range, modulus_pos, bv.
    + pose proof (F.to_Z_range x modulus_pos).
      replace (2 ^ k) with (modulus + c) by (cbv[c]; ring).
      pose proof c_pos; omega.
    + apply base_upper_bound_compatible; auto.
  Qed.

  Lemma add_rep : forall u v x y, u ~= x -> v ~= y ->
    add u v ~= (x+y)%F.
  Proof.
    autounfold; cbv [add]; intros.
    rewrite to_list_from_list; autounfold.
    rewrite add_rep, F.of_Z_add.
    f_equal; assumption.
  Qed.

  Lemma eq_rep_iff : forall u v, (eq u v <-> u ~= decode v).
  Proof.
    reflexivity.
  Qed.

  Lemma eq_dec : forall x y, Decidable.Decidable (eq x y).
  Proof.
    intros.
    destruct (F.eq_dec (decode x) (decode y)); [ left | right ]; congruence.
  Qed.

  Lemma modular_base_system_add_monoid : @monoid digits eq add zero.
  Proof.
    repeat match goal with
           | |- _ => progress intro
           | |- _ => cbv [zero]; rewrite encode_rep
           | |- _ digits eq add => econstructor
           | |- _ digits eq add _ => econstructor
           | |- (_ + _)%F = decode (add ?a ?b) =>  rewrite (add_rep a b) by (try apply add_rep; reflexivity)
           | |- eq _ _ => apply eq_rep_iff
           | |- add _ _ ~= _ => apply add_rep
           | |- decode (add _ _) = _ => apply add_rep
           | |- add _ _ ~= decode _ => etransitivity
           | x : digits |- ?x ~= _ => reflexivity
           | |- _ => apply associative
           | |- _ => apply left_identity
           | |- _ => apply right_identity
           | |- _ => solve [eauto using eq_Equivalence, eq_dec]
           | |- _ => congruence
           end.
  Qed.

  Local Hint Resolve firstn_us_base_ext_base bv ExtBaseVector limb_widths_match_modulus.
  Local Hint Extern 1 => apply limb_widths_match_modulus.

  Lemma reduce_rep : forall us,
    BaseSystem.decode base (reduce us) mod modulus =
    BaseSystem.decode (ext_base limb_widths) us mod modulus.
  Proof.
    cbv [reduce]; intros.
    rewrite extended_shiftadd, base_from_limb_widths_length, pseudomersenne_add, BaseSystemProofs.add_rep.
    change (List.map (Z.mul c)) with (BaseSystem.mul_each c).
    rewrite mul_each_rep; auto.
  Qed.

  Lemma mul_rep : forall u v x y, u ~= x -> v ~= y -> mul u v ~= (x*y)%F.
  Proof.
    autounfold in *; unfold ModularBaseSystem.mul in *.
    intuition idtac; subst.
    rewrite to_list_from_list.
    cbv [ModularBaseSystemList.mul ModularBaseSystemList.decode].
    rewrite F.of_Z_mod, reduce_rep, <-F.of_Z_mod.
    pose proof (@base_from_limb_widths_length limb_widths).
    rewrite @mul_rep by (eauto using ExtBaseVector || rewrite extended_base_length, !length_to_list; omega).
    rewrite 2decode_short by (rewrite ?base_from_limb_widths_length;
      auto using Nat.eq_le_incl, length_to_list with omega).
    apply F.of_Z_mul.
  Qed.

  Lemma modular_base_system_mul_monoid : @monoid digits eq mul one.
  Proof.
    repeat match goal with
           | |- _ => progress intro
           | |- _ => cbv [one]; rewrite encode_rep
           | |- _ digits eq mul => econstructor
           | |- _ digits eq mul _ => econstructor
           | |- (_ * _)%F = decode (mul ?a ?b) =>  rewrite (mul_rep a b) by (try apply mul_rep; reflexivity)
           | |- eq _ _ => apply eq_rep_iff
           | |- mul _ _ ~= _ => apply mul_rep
           | |- decode (mul _ _) = _ => apply mul_rep
           | |- mul _ _ ~= decode _ => etransitivity
           | x : digits |- ?x ~= _ => reflexivity
           | |- _ => apply associative
           | |- _ => apply left_identity
           | |- _ => apply right_identity
           | |- _ => solve [eauto using eq_Equivalence, eq_dec]
           | |- _ => congruence
           end.
  Qed.

  Lemma Fdecode_decode_mod : forall us x,
    decode us = x -> BaseSystem.decode base (to_list us) mod modulus = F.to_Z x.
  Proof.
    autounfold; intros.
    rewrite <-H.
    apply F.to_Z_of_Z.
  Qed.

  Lemma sub_rep : forall mm pf u v x y, u ~= x -> v ~= y ->
    ModularBaseSystem.sub mm pf u v ~= (x-y)%F.
  Proof.
    autounfold; cbv [sub]; intros.
    rewrite to_list_from_list; autounfold.
    cbv [ModularBaseSystemList.sub].
    rewrite BaseSystemProofs.sub_rep, BaseSystemProofs.add_rep.
    rewrite F.of_Z_sub, F.of_Z_add, F.of_Z_mod.
    apply Fdecode_decode_mod in pf; cbv [BaseSystem.decode] in *.
    rewrite pf. rewrite Algebra.left_identity.
    f_equal; assumption.
  Qed.

  Lemma opp_rep : forall mm pf u x, u ~= x -> opp mm pf u ~= F.opp x.
  Proof.
    cbv [opp rep]; intros.
    rewrite sub_rep by (apply encode_rep || eassumption).
    apply F.eq_to_Z_iff.
    rewrite F.to_Z_opp.
    rewrite <-Z.sub_0_l.
    pose proof @F.of_Z_sub.
    transitivity (F.to_Z (F.of_Z modulus (0 - F.to_Z x)));
      [ rewrite F.of_Z_sub, F.of_Z_to_Z; reflexivity | ].
    rewrite F.to_Z_of_Z. reflexivity.
  Qed.

  Section PowInv.
  Context (modulus_gt_2 : 2 < modulus).

  Lemma scalarmult_rep : forall u x n, u ~= x ->
    (@ScalarMult.scalarmult_ref digits mul one n u) ~= (x ^ (N.of_nat n))%F.
  Proof.
    induction n; intros.
    + cbv [N.to_nat ScalarMult.scalarmult_ref]. rewrite F.pow_0_r.
      apply encode_rep.
    + unfold ScalarMult.scalarmult_ref.
      fold (@ScalarMult.scalarmult_ref digits mul one).
      rewrite Nnat.Nat2N.inj_succ, <-N.add_1_l, F.pow_add_r, F.pow_1_r.
      apply mul_rep; auto.
  Qed.

  Lemma pow_rep : forall chain u x, u ~= x ->
    pow u chain ~= F.pow x (fold_chain 0%N N.add chain (1%N :: nil)).
  Proof.
    cbv [pow rep]; intros.
    erewrite (@fold_chain_exp _ _ _ _ modular_base_system_mul_monoid)
      by (apply @ScalarMult.scalarmult_ref_is_scalarmult; apply modular_base_system_mul_monoid).
    etransitivity; [ apply scalarmult_rep; eassumption | ].
    rewrite Nnat.N2Nat.id.
    reflexivity.
  Qed.

  Lemma inv_rep : forall chain pf u x, u ~= x ->
    inv chain pf u ~= F.inv x.
  Proof.
    cbv [inv]; intros.
    rewrite (@F.Fq_inv_fermat _ prime_modulus modulus_gt_2).
    etransitivity; [ apply pow_rep; eassumption | ].
    congruence.
  Qed.

  End PowInv.


  Import Morphisms.

  Global Instance encode_Proper : Proper (Logic.eq ==> eq) encode.
  Proof.
    repeat intro; cbv [eq].
    rewrite !encode_rep. assumption.
  Qed.

  Global Instance add_Proper : Proper (eq ==> eq ==> eq) add.
  Proof.
    repeat intro.
    cbv beta delta [eq] in *.
    erewrite !add_rep; cbv [rep] in *; try reflexivity; assumption.
  Qed.

  Global Instance sub_Proper mm mm_correct
    : Proper (eq ==> eq ==> eq) (sub mm mm_correct).
  Proof.
    repeat intro.
    cbv beta delta [eq] in *.
    erewrite !sub_rep; cbv [rep] in *; try reflexivity; assumption.
  Qed.

  Global Instance opp_Proper mm mm_correct
    : Proper (eq ==> eq) (opp mm mm_correct).
  Proof.
     cbv [opp]; repeat intro.
     apply sub_Proper; assumption || reflexivity.
  Qed.

  Global Instance mul_Proper : Proper (eq ==> eq ==> eq) mul.
  Proof.
    repeat intro.
    cbv beta delta [eq] in *.
    erewrite !mul_rep; cbv [rep] in *; try reflexivity; assumption.
  Qed.

  Global Instance pow_Proper : Proper (eq ==> Logic.eq ==> eq) pow.
  Proof.
    repeat intro.
    cbv beta delta [eq] in *.
    erewrite !pow_rep; cbv [rep] in *; subst; try reflexivity.
    congruence.
  Qed.

  Global Instance inv_Proper chain chain_correct : Proper (eq ==> eq) (inv chain chain_correct).
  Proof.
     cbv [inv]; repeat intro.
    apply pow_Proper; assumption || reflexivity.
  Qed.

  Global Instance div_Proper : Proper (eq ==> eq ==> eq) div.
  Proof.
    cbv [div]; repeat intro; congruence.
  Qed.

  Section FieldProofs.
  Context (modulus_gt_2 : 2 < modulus)
          {sc : SubtractionCoefficient}
          {ec : ExponentiationChain (modulus - 2)}.

  Lemma _zero_neq_one : not (eq zero one).
  Proof.
    cbv [eq zero one]; erewrite !encode_rep.
    pose proof (@F.field_modulo modulus prime_modulus).
    apply zero_neq_one.
  Qed.

  Lemma modular_base_system_field :
    @field digits eq zero one (opp coeff coeff_mod) add (sub coeff coeff_mod) mul (inv chain chain_correct) div.
  Proof.
    eapply (Field.isomorphism_to_subfield_field (phi := decode) (fieldR := @F.field_modulo modulus prime_modulus)).
    Grab Existential Variables.
    + intros; eapply encode_rep.
    + intros; eapply encode_rep.
    + intros; eapply encode_rep.
    + intros; eapply inv_rep; auto.
    + intros; eapply mul_rep; auto.
    + intros; eapply sub_rep; auto using coeff_mod.
    + intros; eapply add_rep; auto.
    + intros; eapply opp_rep; auto using coeff_mod.
    + eapply _zero_neq_one.
    + trivial.
  Qed.
End FieldProofs.

End FieldOperationProofs.
Opaque encode add mul sub inv pow.

Section CarryProofs.
  Context `{prm : PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).
  Local Notation "u ~= x" := (rep u x).
  Local Hint Resolve (@limb_widths_nonneg _ prm) sum_firstn_limb_widths_nonneg.
  Local Hint Resolve log_cap_nonneg.

  Lemma base_length_lt_pred : (pred (length base) < length base)%nat.
  Proof.
    pose proof limb_widths_nonnil; rewrite base_from_limb_widths_length.
    destruct limb_widths; congruence || distr_length.
  Qed.
  Hint Resolve base_length_lt_pred.

  Definition carry_done us := forall i, (i < length base)%nat ->
    0 <= nth_default 0 us i /\ Z.shiftr (nth_default 0 us i) (log_cap i) = 0.

  Lemma carry_done_bounds : forall us, (length us = length base) ->
    (carry_done us <-> forall i, 0 <= nth_default 0 us i < 2 ^ log_cap i).
  Proof.
    intros ? ?; unfold carry_done; split; [ intros Hcarry_done i | intros Hbounds i i_lt ].
    + destruct (lt_dec i (length base)) as [i_lt | i_nlt].
      - specialize (Hcarry_done i i_lt).
        split; [ intuition | ].
        destruct Hcarry_done as [Hnth_nonneg Hshiftr_0].
        apply Z.shiftr_eq_0_iff in Hshiftr_0.
        destruct Hshiftr_0 as [nth_0 | [] ]; [ rewrite nth_0; zero_bounds | ].
        apply Z.log2_lt_pow2; auto.
      - rewrite nth_default_out_of_bounds by omega.
        split; zero_bounds.
    + specialize (Hbounds i).
      split; [ intuition | ].
      destruct Hbounds as [nth_nonneg nth_lt_pow2].
      apply Z.shiftr_eq_0_iff.
      apply Z.le_lteq in nth_nonneg; destruct nth_nonneg; try solve [left; auto].
      right; split; auto.
      apply Z.log2_lt_pow2; auto.
  Qed.

  Lemma carry_decode_eq_reduce : forall us,
    (length us = length limb_widths) ->
    BaseSystem.decode base (carry_and_reduce (pred (length limb_widths)) us) mod modulus
    = BaseSystem.decode base us mod modulus.
  Proof.
    cbv [carry_and_reduce]; intros.
    rewrite carry_gen_decode_eq; auto.
    distr_length.
    assert (0 < length limb_widths)%nat by (pose proof limb_widths_nonnil;
      destruct limb_widths; distr_length; congruence).
    repeat break_if; repeat rewrite ?pred_mod, ?Nat.succ_pred,?Nat.mod_same in * by omega;
      try omega.
    rewrite !nth_default_base by (auto || destruct (length limb_widths); auto).
    rewrite sum_firstn_0.
    autorewrite with zsimplify.
    match goal with |- appcontext[2 ^ ?a * ?b * 2 ^ ?c] =>
      replace (2 ^ a * b * 2 ^ c) with (2 ^ (a + c) * b) end.
    { rewrite <-sum_firstn_succ by (apply nth_error_Some_nth_default; destruct (length limb_widths); auto).
      rewrite Nat.succ_pred by omega.
      remember (pred (length limb_widths)) as pred_len.
      fold k.
      rewrite <-Z.mul_sub_distr_r.
      replace (c - 2 ^ k) with (modulus * -1) by (cbv [c]; ring).
      rewrite <-Z.mul_assoc.
      apply Z.mod_add_l'.
      pose proof prime_modulus. Z.prime_bound. }
    { rewrite Z.pow_add_r; auto using log_cap_nonneg, sum_firstn_limb_widths_nonneg.
      rewrite <-!Z.mul_assoc.
      apply Z.mul_cancel_l; try ring.
      apply Z.pow_nonzero; (omega || auto using log_cap_nonneg). }
  Qed.

  Lemma carry_rep : forall i us x,
    (length us = length limb_widths)%nat ->
    (i < length limb_widths)%nat ->
    forall pf1 pf2,
    from_list _ us pf1 ~= x -> from_list _ (carry i us) pf2 ~= x.
  Proof.
    cbv [carry rep decode]; intros.
    rewrite to_list_from_list.
    pose proof carry_decode_eq_reduce. pose proof (@carry_simple_decode_eq limb_widths).

    specialize_by eauto.
    cbv [ModularBaseSystemList.carry].
    break_if; subst; eauto.
    apply F.eq_of_Z_iff.
    rewrite to_list_from_list.
    apply carry_decode_eq_reduce. auto.
    cbv [ModularBaseSystemList.decode].
    apply F.eq_of_Z_iff.
    rewrite to_list_from_list, carry_simple_decode_eq; try omega; distr_length; auto.
  Qed.
  Hint Resolve carry_rep.

  Lemma decode_mod_Fdecode : forall u, length u = length limb_widths ->
    BaseSystem.decode base u mod modulus= F.to_Z (decode (from_list_default 0 _ u)).
  Proof.
    intros.
    rewrite <-(to_list_from_list _ u) with (pf := H).
    erewrite Fdecode_decode_mod by reflexivity.
    rewrite to_list_from_list.
    rewrite from_list_default_eq with (pf := H).
    reflexivity.
  Qed.

  Lemma carry_sequence_rep : forall is us x,
    (forall i, In i is -> (i < length limb_widths)%nat) ->
    us ~= x -> forall pf, from_list _ (carry_sequence is (to_list _ us)) pf ~= x.
  Proof.
    induction is; intros.
    + cbv [carry_sequence fold_right]. rewrite from_list_to_list. assumption.
    + simpl. apply carry_rep with (pf1 := length_carry_sequence (length_to_list us));
        auto using length_carry_sequence, length_to_list, in_eq.
      apply IHis; auto using in_cons.
  Qed.

  Context `{cc : CarryChain limb_widths}.
  Lemma carry_mul_rep : forall us vs x y,
    rep us x -> rep vs y ->
    rep (carry_mul carry_chain us vs) (x * y)%F.
  Proof.
    cbv [carry_mul]; intros; apply carry_sequence_rep;
      auto using carry_chain_valid,  mul_rep.
  Qed.

  Lemma carry_sub_rep : forall coeff coeff_mod a b,
    eq
      (carry_sub carry_chain coeff coeff_mod a b)
      (sub coeff coeff_mod a b).
  Proof.
    cbv [carry_sub carry_]; intros.
    eapply carry_sequence_rep; auto using carry_chain_valid.
    reflexivity.
  Qed.

  Lemma carry_add_rep : forall a b,
    eq (carry_add carry_chain a b) (add a b).
  Proof.
    cbv [carry_add carry_]; intros.
    eapply carry_sequence_rep; auto using carry_chain_valid.
    reflexivity.
  Qed.

  Lemma carry_opp_rep : forall coeff coeff_mod a,
    eq
      (carry_opp carry_chain coeff coeff_mod a)
      (opp coeff coeff_mod a).
  Proof.
    cbv [carry_opp opp]; intros.
    apply carry_sub_rep.
  Qed.

End CarryProofs.

Hint Rewrite @length_carry_and_reduce @length_carry : distr_length.

Class FreezePreconditions `{prm : PseudoMersenneBaseParams} B int_width :=
  {
    lt_1_length_limb_widths : (1 < length limb_widths)%nat;
    int_width_pos : 0 < int_width;
    B_le_int_width : B <= int_width;
    B_pos : 0 < B;
    B_compat : forall w, In w limb_widths -> w < B;
   (* on the first reduce step, we add at most one bit of width to the first digit *)
   c_reduce1 : c * ((2 ^ B) >> nth_default 0 limb_widths (pred (length limb_widths))) <= 2 ^ (nth_default 0 limb_widths 0);
   (* on the second reduce step, we add at most one bit of width to the first digit,
      and leave room to carry c one more time after the highest bit is carried *)
   c_reduce2 : c <= 2 ^ (nth_default 0 limb_widths 0) - c
  }.

Section CanonicalizationProofs.
  Context `{freeze_pre : FreezePreconditions}.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation digits := (tuple Z (length limb_widths)).
  Local Hint Resolve (@limb_widths_nonneg _ prm) sum_firstn_limb_widths_nonneg.
  Local Hint Resolve log_cap_nonneg.
  Local Notation "u [ i ]"  := (nth_default 0 u i).
  Local Notation "u {{ i }}"  := (carry_sequence (make_chain i) u) (at level 30). (* Can't rely on [Reserved Notation]: https://coq.inria.fr/bugs/show_bug.cgi?id=4970 *)

  Lemma nth_default_carry_and_reduce_full : forall n i us,
   (carry_and_reduce i us) [n]
    = if lt_dec n (length us)
      then
        (if eq_nat_dec n (i mod length limb_widths)
        then Z.pow2_mod (us [n]) (limb_widths [n])
        else us [n]) +
          if eq_nat_dec n (S (i mod length limb_widths) mod length limb_widths)
          then c * (us [i mod length limb_widths]) >> (limb_widths [i mod length limb_widths])
          else 0
      else 0.
  Proof.
    cbv [carry_and_reduce]; intros.
    autorewrite with push_nth_default.
    reflexivity.
  Qed.
  Hint Rewrite @nth_default_carry_and_reduce_full : push_nth_default.

  Lemma nth_default_carry_full : forall n i us,
    length us = length limb_widths ->
    (carry i us) [n]
    = if lt_dec n (length us)
      then
        if eq_nat_dec i (pred (length limb_widths))
        then (if eq_nat_dec n i
             then Z.pow2_mod (us [n]) (limb_widths [n])
             else us [n]) +
               if eq_nat_dec n 0
               then c * ((us [i]) >> (limb_widths [i]))
               else 0
        else if eq_nat_dec n i
             then Z.pow2_mod (us [n]) (limb_widths [n])
             else us [n] +
               if eq_nat_dec n (S i)
               then (us [i]) >> (limb_widths [i])
               else 0
      else 0.
  Proof.
    intros.
    cbv [carry].
    break_if.
    + subst i.
      pose proof lt_1_length_limb_widths.
      autorewrite with push_nth_default natsimplify.
      destruct (eq_nat_dec (length limb_widths) (length us)); congruence.
    + autorewrite with push_nth_default; reflexivity.
  Qed.
  Hint Rewrite @nth_default_carry_full : push_nth_default.

  Lemma nth_default_carry_sequence_make_chain_full : forall i n us,
    length us = length limb_widths ->
    (i <= length limb_widths)%nat ->
    us {{ i }} [n]
    = if lt_dec n (length limb_widths)
      then
          if eq_nat_dec i 0
          then nth_default 0 us n
          else
              if lt_dec i (length limb_widths)
              then
                 if lt_dec n i
                 then
                    if eq_nat_dec n (pred i)
                    then Z.pow2_mod (us {{ pred i }} [n]) (limb_widths [n])
                    else us{{ pred i }} [n]
                 else us{{ pred i}} [n] +
                    (if eq_nat_dec n i
                      then (us{{ pred i}} [pred i]) >> (limb_widths [pred i])
                     else 0)
              else
                  if lt_dec n (pred i)
                  then us {{ pred i }} [n] +
                     (if eq_nat_dec n 0
                      then c * (us{{ pred i}} [pred i]) >> (limb_widths [pred i])
                      else 0)
                  else Z.pow2_mod (us {{ pred i }} [n]) (limb_widths [n])
      else 0.
  Proof.
    induction i; intros; cbv [carry_sequence].
    + cbv [pred make_chain fold_right].
      repeat break_if; subst; omega || reflexivity || auto using Z.add_0_r.
      apply nth_default_out_of_bounds. omega.
    + replace (make_chain (S i)) with (i :: make_chain i) by reflexivity.
      rewrite fold_right_cons.
      pose proof lt_1_length_limb_widths.
      autorewrite with push_nth_default natsimplify;
        rewrite ?Nat.pred_succ; fold (carry_sequence (make_chain i) us);
        rewrite length_carry_sequence; auto.
      repeat break_if; try omega; rewrite ?IHi by (omega || auto);
        rewrite ?Z.add_0_r; try reflexivity.
  Qed.

  Lemma nth_default_carry : forall i us,
    length us = length limb_widths ->
    (i < length us)%nat ->
    nth_default 0 (carry i us) i
    = Z.pow2_mod (us [i]) (limb_widths [i]).
  Proof.
    intros; pose proof lt_1_length_limb_widths; autorewrite with push_nth_default natsimplify; break_match; omega.
  Qed.
  Hint Rewrite @nth_default_carry using (omega || distr_length; omega) : push_nth_default.

  Lemma pow_limb_widths_gt_1 : forall i, (i < length limb_widths)%nat ->
                                         1 < 2 ^ limb_widths [i].
  Proof.
    intros.
    apply Z.pow_gt_1; try omega.
    apply nth_default_preserves_properties_length_dep; intros; try omega.
    auto using limb_widths_pos.
  Qed.

  Lemma carry_sequence_nil_l : forall us, carry_sequence nil us = us.
  Proof.
    reflexivity.
  Qed.

  Ltac bound_during_loop :=
    repeat match goal with
           | |- _ => progress (intros; subst)
           | |- _ => unique pose proof lt_1_length_limb_widths
           | |- _ => unique pose proof c_reduce2
           | |- _ => break_if; try omega
           | |- _ => progress simpl pred in *
           | |- _ => progress rewrite ?Z.add_0_r, ?Z.sub_0_r in *
           | |- _ => rewrite nth_default_out_of_bounds by omega
           | |- _ => rewrite nth_default_carry_sequence_make_chain_full by auto
           | H : forall n, 0 <= _ [n] < _ |- appcontext [ _ [?n] ] => pose proof (H (pred n)); specialize (H n)
           | H : forall n, (n < ?m)%nat -> 0 <= _ [n] < _ |- appcontext [ _ [?n] ] => pose proof (H (pred n)); specialize (H n); specialize_by omega
           | |- appcontext [make_chain 0] => simpl make_chain; rewrite carry_sequence_nil_l
           | |- 0 <= ?a + c * ?b < 2 * ?d => unique assert (c * b <= d);
                                               [ | solve [pose proof c_pos; rewrite <-Z.add_diag; split; zero_bounds] ]
           | |- c * (?e >> (limb_widths[?i])) <= ?b =>
             pose proof (Z.shiftr_le e (2 ^ B) (limb_widths [i])); specialize_by (auto || omega);
               replace (limb_widths [i]) with (limb_widths [pred (length limb_widths)]) in * by (f_equal; omega);
               etransitivity; [ | apply c_reduce1]; apply Z.mul_le_mono_pos_l; try apply c_pos; omega
           | H : 0 <= _ < ?b - (?c >> ?d) |- 0 <= _ + (?e >> ?d) < ?b =>
             pose proof (Z.shiftr_le e c d); specialize_by (auto || omega); solve [split; zero_bounds]
           | IH : forall n, _ -> 0 <= ?u {{ ?i }} [n] < _
             |- 0 <= ?u {{ ?i }} [?n] < _ => specialize (IH n)
           | IH : forall n, _ -> 0 <= ?u {{ ?i }} [n] < _
             |- appcontext [(?u {{ ?i }} [?n]) >> _] => pose proof (IH 0%nat); pose proof (IH (S n)); specialize (IH n); specialize_by omega
           | H : 0 <= ?a < 2 ^ ?n + ?x |- appcontext [?a >> ?n] =>
             assert (x < 2 ^ n) by (omega || auto using pow_limb_widths_gt_1);
               unique assert (0 <= a < 2 * 2 ^ n) by omega
           | H : 0 <= ?a < 2 * 2 ^ ?n |- appcontext [?a >> ?n] =>
             pose proof c_pos;
             apply Z.lt_mul_2_pow_2_shiftr in H; break_if; rewrite H; omega
           | H : 0 <= ?a < 2 ^ ?n |- appcontext [?a >> ?n] =>
             pose proof c_pos;
             apply Z.lt_pow_2_shiftr in H; rewrite H; omega
           | |- 0 <= Z.pow2_mod _ _ < c =>
             rewrite Z.pow2_mod_spec, Z.lt_mul_2_mod_sub; auto; omega
           | |- _ => apply Z.pow2_mod_pos_bound, limb_widths_pos, nth_default_preserves_properties_length_dep; [tauto | omega]
           | |- 0 <= 0 < _ => solve[split; zero_bounds]
           | |- _ => omega
           end.

  Lemma bound_during_first_loop : forall us,
    length us = length limb_widths ->
    (forall n, (n < length limb_widths)%nat -> 0 <= us [n] < 2 ^ B - if eq_nat_dec n 0 then 0 else ((2 ^ B) >> (limb_widths [pred n]))) ->
    forall i n,
    (i <= length limb_widths)%nat ->
    0 <= us{{i}}[n] < if eq_nat_dec i 0 then us[n] + 1 else
      if lt_dec i (length limb_widths)
      then
          if lt_dec n i
          then 2 ^ (limb_widths [n])
          else if eq_nat_dec n i
               then 2 ^ B
               else us[n] + 1
      else
          if eq_nat_dec n 0
          then 2 * 2 ^ limb_widths [n]
          else 2 ^ limb_widths [n].
  Proof.
    induction i; bound_during_loop.
  Qed.

  Lemma bound_after_loop_length_preconditions : forall us (Hlength : length us = length limb_widths)
                                  {bound bound' bound'' : list Z -> nat -> Z}
                                  {X Y : list Z -> nat -> nat -> Z} f,
    (forall us, length us = length limb_widths
                -> (forall n, (n < length limb_widths)%nat -> 0 <= us [n] < bound' us n)
                -> forall i n, (i <= length limb_widths)%nat
                               -> 0 <= us{{i}}[n] < if eq_nat_dec i 0 then X us i n else
                                                      if lt_dec i (length limb_widths)
                                                      then Y us i n
                                                      else bound'' us n) ->
     ((forall n, (n < length limb_widths)%nat -> 0 <= us [n] < bound us n)
                -> forall n, (n < length limb_widths)%nat -> 0 <= (f us) [n] < bound' (f us) n) ->
     length (f us) = length limb_widths ->
     (forall n, (n < length limb_widths)%nat -> 0 <= us [n] < bound us n)
                -> forall n, (n < length limb_widths)%nat -> 0 <= (carry_full (f us)) [n] < bound'' (f us) n.
  Proof.
    pose proof lt_1_length_limb_widths.
    cbv [carry_full full_carry_chain]; intros ? ? ? ? ? ? ? ? Hloop Hfbound Hflength Hbound n.
    specialize (Hfbound Hbound).
    specialize (Hloop (f us) Hflength Hfbound (length limb_widths) n).
    specialize_by omega.
    repeat (break_if; try omega).
  Qed.

  Lemma bound_after_loop : forall us (Hlength : length us = length limb_widths)
                                  {bound bound' bound'' : list Z -> nat -> Z}
                                  {X Y : list Z -> nat -> nat -> Z} f,
    (forall us, length us = length limb_widths
                -> (forall n, 0 <= us [n] < bound' us n)
                -> forall i n, (i <= length limb_widths)%nat
                               -> 0 <= us{{i}}[n] < if eq_nat_dec i 0 then X us i n else
                                                      if lt_dec i (length limb_widths)
                                                      then Y us i n
                                                      else bound'' us n) ->
     ((forall n, (n < length limb_widths)%nat -> 0 <= us [n] < bound us n)
                -> forall n, 0 <= (f us) [n] < bound' (f us) n)
     -> length (f us) = length limb_widths
     -> (forall n, (n < length limb_widths)%nat -> 0 <= us [n] < bound us n)
                -> forall n, 0 <= (carry_full (f us)) [n] < bound'' (f us) n.
  Proof.
    pose proof lt_1_length_limb_widths.
    cbv [carry_full full_carry_chain]; intros ? ? ? ? ? ? ? ? Hloop Hfbound Hflength Hbound n.
    specialize (Hfbound Hbound).
    specialize (Hloop (f us) Hflength Hfbound (length limb_widths) n).
    specialize_by omega.
    repeat (break_if; try omega).
  Qed.

  Lemma bound_after_first_loop_pre : forall us,
    length us = length limb_widths ->
    (forall n, (n < length limb_widths)%nat -> 0 <= us [n] < 2 ^ B - if eq_nat_dec n 0 then 0 else ((2 ^ B) >> (limb_widths [pred n]))) ->
    forall n, (n < length limb_widths)%nat ->
    0 <= (carry_full us)[n] <
      if eq_nat_dec n 0
      then 2 * 2 ^ limb_widths [n]
      else 2 ^ limb_widths [n].
  Proof.
    intros ? ?.
    apply (bound_after_loop_length_preconditions us H id bound_during_first_loop); auto.
  Qed.

  Lemma bound_after_first_loop : forall us,
    length us = length limb_widths ->
    (forall n, (n < length limb_widths)%nat -> 0 <= us [n] < 2 ^ B - if eq_nat_dec n 0 then 0 else ((2 ^ B) >> (limb_widths [pred n]))) ->
    forall n,
    0 <= (carry_full us)[n] <
      if eq_nat_dec n 0
      then 2 * 2 ^ limb_widths [n]
      else 2 ^ limb_widths [n].
  Proof.
    intros.
    destruct (lt_dec n (length limb_widths));
      auto using bound_after_first_loop_pre.
    rewrite !nth_default_out_of_bounds by (rewrite ?length_carry_full; omega).
    autorewrite with zsimplify.
    rewrite Z.pow_0_r.
    break_if; omega.
  Qed.

  Lemma bound_during_second_loop : forall us,
    length us = length limb_widths ->
    (forall n, 0 <= us [n] < if eq_nat_dec n 0 then 2 * 2 ^ limb_widths [n] else 2 ^ limb_widths [n]) ->
    forall i n,
    (i <= length limb_widths)%nat ->
    0 <= us{{i}}[n] < if eq_nat_dec i 0 then us[n] + 1 else
      if lt_dec i (length limb_widths)
      then
          if lt_dec n i
          then 2 ^ (limb_widths [n])
          else if eq_nat_dec n i
               then 2 * 2 ^ limb_widths [n]
               else us[n] + 1
      else
          if eq_nat_dec n 0
          then 2 ^ limb_widths [n] + c
          else 2 ^ limb_widths [n].
  Proof.
    induction i; bound_during_loop.
  Qed.

  Lemma bound_after_second_loop : forall us,
    length us = length limb_widths ->
    (forall n, (n < length limb_widths)%nat -> 0 <= us [n] < 2 ^ B - if eq_nat_dec n 0 then 0 else ((2 ^ B) >> (limb_widths [pred n]))) ->
    forall n,
    0 <= (carry_full (carry_full us)) [n] <
      if eq_nat_dec n 0
      then 2 ^ limb_widths [n] + c
      else 2 ^ limb_widths [n].
  Proof.
    intros ? ?; apply (bound_after_loop us H carry_full bound_during_second_loop);
      auto using length_carry_full, bound_after_first_loop.
  Qed.

  Lemma bound_during_third_loop : forall us,
    length us = length limb_widths ->
    (forall n, 0 <= us [n] < if eq_nat_dec n 0 then 2 ^ limb_widths [n] + c else 2 ^ limb_widths [n]) ->
    forall i n,
    (i <= length limb_widths)%nat ->
    0 <= us{{i}}[n] < if eq_nat_dec i 0 then us[n] + 1 else
      if lt_dec i (length limb_widths)
      then
        if Z_lt_dec (us [0]) (2 ^ limb_widths [0])
        then
          2 ^ limb_widths [n]
        else
          if eq_nat_dec n 0
          then c
          else
            if lt_dec n i
            then 2 ^ limb_widths [n]
            else if eq_nat_dec n i
                 then 2 ^ limb_widths [n] + 1
                 else us[n] + 1
      else
          2 ^ limb_widths [n].
  Proof.
    induction i; bound_during_loop.
  Qed.

  Lemma bound_after_third_loop : forall us,
    length us = length limb_widths ->
    (forall n, (n < length limb_widths)%nat -> 0 <= us [n] < 2 ^ B - if eq_nat_dec n 0 then 0 else ((2 ^ B) >> (limb_widths [pred n]))) ->
    forall n,
    0 <= (carry_full (carry_full (carry_full us))) [n] < 2 ^ limb_widths [n].
  Proof.
    intros ? ?.
    apply (bound_after_loop us H (fun x => carry_full (carry_full x)) bound_during_third_loop);
      auto using length_carry_full, bound_after_second_loop.
  Qed.

  Local Notation initial_bounds u :=
      (forall n : nat, (n < length limb_widths)%nat ->
       0 <= to_list (length limb_widths) u [n] <
       2 ^ B -
       (if eq_nat_dec n 0
        then 0
        else (2 ^ B) >> (limb_widths [pred n]))).
  Local Notation minimal_rep u := ((bounded limb_widths (to_list (length limb_widths) u))
                                   /\ (ge_modulus (to_list _ u) = 0)).

  Lemma decode_bitwise_eq_iff : forall u v, minimal_rep u -> minimal_rep v ->
    (fieldwise Logic.eq u v <->
     decode_bitwise limb_widths (to_list _ u) = decode_bitwise limb_widths (to_list _ v)).
  Proof.
    intros.
    rewrite !decode_bitwise_spec by (tauto || auto using length_to_list).
    rewrite fieldwise_to_list_iff.
    split; intros.
    + apply decode_Proper; auto.
    + apply Forall2_forall_iff with (d := 0); intros; repeat rewrite @length_to_list in *; auto.
      erewrite digit_select with (us := to_list _ u) by intuition eauto.
      erewrite digit_select with (us := to_list _ v) by intuition eauto.
      rewrite H1; reflexivity.
  Qed.

  Lemma c_upper_bound : c - 1 < 2 ^ limb_widths[0].
  Proof.
    pose proof c_reduce2. pose proof c_pos.
    omega.
  Qed.
  Hint Resolve c_upper_bound.

  Lemma minimal_rep_encode : forall x, minimal_rep (encode x).
  Proof.
    split; intros; auto using bounded_encode.
    apply ge_modulus_spec; auto using bounded_encode, length_to_list.
    apply encode_range.
  Qed.

  Lemma encode_minimal_rep : forall u x, rep u x -> minimal_rep u ->
                                         fieldwise Logic.eq u (encode x).
  Proof.
    intros.
    apply decode_bitwise_eq_iff; auto using minimal_rep_encode.
    rewrite !decode_bitwise_spec by (intuition auto; distr_length; try apply minimal_rep_encode).
    apply Fdecode_decode_mod in H.
    pose proof (Fdecode_decode_mod _ _ (encode_rep x)).
    rewrite Z.mod_small in H by (apply ge_modulus_spec; distr_length; intuition auto).
    rewrite Z.mod_small in H1 by (apply ge_modulus_spec; distr_length; auto using c_upper_bound; apply minimal_rep_encode).
    congruence.
  Qed.

  Lemma bounded_canonical : forall u v x y, rep u x -> rep v y ->
                                            minimal_rep u -> minimal_rep v ->
                                            (x = y <-> fieldwise Logic.eq u v).
  Proof.
    intros.
    eapply encode_minimal_rep in H1; eauto.
    eapply encode_minimal_rep in H2; eauto.
    split; intros; subst.
    + etransitivity; eauto; symmetry; eauto.
    + assert (fieldwise Logic.eq (encode x) (encode y)) by
          (transitivity u; [symmetry; eauto | ]; transitivity v; eauto).
      apply decode_bitwise_eq_iff in H4; try apply minimal_rep_encode.
      rewrite !decode_bitwise_spec in H4 by (auto; distr_length; apply minimal_rep_encode).
      apply F.eq_to_Z_iff.
      erewrite <-!Fdecode_decode_mod by eapply encode_rep.
      congruence.
  Qed.

  Lemma int_width_compat : forall x, In x limb_widths -> x < int_width.
  Proof.
    intros. apply B_compat in H.
    eapply Z.lt_le_trans; eauto using B_le_int_width.
  Qed.

  Lemma minimal_rep_freeze : forall u, initial_bounds u ->
      minimal_rep (freeze int_width u).
  Proof.
    repeat match goal with
           | |- _ => progress (cbv [freeze ModularBaseSystemList.freeze])
           | |- _ => progress intros
           | |- minimal_rep _ => split
           | |- _ => rewrite to_list_from_list
           | |- _ => apply bound_after_third_loop
           | |- _ => apply conditional_subtract_lt_modulus
           | |- _ => apply conditional_subtract_modulus_preserves_bounded
           | |- bounded _ (carry_full _) => apply bounded_iff
           | |- _ => solve [auto using Z.lt_le_incl, int_width_pos, int_width_compat, lt_1_length_limb_widths, length_carry_full, length_to_list]
           end.
  Qed.

  Lemma freeze_decode : forall u,
      BaseSystem.decode base (to_list _ (freeze int_width u)) mod modulus =
      BaseSystem.decode base (to_list _ u) mod modulus.
  Proof.
    repeat match goal with
           | |- _ => progress cbv [freeze ModularBaseSystemList.freeze]
           | |- _ => progress intros
           | |- _ => rewrite <-Z.add_opp_r, <-Z.mul_opp_l
           | |- _ => rewrite Z.mod_add by (pose proof prime_modulus; prime_bound)
           | |- _ => rewrite to_list_from_list
           | |- _ => rewrite conditional_subtract_modulus_spec by
                       (auto using Z.lt_le_incl, int_width_pos, int_width_compat, lt_1_length_limb_widths, length_carry_full, length_to_list, ge_modulus_01)
           end.
    rewrite !decode_mod_Fdecode by auto using length_carry_full, length_to_list.
    cbv [carry_full].
    apply F.eq_to_Z_iff.
    rewrite <-@to_list_from_list with (pf := length_carry_sequence (length_carry_sequence (length_to_list _))).
    rewrite from_list_default_eq with (pf := length_carry_sequence (length_to_list _)).
    rewrite carry_sequence_rep; try reflexivity; try apply make_chain_lt.
    cbv [rep].
    rewrite <-from_list_default_eq with (d := 0).
    erewrite <-to_list_from_list with (pf := length_carry_sequence (length_to_list _)).
    rewrite from_list_default_eq with (pf := length_carry_sequence (length_to_list _)).
    rewrite carry_sequence_rep; try reflexivity; try apply make_chain_lt.
    cbv [rep].
    rewrite carry_sequence_rep; try reflexivity; try apply make_chain_lt.
    rewrite from_list_default_eq with (pf := length_to_list _).
    rewrite from_list_to_list; reflexivity.
  Qed.

  Lemma freeze_rep : forall u x, rep u x -> rep (freeze int_width u) x.
  Proof.
    cbv [rep]; intros.
    apply F.eq_to_Z_iff.
    erewrite <-!Fdecode_decode_mod by eauto.
    apply freeze_decode.
  Qed.

  Lemma freeze_canonical : forall u v x y, rep u x -> rep v y ->
                                           initial_bounds u ->
                                           initial_bounds v ->
    (x = y <-> fieldwise Logic.eq (freeze int_width u) (freeze int_width v)).
  Proof.
    intros; apply bounded_canonical; auto using freeze_rep, minimal_rep_freeze.
  Qed.

End CanonicalizationProofs.

Section SquareRootProofs.
  Context `{freeze_pre : FreezePreconditions}.
  Local Notation "u ~= x" := (rep u x).
  Local Notation digits := (tuple Z (length limb_widths)).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Hint Resolve (@limb_widths_nonneg _ prm) sum_firstn_limb_widths_nonneg.

  Definition freeze_input_bounds n :=
     (2 ^ B -
       (if eq_nat_dec n 0
        then 0
        else (2 ^ B) >> (nth_default 0 limb_widths (pred n)))).
  Definition bounded_by u bounds :=
      (forall n : nat, (n < length limb_widths)%nat ->
          0 <= nth_default 0 (to_list (length limb_widths) u) n < bounds n).

  Lemma eqb_true_iff : forall u v x y,
    bounded_by u freeze_input_bounds -> bounded_by v freeze_input_bounds ->
    u ~= x -> v ~= y -> (x = y <-> eqb int_width u v = true).
  Proof.
    cbv [eqb freeze_input_bounds]. intros.
    rewrite fieldwiseb_fieldwise by (apply Z.eqb_eq).
    eauto using freeze_canonical.
  Qed.

  Lemma eqb_false_iff : forall u v x y,
    bounded_by u freeze_input_bounds -> bounded_by v freeze_input_bounds ->
    u ~= x -> v ~= y -> (x <> y <-> eqb int_width u v = false).
  Proof.
    intros.
    case_eq (eqb int_width u v).
    + rewrite <-eqb_true_iff by eassumption; split; intros;
        congruence || contradiction.
    + split; intros; auto.
      intro Hfalse_eq;
        rewrite (eqb_true_iff u v) in Hfalse_eq by eassumption.
      congruence.
  Qed.

  Section Sqrt3mod4.
  Context (modulus_3mod4 : modulus mod 4 = 3).
  Context {ec : ExponentiationChain (modulus / 4 + 1)}.

  Lemma sqrt_3mod4_correct : forall u x, u ~= x ->
    (sqrt_3mod4 chain chain_correct u) ~= F.sqrt_3mod4 x.
  Proof.
    repeat match goal with
           | |- _ => progress (cbv [sqrt_3mod4 F.sqrt_3mod4]; intros)
           | |- _ => rewrite @F.pow_2_r in *
           | |- _ => rewrite eqb_correct in * by eassumption
           | |- _ => rewrite <-chain_correct; apply pow_rep; eassumption
           end.
  Qed.
  End Sqrt3mod4.

  Section Sqrt5mod8.
  Context (modulus_5mod8 : modulus mod 8 = 5).
  Context {ec : ExponentiationChain (modulus / 8 + 1)}.
  Context (sqrt_m1 : digits) (sqrt_m1_correct : mul sqrt_m1 sqrt_m1 ~= F.opp 1%F).

  Lemma sqrt_5mod8_correct : forall u x powx powx_squared, u ~= x ->
    bounded_by u freeze_input_bounds ->
    bounded_by powx_squared freeze_input_bounds ->
    ModularBaseSystem.eq powx (pow u chain) ->
    ModularBaseSystem.eq powx_squared (mul powx powx) ->
    (sqrt_5mod8 int_width powx powx_squared chain chain_correct sqrt_m1 u) ~= F.sqrt_5mod8 (decode sqrt_m1) x.
  Proof.
    cbv [sqrt_5mod8 F.sqrt_5mod8].
    intros.
    repeat match goal with
           | |- _ => progress (cbv [sqrt_5mod8 F.sqrt_5mod8]; intros)
           | |- _ => rewrite @F.pow_2_r in *
           | |- _ => rewrite eqb_correct in * by eassumption
           | |- (if eqb _ ?a ?b then _ else _) ~=
                (if dec (?c = _) then _ else _) =>
             assert (a ~= c) by
                 (cbv [rep]; rewrite <-chain_correct, <-pow_rep, <-mul_rep;
                  eassumption); repeat break_if
           | |- _ => apply mul_rep; try reflexivity;
                       rewrite <-chain_correct, <-pow_rep; eassumption
           | |- _ => rewrite <-chain_correct, <-pow_rep; eassumption
           | H : eqb _ ?a ?b = true, H1 : ?b ~= ?y, H2 : ?a ~= ?x |- _ =>
             rewrite <-(eqb_true_iff a b x y) in H by eassumption
           | H : eqb _ ?a ?b = false, H1 : ?b ~= ?y, H2 : ?a ~= ?x |- _ =>
             rewrite <-(eqb_false_iff a b x y) in H by eassumption
           | |- _ => congruence
           end.
  Qed.
  End Sqrt5mod8.

End SquareRootProofs.

Section ConversionProofs.
  Context `{prm :PseudoMersenneBaseParams}.
  Context {target_widths}
          (target_widths_nonneg : forall x, In x target_widths -> 0 <= x)
          (bits_eq : sum_firstn limb_widths   (length limb_widths) =
                     sum_firstn target_widths (length target_widths)).
  Local Notation target_base := (base_from_limb_widths target_widths).

  Lemma pack_rep : forall w,
    bounded limb_widths (to_list _ w) ->
    bounded target_widths (to_list _ w) ->
    rep w (F.of_Z modulus
                  (BaseSystem.decode
                     target_base
                     (to_list _ (pack target_widths_nonneg bits_eq w)))).
  Proof.
    intros; cbv [pack ModularBaseSystemList.pack rep].
    rewrite Tuple.to_list_from_list.
    apply F.eq_to_Z_iff.
    rewrite F.to_Z_of_Z.
    rewrite <-Conversion.convert_correct; auto using length_to_list.
  Qed.

  Lemma unpack_rep : forall w,
    bounded target_widths (to_list _ w) ->
    rep (unpack target_widths_nonneg bits_eq w)
        (F.of_Z modulus (BaseSystem.decode target_base (to_list _ w))).
  Proof.
    intros; cbv [unpack ModularBaseSystemList.unpack rep].
    apply F.eq_to_Z_iff.
    rewrite <-from_list_default_eq with (d := 0).
    rewrite <-decode_mod_Fdecode by apply Conversion.length_convert.
    rewrite F.to_Z_of_Z.
    rewrite <-Conversion.convert_correct; auto using length_to_list.
  Qed.
    

End ConversionProofs.
