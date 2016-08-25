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

  Class SubtractionCoefficient {m : Z} {prm : PseudoMersenneBaseParams m} := {
    coeff : tuple Z (length limb_widths);
    coeff_mod: decode coeff = 0%F
  }.

  Class InvExponentiationChain {m : Z} {prm : PseudoMersenneBaseParams m} := {
    chain : list (nat * nat);
    chain_correct : fold_chain 0%N N.add chain (1%N :: nil) = Z.to_N (m - 2)
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
      match goal with |- appcontext [?a mod modulus] =>
                      pose proof (Z.mod_pos_bound a modulus modulus_pos) end.
      pose proof lt_modulus_2k.
      omega.
    + eauto using base_upper_bound_compatible, limb_widths_nonneg.
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
    change (map (Z.mul c)) with (BaseSystem.mul_each c).
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

  Section Subtraction.
  Context (mm : digits) (mm_spec : decode mm = 0%F).

  Lemma sub_rep : forall u v x y, u ~= x -> v ~= y ->
    ModularBaseSystem.sub mm u v ~= (x-y)%F.
  Proof.
    autounfold; cbv [sub]; intros.
    rewrite to_list_from_list; autounfold.
    cbv [ModularBaseSystemList.sub].
    rewrite BaseSystemProofs.sub_rep, BaseSystemProofs.add_rep.
    rewrite F.of_Z_sub, F.of_Z_add, F.of_Z_mod.
    apply Fdecode_decode_mod in mm_spec; cbv [BaseSystem.decode] in *.
    rewrite mm_spec. rewrite Algebra.left_identity.
    f_equal; assumption.
  Qed.

  Lemma opp_rep : forall u x, u ~= x -> opp mm u ~= F.opp x.
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
  End Subtraction.

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

  Global Instance opp_Proper : Proper (Logic.eq ==> eq ==> eq) opp.
  Admitted.

  Global Instance add_Proper : Proper (eq ==> eq ==> eq) add.
  Admitted.
  
  Global Instance sub_Proper : Proper (Logic.eq ==> eq ==> eq ==> eq) sub.
  Admitted.
  
  Global Instance mul_Proper : Proper (eq ==> eq ==> eq) mul.
  Admitted.

  Global Instance inv_Proper chain chain_correct : Proper (eq ==> eq) (inv chain chain_correct).
  Admitted.

  Global Instance div_Proper : Proper (eq ==> eq ==> eq) div.
  Admitted.


  Section FieldProofs.
  Context (modulus_gt_2 : 2 < modulus)
          {sc : SubtractionCoefficient}
          {ic : InvExponentiationChain}.

  Lemma _zero_neq_one : not (eq zero one).
  Proof.
    cbv [eq zero one]; erewrite !encode_rep.
    pose proof (@F.field_modulo modulus prime_modulus).
    apply zero_neq_one.
  Qed.

  Lemma modular_base_system_field :
    @field digits eq zero one (opp coeff) add (sub coeff) mul (inv chain chain_correct) div.
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

  Lemma carry_full_preserves_rep : forall us x,
    rep us x -> rep (carry_full us) x.
  Proof.
    unfold carry_full; intros.
    apply carry_sequence_rep; auto.
    unfold full_carry_chain; apply make_chain_lt.
  Qed.

  Opaque carry_full.

  Context `{cc : CarryChain limb_widths}.
  Lemma carry_mul_rep : forall us vs x y,
    rep us x -> rep vs y ->
    rep (carry_mul carry_chain us vs) (x * y)%F.
  Proof.
    cbv [carry_mul]; intros; apply carry_sequence_rep;
      auto using carry_chain_valid,  mul_rep.
  Qed.

End CarryProofs.

Hint Rewrite @length_carry_and_reduce @length_carry : distr_length.

Section CanonicalizationProofs.
  Context `{prm : PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).
  Context (lt_1_length_base : (1 < length limb_widths)%nat)
   {B} (B_pos : 0 < B) (B_compat : forall w, In w limb_widths -> w <= B)
   (* on the first reduce step, we add at most one bit of width to the first digit *)
   (c_reduce1 : c * ((2 ^ B) >> log_cap (pred (length limb_widths))) <= 2 ^ log_cap 0)
   (* on the second reduce step, we add at most one bit of width to the first digit,
      and leave room to carry c one more time after the highest bit is carried *)
   (c_reduce2 : c <= nth_default 0 modulus_digits 0)
   (* this condition is probably implied by c_reduce2, but is more straighforward to compute than to prove *)
   (two_pow_k_le_2modulus : 2 ^ k <= 2 * modulus).
  Local Hint Resolve (@limb_widths_nonneg _ prm) sum_firstn_limb_widths_nonneg.
  Local Hint Resolve log_cap_nonneg.

  Lemma nth_default_carry_and_reduce_full : forall n i us,
    nth_default 0 (carry_and_reduce i us) n
    = if lt_dec n (length us)
      then
        (if eq_nat_dec n (i mod length limb_widths)
        then Z.pow2_mod (nth_default 0 us n) (log_cap n)
        else nth_default 0 us n) +
          if eq_nat_dec n (S (i mod length limb_widths) mod length limb_widths)
          then c * nth_default 0 us (i mod length limb_widths) >> log_cap (i mod length limb_widths)
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
    nth_default 0 (carry i us) n
    = if lt_dec n (length us)
      then
        if eq_nat_dec i (pred (length limb_widths))
        then (if eq_nat_dec n i
             then Z.pow2_mod (nth_default 0 us n) (log_cap n)
             else nth_default 0 us n) +
               if eq_nat_dec n 0
               then c * (nth_default 0 us i >> log_cap i)
               else 0
        else if eq_nat_dec n i
             then Z.pow2_mod (nth_default 0 us n) (log_cap n)
             else nth_default 0 us n +
               if eq_nat_dec n (S i)
               then nth_default 0 us i >> log_cap i
               else 0
      else 0.
  Proof.
    intros.
    cbv [carry].
    break_if.
    + subst i. autorewrite with push_nth_default natsimplify.
      destruct (eq_nat_dec (length limb_widths) (length us)); congruence.
    + autorewrite with push_nth_default; reflexivity.
  Qed.
  Hint Rewrite @nth_default_carry_full : push_nth_default.

  Lemma nth_default_carry_sequence_make_chain_full : forall i n us,
    length us = length limb_widths ->
    (i <= length limb_widths)%nat ->
    nth_default 0 (carry_sequence (make_chain i) us) n
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
                    then Z.pow2_mod
                          (nth_default 0 (carry_sequence (make_chain (pred i)) us) n)
                          (log_cap n)
                    else nth_default 0 (carry_sequence (make_chain (pred i)) us) n
                 else nth_default 0 (carry_sequence (make_chain (pred i)) us) n +
                    (if eq_nat_dec n i
                     then (nth_default 0 (carry_sequence (make_chain (pred i)) us) (pred i))
                            >> log_cap (pred i)
                     else 0)
              else
                  if lt_dec n (pred i)
                  then nth_default 0 (carry_sequence (make_chain (pred i)) us) n +
                     (if eq_nat_dec n 0
                      then c * (nth_default 0 (carry_sequence (make_chain (pred i)) us) (pred i))
                             >> log_cap (pred i)
                      else 0)
                  else Z.pow2_mod
                         (nth_default 0 (carry_sequence (make_chain (pred i)) us) n)
                         (log_cap n)
      else 0.
  Proof.
    induction i; intros; cbv [ModularBaseSystemList.carry_sequence].
    + cbv [pred make_chain fold_right].
      repeat break_if; subst; omega || reflexivity || auto using Z.add_0_r.
      apply nth_default_out_of_bounds. omega.
    + replace (make_chain (S i)) with (i :: make_chain i) by reflexivity.
      rewrite fold_right_cons.
      autorewrite with push_nth_default natsimplify;
        rewrite ?Nat.pred_succ; fold (carry_sequence (make_chain i) us);
        rewrite length_carry_sequence; auto.
      repeat break_if; try omega; rewrite ?IHi by (omega || auto);
        rewrite ?Z.add_0_r; try reflexivity.
  Qed.

  Lemma nth_default_carry_full_full : forall n us,
    length us = length limb_widths ->
    nth_default 0 (ModularBaseSystemList.carry_full us) n
    = if lt_dec n (length limb_widths)
      then
           if eq_nat_dec n (pred (length limb_widths))
           then Z.pow2_mod
                  (nth_default 0 (carry_sequence (make_chain (pred (length limb_widths))) us) n)
                  (log_cap n)
           else nth_default 0 (carry_sequence (make_chain (pred (length limb_widths))) us) n +
              (if eq_nat_dec n 0
               then c * (nth_default 0 (carry_sequence (make_chain (pred (length limb_widths))) us) (pred (length limb_widths)))
                      >> log_cap (pred (length limb_widths))
               else 0)
      else 0.
  Proof.
    intros.
    cbv [ModularBaseSystemList.carry_full full_carry_chain].
    rewrite (nth_default_carry_sequence_make_chain_full (length limb_widths)) by omega.
    repeat break_if; try omega; reflexivity.
  Qed.
  Hint Rewrite @nth_default_carry_full_full : push_nth_default.

  Lemma nth_default_carry : forall i us,
    length us = length limb_widths ->
    (i < length us)%nat ->
    nth_default 0 (ModularBaseSystemList.carry i us) i
    = Z.pow2_mod (nth_default 0 us i) (log_cap i).
  Proof.
    intros; autorewrite with push_nth_default natsimplify; break_match; omega.
  Qed.
  Hint Rewrite @nth_default_carry using (omega || distr_length; omega) : push_nth_default.

  Local Notation "u [ i ]"  := (nth_default 0 u i).
  Local Notation "u {{ i }}"  := (carry_sequence (make_chain i) u) (at level 30). (* Can't rely on [Reserved Notation]: https://coq.inria.fr/bugs/show_bug.cgi?id=4970 *)

  Lemma bound_during_first_loop : forall i n us,
    length us = length limb_widths ->
    (i <= length limb_widths)%nat ->
    (forall n, 0 <= nth_default 0 us n < 2 ^ B - if eq_nat_dec n 0 then 0 else ((2 ^ B) >> log_cap (pred n))) ->
    0 <= us{{i}}[n] < if eq_nat_dec i 0 then us[n] + 1 else
      if lt_dec i (length limb_widths)
      then
          if lt_dec n i
          then 2 ^ (log_cap n)
          else if eq_nat_dec n i
               then 2 ^ B
               else us[n] + 1
      else
          if eq_nat_dec n 0
          then 2 * 2 ^ limb_widths [n]
          else 2 ^ limb_widths [n].
  Proof.
    induction i; intros; cbv [ModularBaseSystemList.carry_sequence].
    + break_if; try omega.
      cbv [make_chain fold_right]. split; try omega. apply H1.
    + replace (make_chain (S i)) with (i :: make_chain i) by reflexivity.
      rewrite fold_right_cons.
      autorewrite with push_nth_default natsimplify; rewrite ?Nat.pred_succ;
        fold (carry_sequence (make_chain i) us);  rewrite length_carry_sequence; auto.
      repeat (break_if; try omega);
        try solve [rewrite Z.pow2_mod_spec by auto; autorewrite with zsimplify; apply Z.mod_pos_bound; zero_bounds];
        pose proof (IHi i us); pose proof (IHi n us); specialize_by assumption; specialize_by auto with zarith;
        repeat break_if; try omega; pose proof c_pos; (split; try solve [zero_bounds]).
      (* TODO (jadep) : clean up/automate these leftover cases. *)
      - replace (2 * 2 ^ limb_widths [n]) with (2 ^ limb_widths [n] + 2 ^ limb_widths [n]) by ring.
        apply Z.add_lt_le_mono; subst n. omega.
        eapply Z.le_trans; eauto.
        apply Z.mul_le_mono_nonneg_l; try omega. subst i.
        apply Z.shiftr_le; auto. apply Z.lt_le_incl. apply H2.
      - replace (2 ^ B) with ((2 ^ B - ((2 ^ B) >> log_cap i)) + ((2 ^ B) >> log_cap i)) by ring.
        apply Z.add_lt_le_mono.
        * eapply Z.le_lt_trans with (m := us [n]); try omega.
          replace i with (pred n) by omega.
          eapply Z.lt_le_trans; [ apply H1 | ].
          break_if; omega.
        * apply Z.shiftr_le. auto.
          apply Z.le_trans with (m := us [i]); [ omega | ].
          eapply Z.le_trans. apply Z.lt_le_incl. apply H1.
          break_if; omega.
      - replace (2 ^ B) with ((2 ^ B - ((2 ^ B) >> log_cap i)) + ((2 ^ B) >> log_cap i)) by ring.
        apply Z.add_lt_le_mono.
        * eapply Z.le_lt_trans with (m := us [n]); try omega.
          replace i with (pred n) by omega.
          eapply Z.lt_le_trans; [ apply H1 | ].
          break_if; omega.
        * apply Z.shiftr_le. auto. omega.
  Qed.

  Lemma bound_after_first_loop : forall n us,
    length us = length limb_widths ->
    (forall n, 0 <= nth_default 0 us n < 2 ^ B - if eq_nat_dec n 0 then 0 else ((2 ^ B) >> log_cap (pred n))) ->
    0 <= (ModularBaseSystemList.carry_full us)[n] <
      if eq_nat_dec n 0
      then 2 * 2 ^ limb_widths [n]
      else 2 ^ limb_widths [n].
  Proof.
    cbv [ModularBaseSystemList.carry_full full_carry_chain]; intros.
    pose proof (bound_during_first_loop (length limb_widths) n us).
    specialize_by eauto.
    repeat (break_if; try omega).
  Qed.

  (* TODO(jadep):
     - Proof of bound after 3 loops
     - Proof of correctness for [ge_modulus] and [cond_subtract_modulus]
     - Proof of correctness for [freeze]
       * freeze us = encode (decode us)
       * decode us = x ->
         canonicalized_BSToWord (freeze us)) = FToWord x

         (where [canonicalized_BSToWord] uses bitwise operations to concatenate digits
          in BaseSystem in canonical form, splitting along word capacities)
  *)

End CanonicalizationProofs.
