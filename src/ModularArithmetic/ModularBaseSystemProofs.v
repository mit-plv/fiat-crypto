Require Import Zpower ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil Crypto.Util.NatUtil.
Require Import VerdiTactics.
Require Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystem Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.BaseSystemProofs Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.


Section PseudoMersenneProofs.
  Context `{prm :PseudoMersenneBaseParams}.

  Local Hint Unfold decode.
  Local Notation "u ~= x" := (rep u x).
  Local Notation "u .+ x" := (add u x).
  Local Notation "u .* x" := (ModularBaseSystem.mul u x).
  Local Hint Unfold rep.
  Local Hint Resolve (@limb_widths_nonneg _ prm) sum_firstn_limb_widths_nonneg.
  Local Hint Resolve log_cap_nonneg.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).

  Lemma rep_decode : forall us x, us ~= x -> decode us = x.
  Proof.
    autounfold; intuition.
  Qed.

  Lemma rep_length : forall us x, us ~= x -> length us = length base.
  Proof.
    autounfold; intuition.
  Qed.

  Lemma decode_rep : forall us, length us = length base ->
    rep us (decode us).
  Proof.
    cbv [rep]; auto.
  Qed.

  Lemma lt_modulus_2k : modulus < 2 ^ k.
  Proof.
    replace (2 ^ k) with (modulus + c) by (unfold c; ring).
    pose proof c_pos; omega.
  Qed. Hint Resolve lt_modulus_2k.

  Lemma modulus_pos : 0 < modulus.
  Proof.
    pose proof (NumTheoryUtil.lt_1_p _ prime_modulus); omega.
  Qed. Hint Resolve modulus_pos.

  Lemma encode'_eq : forall (x : F modulus) i, (i <= length limb_widths)%nat ->
    encode' limb_widths x i = BaseSystem.encode' base x (2 ^ k) i.
  Proof.
    rewrite <-base_length; induction i; intros.
    + rewrite encode'_zero. reflexivity.
    + rewrite encode'_succ, <-IHi by omega.
      simpl; do 2 f_equal.
      rewrite Z.land_ones, Z.shiftr_div_pow2 by eauto.
      match goal with H : (S _ <= length base)%nat |- _ =>
        apply le_lt_or_eq in H; destruct H end.
      - repeat f_equal; rewrite nth_default_base  by (eauto || omega); reflexivity.
      - repeat f_equal; try solve [rewrite nth_default_base  by (eauto || omega); reflexivity].
        rewrite nth_default_out_of_bounds by omega.
        unfold k.
        rewrite <-base_length; congruence.
  Qed.

  Lemma encode_eq : forall x : F modulus,
    encode x = BaseSystem.encode base x (2 ^ k).
  Proof.
    unfold encode, BaseSystem.encode; intros.
    rewrite base_length; apply encode'_eq; omega.
  Qed.

  Lemma encode_rep : forall x : F modulus, encode x ~= x.
  Proof.
    intros.
    rewrite encode_eq.
    unfold encode, rep.
    split. {
      unfold BaseSystem.encode.
      auto using encode'_length.
    } {
      unfold decode.
      rewrite encode_rep.
      + apply ZToField_FieldToZ.
      + apply bv.
      + split; [ | etransitivity]; try (apply FieldToZ_range; auto using modulus_pos); auto.
      + unfold base_max_succ_divide; intros.
        match goal with H : (_ <= length base)%nat |- _ =>
          apply le_lt_or_eq in H; destruct H end.
        - apply Z.mod_divide.
          * apply nth_default_base_nonzero; auto using bv, two_k_nonzero.
          * rewrite !nth_default_eq.
            do 2 (erewrite nth_indep with (d := 2 ^ k) (d' := 0) by omega).
            rewrite <-!nth_default_eq.
            apply base_succ; eauto; omega.
        - rewrite nth_default_out_of_bounds with (n := S i) by omega.
          rewrite nth_default_base by (omega || eauto).
          unfold k.
          match goal with H : S _ = length base |- _ =>
            rewrite base_length in H; rewrite <-H end.
          erewrite sum_firstn_succ by (apply nth_error_Some_nth_default with (x0 := 0); omega).
          rewrite Z.pow_add_r by (eauto using sum_firstn_limb_widths_nonneg;
            apply limb_widths_nonneg; rewrite nth_default_eq; apply nth_In; omega).
          apply Z.divide_factor_r.
    }
  Qed.

  Lemma add_rep : forall u v x y, u ~= x -> v ~= y -> BaseSystem.add u v ~= (x+y)%F.
  Proof.
    autounfold; intuition. {
      unfold add.
      auto using add_same_length.
    }
    unfold decode in *; unfold decode in *.
    rewrite add_rep.
    rewrite ZToField_add.
    subst; auto.
  Qed.

  Lemma decode_short : forall (us : BaseSystem.digits),
    (length us <= length base)%nat ->
    BaseSystem.decode base us = BaseSystem.decode ext_base us.
  Proof.
    intros.
    unfold BaseSystem.decode, BaseSystem.decode'.
    rewrite combine_truncate_r.
    rewrite (combine_truncate_r us ext_base).
    f_equal; f_equal.
    unfold ext_base.
    rewrite firstn_app_inleft; auto; omega.
  Qed.

  Lemma mul_rep_extended : forall (us vs : BaseSystem.digits),
      (length us <= length base)%nat ->
      (length vs <= length base)%nat ->
      (BaseSystem.decode base us) * (BaseSystem.decode base vs) = BaseSystem.decode ext_base (BaseSystem.mul ext_base us vs).
  Proof.
      intros.
      rewrite mul_rep by (apply ExtBaseVector || unfold ext_base; simpl_list; omega).
      f_equal; rewrite decode_short; auto.
  Qed.

  Lemma modulus_nonzero : modulus <> 0.
    pose proof (Znumtheory.prime_ge_2 _ prime_modulus); omega.
  Qed.

  (* a = r + s(2^k) = r + s(2^k - c + c) = r + s(2^k - c) + cs = r + cs *)
  Lemma pseudomersenne_add: forall x y, (x + ((2^k) * y)) mod modulus = (x + (c * y)) mod modulus.
  Proof.
    intros.
    replace (2^k) with ((2^k - c) + c) by ring.
    rewrite Z.mul_add_distr_r.
    rewrite Zplus_mod.
    unfold c.
    rewrite Z.sub_sub_distr, Z.sub_diag.
    simpl.
    rewrite Z.mul_comm.
    rewrite Z.mod_add_l; auto using modulus_nonzero.
    rewrite <- Zplus_mod; auto.
  Qed.

  Lemma pseudomersenne_add': forall x y0 y1 z, (z - x + ((2^k) * y0 * y1)) mod modulus = (c * y0 * y1 - x + z) mod modulus.
  Proof.
    intros; rewrite <- !Z.add_opp_r, <- !Z.mul_assoc, pseudomersenne_add; apply f_equal2; omega.
  Qed.

  Lemma extended_shiftadd: forall (us : BaseSystem.digits),
    BaseSystem.decode ext_base us =
      BaseSystem.decode base (firstn (length base) us)
      + (2^k * BaseSystem.decode base (skipn (length base) us)).
  Proof.
    intros.
    unfold BaseSystem.decode; rewrite <- mul_each_rep.
    unfold ext_base.
    replace (map (Z.mul (2 ^ k)) base) with (BaseSystem.mul_each (2 ^ k) base) by auto.
    rewrite base_mul_app.
    rewrite <- mul_each_rep; auto.
  Qed.

  Lemma reduce_rep : forall us,
    BaseSystem.decode base (reduce us) mod modulus =
    BaseSystem.decode ext_base us mod modulus.
  Proof.
    intros.
    rewrite extended_shiftadd.
    rewrite pseudomersenne_add.
    unfold reduce.
    remember (firstn (length base) us) as low.
    remember (skipn (length base) us) as high.
    unfold BaseSystem.decode.
    rewrite BaseSystemProofs.add_rep.
    replace (map (Z.mul c) high) with (BaseSystem.mul_each c high) by auto.
    rewrite mul_each_rep; auto.
  Qed.

  Lemma reduce_length : forall us,
      (length base <= length us <= length ext_base)%nat ->
      (length (reduce us) = length base)%nat.
  Proof.
    rewrite extended_base_length.
    unfold reduce; intros.
    rewrite add_length_exact.
    rewrite map_length, firstn_length, skipn_length.
    rewrite Min.min_l by omega.
    apply Max.max_l; omega.
  Qed.

  Lemma length_mul : forall u v,
      length u = length base
      -> length v = length base
      -> length (u .* v) = length base.
  Proof.
      autounfold in *; unfold ModularBaseSystem.mul in *; intuition eauto.
      apply reduce_length.
      rewrite mul_length_exact, extended_base_length; try omega.
      destruct u; try congruence.
      rewrite @nil_length0 in *.
      pose proof base_length_nonzero; omega.
  Qed.

  Lemma mul_rep : forall u v x y, u ~= x -> v ~= y -> u .* v ~= (x*y)%F.
  Proof.
    split; autounfold in *; unfold ModularBaseSystem.mul in *.
    { apply length_mul; intuition auto. }
    { intuition idtac; subst.
      rewrite ZToField_mod, reduce_rep, <-ZToField_mod.
      rewrite mul_rep by (apply ExtBaseVector || rewrite extended_base_length; omega).
      rewrite 2decode_short by omega.
      apply ZToField_mul. }
  Qed.

  Lemma nth_default_base_positive : forall i, (i < length base)%nat ->
    nth_default 0 base i > 0.
  Proof.
    intros.
    pose proof (nth_error_length_exists_value _ _ H).
    destruct H0.
    pose proof (nth_error_value_In _ _ _ H0).
    pose proof (BaseSystem.base_positive _ H1).
    unfold nth_default.
    rewrite H0; auto.
  Qed.

  Lemma base_succ_div_mult : forall i, ((S i) < length base)%nat ->
    nth_default 0 base (S i) = nth_default 0 base i *
    (nth_default 0 base (S i) / nth_default 0 base i).
  Proof.
    intros.
    apply Z_div_exact_2; try (apply nth_default_base_positive; omega).
    apply base_succ; eauto.
  Qed.

  Lemma Fdecode_decode_mod : forall us x, (length us = length base) ->
    decode us = x -> BaseSystem.decode base us mod modulus = x.
  Proof.
    unfold decode; intros ? ? ? decode_us.
    rewrite <-decode_us.
    apply FieldToZ_ZToField.
  Qed.

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
        destruct Hshiftr_0 as [nth_0 | []]; [ rewrite nth_0; zero_bounds | ].
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

  Context mm (mm_length : length mm = length base) (mm_spec : decode mm = 0%F).

  Lemma length_sub :  forall u v,
      length u = length base
      -> length v = length base
      -> length (ModularBaseSystem.sub mm u v) = length base.
  Proof.
    autounfold; unfold ModularBaseSystem.sub; intuition idtac.
    rewrite sub_length, add_length_exact.
    case_max; try rewrite Max.max_r; omega.
  Qed.

  Lemma sub_rep : forall u v x y, u ~= x -> v ~= y ->
    ModularBaseSystem.sub mm u v ~= (x-y)%F.
  Proof.
    split; autounfold in *.
    { apply length_sub; intuition (auto; omega). }
    { unfold decode, ModularBaseSystem.sub, BaseSystem.decode in *; intuition idtac.
      rewrite BaseSystemProofs.sub_rep, BaseSystemProofs.add_rep.
      rewrite ZToField_sub, ZToField_add.
      match goal with H : _ = 0%F |- _ => rewrite H end.
      rewrite F_add_0_l. congruence. }
  Qed.

End PseudoMersenneProofs.

Section CarryProofs.
  Context `{prm : PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).
  Local Notation "u ~= x" := (rep u x).
  Local Hint Resolve (@limb_widths_nonneg _ prm) sum_firstn_limb_widths_nonneg.

  Lemma base_length_lt_pred : (pred (length base) < length base)%nat.
  Proof.
    pose proof base_length_nonzero; omega.
  Qed.
  Hint Resolve base_length_lt_pred.

  Lemma carry_decode_eq_reduce : forall us,
    (length us = length base) ->
    BaseSystem.decode base (carry_and_reduce (pred (length base)) us) mod modulus
    = BaseSystem.decode base us mod modulus.
  Proof.
    unfold carry_and_reduce; intros ? length_eq.
    pose proof base_length_nonzero.
    rewrite add_to_nth_sum by (rewrite length_set_nth; omega).
    rewrite set_nth_sum by omega.
    rewrite Zplus_comm, <- Z.mul_assoc, <- pseudomersenne_add, BaseSystem.b0_1.
    rewrite (Z.mul_comm (2 ^ k)), <- Zred_factor0.
    f_equal.
    rewrite <- (Z.add_comm (BaseSystem.decode base us)), <- Z.add_assoc, <- Z.add_0_r.
    f_equal.
    destruct (NPeano.Nat.eq_dec (length base) 0) as [length_zero | length_nonzero].
    + apply length0_nil in length_zero.
      pose proof (base_length) as limbs_length.
      rewrite length_zero in length_eq, limbs_length.
      apply length0_nil in length_eq.
      symmetry in limbs_length.
      apply length0_nil in limbs_length.
      subst; rewrite length_zero, limbs_length, nth_default_nil.
      reflexivity.
    + rewrite nth_default_base by (omega || eauto).
      rewrite <- Z.add_opp_l, <- Z.opp_sub_distr.
      unfold Z.pow2_mod.
      rewrite Z.land_ones by eauto using log_cap_nonneg.
      rewrite <- Z.mul_div_eq by (apply Z.gt_lt_iff; apply Z.pow_pos_nonneg; omega || eauto using log_cap_nonneg).
      rewrite Z.shiftr_div_pow2 by eauto using log_cap_nonneg.
      rewrite Zopp_mult_distr_r.
      rewrite Z.mul_comm.
      rewrite Z.mul_assoc.
      rewrite <- Z.pow_add_r by eauto using log_cap_nonneg.
      unfold k.
      replace (length limb_widths) with (S (pred (length base))) by
        (subst; rewrite <- base_length; apply NPeano.Nat.succ_pred; omega).
      rewrite sum_firstn_succ with (x:= log_cap (pred (length base))) by
        (apply nth_error_Some_nth_default; rewrite <- base_length; omega).
      rewrite <- Zopp_mult_distr_r.
      rewrite Z.mul_comm.
      rewrite (Z.add_comm (log_cap (pred (length base)))).
      ring.
  Qed.

  Lemma length_carry_and_reduce : forall i us, length (carry_and_reduce i us) = length us.
  Proof. intros; unfold carry_and_reduce; autorewrite with distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry_and_reduce : distr_length.

  Lemma length_carry : forall i us, length (carry i us) = length us.
  Proof. intros; unfold carry; break_if; autorewrite with distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry : distr_length.

  Local Hint Extern 1 (length _ = _) => progress autorewrite with distr_length.

  Lemma carry_rep : forall i us x,
    (length us = length base) ->
    (i < length base)%nat ->
    us ~= x -> carry i us ~= x.
  Proof.
    pose proof length_carry. pose proof carry_decode_eq_reduce. pose proof (@carry_simple_decode_eq limb_widths).
    specialize_by eauto.
    intros; split; auto.
    unfold rep, decode, carry in *.
    intuition; break_if; subst; eauto; apply F_eq; simpl; intuition.
  Qed.
  Hint Resolve carry_rep.

  Lemma carry_sequence_length: forall is us,
    (length us = length base)%nat ->
    (length (carry_sequence is us) = length base)%nat.
  Proof.
    induction is; boring.
  Qed.
  Hint Resolve carry_sequence_length.

  Lemma carry_sequence_rep : forall is us x,
    (forall i, In i is -> (i < length base)%nat) ->
    (length us = length base) ->
    us ~= x -> carry_sequence is us ~= x.
  Proof.
    induction is; boring.
  Qed.

  Lemma carry_full_length : forall us, (length us = length base)%nat ->
    length (carry_full us) = length base.
  Proof.
    intros; cbv [carry_full]; auto using carry_sequence_length.
  Qed.

  Lemma carry_full_preserves_rep : forall us x,
    rep us x -> rep (carry_full us) x.
  Proof.
    unfold carry_full; intros.
    apply carry_sequence_rep; auto.
    unfold full_carry_chain; rewrite base_length; apply make_chain_lt.
    eauto using rep_length.
  Qed.

  Opaque carry_full.

  Lemma carry_mul_rep : forall us vs x y, rep us x -> rep vs y ->
    rep (carry_mul us vs) (x * y)%F.
  Proof.
    unfold carry_mul; intros; apply carry_full_preserves_rep.
    auto using mul_rep.
  Qed.

  Lemma carry_mul_length : forall us vs,
    length us = length base -> length vs = length base ->
    length (carry_mul us vs) = length base.
  Proof.
    intros; cbv [carry_mul].
    auto using carry_full_length, length_mul.
  Qed.

End CarryProofs.

Hint Rewrite @length_carry_and_reduce @length_carry : distr_length.

Section CanonicalizationProofs.
  Context `{prm : PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).
  Context (lt_1_length_base : (1 < length base)%nat)
   {B} (B_pos : 0 < B) (B_compat : forall w, In w limb_widths -> w <= B)
   (* on the first reduce step, we add at most one bit of width to the first digit *)
   (c_reduce1 : c * (Z.ones (B - log_cap (pred (length base)))) < max_bound 0 + 1)
   (* on the second reduce step, we add at most one bit of width to the first digit,
      and leave room to carry c one more time after the highest bit is carried *)
   (c_reduce2 : c <= max_bound 0 - c)
   (* this condition is probably implied by c_reduce2, but is more straighforward to compute than to prove *)
   (two_pow_k_le_2modulus : 2 ^ k <= 2 * modulus).

  (* BEGIN groundwork proofs *)
  Local Hint Resolve (@log_cap_nonneg limb_widths) limb_widths_nonneg.

  Lemma pow_2_log_cap_pos : forall i, 0 < 2 ^ log_cap i.
  Proof.
    intros; apply Z.pow_pos_nonneg; eauto using log_cap_nonneg; omega.
  Qed.
  Local Hint Resolve pow_2_log_cap_pos.

  Lemma max_bound_log_cap : forall i, Z.succ (max_bound i) = 2 ^ log_cap i.
  Proof.
    intros.
    unfold max_bound, Z.ones.
    rewrite Z.shiftl_1_l.
    omega.
  Qed.

  Lemma pow2_mod_log_cap_range : forall a i, 0 <= Z.pow2_mod a (log_cap i) <= max_bound i.
  Proof.
    intros.
    unfold Z.pow2_mod.
    rewrite Z.land_ones by eauto using log_cap_nonneg.
    unfold max_bound, Z.ones.
    rewrite Z.shiftl_1_l, <-Z.lt_le_pred.
    apply Z_mod_lt.
    pose proof (pow_2_log_cap_pos i).
    omega.
  Qed.

  Lemma pow2_mod_log_cap_bounds_lower : forall a i, 0 <= Z.pow2_mod a (log_cap i).
  Proof.
    intros.
    pose proof (pow2_mod_log_cap_range a  i); omega.
  Qed.

  Lemma pow2_mod_log_cap_bounds_upper : forall a i, Z.pow2_mod a (log_cap i) <= max_bound i.
  Proof.
    intros.
    pose proof (pow2_mod_log_cap_range a  i); omega.
  Qed.

  Lemma pow2_mod_log_cap_small : forall a i, 0 <= a <= max_bound i ->
    Z.pow2_mod a (log_cap i) = a.
  Proof.
    intros.
    unfold Z.pow2_mod.
    rewrite Z.land_ones by eauto using log_cap_nonneg.
    apply Z.mod_small.
    split; try omega.
    rewrite <- max_bound_log_cap.
    omega.
  Qed.

  Lemma max_bound_pos : forall i, (i < length base)%nat -> 0 < max_bound i.
  Proof.
    unfold max_bound; intros; apply Z.ones_pos_pos.
    apply limb_widths_pos.
    rewrite nth_default_eq.
    apply nth_In.
    rewrite <-base_length; assumption.
  Qed.
  Local Hint Resolve max_bound_pos.

  Lemma max_bound_nonneg : forall i, 0 <= max_bound i.
  Proof.
    unfold max_bound; intros; eauto using Z.ones_nonneg.
  Qed.
  Local Hint Resolve max_bound_nonneg.

  Lemma shiftr_eq_0_max_bound : forall i a, Z.shiftr a (log_cap i) = 0 ->
    a <= max_bound i.
  Proof.
    intros ? ? shiftr_0.
    apply Z.shiftr_eq_0_iff in shiftr_0.
    intuition; subst; try apply max_bound_nonneg.
    match goal with H : Z.log2 _ < log_cap _ |- _ => apply Z.log2_lt_pow2 in H;
      replace (2 ^ log_cap i) with (Z.succ (max_bound i)) in H by
        (unfold max_bound, Z.ones; rewrite Z.shiftl_1_l; omega)
    end; auto.
    omega.
  Qed.

  Lemma B_compat_log_cap : forall i, 0 <= B - log_cap i.
  Proof.
    intros.
    destruct (lt_dec i (length limb_widths)).
    + apply Z.le_0_sub.
      apply B_compat.
      rewrite nth_default_eq.
      apply nth_In; assumption.
    + replace (nth_default 0 limb_widths i) with 0; try omega.
      symmetry; apply nth_default_out_of_bounds.
      omega.
  Qed.
  Local Hint Resolve B_compat_log_cap.

  Lemma max_bound_shiftr_eq_0 : forall i a, 0 <= a -> a <= max_bound i ->
    Z.shiftr a (log_cap i) = 0.
  Proof.
    intros ? ? ? le_max_bound.
    apply Z.shiftr_eq_0_iff.
    destruct (Z_eq_dec a 0); auto.
    right.
    split; try omega.
    apply Z.log2_lt_pow2; try omega.
    rewrite <-max_bound_log_cap.
    omega.
  Qed.

  Lemma log_cap_eq : forall i, log_cap i = nth_default 0 limb_widths i.
  Proof.
    reflexivity.
  Qed.

  (* END groundwork proofs *)
  Opaque Z.pow2_mod max_bound.

  (* automation *)
  Ltac carry_length_conditions' := unfold carry_full, add_to_nth;
    rewrite ?length_set_nth, ?length_carry, ?carry_sequence_length;
    try omega; try solve [pose proof base_length; pose proof base_length_nonzero; omega || auto ].
  Ltac carry_length_conditions := try split; try omega; repeat carry_length_conditions'.

  Ltac add_set_nth :=
    rewrite ?add_to_nth_nth_default by carry_length_conditions; break_if; try omega;
    rewrite ?set_nth_nth_default by carry_length_conditions;    break_if; try omega.

  (* BEGIN defs *)

  Definition pre_carry_bounds us := forall i, 0 <= nth_default 0 us i <
    if (eq_nat_dec i 0) then 2 ^ B else 2 ^ B - 2 ^ (B - log_cap (pred i)).

  Lemma pre_carry_bounds_nonzero : forall us, pre_carry_bounds us ->
    (forall i, 0 <= nth_default 0 us i).
  Proof.
    unfold pre_carry_bounds.
    intros ? PCB i.
    specialize (PCB i).
    omega.
  Qed.
  Local Hint Resolve pre_carry_bounds_nonzero.

  (* END defs *)

  (* BEGIN proofs about first carry loop *)

  Lemma nth_default_carry_bound_upper : forall i us, (length us = length base) ->
    nth_default 0 (carry i us) i <= max_bound i.
  Proof.
    unfold carry; intros.
    break_if.
    + unfold carry_and_reduce.
      add_set_nth.
      apply pow2_mod_log_cap_bounds_upper.
    + unfold carry_simple.
      destruct (lt_dec i (length us)).
      - add_set_nth.
        apply pow2_mod_log_cap_bounds_upper.
      - rewrite nth_default_out_of_bounds by carry_length_conditions; auto.
  Qed.
  Local Hint Resolve nth_default_carry_bound_upper.

  Lemma nth_default_carry_bound_lower : forall i us, (length us = length base) ->
    0 <= nth_default 0 (carry i us) i.
  Proof.
    unfold carry; intros.
    break_if.
    + unfold carry_and_reduce.
      add_set_nth.
      apply pow2_mod_log_cap_bounds_lower.
    + unfold carry_simple.
      destruct (lt_dec i (length us)).
      - add_set_nth.
        apply pow2_mod_log_cap_bounds_lower.
      - rewrite nth_default_out_of_bounds by carry_length_conditions; omega.
  Qed.
  Local Hint Resolve nth_default_carry_bound_lower.

  Lemma nth_default_carry_bound_succ_lower : forall i us, (forall i, 0 <= nth_default 0 us i) ->
    (length us = length base) ->
    0 <= nth_default 0 (carry i us) (S i).
  Proof.
    unfold carry; intros ? ? PCB ? .
    break_if.
    + subst. replace (S (pred (length base))) with (length base) by omega.
      rewrite nth_default_out_of_bounds; carry_length_conditions.
      unfold carry_and_reduce.
      carry_length_conditions.
    + unfold carry_simple.
      destruct (lt_dec (S i) (length us)).
      - add_set_nth; zero_bounds.
      - rewrite nth_default_out_of_bounds by carry_length_conditions; omega.
  Qed.

  Lemma carry_unaffected_low : forall i j us, ((0 < i < j)%nat \/ (i = 0 /\ j <> 0 /\ j <> pred (length base))%nat)->
    (length us = length base) ->
    nth_default 0 (carry j us) i = nth_default 0 us i.
  Proof.
    intros.
    unfold carry.
    break_if.
    + unfold carry_and_reduce.
      add_set_nth.
    + unfold carry_simple.
      destruct (lt_dec i (length us)).
      - add_set_nth.
      - rewrite !nth_default_out_of_bounds by
          (omega || rewrite length_add_to_nth; rewrite length_set_nth; pose proof base_length_nonzero; omega).
        reflexivity.
  Qed.

  Lemma carry_unaffected_high : forall i j us, (S j < i)%nat -> (length us = length base) ->
    nth_default 0 (carry j us) i = nth_default 0 us i.
  Proof.
    intros.
    destruct (lt_dec i (length us));
      [ | rewrite !nth_default_out_of_bounds by carry_length_conditions; reflexivity].
    unfold carry, carry_simple.
    break_if; [omega | add_set_nth].
  Qed.

  Lemma carry_nothing : forall i j us, (i < length base)%nat ->
    (length us = length base)%nat ->
    0 <= nth_default 0 us j <= max_bound j ->
    nth_default 0 (carry j us) i = nth_default 0 us i.
  Proof.
    unfold carry, carry_simple, carry_and_reduce; intros.
    break_if; (add_set_nth;
      [ rewrite max_bound_shiftr_eq_0 by omega; ring
      | subst; apply pow2_mod_log_cap_small; assumption ]).
  Qed.

  Lemma carry_carry_done_done : forall i us,
    (length us = length base)%nat ->
    (i < length base)%nat ->
    carry_done us -> carry_done (carry i us).
  Proof.
    unfold carry_done; intros i ? ? i_bound Hcarry_done x x_bound.
    destruct (Hcarry_done x x_bound) as [lower_bound_x shiftr_0_x].
    destruct (Hcarry_done i i_bound) as [lower_bound_i shiftr_0_i].
    split.
    + rewrite carry_nothing; auto.
      split; [ apply Hcarry_done; auto | ].
      apply shiftr_eq_0_max_bound.
      apply Hcarry_done; auto.
    + unfold carry, carry_simple, carry_and_reduce; break_if; subst.
      - add_set_nth; subst.
        * rewrite shiftr_0_i, Z.mul_0_r, Z.add_0_l.
          assumption.
        * rewrite pow2_mod_log_cap_small by (intuition; auto using shiftr_eq_0_max_bound).
          assumption.
      - rewrite shiftr_0_i by omega.
        rewrite pow2_mod_log_cap_small by (intuition; auto using shiftr_eq_0_max_bound).
        add_set_nth; subst; rewrite ?Z.add_0_l; auto.
  Qed.

  Lemma carry_sequence_chain_step : forall i us,
    carry_sequence (make_chain (S i)) us = carry i (carry_sequence (make_chain i) us).
  Proof.
    reflexivity.
  Qed.

  Lemma carry_bounds_0_upper : forall us j, (length us = length base) ->
    (0 < j < length base)%nat ->
    nth_default 0 (carry_sequence (make_chain j) us) 0 <= max_bound 0.
  Proof.
    induction j as [ | [ | j ] IHj ]; [simpl; intros; omega | | ]; intros.
    + subst; simpl; auto.
    + rewrite carry_sequence_chain_step, carry_unaffected_low; carry_length_conditions.
    Qed.

  Lemma carry_bounds_upper : forall i us j, (0 < i < j)%nat -> (length us = length base) ->
    nth_default 0 (carry_sequence (make_chain j) us) i <= max_bound i.
  Proof.
    unfold carry_sequence;
    induction j; [simpl; intros; omega | ].
    intros.
    simpl in *.
    assert (i = j \/ i < j)%nat as cases by omega.
    destruct cases as [eq_j_i | lt_i_j]; subst.
    + apply nth_default_carry_bound_upper; fold (carry_sequence (make_chain j) us); carry_length_conditions.
    + rewrite carry_unaffected_low; try omega.
      fold (carry_sequence (make_chain j) us); carry_length_conditions.
  Qed.

  Lemma carry_sequence_unaffected : forall i us j, (j < i)%nat -> (length us = length base)%nat ->
    nth_default 0 (carry_sequence (make_chain j) us) i = nth_default 0 us i.
  Proof.
    induction j; [simpl; intros; omega | ].
    intros.
    simpl in *.
    rewrite carry_unaffected_high by carry_length_conditions.
    apply IHj; omega.
  Qed.

  (* makes omega run faster *)
  Ltac clear_obvious :=
    match goal with
    | [H : ?a <= ?a |- _] => clear H
    | [H : ?a <= S ?a |- _] => clear H
    | [H : ?a < S ?a |- _] => clear H
    | [H : ?a = ?a |- _] => clear H
    end.

  Lemma carry_sequence_bounds_lower : forall j i us, (length us = length base) ->
    (forall i, 0 <= nth_default 0 us i) -> (j <= length base)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain j) us) i.
  Proof.
    induction j; intros; simpl; auto.
    destruct (lt_dec (S j) i).
    + rewrite carry_unaffected_high by carry_length_conditions.
      apply IHj; auto; omega.
    + assert ((i = S j) \/ (i = j) \/ (i < j))%nat as cases by omega.
      destruct cases as [? | [? | ?]].
      - subst. apply nth_default_carry_bound_succ_lower; carry_length_conditions.
        intros; eapply IHj; auto; omega.
      - subst. apply nth_default_carry_bound_lower; carry_length_conditions.
      - destruct (eq_nat_dec j (pred (length base)));
          [ | rewrite carry_unaffected_low by carry_length_conditions; apply IHj; auto; omega ].
        subst.
        do 2 match goal with H : appcontext[S (pred (length base))] |- _ =>
          erewrite <-(S_pred (length base)) in H by eauto end.
        unfold carry; break_if; [ unfold carry_and_reduce | omega ].
        clear_obvious. pose proof c_pos.
        add_set_nth; [ zero_bounds | ]; apply IHj; auto; omega.
  Qed.

  Ltac carry_seq_lower_bound :=
        repeat (intros; eapply carry_sequence_bounds_lower; eauto; carry_length_conditions).

  Lemma carry_bounds_lower : forall i us j, (0 < i <= j)%nat -> (length us = length base) ->
    (forall i, 0 <= nth_default 0 us i) -> (j <= length base)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain j) us) i.
  Proof.
    unfold carry_sequence;
    induction j; [simpl; intros; omega | ].
    intros.
    simpl in *.
    destruct (eq_nat_dec i (S j)).
    + subst. apply nth_default_carry_bound_succ_lower; auto;
        fold (carry_sequence (make_chain j) us); carry_length_conditions.
      carry_seq_lower_bound.
    + assert (i = j \/ i < j)%nat as cases by omega.
      destruct cases as [eq_j_i | lt_i_j]; subst;
        [apply nth_default_carry_bound_lower| rewrite carry_unaffected_low]; try omega;
        fold (carry_sequence (make_chain j) us); carry_length_conditions.
      carry_seq_lower_bound.
  Qed.

  Lemma carry_full_bounds : forall us i, (i <> 0)%nat -> (forall i, 0 <= nth_default 0 us i) ->
    (length us = length base)%nat ->
    0 <= nth_default 0 (carry_full us) i <= max_bound i.
  Proof.
    unfold carry_full, full_carry_chain; intros.
    split; (destruct (lt_dec i (length limb_widths));
              [ | rewrite nth_default_out_of_bounds by carry_length_conditions; omega || auto ]).
    + apply carry_bounds_lower; carry_length_conditions.
    + apply carry_bounds_upper; carry_length_conditions.
  Qed.

  Lemma carry_simple_no_overflow : forall us i, (i < pred (length base))%nat ->
    length us = length base ->
    0 <= nth_default 0 us i < 2 ^ B ->
    0 <= nth_default 0 us (S i) < 2 ^ B - 2 ^ (B - log_cap i) ->
    0 <= nth_default 0 (carry i us) (S i) < 2 ^ B.
  Proof.
    intros.
    unfold carry, carry_simple; break_if; try omega.
    add_set_nth.
    replace (2 ^ B) with (2 ^ (B - log_cap i) + (2 ^ B - 2 ^ (B - log_cap i))) by omega.
    split; [ zero_bounds | ].
    apply Z.add_lt_mono; try omega.
    rewrite Z.shiftr_div_pow2 by eauto using log_cap_nonneg.
    apply Z.div_lt_upper_bound; try apply pow_2_log_cap_pos.
    rewrite <-Z.pow_add_r by (eauto using log_cap_nonneg || apply B_compat_log_cap).
    replace (log_cap i + (B - log_cap i)) with B by ring.
    omega.
  Qed.

  Lemma carry_sequence_no_overflow : forall i us, pre_carry_bounds us ->
    (length us = length base) ->
    nth_default 0 (carry_sequence (make_chain i) us) i < 2 ^ B.
  Proof.
    unfold pre_carry_bounds.
    intros ? ? PCB ?.
    induction i.
    + simpl. specialize (PCB 0%nat).
      intuition.
    + simpl.
      destruct (lt_eq_lt_dec i (pred (length base))) as [[? | ? ] | ? ].
      - apply carry_simple_no_overflow; carry_length_conditions; carry_seq_lower_bound.
       rewrite carry_sequence_unaffected; try omega.
        specialize (PCB (S i)); rewrite Nat.pred_succ in PCB.
        break_if; intuition.
      - unfold carry; break_if; try omega.
        rewrite nth_default_out_of_bounds; [ apply Z.pow_pos_nonneg; omega | ].
        subst; unfold carry_and_reduce.
        carry_length_conditions.
      - rewrite nth_default_out_of_bounds; [ apply Z.pow_pos_nonneg; omega | ].
        carry_length_conditions.
  Qed.

  Lemma carry_full_bounds_0 : forall us, pre_carry_bounds us ->
    (length us = length base)%nat ->
    0 <= nth_default 0 (carry_full us) 0 <= max_bound 0 + c * (Z.ones (B - log_cap (pred (length base)))).
  Proof.
    unfold carry_full, full_carry_chain; intros.
    rewrite <- base_length.
    replace (length base) with (S (pred (length base))) by omega.
    simpl.
    unfold carry, carry_and_reduce; break_if; try omega.
    clear_obvious; add_set_nth.
    split; [pose proof c_pos; zero_bounds; carry_seq_lower_bound | ].
    rewrite Z.add_comm.
    apply Z.add_le_mono.
    + apply carry_bounds_0_upper; auto; omega.
    + apply Z.mul_le_mono_pos_l; auto using c_pos.
      apply Z.shiftr_ones; eauto;
        [ | pose proof (B_compat_log_cap (pred (length base))); omega ].
      split.
      - apply carry_bounds_lower; auto; omega.
      - apply carry_sequence_no_overflow; auto.
  Qed.

  Lemma carry_full_bounds_lower : forall i us, pre_carry_bounds us ->
    (length us = length base)%nat ->
    0 <= nth_default 0 (carry_full us) i.
  Proof.
   destruct i; intros.
   + apply carry_full_bounds_0; auto.
   + destruct (lt_dec (S i) (length base)).
     - apply carry_bounds_lower; carry_length_conditions.
     - rewrite nth_default_out_of_bounds; carry_length_conditions.
  Qed.

  (* END proofs about first carry loop *)

  (* BEGIN proofs about second carry loop *)

  Lemma carry_sequence_carry_full_bounds_same : forall us i, pre_carry_bounds us ->
    (length us = length base)%nat -> (0 < i < length base)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain i) (carry_full us)) i <= 2 ^ log_cap i.
  Proof.
    induction i; intros; try omega.
    simpl.
    unfold carry, carry_simple; break_if; try omega.
    add_set_nth.
    split.
    + zero_bounds; [destruct (eq_nat_dec i 0); subst | ].
      - simpl; apply carry_full_bounds_0; auto.
      - apply IHi; auto; omega.
      - rewrite carry_sequence_unaffected by carry_length_conditions.
        apply carry_full_bounds; auto; omega.
    + rewrite <-max_bound_log_cap, <-Z.add_1_l.
      apply Z.add_le_mono.
      - rewrite Z.shiftr_div_pow2 by eauto using log_cap_nonneg.
        apply Z.div_floor; auto.
        destruct i.
        * simpl.
          eapply Z.le_lt_trans; [ apply carry_full_bounds_0; auto | ].
          replace (2 ^ log_cap 0 * 2) with (2 ^ log_cap 0 + 2 ^ log_cap 0) by ring.
          rewrite <-max_bound_log_cap, <-Z.add_1_l.
          apply Z.add_lt_le_mono; omega.
        * eapply Z.le_lt_trans; [ apply IHi; auto; omega | ].
          apply Z.lt_mul_diag_r; auto; omega.
      - rewrite carry_sequence_unaffected by carry_length_conditions.
        apply carry_full_bounds; auto; omega.
  Qed.

  Lemma carry_full_2_bounds_0 : forall us, pre_carry_bounds us ->
    (length us = length base)%nat -> (1 < length base)%nat ->
    0 <= nth_default 0 (carry_full (carry_full us)) 0 <= max_bound 0 + c.
  Proof.
    intros.
    unfold carry_full at 1 3, full_carry_chain.
    rewrite <-base_length.
    replace (length base) with (S (pred (length base))) by (pose proof base_length_nonzero; omega).
    simpl.
    unfold carry, carry_and_reduce; break_if; try omega.
    clear_obvious; add_set_nth.
    split.
    + pose proof c_pos; zero_bounds; [ | carry_seq_lower_bound].
      apply carry_sequence_carry_full_bounds_same; auto; omega.
    + rewrite Z.add_comm.
      apply Z.add_le_mono.
      - apply carry_bounds_0_upper; carry_length_conditions.
      - etransitivity; [ | replace c with (c * 1) by ring; reflexivity ].
        apply Z.mul_le_mono_pos_l; try (pose proof c_pos; omega).
        rewrite Z.shiftr_div_pow2 by eauto.
        apply Z.div_le_upper_bound; auto.
        ring_simplify.
        apply carry_sequence_carry_full_bounds_same; auto.
        omega.
  Qed.

  Lemma carry_full_2_bounds_succ : forall us i, pre_carry_bounds us ->
    (length us = length base)%nat -> (0 < i < pred (length base))%nat ->
    ((0 < i < length base)%nat ->
      0 <= nth_default 0
        (carry_sequence (make_chain i) (carry_full (carry_full us))) i <=
      2 ^ log_cap i) ->
      0 <= nth_default 0 (carry_simple limb_widths i
        (carry_sequence (make_chain i) (carry_full (carry_full us)))) (S i) <= 2 ^ log_cap (S i).
  Proof.
    unfold carry_simple; intros ? ? PCB length_eq ? IH.
    add_set_nth.
    split.
    + zero_bounds. destruct i;
        [ simpl; pose proof (carry_full_2_bounds_0 us PCB length_eq); omega | ].
      rewrite carry_sequence_unaffected by carry_length_conditions.
      apply carry_full_bounds; carry_length_conditions.
      carry_seq_lower_bound.
    + rewrite <-max_bound_log_cap, <-Z.add_1_l.
      rewrite Z.shiftr_div_pow2 by eauto using log_cap_nonneg.
      apply Z.add_le_mono.
      - apply Z.div_le_upper_bound; auto.
        ring_simplify. apply IH. omega.
      - rewrite carry_sequence_unaffected by carry_length_conditions.
        apply carry_full_bounds; carry_length_conditions.
        carry_seq_lower_bound.
  Qed.

  Lemma carry_full_2_bounds_same : forall us i, pre_carry_bounds us ->
    (length us = length base)%nat -> (0 < i < length base)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain i) (carry_full (carry_full us))) i <= 2 ^ log_cap i.
  Proof.
    intros; induction i; try omega.
    simpl; unfold carry.
    break_if; try omega.
    split; (destruct (eq_nat_dec i 0); subst;
      [ cbv [make_chain carry_sequence fold_right carry_simple]; add_set_nth
      | eapply carry_full_2_bounds_succ; eauto; omega]).
    + zero_bounds.
      - eapply carry_full_2_bounds_0; eauto.
      - eapply carry_full_bounds; eauto; carry_length_conditions.
        carry_seq_lower_bound.
    + rewrite <-max_bound_log_cap, <-Z.add_1_l.
      rewrite Z.shiftr_div_pow2 by eauto using log_cap_nonneg.
      apply Z.add_le_mono.
      - apply Z.div_floor; auto.
        eapply Z.le_lt_trans; [ eapply carry_full_2_bounds_0; eauto | ].
        replace (Z.succ 1) with (2 ^ 1) by ring.
        rewrite <-max_bound_log_cap.
        ring_simplify. pose proof c_pos; omega.
      - apply carry_full_bounds; carry_length_conditions; carry_seq_lower_bound.
  Qed.

  Lemma carry_full_2_bounds' : forall us i j, pre_carry_bounds us ->
    (length us = length base)%nat -> (0 < i < length base)%nat -> (i + j < length base)%nat -> (j <> 0)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain (i + j)) (carry_full (carry_full us))) i <= max_bound i.
  Proof.
    induction j; intros; try omega.
    split; (destruct j; [ rewrite Nat.add_1_r; simpl
                         | rewrite <-plus_n_Sm; simpl; rewrite carry_unaffected_low by carry_length_conditions; eapply IHj; eauto; omega ]).
    + apply nth_default_carry_bound_lower; carry_length_conditions.
    + apply nth_default_carry_bound_upper; carry_length_conditions.
  Qed.

  Lemma carry_full_2_bounds : forall us i j, pre_carry_bounds us ->
    (length us = length base)%nat -> (0 < i < length base)%nat -> (i < j < length base)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain j) (carry_full (carry_full us))) i <= max_bound i.
  Proof.
    intros.
    replace j with (i + (j - i))%nat by omega.
    eapply carry_full_2_bounds'; eauto; omega.
  Qed.

  Lemma carry_carry_full_2_bounds_0_lower : forall us i, pre_carry_bounds us ->
    (length us = length base)%nat -> (0 < i < length base)%nat ->
    (0 <= nth_default 0 (carry_sequence (make_chain i) (carry_full (carry_full us))) 0).
  Proof.
    induction i; try omega.
    intros ? length_eq ?; simpl.
    destruct i.
    + unfold carry.
      break_if;
        [ pose proof base_length_nonzero; replace (length base) with 1%nat in *; omega | ].
      simpl.
      unfold carry_simple.
      add_set_nth.
      apply pow2_mod_log_cap_bounds_lower.
    + rewrite carry_unaffected_low by carry_length_conditions.
      assert (0 < S i < length base)%nat by omega.
      intuition.
  Qed.

  Lemma carry_full_2_bounds_lower :forall us i, pre_carry_bounds us ->
    (length us = length base)%nat ->
    0 <= nth_default 0 (carry_full (carry_full us)) i.
  Proof.
    intros; destruct i.
    + apply carry_full_2_bounds_0; auto.
    + apply carry_full_bounds; try solve [carry_length_conditions].
      intro j; destruct j.
      - apply carry_full_bounds_0; auto.
      - apply carry_full_bounds; carry_length_conditions.
  Qed.

  Local Hint Resolve carry_full_length.

  Lemma carry_carry_full_2_bounds_0_upper : forall us i, pre_carry_bounds us ->
    (length us = length base)%nat -> (0 < i < length base)%nat ->
    (nth_default 0 (carry_sequence (make_chain i) (carry_full (carry_full us))) 0 <= max_bound 0 - c)
    \/ carry_done (carry_sequence (make_chain i) (carry_full (carry_full us))).
  Proof.
    induction i; try omega.
    intros ? length_eq ?; simpl.
    destruct i.
    + destruct (Z_le_dec (nth_default 0 (carry_full (carry_full us)) 0) (max_bound 0)).
      - right.
        apply carry_carry_done_done; try solve [carry_length_conditions].
        apply carry_done_bounds; try solve [carry_length_conditions].
        intros.
        simpl.
        split; [ auto using carry_full_2_bounds_lower | ].
        destruct i; rewrite <-max_bound_log_cap, Z.lt_succ_r; auto.
        apply carry_full_bounds; auto using carry_full_bounds_lower.
      - left; unfold carry, carry_simple.
        break_if;
          [ pose proof base_length_nonzero; replace (length base) with 1%nat in *; omega | ].
        add_set_nth. simpl.
        remember ((nth_default 0 (carry_full (carry_full us)) 0)) as x.
        apply Z.le_trans with (m := (max_bound 0 + c) - (1 + max_bound 0)); try omega.
        replace x with ((x - 2 ^ log_cap 0) + (1 * 2 ^ log_cap 0)) by ring.
        rewrite Z.pow2_mod_spec by eauto.
        cbv [make_chain carry_sequence fold_right].
        rewrite Z.mod_add by (pose proof (pow_2_log_cap_pos 0); omega).
        rewrite <-max_bound_log_cap, <-Z.add_1_l, Z.mod_small;
          [ apply Z.sub_le_mono_r; subst; apply carry_full_2_bounds_0; auto | ].
        split; try omega.
        pose proof carry_full_2_bounds_0.
        apply Z.le_lt_trans with (m := (max_bound 0 + c) - (1 + max_bound 0));
          [ apply Z.sub_le_mono_r; subst x; apply carry_full_2_bounds_0; auto;
          ring_simplify | ]; pose proof c_pos; omega.
    + rewrite carry_unaffected_low by carry_length_conditions.
      assert (0 < S i < length base)%nat by omega.
      intuition; right.
      apply carry_carry_done_done; try solve [carry_length_conditions].
      assumption.
  Qed.


  (* END proofs about second carry loop *)

  (* BEGIN proofs about third carry loop *)

  Lemma carry_full_3_bounds : forall us i, pre_carry_bounds us ->
    (length us = length base)%nat ->(i < length base)%nat ->
    0 <= nth_default 0 (carry_full (carry_full (carry_full us))) i <= max_bound i.
  Proof.
    intros.
    destruct i; [ | apply carry_full_bounds; carry_length_conditions;
                    carry_seq_lower_bound ].
    unfold carry_full at 1 4, full_carry_chain.
    case_eq limb_widths; [intros; pose proof limb_widths_nonnil; congruence | ].
    simpl.
    intros ? ? limb_widths_eq.
    replace (length l) with (pred (length limb_widths)) by (rewrite limb_widths_eq; auto).
    rewrite <- base_length.
    unfold carry, carry_and_reduce; break_if; try omega; intros.
    add_set_nth. pose proof c_pos.
    split.
    + zero_bounds.
      - eapply carry_full_2_bounds_same; eauto; omega.
      - eapply carry_carry_full_2_bounds_0_lower; eauto; omega.
    + pose proof (carry_carry_full_2_bounds_0_upper us (pred (length base))).
      assert (0 < pred (length base) < length base)%nat by omega.
      intuition.
      - replace (max_bound 0) with (c + (max_bound 0 - c)) by ring.
        apply Z.add_le_mono; try assumption.
        etransitivity; [ | replace c with (c * 1) by ring; reflexivity ].
        apply Z.mul_le_mono_pos_l; try omega.
        rewrite Z.shiftr_div_pow2 by eauto.
        apply Z.div_le_upper_bound; auto.
        ring_simplify.
        apply carry_full_2_bounds_same; auto.
      - match goal with H0 : (pred (length base) < length base)%nat,
                        H : carry_done _ |- _ =>
          destruct (H (pred (length base)) H0) as [Hcd1 Hcd2]; rewrite Hcd2 by omega end.
        ring_simplify.
        apply shiftr_eq_0_max_bound; auto.
        assert (0 < length base)%nat as zero_lt_length by omega.
        match goal with H : carry_done _ |- _ =>
          destruct (H 0%nat zero_lt_length) end.
       assumption.
  Qed.

  Lemma carry_full_3_done : forall us, pre_carry_bounds us ->
    (length us = length base)%nat ->
    carry_done (carry_full (carry_full (carry_full us))).
  Proof.
    intros.
    apply carry_done_bounds; [ carry_length_conditions | intros ].
    destruct (lt_dec i (length base)).
    + rewrite <-max_bound_log_cap, Z.lt_succ_r.
      auto using carry_full_3_bounds.
    + rewrite nth_default_out_of_bounds; carry_length_conditions.
  Qed.

  (* END proofs about third carry loop *)

  Lemma isFull'_false : forall us n, isFull' us false n = false.
  Proof.
    unfold isFull'; induction n; intros; rewrite Bool.andb_false_r; auto.
  Qed.

  Lemma isFull'_last : forall us b j, (j <> 0)%nat -> isFull' us b j = true ->
    max_bound j = nth_default 0 us j.
  Proof.
    induction j; simpl; intros; try omega.
    match goal with
    | [H : isFull' _ ((?comp ?a ?b) && _) _ = true |- _ ]  =>
        case_eq (comp a b); rewrite ?Z.eqb_eq; intro comp_eq; try assumption;
        rewrite comp_eq, Bool.andb_false_l, isFull'_false in H; congruence
    end.
  Qed.

  Lemma isFull'_lower_bound_0 : forall j us b, isFull' us b j = true ->
    max_bound 0 - c < nth_default 0 us 0.
  Proof.
    induction j; intros.
    + match goal with H : isFull' _ _ 0 = _ |- _ => cbv [isFull'] in H;
       apply Bool.andb_true_iff in H; destruct H end.
      apply Z.ltb_lt; assumption.
    + eauto.
  Qed.

  Lemma isFull'_true_full : forall us i j b, (i <> 0)%nat -> (i <= j)%nat -> isFull' us b j = true ->
    max_bound i = nth_default 0 us i.
  Proof.
    induction j; intros; try omega.
    assert (i = S j \/ i <= j)%nat as cases by omega.
    destruct cases.
    + subst. eapply isFull'_last; eauto.
    + eapply IHj; eauto.
  Qed.

  Lemma max_ones_nonneg : 0 <= max_ones.
  Proof.
    unfold max_ones.
    apply Z.ones_nonneg.
    clear.
    pose proof limb_widths_nonneg.
    induction limb_widths as [|?? IHl].
    cbv; congruence.
    simpl.
    apply Z.max_le_iff.
    right.
    apply IHl; eauto using in_cons.
  Qed.

  Lemma land_max_ones_noop : forall x i, 0 <= x < 2 ^ log_cap i -> Z.land max_ones x = x.
  Proof.
    unfold max_ones.
    intros ? ? x_range.
    rewrite Z.land_comm.
    rewrite Z.land_ones by apply Z.le_fold_right_max_initial.
    apply Z.mod_small.
    split; try omega.
    eapply Z.lt_le_trans; try eapply x_range.
    apply Z.pow_le_mono_r; try omega.
    destruct (lt_dec i (length limb_widths)).
    + apply Z.le_fold_right_max.
      - apply limb_widths_nonneg.
      - rewrite nth_default_eq.
        auto using nth_In.
    + rewrite nth_default_out_of_bounds by omega.
      apply Z.le_fold_right_max_initial.
  Qed.

  Lemma full_isFull'_true : forall j us, (length us = length base) ->
    ( max_bound 0 - c < nth_default 0 us 0
    /\ (forall i, (0 < i <= j)%nat -> nth_default 0 us i = max_bound i)) ->
    isFull' us true j = true.
  Proof.
    induction j; intros.
    + cbv [isFull']; apply Bool.andb_true_iff.
      rewrite Z.ltb_lt; intuition.
    + intuition.
      simpl.
      match goal with H : forall j, _ -> ?b j = ?a j |- appcontext[?a ?i =? ?b ?i] =>
        replace (a i =? b i) with true  by (symmetry; apply Z.eqb_eq; symmetry; apply H; omega) end.
      apply IHj; auto; intuition.
  Qed.

  Lemma isFull'_true_iff : forall j us, (length us = length base) -> (isFull' us true j = true <->
    max_bound 0 - c < nth_default 0 us 0
    /\ (forall i, (0 < i <= j)%nat -> nth_default 0 us i = max_bound i)).
  Proof.
    intros; split; intros; auto using full_isFull'_true.
    split; eauto using isFull'_lower_bound_0.
    intros.
    symmetry; eapply isFull'_true_full; [ omega | | eauto].
    omega.
  Qed.

  Lemma isFull'_true_step : forall us j, isFull' us true (S j) = true ->
    isFull' us true j = true.
  Proof.
    simpl; intros ? ? succ_true.
    destruct (max_bound (S j) =? nth_default 0 us (S j)); auto.
    rewrite isFull'_false in succ_true.
    congruence.
  Qed.

  Opaque isFull' max_ones.

  Lemma carry_full_3_length : forall us, (length us = length base) ->
    length (carry_full (carry_full (carry_full us))) = length us.
  Proof.
    intros.
    repeat rewrite carry_full_length by (repeat rewrite carry_full_length; auto); auto.
  Qed.
  Local Hint Resolve carry_full_3_length.

  Lemma modulus_digits'_length : forall i, length (modulus_digits' i) = S i.
  Proof.
    induction i; intros; [ cbv; congruence | ].
    unfold modulus_digits'; fold modulus_digits'.
    rewrite app_length, IHi.
    cbv [length]; omega.
  Qed.

  Lemma modulus_digits_length : length modulus_digits = length base.
  Proof.
    unfold modulus_digits.
    rewrite modulus_digits'_length; omega.
  Qed.

  (* Helps with solving goals of the form [x = y -> min x y = x] or [x = y -> min x y = y] *)
  Local Hint Resolve Nat.eq_le_incl eq_le_incl_rev.

  Hint Rewrite app_length cons_length map2_length modulus_digits_length length_zeros
               map_length combine_length firstn_length map_app : lengths.
  Ltac simpl_lengths := autorewrite with lengths;
    repeat rewrite carry_full_length by (repeat rewrite carry_full_length; auto);
    auto using Min.min_l; auto using Min.min_r.

  Lemma freeze_length : forall us, (length us = length base) ->
    length (freeze us) = length us.
  Proof.
    unfold freeze; intros; simpl_lengths.
    rewrite Min.min_l by omega. congruence.
  Qed.

  Lemma decode_firstn_succ : forall n us, (length us = length base) ->
   (n < length base)%nat ->
   BaseSystem.decode' (firstn (S n) base) (firstn (S n) us) =
   BaseSystem.decode' (firstn n base) (firstn n us) +
     nth_default 0 base n * nth_default 0 us n.
  Proof.
    intros.
    rewrite !firstn_succ with (d := 0) by omega.
    rewrite base_app, firstn_app.
    autorewrite with lengths; rewrite !Min.min_l by omega.
    rewrite Nat.sub_diag, firstn_firstn, firstn0, app_nil_r by omega.
    rewrite skipn_app_sharp by (autorewrite with lengths; apply Min.min_l; omega).
    rewrite decode'_cons, decode_nil, Z.add_0_r.
    reflexivity.
  Qed.

  Local Hint Resolve sum_firstn_limb_widths_nonneg.
  Local Hint Resolve limb_widths_nonneg.
  Local Hint Resolve nth_error_value_In.

  Lemma decode_carry_done_upper_bound' : forall n us, carry_done us ->
    (length us = length base) ->
    BaseSystem.decode (firstn n base) (firstn n us) < 2 ^ (sum_firstn limb_widths n).
  Proof.
    induction n; intros; [ cbv; congruence | ].
    destruct (lt_dec n (length base)) as [ n_lt_length | ? ].
    + rewrite decode_firstn_succ; auto.
      rewrite base_length in n_lt_length.
      destruct (nth_error_length_exists_value _ _ n_lt_length).
      erewrite sum_firstn_succ; eauto.
      rewrite Z.pow_add_r; eauto.
      rewrite nth_default_base by
        (try rewrite base_from_limb_widths_length; omega || eauto).
      rewrite Z.lt_add_lt_sub_r.
      eapply Z.lt_le_trans; eauto.
      rewrite Z.mul_comm at 1.
      rewrite <-Z.mul_sub_distr_l.
      rewrite <-Z.mul_1_r at 1.
      apply Z.mul_le_mono_nonneg_l; [ apply Z.pow_nonneg; omega | ].
      replace 1 with (Z.succ 0) by reflexivity.
      rewrite Z.le_succ_l, Z.lt_0_sub.
      match goal with H : carry_done us |- _ => rewrite carry_done_bounds in H by auto; specialize (H n) end.
      replace x with (log_cap n); try intuition.
      apply nth_error_value_eq_nth_default; auto.
    + repeat erewrite firstn_all_strong by omega.
      rewrite sum_firstn_all_succ by (rewrite <-base_length; omega).
      eapply Z.le_lt_trans; [ | eauto].
      repeat erewrite firstn_all_strong by omega.
      omega.
  Qed.

  Lemma decode_carry_done_upper_bound : forall us, carry_done us ->
    (length us = length base) -> BaseSystem.decode base us < 2 ^ k.
  Proof.
    unfold k; intros.
    rewrite <-(firstn_all_strong base (length limb_widths)) by (rewrite <-base_length; auto).
    rewrite <-(firstn_all_strong us   (length limb_widths)) by (rewrite <-base_length; auto).
    auto using decode_carry_done_upper_bound'.
  Qed.

  Lemma decode_carry_done_lower_bound' : forall n us, carry_done us ->
    (length us = length base) ->
    0 <= BaseSystem.decode (firstn n base) (firstn n us).
  Proof.
    induction n; intros; [ cbv; congruence | ].
    destruct (lt_dec n (length base)) as [ n_lt_length | ? ].
    + rewrite decode_firstn_succ by auto.
      zero_bounds.
      - rewrite nth_default_base by (omega || eauto).
        apply Z.pow_nonneg; omega.
      - match goal with H : carry_done us |- _ => rewrite carry_done_bounds in H by auto; specialize (H n) end.
        intuition.
    + eapply Z.le_trans; [ apply IHn; eauto | ].
      repeat rewrite firstn_all_strong by omega.
      omega.
  Qed.

  Lemma decode_carry_done_lower_bound : forall us, carry_done us ->
    (length us = length base) -> 0 <= BaseSystem.decode base us.
  Proof.
    intros.
    rewrite <-(firstn_all_strong base (length limb_widths)) by (rewrite <-base_length; auto).
    rewrite <-(firstn_all_strong us   (length limb_widths)) by (rewrite <-base_length; auto).
    auto using decode_carry_done_lower_bound'.
  Qed.


  Lemma nth_default_modulus_digits' : forall d j i,
    nth_default d (modulus_digits' j) i =
      if lt_dec i (S j)
      then (if (eq_nat_dec i 0) then max_bound i - c + 1 else max_bound i)
      else d.
  Proof.
    induction j; intros; (break_if; [| apply nth_default_out_of_bounds; rewrite modulus_digits'_length; omega]).
    + replace i with 0%nat by omega.
      apply nth_default_cons.
    + simpl. rewrite nth_default_app.
      rewrite modulus_digits'_length.
      break_if.
      - rewrite IHj; break_if; try omega; reflexivity.
      - replace i with (S j) by omega.
        rewrite Nat.sub_diag, nth_default_cons.
        reflexivity.
  Qed.

  Lemma nth_default_modulus_digits : forall d i,
    nth_default d modulus_digits i =
      if lt_dec i (length base)
      then (if (eq_nat_dec i 0) then max_bound i - c + 1 else max_bound i)
      else d.
  Proof.
    unfold modulus_digits; intros.
    rewrite nth_default_modulus_digits'.
    replace (S (length base - 1)) with (length base) by omega.
    reflexivity.
  Qed.

  Lemma carry_done_modulus_digits : carry_done modulus_digits.
  Proof.
    apply carry_done_bounds; [apply modulus_digits_length | ].
    intros.
    rewrite nth_default_modulus_digits.
    break_if; [ | split; auto; omega].
    break_if; subst; split; auto; try rewrite <- max_bound_log_cap; pose proof c_pos; omega.
  Qed.
  Local Hint Resolve carry_done_modulus_digits.

  Lemma decode_mod : forall us vs x, (length us = length base) -> (length vs = length base) ->
    decode us = x ->
    BaseSystem.decode base us mod modulus = BaseSystem.decode base vs mod modulus ->
    decode vs = x.
  Proof.
    unfold decode; intros until 2; intros decode_us_x BSdecode_eq.
    rewrite ZToField_mod in decode_us_x |- *.
    rewrite <-BSdecode_eq.
    assumption.
  Qed.

  Lemma decode_map2_sub : forall us vs,
    (length us = length vs) ->
    BaseSystem.decode' base (map2 (fun x y => x - y) us vs)
    = BaseSystem.decode' base us - BaseSystem.decode' base vs.
  Proof.
    induction us using rev_ind; induction vs using rev_ind;
      intros; autorewrite with lengths in *; simpl_list_lengths;
      rewrite ?decode_nil; try omega.
    rewrite map2_app by omega.
    rewrite map2_cons, map2_nil_l.
    rewrite !set_higher.
    autorewrite with lengths.
    rewrite Min.min_l by omega.
    rewrite IHus by omega.
    replace (length vs) with (length us) by omega.
    ring.
  Qed.

  Lemma decode_modulus_digits' : forall i, (i <= length base)%nat ->
    BaseSystem.decode' base (modulus_digits' i) = 2 ^ (sum_firstn limb_widths (S i)) - c.
  Proof.
    induction i; intros; unfold modulus_digits'; fold modulus_digits'.
    + let base := constr:(base) in
      case_eq base;
        [ intro base_eq; rewrite base_eq, (@nil_length0 Z) in lt_1_length_base; omega | ].
      intros z ? base_eq.
      rewrite decode'_cons, decode_nil, Z.add_0_r.
      replace z with (nth_default 0 base 0) by (rewrite base_eq; auto).
      rewrite nth_default_base by (omega || eauto).
      replace (max_bound 0 - c + 1) with (Z.succ (max_bound 0) - c) by ring.
      rewrite max_bound_log_cap.
      rewrite sum_firstn_succ with (x := log_cap 0) by (
        apply nth_error_Some_nth_default; rewrite <-base_length; omega).
      rewrite Z.pow_add_r by eauto.
      cbv [sum_firstn fold_right firstn].
      ring.
    + assert (S i < length base \/ S i = length base)%nat as cases by omega.
      destruct cases.
      - rewrite sum_firstn_succ with (x := log_cap (S i)) by
          (apply nth_error_Some_nth_default;
          rewrite <-base_length; omega).
        rewrite Z.pow_add_r, <-max_bound_log_cap, set_higher by eauto.
        rewrite IHi, modulus_digits'_length by omega.
        rewrite nth_default_base by (omega || eauto).
        ring.
      - rewrite sum_firstn_all_succ by (rewrite <-base_length; omega).
        rewrite decode'_splice, modulus_digits'_length, firstn_all by auto.
        rewrite skipn_all, decode_base_nil, Z.add_0_r by omega.
        apply IHi.
        omega.
  Qed.

  Lemma decode_modulus_digits : BaseSystem.decode' base modulus_digits = modulus.
  Proof.
    unfold modulus_digits; rewrite decode_modulus_digits' by omega.
    replace (S (length base - 1)) with (length base) by omega.
    rewrite base_length.
    fold k. unfold c.
    ring.
  Qed.

  Lemma map_land_max_ones_modulus_digits' : forall i,
    map (Z.land max_ones) (modulus_digits' i) = (modulus_digits' i).
  Proof.
    induction i; intros.
    + cbv [modulus_digits' map].
      f_equal.
      apply land_max_ones_noop with (i := 0%nat).
      rewrite <-max_bound_log_cap.
      pose proof c_pos; omega.
    + unfold modulus_digits'; fold modulus_digits'.
      rewrite map_app.
      f_equal; [ apply IHi; omega | ].
      cbv [map]; f_equal.
      apply land_max_ones_noop with (i := S i).
      rewrite <-max_bound_log_cap.
      split; auto; omega.
  Qed.

  Lemma map_land_max_ones_modulus_digits : map (Z.land max_ones) modulus_digits = modulus_digits.
  Proof.
    apply map_land_max_ones_modulus_digits'.
  Qed.

  Opaque modulus_digits.

  Lemma map_land_zero : forall ls, map (Z.land 0) ls = BaseSystem.zeros (length ls).
  Proof.
    induction ls; boring.
  Qed.

  Lemma carry_full_preserves_Fdecode : forall us x, (length us = length base) ->
    decode us = x -> decode (carry_full us) = x.
  Proof.
    intros.
    apply carry_full_preserves_rep; auto.
    unfold rep; auto.
  Qed.

  Lemma freeze_preserves_rep : forall us x, rep us x -> rep (freeze us) x.
  Proof.
    unfold rep; intros.
    intuition; rewrite ?freeze_length; auto.
    unfold freeze, and_term.
    break_if.
    + apply decode_mod with (us := carry_full (carry_full (carry_full us))).
      - rewrite carry_full_3_length; auto.
      - autorewrite with lengths.
        apply Min.min_r.
        simpl_lengths; omega.
      - repeat apply carry_full_preserves_rep; repeat rewrite carry_full_length; auto.
        unfold rep; intuition.
      - rewrite decode_map2_sub by (simpl_lengths; omega).
        rewrite map_land_max_ones_modulus_digits.
        rewrite decode_modulus_digits.
        destruct (Z_eq_dec modulus 0); [ subst; rewrite !Zmod_0_r; reflexivity | ].
        rewrite <-Z.add_opp_r.
        replace (-modulus) with (-1 * modulus) by ring.
        symmetry; auto using Z.mod_add.
    + eapply decode_mod; eauto.
      simpl_lengths.
      rewrite map_land_zero, decode_map2_sub, zeros_rep, Z.sub_0_r by simpl_lengths.
      match goal with H : decode ?us = ?x |- _ => erewrite Fdecode_decode_mod; eauto;
        do 3 apply carry_full_preserves_Fdecode in H; simpl_lengths
      end.
      erewrite Fdecode_decode_mod; eauto; simpl_lengths.
  Qed.
  Hint Resolve freeze_preserves_rep.

  Lemma isFull_true_iff : forall us, (length us = length base) -> (isFull us = true <->
    max_bound 0 - c < nth_default 0 us 0
    /\ (forall i, (0 < i <= length base - 1)%nat -> nth_default 0 us i = max_bound i)).
  Proof.
    unfold isFull; intros; auto using isFull'_true_iff.
  Qed.

  Definition minimal_rep us := BaseSystem.decode base us = (BaseSystem.decode base us) mod modulus.

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

  Lemma compare'_Eq : forall us vs i, (length us = length vs) ->
    compare' us vs i = Eq -> firstn i us = firstn i vs.
  Proof.
    induction i; intros; [ cbv; congruence | ].
    destruct (lt_dec i (length us)).
    + repeat rewrite firstn_succ with (d := 0) by omega.
      match goal with H : compare' _ _ (S _) = Eq |- _ =>
        inversion H end.
      break_if; f_equal; auto.
      - f_equal; auto.
      - rewrite Z.compare_eq_iff in *. congruence.
      - rewrite Z.compare_eq_iff in *. congruence.
    + rewrite !firstn_all_strong in IHi by omega.
      match goal with H : compare' _ _ (S _) = Eq |- _ =>
        inversion H end.
      rewrite (nth_default_out_of_bounds i us) in * by omega.
      rewrite (nth_default_out_of_bounds i vs) in * by omega.
      break_if; try congruence.
      f_equal; auto.
  Qed.

  Lemma compare_Eq : forall us vs, (length us = length vs) ->
    compare us vs = Eq -> us = vs.
  Proof.
    intros.
    erewrite <-(firstn_all _ us); eauto.
    erewrite <-(firstn_all _ vs); eauto.
    apply compare'_Eq; auto.
  Qed.

  Lemma decode_lt_next_digit : forall us n, (length us = length base) ->
    (n < length base)%nat -> (n < length us)%nat ->
    carry_done us ->
    BaseSystem.decode' (firstn n base) (firstn n us) <
      (nth_default 0 base n).
  Proof.
    induction n; intros ? ? ? bounded.
    + cbv [firstn].
      rewrite decode_base_nil.
      apply Z.gt_lt; auto using nth_default_base_positive.
    + rewrite decode_firstn_succ by (auto || omega).
      rewrite nth_default_base_succ by (eauto || omega).
      eapply Z.lt_le_trans.
      - apply Z.add_lt_mono_r.
        apply IHn; auto; omega.
      - rewrite <-(Z.mul_1_r (nth_default 0 base n)) at 1.
        rewrite <-Z.mul_add_distr_l, Z.mul_comm.
        apply Z.mul_le_mono_pos_r.
        * apply Z.gt_lt. apply nth_default_base_positive; omega.
        * rewrite Z.add_1_l.
          apply Z.le_succ_l.
          rewrite carry_done_bounds in bounded by assumption.
          apply bounded.
  Qed.

  Lemma highest_digit_determines : forall us vs n x, (x < 0) ->
    (length us = length base) ->
    (length vs = length base) ->
    (n < length us)%nat -> carry_done us ->
    (n < length vs)%nat -> carry_done vs ->
    BaseSystem.decode (firstn n base) (firstn n us) +
    nth_default 0 base n * x -
    BaseSystem.decode (firstn n base) (firstn n vs) < 0.
  Proof.
    intros.
    eapply Z.le_lt_trans.
    + apply Z.le_sub_nonneg.
      apply decode_carry_done_lower_bound'; auto.
    + eapply Z.le_lt_trans.
      - eapply Z.add_le_mono with (q := nth_default 0 base n * -1); [ apply Z.le_refl | ].
        apply Z.mul_le_mono_nonneg_l; try omega.
        rewrite nth_default_base by (omega || eauto).
        zero_bounds.
      - ring_simplify.
        apply Z.lt_sub_0.
        apply decode_lt_next_digit; auto.
        omega.
  Qed.

  Lemma Z_compare_decode_step_eq : forall n us vs,
    (length us = length base) ->
    (length us = length vs) ->
    (S n <= length base)%nat ->
    (nth_default 0 us n = nth_default 0 vs n) ->
    (BaseSystem.decode (firstn (S n) base) us ?=
     BaseSystem.decode (firstn (S n) base) vs) =
     (BaseSystem.decode (firstn n base) us ?=
     BaseSystem.decode (firstn n base) vs).
  Proof.
    intros until 3; intro nth_default_eq.
    destruct (lt_dec n (length us)); try omega.
    rewrite firstn_succ with (d := 0), !base_app by omega.
    autorewrite with lengths; rewrite Min.min_l by omega.
    do 2 (rewrite skipn_nth_default with (d := 0) by omega;
      rewrite decode'_cons, decode_base_nil, Z.add_0_r).
    rewrite Z.compare_sub, nth_default_eq, Z.add_add_simpl_r_r.
    rewrite BaseSystem.decode'_truncate with (us := us).
    rewrite BaseSystem.decode'_truncate with (us := vs).
    rewrite firstn_length, Min.min_l, <-Z.compare_sub by omega.
    reflexivity.
  Qed.

  Lemma Z_compare_decode_step_lt : forall n us vs,
    (length us = length base) ->
    (length us = length vs) ->
    (S n <= length base)%nat ->
    carry_done us -> carry_done vs ->
    (nth_default 0 us n < nth_default 0 vs n) ->
    (BaseSystem.decode (firstn (S n) base) us ?=
     BaseSystem.decode (firstn (S n) base) vs) = Lt.
  Proof.
    intros until 5; intro nth_default_lt.
    destruct (lt_dec n (length us)).
    + rewrite firstn_succ with (d := 0) by omega.
      rewrite !base_app.
      autorewrite with lengths; rewrite Min.min_l by omega.
      do 2 (rewrite skipn_nth_default with (d := 0) by omega;
        rewrite decode'_cons, decode_base_nil, Z.add_0_r).
      rewrite Z.compare_sub.
      apply Z.compare_lt_iff.
      ring_simplify.
      rewrite <-Z.add_sub_assoc.
      rewrite <-Z.mul_sub_distr_l.
      apply highest_digit_determines; auto; omega.
    + rewrite !nth_default_out_of_bounds in nth_default_lt; omega.
  Qed.

  Lemma Z_compare_decode_step_neq : forall n us vs,
    (length us = length base) -> (length us = length vs) ->
    (S n <= length base)%nat ->
    carry_done us -> carry_done vs ->
    (nth_default 0 us n <> nth_default 0 vs n) ->
    (BaseSystem.decode (firstn (S n) base) us ?=
     BaseSystem.decode (firstn (S n) base) vs) =
    (nth_default 0 us n ?= nth_default 0 vs n).
  Proof.
    intros.
    destruct (Z_dec (nth_default 0 us n) (nth_default 0 vs n)) as [[?|Hgt]|?]; try congruence.
    + etransitivity; try apply Z_compare_decode_step_lt; auto.
    + match goal with |- (?a ?= ?b) = (?c ?= ?d) =>
        rewrite (Z.compare_antisym b a); rewrite (Z.compare_antisym d c) end.
      apply CompOpp_inj; rewrite !CompOpp_involutive.
      apply Z.gt_lt_iff in Hgt.
      etransitivity; try apply Z_compare_decode_step_lt; auto; omega.
  Qed.

  Lemma decode_compare' : forall n us vs,
    (length us = length base) ->
    (length us = length vs) ->
    (n <= length base)%nat ->
    carry_done us -> carry_done vs ->
    (BaseSystem.decode (firstn n base) us ?= BaseSystem.decode (firstn n base) vs)
    = compare' us vs n.
  Proof.
    induction n; intros.
    + cbv [firstn compare']; rewrite !decode_base_nil; auto.
    + unfold compare'; fold compare'.
      break_if.
      - rewrite Z_compare_decode_step_eq by (auto || omega).
        apply IHn; auto; omega.
      - rewrite Z_compare_decode_step_neq; (auto || omega).
  Qed.

  Lemma decode_compare : forall us vs,
    (length us = length base) -> carry_done us ->
    (length vs = length base) -> carry_done vs ->
    Z.compare (BaseSystem.decode base us) (BaseSystem.decode base vs) = compare us vs.
  Proof.
    unfold compare; intros.
    erewrite <-(firstn_all _ base).
    + apply decode_compare'; auto; omega.
    + assumption.
  Qed.

  Lemma compare'_succ : forall us j vs, compare' us vs (S j) =
    if Z.eq_dec (nth_default 0 us j) (nth_default 0 vs j)
    then compare' us vs j
    else nth_default 0 us j ?= nth_default 0 vs j.
  Proof.
    reflexivity.
  Qed.

  Lemma compare'_firstn_r_small_index : forall us j vs, (j <= length vs)%nat ->
    compare' us vs j = compare' us (firstn j vs) j.
  Proof.
    induction j; intros; auto.
    rewrite !compare'_succ by omega.
    rewrite firstn_succ with (d := 0) by omega.
    rewrite nth_default_app.
    simpl_lengths.
    rewrite Min.min_l by omega.
    destruct (lt_dec j j); try omega.
    rewrite Nat.sub_diag.
    rewrite nth_default_cons.
    break_if; try reflexivity.
    rewrite IHj with (vs := firstn j vs ++ nth_default 0 vs j :: nil) by
      (autorewrite with lengths; rewrite Min.min_l; omega).
    rewrite firstn_app_sharp by (autorewrite with lengths; apply Min.min_l; omega).
    apply IHj; omega.
  Qed.

  Lemma compare'_firstn_r : forall us j vs,
    compare' us vs j = compare' us (firstn j vs) j.
  Proof.
    intros.
    destruct (le_dec j (length vs)).
    + auto using compare'_firstn_r_small_index.
    + f_equal. symmetry.
      apply firstn_all_strong.
      omega.
  Qed.

  Lemma compare'_not_Lt : forall us vs j, j <> 0%nat ->
    (forall i, (0 < i < j)%nat -> 0 <= nth_default 0 us i <= nth_default 0 vs i) ->
    compare' us vs j <> Lt ->
    nth_default 0 vs 0 <= nth_default 0 us 0 /\
    (forall i : nat, (0 < i < j)%nat -> nth_default 0 us i = nth_default 0 vs i).
  Proof.
    induction j; try congruence.
    rewrite compare'_succ.
    intros; destruct (eq_nat_dec j 0).
    + break_if; subst; split; intros; try omega.
      rewrite Z.compare_ge_iff in *; omega.
    + break_if.
      - split; intros; [ | destruct (eq_nat_dec i j); subst; auto ];
        apply IHj; auto; intros; try omega;
        match goal with H : forall i, _ -> 0 <= ?f i <= ?g i |- 0 <= ?f _ <= ?g _ =>
          apply H; omega end.
      - exfalso. rewrite Z.compare_ge_iff in *.
        match goal with H : forall i, ?P -> 0 <= ?f i <= ?g i |- _ =>
          specialize (H j) end; omega.
  Qed.

  Lemma isFull'_compare' : forall us j, j <> 0%nat -> (length us = length base) ->
    (j <= length base)%nat -> carry_done us ->
    (isFull' us true (j - 1) = true <-> compare' us modulus_digits j <> Lt).
  Proof.
    unfold compare; induction j; intros; try congruence.
    replace (S j - 1)%nat with j by omega.
    split; intros.
    + simpl.
      break_if; [destruct (eq_nat_dec j 0) | ].
      - subst. cbv; congruence.
      - apply IHj; auto; try omega.
        apply isFull'_true_step.
        replace (S (j - 1)) with j by omega; auto.
      - rewrite nth_default_modulus_digits in *.
        repeat (break_if; try omega).
        * subst.
          match goal with H : isFull' _ _ _ = true |- _ =>
            apply isFull'_lower_bound_0 in H end.
          apply Z.compare_ge_iff.
          omega.
        * match goal with H : isFull' _ _ _ = true |- _ =>
            apply isFull'_true_iff in H; try assumption; destruct H as [? eq_max_bound] end.
          specialize (eq_max_bound j).
          omega.
    + apply isFull'_true_iff; try assumption.
      match goal with H : compare' _ _ _ <> Lt |- _ => apply compare'_not_Lt in H; [ destruct H as [Hdigit0 Hnonzero] | | ] end.
      - split; [ | intros i i_range; assert (0 < i < S j)%nat as  i_range' by omega;
                   specialize (Hnonzero  i i_range')];
        rewrite nth_default_modulus_digits in *;
        repeat (break_if; try omega).
      - congruence.
      - intros.
        rewrite nth_default_modulus_digits.
        repeat (break_if; try omega).
        rewrite <-Z.lt_succ_r with (m := max_bound i).
        rewrite max_bound_log_cap; apply carry_done_bounds; assumption.
  Qed.

  Lemma isFull_compare : forall us, (length us = length base) -> carry_done us ->
    (isFull us = true <-> compare us modulus_digits <> Lt).
  Proof.
    unfold compare, isFull; intros ? lengths_eq. intros.
    rewrite lengths_eq.
    apply isFull'_compare'; try omega.
    assumption.
  Qed.

  Lemma isFull_decode :  forall us, (length us = length base) -> carry_done us ->
    (isFull us = true <->
      (BaseSystem.decode base us ?= BaseSystem.decode base modulus_digits <> Lt)).
  Proof.
    intros.
    rewrite decode_compare; autorewrite with lengths; auto.
    apply isFull_compare; auto.
  Qed.

  Lemma isFull_false_upper_bound : forall us, (length us = length base) ->
    carry_done us -> isFull us = false ->
    BaseSystem.decode base us < modulus.
  Proof.
    intros.
    destruct (Z_lt_dec (BaseSystem.decode base us) modulus) as [? | nlt_modulus];
      [assumption | exfalso].
    apply Z.compare_nlt_iff in nlt_modulus.
    rewrite <-decode_modulus_digits in nlt_modulus at 2.
    apply isFull_decode in nlt_modulus; try assumption; congruence.
  Qed.

  Lemma isFull_true_lower_bound : forall us, (length us = length base) ->
    carry_done us -> isFull us = true ->
    modulus <= BaseSystem.decode base us.
  Proof.
    intros.
    rewrite <-decode_modulus_digits at 1.
    apply Z.compare_ge_iff.
    apply isFull_decode; auto.
  Qed.

  Lemma freeze_in_bounds : forall us,
    pre_carry_bounds us -> (length us = length base) ->
    carry_done (freeze us).
  Proof.
    unfold freeze, and_term; intros ? PCB lengths_eq.
    rewrite carry_done_bounds by simpl_lengths; intro i.
    rewrite nth_default_map2 with (d1 := 0) (d2 := 0).
    simpl_lengths.
    break_if; [ | split; (omega || auto)].
    break_if.
    + rewrite map_land_max_ones_modulus_digits.
      apply isFull_true_iff in Heqb; [ | simpl_lengths].
      destruct Heqb as [first_digit high_digits].
      destruct (eq_nat_dec i 0).
      - subst.
        clear high_digits.
        rewrite nth_default_modulus_digits.
        repeat (break_if; try omega).
        pose proof (carry_full_3_done us PCB lengths_eq) as cf3_done.
        rewrite carry_done_bounds in cf3_done by simpl_lengths.
        specialize (cf3_done 0%nat).
        pose proof c_pos; omega.
      - assert ((0 < i <= length base - 1)%nat) as i_range by
          (simpl_lengths; apply lt_min_l in l; omega).
        specialize (high_digits i i_range).
        clear first_digit i_range.
        rewrite high_digits.
        rewrite <-max_bound_log_cap.
        rewrite nth_default_modulus_digits.
        repeat (break_if; try omega).
        * rewrite Z.sub_diag.
          split; try omega.
          apply Z.lt_succ_r; auto.
        * rewrite Z.lt_succ_r, Z.sub_0_r. split; (omega || auto).
    + rewrite map_land_zero, nth_default_zeros.
      rewrite Z.sub_0_r.
      apply carry_done_bounds; [ simpl_lengths | ].
      auto using carry_full_3_done.
  Qed.
  Local Hint Resolve freeze_in_bounds.

  Local Hint Resolve carry_full_3_done.

  Lemma freeze_minimal_rep : forall us, pre_carry_bounds us -> (length us = length base) ->
    minimal_rep (freeze us).
  Proof.
    unfold minimal_rep, freeze, and_term.
    intros.
    symmetry. apply Z.mod_small.
    split; break_if; rewrite decode_map2_sub; simpl_lengths.
    + rewrite map_land_max_ones_modulus_digits, decode_modulus_digits.
      apply Z.le_0_sub.
      apply isFull_true_lower_bound; simpl_lengths.
    + rewrite map_land_zero, zeros_rep, Z.sub_0_r.
      apply decode_carry_done_lower_bound; simpl_lengths.
    + rewrite map_land_max_ones_modulus_digits, decode_modulus_digits.
      rewrite Z.lt_sub_lt_add_r.
      apply Z.lt_le_trans with (m := 2 * modulus); try omega.
      eapply Z.lt_le_trans; [ | apply two_pow_k_le_2modulus ].
      apply decode_carry_done_upper_bound; simpl_lengths.
    + rewrite map_land_zero, zeros_rep, Z.sub_0_r.
      apply isFull_false_upper_bound; simpl_lengths.
  Qed.
  Local Hint Resolve freeze_minimal_rep.

  Lemma rep_decode_mod : forall us vs x, rep us x -> rep vs x ->
    (BaseSystem.decode base us) mod modulus = (BaseSystem.decode base vs) mod modulus.
  Proof.
    unfold rep, decode; intros.
    intuition.
    repeat rewrite <-FieldToZ_ZToField.
    congruence.
  Qed.

  Lemma minimal_rep_unique : forall us vs x,
    rep us x -> minimal_rep us -> carry_done us ->
    rep vs x -> minimal_rep vs -> carry_done vs ->
    us = vs.
  Proof.
   intros.
   match goal with Hrep1 : rep _ ?x, Hrep2 : rep _ ?x |- _ =>
     pose proof (rep_decode_mod _ _ _ Hrep1 Hrep2) as eqmod end.
   repeat match goal with Hmin : minimal_rep ?us |- _ => unfold minimal_rep in Hmin;
     rewrite <- Hmin in eqmod; clear Hmin end.
   apply Z.compare_eq_iff in eqmod.
   rewrite decode_compare in eqmod; unfold rep in *; auto; intuition; try congruence.
   apply compare_Eq; auto.
   congruence.
  Qed.

  Lemma freeze_canonical : forall us vs x,
    pre_carry_bounds us -> rep us x ->
    pre_carry_bounds vs -> rep vs x ->
    freeze us = freeze vs.
  Proof.
    intros.
    assert (length us = length base) by (unfold rep in *; intuition).
    assert (length vs = length base) by (unfold rep in *; intuition).
    eapply minimal_rep_unique; eauto; rewrite freeze_length; assumption.
  Qed.

End CanonicalizationProofs.
