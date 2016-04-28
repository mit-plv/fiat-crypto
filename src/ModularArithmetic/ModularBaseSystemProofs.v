Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import VerdiTactics.
Require Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystem Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.BaseSystemProofs Crypto.ModularArithmetic.PseudoMersenneBaseParams Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs Crypto.ModularArithmetic.ExtendedBaseVector.
Local Open Scope Z_scope.

Section PseudoMersenneProofs.
  Context `{prm :PseudoMersenneBaseParams}.

  Local Hint Unfold decode.
  Local Notation "u '~=' x" := (rep u x) (at level 70).
  Local Notation "u '.+' x" := (add u x) (at level 70).
  Local Notation "u '.*' x" := (ModularBaseSystem.mul u x) (at level 70).
  Local Hint Unfold rep.

  Lemma rep_decode : forall us x, us ~= x -> decode us = x.
  Proof.
    autounfold; intuition.
  Qed.

  Lemma encode_rep : forall x : F modulus, encode x ~= x.
  Proof.
    intros. unfold encode, rep.
    split. {
      unfold encode; simpl.
      apply base_length_nonzero.
    } {
      unfold decode.
      rewrite encode_rep.
      apply ZToField_FieldToZ.
      apply bv.
    }
  Qed.

  Lemma add_rep : forall u v x y, u ~= x -> v ~= y -> BaseSystem.add u v ~= (x+y)%F.
  Proof.
    autounfold; intuition. {
      unfold add.
      rewrite add_length_le_max.
      case_max; try rewrite Max.max_r; omega.
    }
    unfold decode in *; unfold decode in *.
    rewrite add_rep.
    rewrite ZToField_add.
    subst; auto.
  Qed.

  Lemma sub_rep : forall u v x y, u ~= x -> v ~= y -> BaseSystem.sub u v ~= (x-y)%F.
  Proof.
    autounfold; intuition. {
      rewrite sub_length_le_max.
      case_max; try rewrite Max.max_r; omega.
    }
    unfold decode in *; unfold BaseSystem.decode in *.
    rewrite sub_rep.
    rewrite ZToField_sub.
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
    rewrite mod_mult_plus; auto using modulus_nonzero.
    rewrite <- Zplus_mod; auto.
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
      (length us <= length ext_base)%nat ->
      (length (reduce us) <= length base)%nat.
  Proof.
    intros.
    unfold reduce.
    remember (map (Z.mul c) (skipn (length base) us)) as high.
    remember (firstn (length base) us) as low.
    assert (length low >= length high)%nat. {
      subst. rewrite firstn_length.
      rewrite map_length.
      rewrite skipn_length.
      destruct (le_dec (length base) (length us)). {
        rewrite Min.min_l by omega.
        rewrite extended_base_length in H. omega.
      } {
        rewrite Min.min_r; omega.
      }
    }
    assert ((length low <= length base)%nat)
      by (rewrite Heqlow; rewrite firstn_length; apply Min.le_min_l).
    assert (length high <= length base)%nat 
      by (rewrite Heqhigh; rewrite map_length; rewrite skipn_length;
      rewrite extended_base_length in H; omega).
    rewrite add_trailing_zeros; auto.
    rewrite (add_same_length _ _ (length low)); auto.
    rewrite app_length.
    rewrite length_zeros; intuition.
  Qed.

  Lemma mul_rep : forall u v x y, u ~= x -> v ~= y -> u .* v ~= (x*y)%F.
  Proof.
    autounfold; unfold ModularBaseSystem.mul; intuition.
    {
      apply reduce_length.
      rewrite mul_length, extended_base_length.
      omega.
    } {
      rewrite ZToField_mod, reduce_rep, <-ZToField_mod.
      rewrite mul_rep by
        (apply ExtBaseVector || rewrite extended_base_length; omega).
      subst.
      do 2 rewrite decode_short by auto.
      apply ZToField_mul.
    }
  Qed.

  Lemma set_nth_sum : forall n x us, (n < length us)%nat ->
    BaseSystem.decode base (set_nth n x us) = 
    (x - nth_default 0 us n) * nth_default 0 base n + BaseSystem.decode base us.
  Proof.
    intros.
    unfold BaseSystem.decode.
    nth_inbounds; auto. (* TODO(andreser): nth_inbounds should do this auto*)
    unfold splice_nth.
    rewrite <- (firstn_skipn n us) at 4.
    do 2 rewrite decode'_splice.
    remember (length (firstn n us)) as n0.
    ring_simplify.
    remember (BaseSystem.decode' (firstn n0 base) (firstn n us)).
    rewrite (skipn_nth_default n us 0) by omega.
    rewrite firstn_length in Heqn0.
    rewrite Min.min_l in Heqn0 by omega; subst n0.
    destruct (le_lt_dec (length base) n). {
      rewrite nth_default_out_of_bounds by auto.
      rewrite skipn_all by omega.
      do 2 rewrite decode_base_nil.
      ring_simplify; auto.
    } {
      rewrite (skipn_nth_default n base 0) by omega.
      do 2 rewrite decode'_cons.
      ring_simplify; ring.
    }
  Qed.

  Lemma add_to_nth_sum : forall n x us, (n < length us)%nat ->
    BaseSystem.decode base (add_to_nth n x us) = 
    x * nth_default 0 base n + BaseSystem.decode base us.
  Proof.
    unfold add_to_nth; intros; rewrite set_nth_sum; try ring_simplify; auto.
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
    apply base_succ; auto.
  Qed.

End PseudoMersenneProofs.

Section CarryProofs.
  Context `{prm : PseudoMersenneBaseParams}.
  Local Notation "u '~=' x" := (rep u x) (at level 70).
  Hint Unfold log_cap.
  
  Lemma base_length_lt_pred : (pred (length base) < length base)%nat.
  Proof.
    pose proof base_length_nonzero; omega.
  Qed.
  Hint Resolve base_length_lt_pred.

  Lemma log_cap_nonneg : forall i, 0 <= log_cap i.
  Proof.
    unfold log_cap, nth_default; intros.
    case_eq (nth_error limb_widths i); intros; try omega.
    apply limb_widths_nonneg.
    eapply nth_error_value_In; eauto.
  Qed.
    
  Lemma nth_default_base_succ : forall i, (S i < length base)%nat ->
    nth_default 0 base (S i) = 2 ^ log_cap i * nth_default 0 base i.
  Proof.
    intros.
    repeat rewrite nth_default_base by omega.
    rewrite <- Z.pow_add_r by (apply log_cap_nonneg || apply sum_firstn_limb_widths_nonneg).
    destruct (NPeano.Nat.eq_dec i 0).
    + subst; f_equal.
      unfold sum_firstn, log_cap.
      destruct limb_widths; auto.
    + erewrite sum_firstn_succ; eauto.
      unfold log_cap.
      apply nth_error_Some_nth_default.
      rewrite <- base_length; omega.
  Qed.

  Lemma carry_simple_decode_eq : forall i us,
    (length us = length base) ->
    (i < (pred (length base)))%nat ->
    BaseSystem.decode base (carry_simple i us) = BaseSystem.decode base us.
  Proof.
    unfold carry_simple. intros.
    rewrite add_to_nth_sum by (rewrite length_set_nth; omega).
    rewrite set_nth_sum by omega.
    unfold pow2_mod.
    rewrite Z.land_ones by apply log_cap_nonneg.
    rewrite Z.shiftr_div_pow2 by apply log_cap_nonneg.
    rewrite nth_default_base_succ by omega.
    rewrite Z.mul_assoc.
    rewrite (Z.mul_comm _ (2 ^ log_cap i)).
    rewrite mul_div_eq; try ring.
    apply gt_lt_symmetry.
    apply Z.pow_pos_nonneg; omega || apply log_cap_nonneg.
  Qed.

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
      unfold log_cap.
      subst; rewrite length_zero, limbs_length, nth_default_nil.
      reflexivity.
    + rewrite nth_default_base by omega.
      rewrite <- Z.add_opp_l, <- Z.opp_sub_distr.
      unfold pow2_mod.
      rewrite Z.land_ones by apply log_cap_nonneg.
      rewrite <- mul_div_eq by (apply gt_lt_symmetry; apply Z.pow_pos_nonneg; omega || apply log_cap_nonneg).
      rewrite Z.shiftr_div_pow2 by apply log_cap_nonneg.
      rewrite Zopp_mult_distr_r.
      rewrite Z.mul_comm.
      rewrite Z.mul_assoc.
      rewrite <- Z.pow_add_r by (apply log_cap_nonneg || apply sum_firstn_limb_widths_nonneg).
      unfold k.
      replace (length limb_widths) with (S (pred (length base))) by
        (subst; rewrite <- base_length; apply NPeano.Nat.succ_pred; omega).
      rewrite sum_firstn_succ with (x:= log_cap (pred (length base))) by
        (unfold log_cap; apply nth_error_Some_nth_default; rewrite <- base_length; omega).
      rewrite <- Zopp_mult_distr_r.
      rewrite Z.mul_comm.
      rewrite (Z.add_comm (log_cap (pred (length base)))).
      ring.
  Qed.

  Lemma carry_length : forall i us,
    (length       us     <= length base)%nat ->
    (length (carry i us) <= length base)%nat.
  Proof.
    unfold carry, carry_simple, carry_and_reduce, add_to_nth.
    intros; break_if; subst; repeat (rewrite length_set_nth); auto.
  Qed.
  Hint Resolve carry_length.

  Lemma carry_rep : forall i us x,
    (length us = length base) ->
    (i < length base)%nat ->
    us ~= x -> carry i us ~= x.
  Proof.
    pose carry_length. pose carry_decode_eq_reduce. pose carry_simple_decode_eq.
    unfold rep, decode, carry in *; intros.
    intuition; break_if; subst; eauto;
    apply F_eq; simpl; intuition.
  Qed.
  Hint Resolve carry_rep.

  Lemma carry_sequence_length: forall is us,
    (length us <= length base)%nat ->
    (length (carry_sequence is us) <= length base)%nat.
  Proof.
    induction is; boring.
  Qed.
  Hint Resolve carry_sequence_length.

  Lemma carry_length_exact : forall i us,
    (length       us     = length base)%nat ->
    (length (carry i us) = length base)%nat.
  Proof.
    unfold carry, carry_simple, carry_and_reduce, add_to_nth.
    intros; break_if; subst; repeat (rewrite length_set_nth); auto.
  Qed.

  Lemma carry_sequence_length_exact: forall is us,
    (length us = length base)%nat ->
    (length (carry_sequence is us) = length base)%nat.
  Proof.
    induction is; boring.
    apply carry_length_exact; auto.
  Qed.
  Hint Resolve carry_sequence_length_exact.

  Lemma carry_sequence_rep : forall is us x,
    (forall i, In i is -> (i < length base)%nat) ->
    (length us = length base) ->
    us ~= x -> carry_sequence is us ~= x.
  Proof.
    induction is; boring.
  Qed.

End CarryProofs.
