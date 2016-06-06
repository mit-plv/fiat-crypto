Require Import Zpower ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
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

  Lemma sub_rep : forall c c_0modq, (length c <= length base)%nat ->
    forall u v x y, u ~= x -> v ~= y -> 
    ModularBaseSystem.sub c c_0modq u v ~= (x-y)%F.
  Proof.
    autounfold; unfold ModularBaseSystem.sub; intuition. {
      rewrite sub_length_le_max.
      case_max; try rewrite Max.max_r; try omega.
      rewrite add_length_le_max.
      case_max; try rewrite Max.max_r; omega.
    }
    unfold decode in *; unfold BaseSystem.decode in *.
    rewrite BaseSystemProofs.sub_rep, BaseSystemProofs.add_rep.
    rewrite ZToField_sub, ZToField_add, ZToField_mod.
    rewrite c_0modq, F_add_0_l.
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

Section CanonicalizationProofs.
  Context `{prm : PseudoMersenneBaseParams} (lt_1_length_base : (1 < length base)%nat) (c_pos : 0 < c) {B} (B_pos : 0 < B) (B_compat : forall w, In w limb_widths -> w <= B).

  (* TODO : move *)
  Lemma set_nth_nth_default : forall {A} (d:A) n x l i, (0 <= i < length l)%nat ->
    nth_default d (set_nth n x l) i =
    if (eq_nat_dec i n) then x else nth_default d l i.
  Proof.
    induction n; (destruct l; [intros; simpl in *; omega | ]); simpl;
      destruct i; break_if; try omega; intros; try apply nth_default_cons;
        rewrite !nth_default_cons_S, ?IHn; try break_if; omega || reflexivity.
  Qed.

  (* TODO : move *)
  Lemma add_to_nth_nth_default : forall n x l i, (0 <= i < length l)%nat ->
    nth_default 0 (add_to_nth n x l) i =
    if (eq_nat_dec i n) then x + nth_default 0 l i else nth_default 0 l i.
  Proof.
    intros.
    unfold add_to_nth.
    rewrite set_nth_nth_default by assumption.
    break_if; subst; reflexivity.
  Qed.

  (* TODO : move *)
  Lemma length_add_to_nth : forall n x l, length (add_to_nth n x l) = length l.
  Proof.
    unfold add_to_nth; intros; apply length_set_nth.
  Qed.

  (* TODO : move *)
  Lemma singleton_list : forall {A} (l : list A), length l = 1%nat -> exists x, l = x :: nil.
  Proof.
    intros; destruct l; simpl in *; try congruence.
    eexists; f_equal.
    apply length0_nil; omega.
  Qed.

  (* BEGIN groundwork proofs *)

  Lemma pow_2_log_cap_pos : forall i, 0 < 2 ^ log_cap i.
  Proof.
    intros; apply Z.pow_pos_nonneg; auto using log_cap_nonneg; omega.
  Qed.
  Local Hint Resolve pow_2_log_cap_pos.

  Lemma max_bound_log_cap : forall i, Z.succ (max_bound i) = 2 ^ log_cap i.
  Proof.
    intros.
    unfold max_bound, Z.ones.
    rewrite Z.shiftl_1_l.
    omega.
  Qed.

  Hint Resolve log_cap_nonneg.
  Lemma pow2_mod_log_cap_range : forall a i, 0 <= pow2_mod a (log_cap i) <= max_bound i.
  Proof.
    intros.
    unfold pow2_mod.
    rewrite Z.land_ones by apply log_cap_nonneg.
    unfold max_bound, Z.ones.
    rewrite Z.shiftl_1_l, <-Z.lt_le_pred.
    apply Z_mod_lt.
    pose proof (pow_2_log_cap_pos i).
    omega.
  Qed.

  Lemma pow2_mod_log_cap_bounds_lower : forall a i, 0 <= pow2_mod a (log_cap i).
  Proof.
    intros.
    pose proof (pow2_mod_log_cap_range a  i); omega.
  Qed.

  Lemma pow2_mod_log_cap_bounds_upper : forall a i, pow2_mod a (log_cap i) <= max_bound i.
  Proof.
    intros.
    pose proof (pow2_mod_log_cap_range a  i); omega.
  Qed.

  Lemma pow2_mod_log_cap_small : forall a i, 0 <= a <= max_bound i ->
    pow2_mod a (log_cap i) = a.
  Proof.
    intros.
    unfold pow2_mod.
    rewrite Z.land_ones by apply log_cap_nonneg.
    apply Z.mod_small.
    split; try omega.
    rewrite <- max_bound_log_cap.
    omega.
  Qed.

  Lemma max_bound_nonneg : forall i, 0 <= max_bound i.
  Proof.
    unfold max_bound; intros; auto using Z_ones_nonneg.
  Qed.
  Local Hint Resolve max_bound_nonneg.

  Lemma pow2_mod_spec : forall a b, (0 <= b) -> pow2_mod a b = a mod (2 ^ b).
  Proof.
    intros.
    unfold pow2_mod.
    rewrite Z.land_ones; auto.
  Qed.

  Lemma pow2_mod_upper_bound : forall a b, (0 <= a) -> (0 <= b) -> pow2_mod a b <= a.
  Proof.
    intros.
    unfold pow2_mod.
    rewrite Z.land_ones; auto.
    apply Z.mod_le; auto.
    apply Z.pow_pos_nonneg; omega.
  Qed.

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
    unfold log_cap; intros.
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

  (* END groundwork proofs *)
  Opaque pow2_mod log_cap max_bound.

  (* automation *)
  Ltac carry_length_conditions' := unfold carry_full, add_to_nth;
    rewrite ?length_set_nth, ?carry_length_exact, ?carry_sequence_length_exact, ?carry_sequence_length_exact;
    try omega; try solve [pose proof base_length; pose proof base_length_nonzero; omega || auto ].
  Ltac carry_length_conditions := try split; try omega; repeat carry_length_conditions'.

  Ltac add_set_nth := rewrite ?add_to_nth_nth_default; try solve [carry_length_conditions];
    try break_if; try omega; rewrite ?set_nth_nth_default; try solve [carry_length_conditions];
    try break_if; try omega.

  (* BEGIN defs *)

  Definition c_carry_constraint : Prop :=
    (c * (Z.ones (B - log_cap (pred (length base)))) < max_bound 0 + 1)
    /\ (max_bound 0 + c < 2 ^ (log_cap 0 + 1))
    /\ (c <= max_bound 0 - c).

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
  Hint Resolve pre_carry_bounds_nonzero.

  Definition carry_done us := forall i, (i < length base)%nat -> Z.shiftr (nth_default 0 us i) (log_cap i) = 0.

  Lemma carry_carry_done_done : forall i us,
    (length us = length base)%nat ->
    (i < length base)%nat ->
    (forall i, 0 <= nth_default 0 us i) ->
    carry_done us -> carry_done (carry i us).
  Proof.
    unfold carry_done; intros until 3. intros Hcarry_done ? ?.
    unfold carry, carry_simple, carry_and_reduce; break_if; subst.
    + rewrite Hcarry_done by omega.
      rewrite pow2_mod_log_cap_small by (intuition; auto using shiftr_eq_0_max_bound).
      destruct i0; add_set_nth; rewrite ?Z.mul_0_r, ?Z.add_0_l; auto.
      match goal with H : S _ = pred (length base) |- _ => rewrite H; auto end.
   + rewrite Hcarry_done by omega.
     rewrite pow2_mod_log_cap_small by (intuition; auto using shiftr_eq_0_max_bound).
     destruct i0; add_set_nth; subst; rewrite ?Z.add_0_l; auto.    
  Qed.

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

  Lemma nth_default_carry_bound_succ_lower : forall i us, (forall i, 0 <= nth_default 0 us i) ->
    (length us = length base) ->
    0 <= nth_default 0 (carry i us) (S i).
  Proof.
    unfold carry; intros ? ? PCB ? .
    break_if.
    + subst. replace (S (pred (length base))) with (length base) by omega.
      rewrite nth_default_out_of_bounds; carry_length_conditions.
      unfold carry_and_reduce.
      add_set_nth.
    + unfold carry_simple.
      destruct (lt_dec (S i) (length us)).
      - add_set_nth.
        apply Z.add_nonneg_nonneg; [ apply Z.shiftr_nonneg | ]; unfold pre_carry_bounds in PCB.
        * specialize (PCB i). omega.
        * specialize (PCB (S i)). omega.
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
    break_if; add_set_nth.
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

  Lemma carry_bounds_0_upper : forall us j, (length us = length base) ->
    (0 < j < length base)%nat ->
    nth_default 0 (carry_sequence (make_chain j) us) 0 <= max_bound 0.
  Proof.
    unfold carry_sequence; induction j; [simpl; intros; omega | ].
    intros.
    simpl in *.
    destruct (eq_nat_dec 0 j).
    + subst. 
      apply nth_default_carry_bound_upper; fold (carry_sequence (make_chain 0) us); carry_length_conditions.
    + rewrite carry_unaffected_low; try omega.
        fold (carry_sequence (make_chain j) us); carry_length_conditions.
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

  Lemma carry_sequence_bounds_lower : forall j i us, (length us = length base) ->
    (forall i, 0 <= nth_default 0 us i) -> (j <= length base)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain j) us) i.
  Proof.
    induction j; intros.
    + simpl. auto.
    + simpl.
      destruct (lt_dec (S j) i).
      - rewrite carry_unaffected_high by carry_length_conditions.
        apply IHj; auto; omega.
      - assert ((i = S j) \/ (i = j) \/ (i < j))%nat as cases by omega.
        destruct cases as [? | [? | ?]].
        * subst. apply nth_default_carry_bound_succ_lower; carry_length_conditions.
          intros.
          eapply IHj; auto; omega.
        * subst. apply nth_default_carry_bound_lower; carry_length_conditions.
        * destruct (eq_nat_dec j (pred (length base)));
            [ | rewrite carry_unaffected_low by carry_length_conditions; apply IHj; auto; omega ].
          subst.
          unfold carry, carry_and_reduce; break_if; try omega.
          add_set_nth; [ | apply IHj; auto; omega ].
          apply Z.add_nonneg_nonneg; [ | apply IHj; auto; omega ].
          apply Z.mul_nonneg_nonneg; try omega.
          apply Z.shiftr_nonneg.
          apply IHj; auto; omega.
  Qed.

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
      intros.
      apply carry_sequence_bounds_lower; auto; omega.
    + assert (i = j \/ i < j)%nat as cases by omega.
      destruct cases as [eq_j_i | lt_i_j]; subst;
        [apply nth_default_carry_bound_lower| rewrite carry_unaffected_low]; try omega;
        fold (carry_sequence (make_chain j) us); carry_length_conditions.
      apply carry_sequence_bounds_lower; auto; omega.
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
    split.
    + apply Z.add_nonneg_nonneg; try omega.
      apply Z.shiftr_nonneg; try omega.
    + apply Z.add_lt_mono; try omega.
      rewrite Z.shiftr_div_pow2 by apply log_cap_nonneg.
      apply Z.div_lt_upper_bound; try apply pow_2_log_cap_pos.
      rewrite <-Z.pow_add_r by (apply log_cap_nonneg || apply B_compat_log_cap).
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
      - apply carry_simple_no_overflow; carry_length_conditions.
        apply carry_sequence_bounds_lower; carry_length_conditions.
        apply carry_sequence_bounds_lower; carry_length_conditions.
        rewrite carry_sequence_unaffected; try omega.
        specialize (PCB (S i)); rewrite Nat.pred_succ in PCB.
        break_if; intuition.
      - unfold carry; break_if; try omega.
        rewrite nth_default_out_of_bounds; [ apply Z.pow_pos_nonneg; omega | ].
        subst.
        unfold carry_and_reduce.
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
    replace (length base) with (S (pred (length base))) at 1 2 by omega.
    simpl.
    unfold carry, carry_and_reduce; break_if; try omega.
    add_set_nth.
    split.
    + apply Z.add_nonneg_nonneg.
      - apply Z.mul_nonneg_nonneg; try omega.
        apply Z.shiftr_nonneg.
        apply carry_sequence_bounds_lower; auto; omega.
      - apply carry_sequence_bounds_lower; auto; omega.
    + rewrite Z.add_comm.
      apply Z.add_le_mono.
      - apply carry_bounds_0_upper; auto; omega.
      - apply Z.mul_le_mono_pos_l; auto.
        apply Z_shiftr_ones; auto;
          [ | pose proof (B_compat_log_cap (pred (length base))); omega ].
        split.
        * apply carry_bounds_lower; auto; try omega.
        * apply carry_sequence_no_overflow; auto.
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

  Lemma carry_sequence_carry_full_bounds_same : forall us i, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat -> (0 < i < length base)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain i) (carry_full us)) i <= 2 ^ log_cap i.
  Proof.
    induction i; intros; try omega.
    simpl.
    unfold carry, carry_simple; break_if; try omega.
    add_set_nth.
    split.
    + apply Z.add_nonneg_nonneg.
      - apply Z.shiftr_nonneg.
        destruct (eq_nat_dec i 0); subst.
        * simpl.
          apply carry_full_bounds_0; auto.
        * apply IHi; auto; omega.
      - rewrite carry_sequence_unaffected by carry_length_conditions.
        apply carry_full_bounds; auto; omega.
    + rewrite <-max_bound_log_cap, <-Z.add_1_l.
      apply Z.add_le_mono.
      - rewrite Z.shiftr_div_pow2 by apply log_cap_nonneg.
        apply Z_div_floor; auto.
        destruct i.
        * simpl.
          eapply Z.le_lt_trans; [ apply carry_full_bounds_0; auto | ].
          replace (2 ^ log_cap 0 * 2) with (2 ^ log_cap 0 + 2 ^ log_cap 0) by ring.
          rewrite <-max_bound_log_cap, <-Z.add_1_l.
          apply Z.add_lt_le_mono; try omega.
          unfold c_carry_constraint in *.
          intuition.
        * eapply Z.le_lt_trans; [ apply IHi; auto; omega | ].
          apply Z.lt_mul_diag_r; auto; omega. 
      - rewrite carry_sequence_unaffected by carry_length_conditions.
        apply carry_full_bounds; auto; omega.
  Qed.

  Lemma carry_full_2_bounds_0 : forall us, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat -> (1 < length base)%nat ->
    0 <= nth_default 0 (carry_full (carry_full us)) 0 <= max_bound 0 + c.
  Proof.
    intros.
    unfold carry_full at 1 3, full_carry_chain.
    rewrite <-base_length.
    replace (length base) with (S (pred (length base))) by (pose proof base_length_nonzero; omega).
    simpl.
    unfold carry, carry_and_reduce; break_if; try omega.
    add_set_nth.
    split.
    + apply Z.add_nonneg_nonneg.
      apply Z.mul_nonneg_nonneg; try omega.
      apply Z.shiftr_nonneg.
      apply carry_sequence_carry_full_bounds_same; auto; omega.
      eapply carry_sequence_bounds_lower; eauto; carry_length_conditions.
      intros.
      eapply carry_sequence_bounds_lower; eauto; carry_length_conditions.
    + rewrite Z.add_comm.
      apply Z.add_le_mono.
      - apply carry_bounds_0_upper; carry_length_conditions.
      - replace c with (c * 1) at 2 by ring.
        apply Z.mul_le_mono_pos_l; try omega.
        rewrite Z.shiftr_div_pow2 by auto.
        apply Z.div_le_upper_bound; auto.
        ring_simplify.
        apply carry_sequence_carry_full_bounds_same; auto.
        omega.
  Qed.

  Lemma carry_full_2_bounds_succ : forall us i, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat -> (0 < i < pred (length base))%nat ->
    ((0 < i < length base)%nat ->
      0 <= nth_default 0
        (carry_sequence (make_chain i) (carry_full (carry_full us))) i <=
      2 ^ log_cap i) ->
      0 <= nth_default 0 (carry_simple i
        (carry_sequence (make_chain i) (carry_full (carry_full us)))) (S i) <= 2 ^ log_cap (S i).
  Proof.
    unfold carry_simple; intros ? ? PCB CCC length_eq ? IH.
    add_set_nth.
    split.
    + apply Z.add_nonneg_nonneg.
      apply Z.shiftr_nonneg. 
      destruct i;
        [ simpl; pose proof (carry_full_2_bounds_0 us PCB CCC length_eq); omega | ].
      - assert (0 < S i < length base)%nat as IHpre by omega.
        specialize (IH IHpre).
        omega.
      - rewrite carry_sequence_unaffected by carry_length_conditions.
        apply carry_full_bounds; carry_length_conditions.
        intros.
        apply carry_sequence_bounds_lower; eauto; carry_length_conditions.
    + rewrite <-max_bound_log_cap, <-Z.add_1_l.
      rewrite Z.shiftr_div_pow2 by apply log_cap_nonneg.
      apply Z.add_le_mono.
      - apply Z.div_le_upper_bound; auto.
        ring_simplify. apply IH. omega.
      - rewrite carry_sequence_unaffected by carry_length_conditions.
        apply carry_full_bounds; carry_length_conditions.
        intros; apply carry_sequence_bounds_lower; eauto; carry_length_conditions.
  Qed.

  Lemma carry_full_2_bounds_same : forall us i, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat -> (0 < i < length base)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain i) (carry_full (carry_full us))) i <= 2 ^ log_cap i.
  Proof.
    intros; induction i; try omega.
    simpl; unfold carry.
    break_if; try omega.
    split; (destruct (eq_nat_dec i 0); subst;
      [ cbv [make_chain carry_sequence fold_right carry_simple]; add_set_nth
      | eapply carry_full_2_bounds_succ; eauto; omega]).
    + apply Z.add_nonneg_nonneg.
      apply Z.shiftr_nonneg.
      eapply carry_full_2_bounds_0; eauto.
      eapply carry_full_bounds; eauto; carry_length_conditions.
      intros; apply carry_sequence_bounds_lower; eauto; carry_length_conditions.
    + rewrite <-max_bound_log_cap, <-Z.add_1_l.
      rewrite Z.shiftr_div_pow2 by apply log_cap_nonneg.
      apply Z.add_le_mono.
      - apply Z_div_floor; auto.
        eapply Z.le_lt_trans; [ eapply carry_full_2_bounds_0; eauto | ].
        replace (Z.succ 1) with (2 ^ 1) by ring.
        rewrite <-Z.pow_add_r by (omega || auto).
        unfold c_carry_constraint in *.
        intuition.
      - apply carry_full_bounds; carry_length_conditions.
        intros; apply carry_sequence_bounds_lower; eauto; carry_length_conditions.
  Qed.

  Lemma carry_full_2_bounds' : forall us i j, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat -> (0 < i < length base)%nat -> (i + j < length base)%nat -> (j <> 0)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain (i + j)) (carry_full (carry_full us))) i <= max_bound i.
  Proof.
    induction j; intros; try omega.
    split; (destruct j; [ rewrite Nat.add_1_r; simpl 
                         | rewrite <-plus_n_Sm; simpl; rewrite carry_unaffected_low by carry_length_conditions; eapply IHj; eauto; omega ]).
    + apply nth_default_carry_bound_lower; carry_length_conditions.
    + apply nth_default_carry_bound_upper; carry_length_conditions.
  Qed.

  Lemma carry_full_2_bounds : forall us i j, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat -> (0 < i < length base)%nat -> (i < j < length base)%nat ->
    0 <= nth_default 0 (carry_sequence (make_chain j) (carry_full (carry_full us))) i <= max_bound i.
  Proof.
    intros.
    replace j with (i + (j - i))%nat by omega.
    eapply carry_full_2_bounds'; eauto; omega.
  Qed.

  Lemma carry_carry_full_2_bounds_0_lower : forall us i, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat -> (0 < i < length base)%nat ->
    (0 <= nth_default 0 (carry_sequence (make_chain i) (carry_full (carry_full us))) 0).
  Proof.
    induction i; try omega.
    intros ? ? length_eq ?; simpl.
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

  Lemma carry_full_2_bounds_lower :forall us i, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat ->
    0 <= nth_default 0 (carry_full (carry_full us)) i.
  Proof.
    intros.
    destruct i.
    + apply carry_full_2_bounds_0; auto.
    + apply carry_full_bounds; try solve [carry_length_conditions].
      intro j.
      destruct j.
      - apply carry_full_bounds_0; auto.
      - apply carry_full_bounds; carry_length_conditions.
  Qed.

  Lemma carry_carry_full_2_bounds_0_upper : forall us i, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat -> (0 < i < length base)%nat ->
    (nth_default 0 (carry_sequence (make_chain i) (carry_full (carry_full us))) 0 <= max_bound 0 - c)
    \/ carry_done (carry_sequence (make_chain i) (carry_full (carry_full us))).
  Proof.
    induction i; try omega.
    intros ? ? length_eq ?; simpl.
    destruct i.
    + destruct (Z_le_dec (nth_default 0 (carry_full (carry_full us)) 0) (max_bound 0)).
      - right.
        unfold carry_done.
        intros.
        apply max_bound_shiftr_eq_0; simpl; rewrite carry_nothing; try solve [carry_length_conditions].
        * apply carry_full_2_bounds_lower; auto.
        * split; try apply carry_full_2_bounds_lower; auto.
        * destruct i; auto.
          apply carry_full_bounds; try solve [carry_length_conditions].
          auto using carry_full_bounds_lower.
        * split; auto.
          apply carry_full_2_bounds_lower; auto.
      - unfold carry.
        break_if;
          [ pose proof base_length_nonzero; replace (length base) with 1%nat in *; omega | ].
        simpl.
        unfold carry_simple.
        add_set_nth. left.
        remember ((nth_default 0 (carry_full (carry_full us)) 0)) as x.
        apply Z.le_trans with (m := (max_bound 0 + c) - (1 + max_bound 0)).
        * replace x with ((x - 2 ^ log_cap 0) + (1 * 2 ^ log_cap 0)) by ring.
          rewrite pow2_mod_spec by auto.
          rewrite Z.mod_add by (pose proof (pow_2_log_cap_pos 0); omega).
          rewrite <-max_bound_log_cap, <-Z.add_1_l, Z.mod_small.
          apply Z.sub_le_mono_r.
          subst; apply carry_full_2_bounds_0; auto.
          split; try omega.
          pose proof carry_full_2_bounds_0.
          apply Z.le_lt_trans with (m := (max_bound 0 + c) - (1 + max_bound 0));
            [ apply Z.sub_le_mono_r; subst x; apply carry_full_2_bounds_0; auto;
            ring_simplify; unfold c_carry_constraint in *; omega | ].
          ring_simplify; unfold c_carry_constraint in *; omega.
        * ring_simplify; unfold c_carry_constraint in *; omega.
    + rewrite carry_unaffected_low by carry_length_conditions.
      assert (0 < S i < length base)%nat by omega. 
      intuition.
      right.
      apply carry_carry_done_done; try solve [carry_length_conditions].
      intro j.
      destruct j.
      - apply carry_carry_full_2_bounds_0_lower; auto.
      - destruct (lt_eq_lt_dec j i) as [[? | ?] | ?].
        * apply carry_full_2_bounds; auto; omega.
        * subst. apply carry_full_2_bounds_same; auto; omega.
        * rewrite carry_sequence_unaffected; try solve [carry_length_conditions].
          apply carry_full_2_bounds_lower; auto; omega.
  Qed.
 
  (* END proofs about second carry loop *)
 
  (* BEGIN proofs about third carry loop *)

  Lemma carry_full_3_bounds : forall us i, pre_carry_bounds us -> c_carry_constraint ->
    (length us = length base)%nat ->(i < length base)%nat ->
    0 <= nth_default 0 (carry_full (carry_full (carry_full us))) i <= max_bound i.
  Proof.
    intros.
    destruct i; [ | apply carry_full_bounds; carry_length_conditions;
                    do 2 (intros; apply carry_sequence_bounds_lower; eauto; carry_length_conditions) ].
    unfold carry_full at 1 4, full_carry_chain.
    case_eq limb_widths; [intros; pose proof limb_widths_nonnil; congruence | ].
    simpl.
    intros ? ? limb_widths_eq.
    replace (length l) with (pred (length limb_widths)) by (rewrite limb_widths_eq; auto).
    rewrite <- base_length.
    unfold carry, carry_and_reduce; break_if; try omega; intros.
    add_set_nth.
    split.
    + apply Z.add_nonneg_nonneg.
      - apply Z.mul_nonneg_nonneg; auto; try omega.
        apply Z.shiftr_nonneg.
        eapply carry_full_2_bounds_same; eauto; omega.
      - eapply carry_carry_full_2_bounds_0_lower; eauto; omega.
    + pose proof (carry_carry_full_2_bounds_0_upper us (pred (length base))).
      assert (0 < pred (length base) < length base)%nat by omega.
      intuition.
      - replace (max_bound 0) with (c + (max_bound 0 - c)) by ring.
        apply Z.add_le_mono; try assumption.
        replace c with (c * 1) at 2 by ring.
        apply Z.mul_le_mono_pos_l; try omega.
        rewrite Z.shiftr_div_pow2 by auto.
        apply Z.div_le_upper_bound; auto.
        ring_simplify.
        apply carry_full_2_bounds_same; auto.
      - match goal with H : carry_done _ |- _ => unfold carry_done in H; rewrite H by omega end.
        ring_simplify.
        apply shiftr_eq_0_max_bound; auto; omega.
  Qed.

  Lemma nth_error_combine : forall {A B} i (x : A) (x' : B) l l', nth_error l i = Some x ->
    nth_error l' i = Some x' -> nth_error (combine l l') i = Some (x, x').
  Admitted.

  Lemma nth_error_range : forall {A} i (l : list A), (i < length l)%nat ->
    nth_error (range (length l)) i = Some i.
  Admitted.

  (* END proofs about third carry loop *)
  Opaque carry_full.

  Lemma freeze_in_bounds : forall us i, (us <> nil)%nat ->
    0 <= nth_default 0 (freeze us) i < 2 ^ log_cap i.
  Proof.
  Admitted.

  Lemma freeze_canonical : forall us vs x, rep us x -> rep vs x ->
    freeze us = freeze vs.
  Admitted.

End CanonicalizationProofs.