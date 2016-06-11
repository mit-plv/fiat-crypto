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
  Context `{prm : PseudoMersenneBaseParams} (lt_1_length_base : (1 < length base)%nat) 
   {B} (B_pos : 0 < B) (B_compat : forall w, In w limb_widths -> w <= B)
   (c_pos : 0 < c)
   (* on the first reduce step, we add at most one bit of width to the first digit *)
   (c_reduce1 : c * (Z.ones (B - log_cap (pred (length base)))) < max_bound 0 + 1)
   (* on the second reduce step, we add at most one bit of width to the first digit,
      and leave room to carry c one more time after the highest bit is carried *)
   (c_reduce2 : c <= max_bound 0 - c).
(* TODO  (c_reduce2: max_bound 0 + c < 2 ^ (log_cap 0 + 1)). c < max_bound 0 + 2*)

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

  (* TODO : move *)
  Lemma Z_ones_pos_pos : forall i, (0 < i) -> 0 < Z.ones i.
  Proof.
    intros.
    unfold Z.ones.
    rewrite Z.shiftl_1_l.
    apply Z.lt_succ_lt_pred.
    apply Z.pow_gt_1; omega.
  Qed.

  Lemma max_bound_pos : forall i, (i < length base)%nat -> 0 < max_bound i.
  Proof.
    unfold max_bound, log_cap; intros; apply Z_ones_pos_pos.
    apply limb_widths_pos.
    rewrite nth_default_eq.
    apply nth_In.
    rewrite <-base_length; assumption.
  Qed.
  Local Hint Resolve max_bound_pos.

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

  Lemma log_cap_eq : forall i, log_cap i = nth_default 0 limb_widths i.
  Proof.
    reflexivity.
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

  Lemma carry_done_bounds : forall us, carry_done us <->
    (forall i, 0 <= nth_default 0 us i < 2 ^ log_cap i).
  Admitted.

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

  Lemma carry_sequence_carry_full_bounds_same : forall us i, pre_carry_bounds us ->
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

  Lemma carry_full_2_bounds_succ : forall us i, pre_carry_bounds us ->
    (length us = length base)%nat -> (0 < i < pred (length base))%nat ->
    ((0 < i < length base)%nat ->
      0 <= nth_default 0
        (carry_sequence (make_chain i) (carry_full (carry_full us))) i <=
      2 ^ log_cap i) ->
      0 <= nth_default 0 (carry_simple i
        (carry_sequence (make_chain i) (carry_full (carry_full us)))) (S i) <= 2 ^ log_cap (S i).
  Proof.
    unfold carry_simple; intros ? ? PCB length_eq ? IH.
    add_set_nth.
    split.
    + apply Z.add_nonneg_nonneg.
      apply Z.shiftr_nonneg. 
      destruct i;
        [ simpl; pose proof (carry_full_2_bounds_0 us PCB length_eq); omega | ].
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
        rewrite <-max_bound_log_cap.
        ring_simplify. omega.
      - apply carry_full_bounds; carry_length_conditions.
        intros; apply carry_sequence_bounds_lower; eauto; carry_length_conditions.
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
        apply Z.le_trans with (m := (max_bound 0 + c) - (1 + max_bound 0)); try omega.
        replace x with ((x - 2 ^ log_cap 0) + (1 * 2 ^ log_cap 0)) by ring.
        rewrite pow2_mod_spec by auto.
        rewrite Z.mod_add by (pose proof (pow_2_log_cap_pos 0); omega).
        rewrite <-max_bound_log_cap, <-Z.add_1_l, Z.mod_small.
        apply Z.sub_le_mono_r.
        subst; apply carry_full_2_bounds_0; auto.
        split; try omega.
        pose proof carry_full_2_bounds_0.
        apply Z.le_lt_trans with (m := (max_bound 0 + c) - (1 + max_bound 0));
          [ apply Z.sub_le_mono_r; subst x; apply carry_full_2_bounds_0; auto;
          ring_simplify | ]; omega.
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

  Lemma carry_full_3_bounds : forall us i, pre_carry_bounds us ->
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

  Lemma carry_full_3_done : forall us, pre_carry_bounds us ->
    (length us = length base)%nat ->
    carry_done (carry_full (carry_full (carry_full us))).
  Proof.
    intros.
    apply carry_done_bounds; intro i.
    destruct (lt_dec i (length base)).
    + rewrite <-max_bound_log_cap, Z.lt_succ_r.
      auto using carry_full_3_bounds.
    + rewrite nth_default_out_of_bounds; carry_length_conditions.
  Qed.

  (* END proofs about third carry loop *)

  Lemma nth_error_combine : forall {A B} i (x : A) (x' : B) l l', nth_error l i = Some x ->
    nth_error l' i = Some x' -> nth_error (combine l l') i = Some (x, x').
  Admitted.
(*
  Lemma nth_error_range : forall i r, (i < r)%nat ->
    nth_error (range r) i = Some i.
  Admitted.
*)
  Lemma carry_full_length : forall us, (length us = length base)%nat ->
    length (carry_full us) = length us.
  Proof.
    intros; carry_length_conditions.
  Qed.

  (* TODO : move? *)
  Lemma make_chain_lt : forall x i : nat, In i (make_chain x) -> (i < x)%nat.
  Proof.
    induction x; simpl; intuition.
  Qed.

  Lemma carry_full_preserves_rep : forall us x, (length us = length base)%nat ->
    rep us x -> rep (carry_full us) x.
  Proof.
    unfold carry_full; intros.
    apply carry_sequence_rep; auto.
    unfold full_carry_chain; rewrite base_length; apply make_chain_lt.
  Qed.

  Opaque carry_full.
(*
  Lemma length_range : forall n, length (range n) = n.
  Proof.
    induction n; intros; auto.
    simpl.
    rewrite app_length, cons_length, nil_length0.
    omega.
  Qed.

  Lemma range0_nil : range 0 = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma range_succ : forall n, range (S n) = range n ++ n :: nil.
  Proof.
    reflexivity.
  Qed.

  Lemma nth_default_range : forall d r n, (n < r)%nat -> nth_default d (range r) n = n.
  Proof.
    induction r; intro; try omega.
    intros.
    assert (n = r \/ n < r)%nat as cases by omega.
    destruct cases; subst; rewrite range_succ, nth_default_app, length_range; break_if; try omega.
    + rewrite Nat.sub_diag.
      auto using nth_default_cons.
    + apply IHr; omega.
  Qed.

  Lemma combine_app : forall {A B} (x y : list A) (z : list B), (length (x ++ y) <= length z)%nat ->
    combine (x ++ y) z = combine x z ++ combine y (skipn (length x) z).
  Proof.
    intros.
    rewrite <- (firstn_skipn (length x) z) at 1.
    rewrite combine_app_samelength by
      (rewrite firstn_length, Nat.min_l; auto; rewrite app_length in *; omega).
    rewrite <-combine_truncate_r; reflexivity.
  Qed.

  Lemma combine_range_succ : forall l r, (S r <= length l)%nat ->
    combine (range (S r)) l = (combine (range r) l) ++ (r,nth_default 0 l r) :: nil.
  Proof.
    intros.
    simpl.
    rewrite combine_app by (rewrite app_length, cons_length, length_range, nil_length0; omega).
    f_equal.
    rewrite length_range.
    erewrite skipn_nth_default by omega.
    reflexivity.
  Qed.
  Opaque range.

  Lemma map_sub_combine_range : forall d d' f l i, (l <> nil) -> (i < length l)%nat ->
    nth_default d (map (fun x => snd x - f (fst x)) (combine (range (length l)) l)) i =
    nth_default d' l i - f i.
  Proof.
    intros until 1.
    intros lt_i_length.
    destruct (nth_error_length_exists_value i l lt_i_length).
    erewrite nth_error_value_eq_nth_default; auto.
    erewrite map_nth_error;
      [ | apply nth_error_combine; try apply nth_error_range; eauto].
    erewrite nth_error_value_eq_nth_default; eauto.
  Qed.
*)
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

  Lemma isFull_lower_bound_0 : forall us, isFull us = true ->
    max_bound 0 - c < nth_default 0 us 0.
  Proof.
    eauto using isFull'_lower_bound_0.
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

  Lemma isFull_true_full : forall i us, (length us = length base) ->
    (0 < i < length base)%nat -> isFull us = true ->
    max_bound i = nth_default 0 us i.
  Proof.
    unfold isFull; intros.
    eapply isFull'_true_full with (j := (length us - 1)%nat); eauto; omega.
  Qed.

  (* TODO : move *)
  Lemma N_le_1_l : forall p, (1 <= N.pos p)%N.
  Proof.
    destruct p; cbv; congruence.
  Qed.

  (* TODO : move *)
  Lemma Pos_land_upper_bound_l : forall a b, (Pos.land a b <= N.pos a)%N.
  Proof.
    induction a; destruct b; intros; try solve [cbv; congruence];
      simpl; specialize (IHa b); case_eq (Pos.land a b); intro; simpl;
      try (apply N_le_1_l || apply N.le_0_l); intro land_eq;
      rewrite land_eq in *; unfold N.le, N.compare in *;
      rewrite ?Pos.compare_xI_xI, ?Pos.compare_xO_xI, ?Pos.compare_xO_xO;
      try assumption.
    destruct (p ?=a)%positive; cbv; congruence.
  Qed.

  Lemma Zneg_nonneg_false : forall p, 0 <= Z.neg p -> False.
  Admitted.
  Hint Resolve Zneg_nonneg_false.

  (* TODO : move *)
  Lemma Z_land_upper_bound_l : forall a b, (0 <= a) -> (0 <= b) ->
    Z.land a b <= a.
  Proof.
    intros.
    destruct a, b; try solve [exfalso; auto]; try solve [cbv; congruence].
    cbv [Z.land].
    rewrite <-N2Z.inj_pos, <-N2Z.inj_le.
    auto using Pos_land_upper_bound_l.
  Qed.

  (* TODO : move *)
  Lemma Z_land_upper_bound_r : forall a b, (0 <= a) -> (0 <= b) ->
    Z.land a b <= b.
  Proof.
    intros.
    rewrite Z.land_comm.
    auto using Z_land_upper_bound_l.
  Qed.

  Lemma max_ones_nonneg : 0 <= max_ones.
  Proof.
    unfold max_ones.
    apply Z_ones_nonneg.
    pose proof limb_widths_nonneg.
    induction limb_widths.
    cbv; congruence.
    simpl.
    apply Z.max_le_iff.
    right.
    apply IHl; auto using in_cons.
  Qed.
  Hint Resolve max_ones_nonneg.
(*
  Lemma sub_land_max_bound_max_ones_lower :
    forall us i, (length us = length base) -> isFull us = true ->
    (i < length us)%nat ->
    0 <= nth_default 0 us i - land_max_bound max_ones i.
  Proof.
    unfold land_max_bound; intros.
    break_if.
    + subst. apply Z.le_0_sub.
      etransitivity.
      - apply Z_land_upper_bound_r; auto.
        apply Z.le_trans with (m := c - 1); omega.
      - rewrite Z.add_1_r.
        apply Z.le_succ_l.
        auto using isFull_lower_bound_0.
    + apply Z.le_0_sub.
      etransitivity.
      apply Z_land_upper_bound_r; auto.
      apply Z.eq_le_incl.
      apply isFull_true_full; auto.
      omega.
  Qed.
*)
  (* TODO : move *)
  Lemma Z_le_fold_right_max : forall low l x, (forall y, In y l -> low <= y) ->
    In x l -> x <= fold_right Z.max low l.
  Proof.
    induction l; intros ? lower_bound In_list; [cbv [In] in *; intuition | ].
    simpl.
    destruct (in_inv In_list); subst.
    + apply Z.le_max_l.
    + etransitivity.
      - apply IHl; auto; intuition.
      - apply Z.le_max_r.
  Qed.

  (* TODO : move *)
  Lemma Z_le_fold_right_max_initial : forall low l, low <= fold_right Z.max low l.
  Proof.
    induction l; intros; try reflexivity.
    etransitivity; [ apply IHl | apply Z.le_max_r ].
  Qed.

  Lemma land_max_ones_noop : forall x i, 0 <= x < 2 ^ log_cap i -> Z.land max_ones x = x.
  Proof.
    unfold max_ones.
    intros ? ? x_range.
    rewrite Z.land_comm.
    rewrite Z.land_ones by apply Z_le_fold_right_max_initial.
    apply Z.mod_small.
    split; try omega.
    eapply Z.lt_le_trans; try eapply x_range.
    apply Z.pow_le_mono_r; try omega.
    rewrite log_cap_eq.
    destruct (lt_dec i (length limb_widths)).
    + apply Z_le_fold_right_max.
      - apply limb_widths_nonneg.
      - rewrite nth_default_eq.
        auto using nth_In.
    + rewrite nth_default_out_of_bounds by omega.
      apply Z_le_fold_right_max_initial.
  Qed.

  Lemma land_max_ones_max_bound : forall i, Z.land max_ones (max_bound i) = max_bound i.
  Proof.
    intros.
    apply land_max_ones_noop with (i := i).
    rewrite <-max_bound_log_cap.
    split; auto; omega.
  Qed.

  Lemma land_max_ones_max_bound_sub_c :
    Z.land max_ones (max_bound 0 - c + 1) = max_bound 0 - c + 1.
  Proof.
    apply land_max_ones_noop with (i := 0%nat).
    rewrite <-max_bound_log_cap.
    split; auto; try omega.
  Qed.
(*
  Lemma land_max_bound_pos : forall i, (i < length base)%nat ->
    0 < land_max_bound max_ones i.
  Proof.
    unfold land_max_bound; intros.
    break_if.
    + subst.
      rewrite land_max_ones_max_bound_sub_c by assumption.
      apply Z.lt_le_trans with (m := c); auto. omega.
    + rewrite land_max_ones_max_bound by assumption.
      auto using max_bound_pos.
  Qed.
  Local Hint Resolve land_max_bound_pos.


  Lemma sub_land_max_bound_max_ones_upper :
    forall us i, nth_default 0 us i <= max_bound i ->
    (length us = length base) -> (i < length us)%nat ->
    nth_default 0 us i - land_max_bound max_ones i < 2 ^ log_cap i.
  Proof.
    intros.
    eapply Z.lt_trans.
    + eapply Z.lt_sub_pos.
      apply land_max_bound_pos; auto; omega.
    + rewrite <-max_bound_log_cap.
      omega.
  Qed.


  Lemma land_max_bound_0 : forall i, land_max_bound 0 i = 0.
  Admitted.
*)

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

  Opaque isFull' (* TODO isFull *) max_ones.

  (* TODO : move *)
  Lemma length_nonzero_nonnil : forall {A} (l : list A), (0 < length l)%nat ->
    l <> nil.
  Proof.
    destruct l; boring; congruence.
  Qed.

  Lemma carry_full_3_length : forall us, (length us = length base) ->
    length (carry_full (carry_full (carry_full us))) = length us.
  Proof.
    intros.
    repeat rewrite carry_full_length by (repeat rewrite carry_full_length; auto); auto.
  Qed.
  Local Hint Resolve carry_full_3_length.

  Lemma freeze_in_bounds : forall us,
    pre_carry_bounds us -> (length us = length base) ->
    carry_done (freeze us).
  Proof.
    unfold freeze; intros.
    rewrite carry_done_bounds; intro i.
    destruct (lt_dec i (length us)).
    + rewrite map_sub_combine_range with (d' := 0) by (try apply length_nonzero_nonnil;
        (repeat rewrite carry_full_length by (repeat rewrite carry_full_length; auto)); auto; try omega).
      break_if.
      - split; [apply sub_land_max_bound_max_ones_lower
               |apply sub_land_max_bound_max_ones_upper ];
          rewrite ?carry_full_3_length; auto.
        apply carry_full_3_bounds; auto; omega.
      - rewrite land_max_bound_0, <-max_bound_log_cap, Z.lt_succ_r, Z.sub_0_r.
        apply carry_full_3_bounds; auto; omega.
    + rewrite nth_default_out_of_bounds; [ split; auto; omega | ].
      rewrite map_length, combine_length, length_range, Nat.min_id.
      repeat rewrite carry_full_length by (repeat rewrite carry_full_length; auto).
      omega.
  Qed.

  Lemma freeze_length : forall us, (length us = length base) ->
    length (freeze us) = length us.
  Proof.
    unfold freeze; intros.
    rewrite map_length, combine_length, length_range, Nat.min_id.
    auto.
  Qed.

  (* TODO : move *)
  Lemma nth_default_same_lists_same : (* TODO : rename if this works *)
    forall {A} d (l' l : list A), (length l = length l') ->
    (forall i, nth_default d l i = nth_default d l' i) ->
    l = l'.
  Proof.
    induction l'; intros until 0; intros lengths_equal nth_default_match.
    + apply length0_nil; auto.
    + destruct l; rewrite ?nil_length0, !cons_length in lengths_equal;
        [congruence | ].
      pose proof (nth_default_match 0%nat) as nth_default_match_0.
      rewrite !nth_default_cons in nth_default_match_0.
      f_equal; auto.
      apply IHl'; [ omega | ].
      intros.
      specialize (nth_default_match (S i)).
      rewrite !nth_default_cons_S in nth_default_match.
      assumption.
  Qed.

  Lemma not_full_no_change : forall us, length us = length base ->
   map (fun x : nat * Z => snd x - land_max_bound 0 (fst x))
   (combine (range (length us)) us) = us.
  Proof.
    intros ? lengths_eq.
    apply nth_default_same_lists_same with (d := 0).
    + rewrite map_length, combine_length, length_range, Nat.min_id; auto.
    + intros.
      destruct (lt_dec i (length us)).
      - erewrite map_sub_combine_range by (auto; intro false_eq; subst;
          rewrite nil_length0 in lengths_eq; omega).
        rewrite land_max_bound_0.
        apply Z.sub_0_r.
      - rewrite !nth_default_out_of_bounds; try omega.
        rewrite map_length, combine_length, length_range, Nat.min_id; omega.
  Qed.

  (* TODO : move *)
  Lemma map_cons : forall {A B} (f : A -> B) x xs, map f (x :: xs) = f x :: (map f xs).
  Proof.
    auto.
  Qed.
  
  (* TODO : move *)
  Lemma firstn_firstn : forall {A} m n (l : list A), (n <= m)%nat ->
    firstn n (firstn m l) = firstn n l.
  Proof.
    induction m; destruct n; intros; try omega; auto.
    destruct l; auto.
    simpl.
    f_equal.
    apply IHm; omega.
  Qed.

  (* TODO : move *)
  Lemma firstn_succ : forall n l, (n < length l)%nat ->
    firstn (S n) l = (firstn n l) ++ nth_default 0 l n :: nil.
  Proof.
    induction n; destruct l; rewrite ?(@nil_length0 Z); intros; try omega.
    + rewrite nth_default_cons; auto.
    + simpl.
      rewrite nth_default_cons_S.
      rewrite <-IHn by (rewrite cons_length in *; omega).
      reflexivity.
  Qed.
(*
Print BaseSystem.accumulate.
SearchAbout combine range.
mapi : forall {A B}, (nat -> A -> B) -> list A -> list B
mapi (fun x y => (x, y)) ls
map2 : forall {A B C}, (A -> B -> C) -> list A -> list B -> list C

BaseSystem.decode u (map2 (fun x y => x - y) v w)
= BaseSystem.decode u v - BaseSystem.decode u w

map2 f ls1 ls2 = map (fun xy => f (fst xy) (snd xy)) (combine ls1 ls2)

map2 f (map g ls1) ls2 = map2 (fun x y => f (g x) y) ls1 ls2
map2 f ls1 (map g ls2) = map2 (fun x y => f x (g y)) ls1 ls2

Locate mapi.
*)
Print map.

  Fixpoint mapi' {A B} (f : nat -> A -> B) i (l : list A) : list B :=
    match l with
    | nil => nil
    | x :: l' => f i x :: mapi' f (S i) l'
    end.

  Definition mapi {A B} (f : nat -> A -> B) (l : list A) : list B := mapi' f 0%nat l.


  Fixpoint map2 {A B C} (f : A -> B -> C) (la : list A) (lb : list B) : list C :=
    match la with
    | nil => nil
    | a :: la' => match lb with
                  | nil => nil
                  | b :: lb' => f a b :: map2 f la' lb'
                  end
    end.

  Lemma map2_combine : forall {A B C} (f : A -> B -> C) ls1 ls2,
    map2 f ls1 ls2 = map (fun xy => f (fst xy) (snd xy)) (combine ls1 ls2).
  Admitted.

  Lemma map2_map_l : forall {A' A B C} (f : A -> B -> C) (g : A' -> A) ls1 ls2,
     map2 f (map g ls1) ls2 = map2 (fun x y => f (g x) y) ls1 ls2.
  Admitted.

  Lemma map2_map_r :forall {B' A B C} (f : A -> B -> C) (g : B' -> B) ls1 ls2,
    map2 f ls1 (map g ls2) = map2 (fun x y => f x (g y)) ls1 ls2.
  Admitted.

  (* TODO : rewrite using the above? *)

  Hint Rewrite app_length cons_length map_length combine_length length_range firstn_length map_app : lengths.

  Lemma decode_subtract_elementwise: forall f r l, (length l = length base) ->
   (r <= length l)%nat ->
    BaseSystem.decode (firstn r base) (map (fun x => snd x - f (fst x)) (combine (range r) l)) =
    BaseSystem.decode (firstn r base) (firstn r l) - BaseSystem.decode (firstn r base) (map f (range r)).
  Proof.
    induction r; intros.
    + rewrite range0_nil.
      cbv [combine map BaseSystem.decode sum_firstn firstn fold_right].
      rewrite decode_nil.
      auto.
    + rewrite combine_range_succ by assumption.
      rewrite (firstn_succ _ l) by omega.
      rewrite range_succ.
      rewrite !map_app, !decode'_splice.
      autorewrite with lengths.
      rewrite Min.min_l, firstn_firstn, firstn_succ by omega.
      rewrite skipn_app_sharp by (rewrite firstn_length, Nat.min_l; omega).
      simpl.
      rewrite !decode'_cons, decode_nil, IHr by omega.
      unfold BaseSystem.decode.
      ring.
  Qed.

  Definition modulus_digit i := if (eq_nat_dec i 0) then max_bound i - c + 1 else max_bound i.
  (* TODO : maybe use this more? *)

  Lemma modulus_digit_nonneg : forall i, 0 <= modulus_digit i.
  Proof.
    unfold modulus_digit; intros; break_if; auto; subst; omega.
  Qed.
  Hint Resolve modulus_digit_nonneg.
    
  Lemma modulus_digit_lt_cap : forall i,
    modulus_digit i < 2 ^ log_cap i.
  Proof.
    unfold modulus_digit; intros; rewrite <- max_bound_log_cap; break_if; omega.
  Qed.
  Hint Resolve modulus_digit_lt_cap.

  Lemma modulus_digit_land_max_bound_max_ones : forall i,
    land_max_bound max_ones i = modulus_digit i.
  Proof.
    unfold land_max_bound; intros.
    eapply land_max_ones_noop; eauto.
  Qed.

  Lemma decode_modulus_digit_partial : forall n, (0 < n <= length base)%nat ->
    BaseSystem.decode (firstn n base) (map modulus_digit (range (length base))) =
    2 ^ (sum_firstn limb_widths n) - c.
  Proof.
    induction n; intros; try omega.
    rewrite firstn_succ by omega.
    rewrite base_app.
    rewrite decode'_truncate, firstn_length, Min.min_l in * by omega.
    rewrite firstn_firstn by omega.
    rewrite skipn_nth_default with (d := 0) by (autorewrite with lengths; omega).
    rewrite decode'_cons, decode_base_nil, Z.add_0_r.
    erewrite map_nth_default with (y := 0) (x := 0%nat) by
      (autorewrite with lengths; omega).
    rewrite nth_default_range by (autorewrite with lengths; omega).
    rewrite nth_default_base by omega.
    unfold modulus_digit at 2; break_if.
    + subst.
      clear IHn.
      cbv [firstn BaseSystem.decode' combine fold_right].
      destruct (nth_error_length_exists_value 0 limb_widths); try (rewrite <-base_length; omega).
      erewrite sum_firstn_succ; eauto.
      replace (max_bound 0) with (2 ^ log_cap 0 - 1) by (rewrite <-max_bound_log_cap; omega).
      rewrite log_cap_eq.
      erewrite nth_error_value_eq_nth_default; eauto.
      rewrite Z.pow_add_r by (auto using sum_firstn_limb_widths_nonneg; apply limb_widths_nonneg;
        auto using (nth_error_value_In 0)).
      cbv [sum_firstn firstn fold_right].
      ring.
    + rewrite IHn by (auto; omega).
      replace (max_bound n) with (2 ^ log_cap n - 1) by (rewrite <-max_bound_log_cap; omega).
      rewrite log_cap_eq.
      destruct (nth_error_length_exists_value n limb_widths); try (rewrite <- base_length; omega).
      erewrite sum_firstn_succ; eauto.
      erewrite nth_error_value_eq_nth_default; eauto.
      rewrite Z.pow_add_r by (auto using sum_firstn_limb_widths_nonneg; apply limb_widths_nonneg;
        auto using (nth_error_value_In n)).
      ring.
  Qed.

  Lemma decode_map_modulus_digit :
    BaseSystem.decode base (map modulus_digit (range (length base))) = modulus.
  Proof.
    erewrite <-(firstn_all _ base) at 1 by reflexivity.
    rewrite decode_modulus_digit_partial by omega.
    rewrite base_length.
    fold k; unfold c.
    ring.
  Qed.

  Lemma decode_subtract_modulus_elementwise : forall us, (length us = length base) ->
    BaseSystem.decode base
     (map (fun x0 : nat * Z => snd x0 - land_max_bound max_ones (fst x0))
       (combine (range (length us)) us)) = BaseSystem.decode base us - modulus.
  Proof.
    intros.
    replace base with (firstn (length us) base) at 1 by (auto using firstn_all).
    rewrite decode_subtract_elementwise by omega.
    rewrite !firstn_all by auto.
    f_equal.
    erewrite map_ext; [ | eapply modulus_digit_land_max_bound_max_ones ].
    replace (length us) with (length base) by assumption.
    exact decode_map_modulus_digit.
  Qed.

  (* TODO : move *)
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

  Lemma freeze_preserves_rep : forall us x, (length us = length base) ->
    rep us x -> rep (freeze us) x.
  Proof.
    unfold rep; intros.
    intuition; rewrite ?freeze_length; auto.
    unfold freeze.
    break_if.
    + apply decode_mod with (us := carry_full (carry_full (carry_full us))).
      - rewrite carry_full_3_length; auto.
      - autorewrite with lengths.
        rewrite Nat.min_id.
        rewrite carry_full_3_length; auto.
      - repeat apply carry_full_preserves_rep; repeat rewrite carry_full_length; auto.
        unfold rep; intuition.
      - rewrite decode_subtract_modulus_elementwise by (rewrite carry_full_3_length; auto).
        destruct (Z_eq_dec modulus 0); [ subst; rewrite !Zmod_0_r; reflexivity | ].
        rewrite <-Z.add_opp_r.
        replace (-modulus) with (-1 * modulus) by ring.
        symmetry; auto using Z.mod_add.
    + rewrite not_full_no_change by (rewrite carry_full_3_length; auto).
      repeat (apply carry_full_preserves_rep; repeat rewrite carry_full_length; auto).
      unfold rep; auto.
  Qed.

  Lemma isFull_true_iff : forall us, (length us = length base) -> (isFull us = true <->
    max_bound 0 - c < nth_default 0 us 0
    /\ (forall i, (0 < i <= length us - 1)%nat -> nth_default 0 us i = max_bound i)).
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
     (in our context, this is the most significant end). *)
  Definition compare us vs := compare' us vs (length us).

  Lemma decode_firstn_succ : forall n us, (length us = length base) ->
   (n < length base)%nat ->
   BaseSystem.decode' (firstn (S n) base) (firstn (S n) us) =
   BaseSystem.decode' (firstn n base) (firstn n us) +
     nth_default 0 base n * nth_default 0 us n.
  Proof.
    intros.
    rewrite !firstn_succ by omega.
    rewrite base_app, firstn_app.
    autorewrite with lengths; rewrite !Min.min_l by omega.
    rewrite Nat.sub_diag, firstn_firstn, firstn0, app_nil_r by omega.
    rewrite skipn_app_sharp by (autorewrite with lengths; apply Min.min_l; omega).
    rewrite decode'_cons, decode_nil, Z.add_0_r.
    reflexivity.
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
      rewrite nth_default_base_succ by omega.
      eapply Z.lt_le_trans.
      - apply Z.add_lt_mono_r.
        apply IHn; auto; omega.
      - rewrite <-(Z.mul_1_r (nth_default 0 base n)) at 1.
        rewrite <-Z.mul_add_distr_l, Z.mul_comm.
        apply Z.mul_le_mono_pos_r.
        * apply Z.gt_lt. apply nth_default_base_positive; omega.
        * rewrite Z.add_1_l.
          apply Z.le_succ_l.
          rewrite carry_done_bounds in bounded.
          apply bounded.
  Qed.

  Lemma highest_digit_determines : forall us vs n x, (x < 0) ->
    (length us = length base) ->
    (n < length us)%nat -> carry_done us ->
    (n < length vs)%nat -> carry_done vs ->
    BaseSystem.decode' (firstn n base) (firstn n us) +
    nth_default 0 base n * x -
    BaseSystem.decode' (firstn n base) (firstn n vs) < 0.
  Proof.
    intros.
    eapply Z.le_lt_trans.
    apply Z.le_sub_nonneg.
    admit. (* TODO : decode' is nonnegative *)
    eapply Z.le_lt_trans.
    eapply Z.add_le_mono with (q := nth_default 0 base n * -1); [ apply Z.le_refl | ].
    apply Z.mul_le_mono_nonneg_l; try omega.
    admit. (* TODO : 0 <= nth_default 0 base n *)
    ring_simplify.
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
    rewrite firstn_succ, !base_app by omega.
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
    + rewrite firstn_succ by omega.
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
      apply gt_lt_symmetry in Hgt.
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

  Transparent isFull'.
  Print compare'.
  Lemma compare'_succ : forall us j vs, compare' us vs (S j) =
    if Z.eq_dec (nth_default 0 us j) (nth_default 0 vs j)
    then compare' us vs j
    else nth_default 0 us j ?= nth_default 0 vs j.
  Proof.
    reflexivity.
  Qed.


  Lemma compare'_firstn_r : forall us j vs, (j <= length vs)%nat ->
    compare' us vs j = compare' us (firstn j vs) j.
  Proof.
    induction j; intros; auto.
    rewrite !compare'_succ.
    rewrite firstn_succ by omega.
    rewrite nth_default_app.
    autorewrite with lengths; rewrite Min.min_l by omega.
    destruct (lt_dec j j); try omega.
    rewrite Nat.sub_diag.
    rewrite nth_default_cons.
    break_if; try reflexivity.
    rewrite IHj with (vs := firstn j vs ++ nth_default 0 vs j :: nil) by
      (autorewrite with lengths; rewrite Min.min_l; omega).
    rewrite firstn_app_sharp by (autorewrite with lengths; apply Min.min_l; omega).
    apply IHj; omega.
  Qed.

  Lemma isFull'_true_step : forall us j, isFull' us true (S j) = true ->
    isFull' us true j = true.
  Proof.
    simpl; intros ? ? succ_true.
    destruct (max_bound (S j) =? nth_default 0 us (S j)); auto.
    rewrite isFull'_false in succ_true.
    congruence.
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

  Lemma nth_default_map_range : forall f n r, (n < r)%nat ->
    nth_default 0 (map f (range r)) n = f n.
  Proof.
    intros.
    rewrite map_nth_default with (x := 0%nat) by (autorewrite with lengths; omega).
    rewrite nth_default_range by omega.
    reflexivity.
  Qed.

  Lemma isFull'_compare' : forall us j, j <> 0%nat -> (length us = length base) -> carry_done us ->
    (isFull' us true (j - 1) = true <->
      compare' us (map modulus_digit (range j)) j <> Lt).
  Proof.
    unfold compare; induction j; intros; try congruence.
    replace (S j - 1)%nat with j by omega.
    (* rewrite isFull'_true_iff by assumption; *)
    split; intros.
    + simpl.
      break_if.
      - rewrite compare'_firstn_r by (autorewrite with lengths; omega).
        rewrite range_succ, map_app, firstn_app.
        autorewrite with lengths.
        rewrite Nat.sub_diag, app_nil_r.
        rewrite firstn_all by (autorewrite with lengths; reflexivity).
        destruct (eq_nat_dec j 0); [ subst; simpl; try congruence | ].
        apply IHj; auto.
        apply isFull'_true_step.
        replace (S (j - 1)) with j by omega; auto.
      - match goal with |- appcontext[?a ?= ?b]  => case_eq (a ?= b) end;
          intros compare_eq; try congruence.
        rewrite Z.compare_lt_iff in compare_eq.
        rewrite nth_default_map_range in * by omega.
        match goal with H : isFull' _ _ _ = true |- _ =>  apply isFull'_true_iff in H; auto; destruct H end.
         
        destruct (eq_nat_dec j 0).
        * subst. cbv [modulus_digit] in compare_eq.
          break_if; try congruence. omega.
        * assert (0 < j <= j)%nat as j_range by omega.
          specialize (H3 j j_range).
          unfold modulus_digit in n.
          break_if; omega.
    + apply isFull'_true_iff; try assumption.
      match goal with H : compare' _ _ _ <> Lt |- _ => apply compare'_not_Lt in H; [ destruct H as [Hdigit0 Hnonzero] | | ] end.
      - rewrite nth_default_map_range in * by omega.
        split; [ unfold modulus_digit in *; break_if; omega | ].
        intros i i_range.
        assert (0 < i < S j)%nat as  i_range' by omega.
        specialize (Hnonzero  i i_range').
        rewrite nth_default_map_range in * by omega.
        unfold modulus_digit in Hnonzero; break_if; omega.
      - congruence.
      - intros; rewrite nth_default_map_range by omega.
        unfold modulus_digit; break_if; try omega.
        rewrite <-Z.lt_succ_r with (m := max_bound i).
        rewrite max_bound_log_cap; apply carry_done_bounds.
        assumption.
  Qed.

  Lemma isFull_compare : forall us, (length us = length base) -> carry_done us ->
    (isFull us = true <->
      compare us (map modulus_digit (range (length base))) <> Lt).
  Proof.
    unfold compare, isFull; intros ? lengths_eq. intros.
    rewrite lengths_eq.
    apply isFull'_compare'; try omega.
    assumption.
  Qed.

  Lemma isFull_decode :  forall us, (length us = length base) -> carry_done us ->
    (isFull us = true <->
      (BaseSystem.decode base us ?= BaseSystem.decode base (map modulus_digit (range (length base)))) <> Lt).
  Proof.
    intros.
    rewrite decode_compare; autorewrite with lengths; auto;
      [ apply isFull_compare; auto | ].
    rewrite carry_done_bounds; intro i.
    destruct (lt_dec i (length base)).
    + rewrite nth_default_map_range; auto.
    + rewrite nth_default_out_of_bounds by (autorewrite with lengths; omega).
      split; auto; omega.
  Qed.

  Lemma isFull_false_upper_bound : forall us, (length us = length base) -> carry_done us ->
    isFull us = false ->
    BaseSystem.decode base us < modulus.
  Proof.
    intros.
    destruct (Z_lt_dec (BaseSystem.decode base us) modulus) as [? | nlt_modulus];
      [assumption | exfalso].
    apply Z.compare_nlt_iff in nlt_modulus.
    rewrite <-decode_map_modulus_digit in nlt_modulus at 2.
    apply isFull_decode in nlt_modulus; try assumption; congruence.
  Qed.

(* Road map:
 * x prove isFull us = false -> us < modulus
 * _ prove (carry_full^3 us) < 2 * modulus
 *)

  Definition twoKMinusOne := mapi (fun _ => max_bound i

  Lemma bounded_digits_lt_2modulus : forall us, (length us = length base) -> carry_done us ->
    BaseSystem.decode base us < 2 ^ k.
  Proof.
    unfold k.
    SearchAbout sum_firstn limb_widths.
  Qed.

  Lemma bounded_digits_lt_2modulus : forall us, (length us = length base) -> carry_done us ->
    BaseSystem.decode base us < 2 * modulus.
  Proof.
    

  SearchAbout (carry_full (carry_full (carry_full _))).


  Lemma freeze_minimal_rep : forall us, minimal_rep (freeze us).
  Proof.
    unfold minimal_rep, freeze.
    intros.
    symmetry. apply Z.mod_small.
    split.
    + admit.
    + break_if.
      remember (carry_full (carry_full (carry_full us))) as cf3us.
      rewrite decode_subtract_modulus_elementwise.
      apply isFull_true_
  Qed.
  Hint Resolve freeze_minimal_rep.

  Lemma minimal_rep_unique_if_bounded : forall us vs,
    minimal_rep us -> minimal_rep vs ->
    (forall i, 0 <= nth_default 0 us i < 2 ^ log_cap i) ->
    (forall i, 0 <= nth_default 0 vs i < 2 ^ log_cap i) ->
    us = vs.
  Proof.
    
  Admitted.

  Lemma freeze_canonical : forall us vs x y, c_carry_constraint ->
    pre_carry_bounds us -> (length us = length base) -> rep us x -> 
    pre_carry_bounds vs -> (length vs = length base) -> rep vs y ->
    (x mod modulus = y mod modulus) ->
    freeze us = freeze vs.
  Proof.
    unfold rep; intros.
    apply minimal_rep_unique_if_bounded; auto.
    intros. apply freeze_in_bounds; auto.
    intros. apply freeze_in_bounds; auto.
  Qed.

End CanonicalizationProofs.