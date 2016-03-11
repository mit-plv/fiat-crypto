Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import VerdiTactics.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Class PseudoMersenneBaseParams (modulus : Z) (base : list Z) (bv : BaseSystem.BaseVector base) := {
  k : Z;
  c : Z;
  modulus_pseudomersenne : modulus = 2^k - c;
  prime_modulus : Znumtheory.prime modulus;
  base_matches_modulus :
    forall i j,
    (i   <  length base)%nat ->
    (j   <  length base)%nat ->
    (i+j >= length base)%nat->
    let b := nth_default 0 base in
    let r := (b i * b j)  /   (2^k * b (i+j-length base)%nat) in
              b i * b j = r * (2^k * b (i+j-length base)%nat);
  base_succ : forall i, ((S i) < length base)%nat -> 
    let b := nth_default 0 base in
    b (S i) mod b i = 0;
  base_tail_matches_modulus:
    2^k mod nth_default 0 base (pred (length base)) = 0;
  k_nonneg : 0 <= k (* Probably implied by modulus_pseudomersenne. *)
}.
(*
Class RepZMod (modulus : Z) := {
  T : Type;
  encode : F modulus -> T;
  decode : T -> F modulus;

  rep : T -> F modulus -> Prop;
  encode_rep : forall x, rep (encode x) x;
  rep_decode : forall u x, rep u x -> decode u = x;

  add : T -> T -> T;
  add_rep : forall u v x y, rep u x -> rep v y -> rep (add u v) (x+y)%F;

  sub : T -> T -> T;
  sub_rep : forall u v x y, rep u x -> rep v y -> rep (sub u v) (x-y)%F;

  mul : T -> T -> T;
  mul_rep : forall u v x y, rep u x -> rep v y -> rep (mul u v) (x*y)%F
}.
*)
Print PseudoMersenneBaseParams.
Section ExtendedBaseVector.
  Context (base : list Z) {modulus : Z} `(params : PseudoMersenneBaseParams modulus base).
  (* This section defines a new BaseVector that has double the length of the BaseVector
  * used to construct [params]. The coefficients of the new vector are as follows:
  *
  * ext_base[i] = if (i < length base) then base[i] else 2^k * base[i]
  *
  * The purpose of this construction is that it allows us to multiply numbers expressed
  * using [base], obtaining a number expressed using [ext_base]. (Numbers are "expressed" as
  * vectors of digits; the value of a digit vector is obtained by doing a dot product with
  * the base vector.) So if x, y are digit vectors:
  *
  * (x \dot base) * (y \dot base) = (z \dot ext_base)
  *
  * Then we can separate z into its first and second halves: 
  *
  * (z \dot ext_base) = (z1 \dot base) + (2 ^ k) * (z2 \dot base)
  *
  * Now, if we want to reduce the product modulo 2 ^ k - c:
  * 
  * (z \dot ext_base) mod (2^k-c)= (z1 \dot base) + (2 ^ k) * (z2 \dot base) mod (2^k-c)
  * (z \dot ext_base) mod (2^k-c)= (z1 \dot base) + c * (z2 \dot base) mod (2^k-c)
  *
  * This sum may be short enough to express using base; if not, we can reduce again.
  *)
  Definition ext_base := base ++ (map (Z.mul (2^k)) base).
    
  Lemma ext_base_positive : forall b, In b ext_base -> b > 0.
  Proof.
    unfold ext_base. intros b In_b_base.
    rewrite in_app_iff in In_b_base.
    destruct In_b_base as [? | In_b_extbase]; auto using BaseSystem.base_positive.
    apply in_map_iff in In_b_extbase.
    destruct In_b_extbase as [b' [b'_2k_b  In_b'_base]].
    subst.
    specialize (BaseSystem.base_positive b' In_b'_base); intro base_pos.
    replace 0 with (2 ^ k * 0) by ring.
    apply (Zmult_gt_compat_l b' 0 (2 ^ k)); [| apply base_pos; intuition].
    rewrite Z.gt_lt_iff.
    apply Z.pow_pos_nonneg; intuition.
    pose proof k_nonneg; omega.
  Qed.

  Lemma base_length_nonzero : (0 < length base)%nat.
  Proof.
    assert (nth_default 0 base 0 = 1) by (apply BaseSystem.b0_1).
    unfold nth_default in H.
    case_eq (nth_error base 0); intros;
      try (rewrite H0 in H; omega).
    apply (nth_error_value_length _ 0 base z); auto.
  Qed.

  Lemma b0_1 : forall x, nth_default x ext_base 0 = 1.
  Proof.
    intros. unfold ext_base.
    rewrite nth_default_app.
    assert (0 < length base)%nat by (apply base_length_nonzero).
    destruct (lt_dec 0 (length base)); try apply BaseSystem.b0_1; try omega.
  Qed.

  Lemma two_k_nonzero : 2^k <> 0.
  Proof.
    pose proof (Z.pow_eq_0 2 k k_nonneg).
    intuition.
  Qed.

  Lemma map_nth_default_base_high : forall n, (n < (length base))%nat -> 
    nth_default 0 (map (Z.mul (2 ^ k)) base) n =
    (2 ^ k) * (nth_default 0 base n).
  Proof.
    intros.
    erewrite map_nth_default; auto.
  Qed.

  Lemma ext_base_succ : forall i, ((S i) < length ext_base)%nat ->
  let b := nth_default 0 ext_base in
  b (S i) mod b i = 0.
  Proof.
    intros; subst b; unfold ext_base.
    repeat rewrite nth_default_app.
    do 2 break_if; [apply base_succ; auto | omega | | ]. {
      destruct (lt_eq_lt_dec (S i) (length base)); try omega.
        destruct s; intuition.
        rewrite map_nth_default_base_high by omega.
        replace i with (pred(length base)) by omega.
        rewrite <- Zmult_mod_idemp_l.
        rewrite base_tail_matches_modulus.
        rewrite Zmod_0_l; auto.
    } {
      unfold ext_base in *; rewrite app_length, map_length in *.
      repeat rewrite map_nth_default_base_high by omega.
      rewrite Zmult_mod_distr_l.
      rewrite <- minus_Sn_m by omega.
      rewrite base_succ by omega; ring.
    }
  Qed. 

  Lemma base_good_over_boundary : forall
    (i : nat)
    (l : (i < length base)%nat)
    (j' : nat)
    (Hj': (i + j' < length base)%nat)
    ,
    2 ^ k * (nth_default 0 base i * nth_default 0 base j') =
    2 ^ k * (nth_default 0 base i * nth_default 0 base j') /
    (2 ^ k * nth_default 0 base (i + j')) *
    (2 ^ k * nth_default 0 base (i + j'))
  .
  Proof.
    intros.
    remember (nth_default 0 base) as b.
    rewrite Zdiv_mult_cancel_l by (exact two_k_nonzero).
    replace (b i * b j' / b (i + j')%nat * (2 ^ k * b (i + j')%nat))
     with  ((2 ^ k * (b (i + j')%nat * (b i * b j' / b (i + j')%nat)))) by ring.
    rewrite Z.mul_cancel_l by (exact two_k_nonzero).
    replace (b (i + j')%nat * (b i * b j' / b (i + j')%nat))
     with ((b i * b j' / b (i + j')%nat) * b (i + j')%nat) by ring.
    subst b.
    apply (BaseSystem.base_good i j'); omega.
  Qed.

  Lemma ext_base_good :
    forall i j, (i+j < length ext_base)%nat ->
    let b := nth_default 0 ext_base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
  Proof.
    intros.
    subst b. subst r.
    unfold ext_base in *.
    rewrite app_length in H; rewrite map_length in H.
    repeat rewrite nth_default_app.
    destruct (lt_dec i (length base));
      destruct (lt_dec j (length base));
      destruct (lt_dec (i + j) (length base));
      try omega.
    { (* i < length base, j < length base, i + j < length base *)
      apply BaseSystem.base_good; auto.
    } { (* i < length base, j < length base, i + j >= length base *)
      rewrite (map_nth_default _ _ _ _ 0) by omega.
      apply base_matches_modulus; omega.
    } { (* i < length base, j >= length base, i + j >= length base *)
      do 2 rewrite map_nth_default_base_high by omega.
      remember (j - length base)%nat as j'.
      replace (i + j - length base)%nat with (i + j')%nat by omega.
      replace (nth_default 0 base i * (2 ^ k * nth_default 0 base j'))
         with (2 ^ k * (nth_default 0 base i * nth_default 0 base j'))
         by ring.
      eapply base_good_over_boundary; eauto; omega.
    } { (* i >= length base, j < length base, i + j >= length base *)
      do 2 rewrite map_nth_default_base_high by omega.
      remember (i - length base)%nat as i'.
      replace (i + j - length base)%nat with (j + i')%nat by omega.
      replace (2 ^ k * nth_default 0 base i' * nth_default 0 base j)
         with (2 ^ k * (nth_default 0 base j * nth_default 0 base i'))
         by ring.
      eapply base_good_over_boundary; eauto; omega.
    }
  Qed.
  Instance ExtBaseVector : BaseSystem.BaseVector ext_base := {
    base_positive := ext_base_positive;
    b0_1 := b0_1;
    base_good := ext_base_good
  }.
End ExtendedBaseVector.

Print ExtBaseVector.
Section PseudoMersenneBase.
  Context `(prm :PseudoMersenneBaseParams).

  Definition T := BaseSystem.digits.
  Definition decode (us : T) : F modulus := ZToField (BaseSystem.decode base us).
  Local Hint Unfold decode.
  Definition rep (us : T) (x : F modulus) := (length us <= length base)%nat /\ decode us = x.
  Local Notation "u '~=' x" := (rep u x) (at level 70).
  Local Hint Unfold rep.

  Lemma rep_decode : forall us x, us ~= x -> decode us = x.
  Proof.
    autounfold; intuition.
  Qed.

  Definition encode (x : F modulus) := BaseSystem.encode x.

  Lemma encode_rep : forall x : F modulus, encode x ~= x.
  Proof.
    intros. unfold encode, rep.
    split. {
      unfold encode; simpl.
      apply base_length_nonzero.
      assumption.
    } {
      unfold decode.
      rewrite BaseSystem.encode_rep.
      apply ZToField_FieldToZ.
      assumption.
    }
  Qed.

  Lemma add_rep : forall u v x y, u ~= x -> v ~= y -> BaseSystem.add u v ~= (x+y)%F.
  Proof.
    autounfold; intuition. {
      unfold add.
      rewrite BaseSystem.add_length_le_max.
      case_max; try rewrite Max.max_r; omega.
    }
    unfold decode in *; unfold BaseSystem.decode in *.
    rewrite BaseSystem.add_rep.
    rewrite ZToField_add.
    subst; auto.
  Qed.

  Lemma sub_rep : forall u v x y, u ~= x -> v ~= y -> BaseSystem.sub u v ~= (x-y)%F.
  Proof.
    autounfold; intuition. {
      rewrite BaseSystem.sub_length_le_max.
      case_max; try rewrite Max.max_r; omega.
    }
    unfold decode in *; unfold BaseSystem.decode in *.
    rewrite BaseSystem.sub_rep.
    rewrite ZToField_sub.
    subst; auto.
  Qed.

  Lemma decode_short : forall (us : T), 
    (length us <= length base)%nat ->
    BaseSystem.decode base us = BaseSystem.decode (ext_base base prm) us.
  Proof.
    intros.
    unfold BaseSystem.decode, BaseSystem.decode'.
    rewrite combine_truncate_r.
    rewrite (combine_truncate_r us (ext_base base prm)).
    f_equal; f_equal.
    unfold ext_base.
    rewrite firstn_app_inleft; auto; omega.
  Qed.

  Lemma extended_base_length:
      length (ext_base base prm) = (length base + length base)%nat.
  Proof.
    unfold ext_base; rewrite app_length; rewrite map_length; auto.
  Qed.

  Lemma mul_rep_extended : forall (us vs : T),
      (length us <= length base)%nat -> 
      (length vs <= length base)%nat ->
      (BaseSystem.decode base us) * (BaseSystem.decode base vs) = BaseSystem.decode (ext_base base prm) (BaseSystem.mul (ext_base base prm) us vs).
  Proof.
      intros. 
      rewrite BaseSystem.mul_rep by (apply ExtBaseVector || unfold ext_base; simpl_list; omega).
      f_equal; rewrite decode_short; auto.
  Qed.

  (* Converts from length of extended base to length of base by reduction modulo M.*)
  Definition reduce (us : T) : T :=
    let high := skipn (length base) us in
    let low := firstn (length base) us in
    let wrap := map (Z.mul c) high in
    BaseSystem.add low wrap.

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
    rewrite <- modulus_pseudomersenne.
    rewrite Z.mul_comm.
    rewrite mod_mult_plus; auto using modulus_nonzero.
    rewrite <- Zplus_mod; auto.
  Qed.

  Lemma extended_shiftadd: forall (us : T),
    BaseSystem.decode (ext_base base prm) us =
      BaseSystem.decode base (firstn (length base) us)
      + (2^k * BaseSystem.decode base (skipn (length base) us)).
  Proof.
    intros.
    unfold BaseSystem.decode; rewrite <- BaseSystem.mul_each_rep.
    unfold ext_base.
    replace (map (Z.mul (2 ^ k)) base) with (BaseSystem.mul_each (2 ^ k) base) by auto.
    rewrite BaseSystem.base_mul_app.
    rewrite <- BaseSystem.mul_each_rep; auto.
  Qed.

  Lemma reduce_rep : forall us,
    BaseSystem.decode base (reduce us) mod modulus =
    BaseSystem.decode (ext_base base prm) us mod modulus.
  Proof.
    intros.
    rewrite extended_shiftadd.
    rewrite pseudomersenne_add.
    unfold reduce.
    remember (firstn (length base) us) as low.
    remember (skipn (length base) us) as high.
    unfold BaseSystem.decode.
    rewrite BaseSystem.add_rep.
    replace (map (Z.mul c) high) with (BaseSystem.mul_each c high) by auto.
    rewrite BaseSystem.mul_each_rep; auto.
  Qed.

  Lemma reduce_length : forall us, 
      (length us <= length (ext_base base prm))%nat ->
      (length (reduce us) <= length (base))%nat.
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
    rewrite BaseSystem.add_trailing_zeros; auto.
    rewrite (BaseSystem.add_same_length _ _ (length low)); auto.
    rewrite app_length.
    rewrite BaseSystem.length_zeros; intuition.
  Qed.

  Definition mul (us vs : T) := reduce (BaseSystem.mul (ext_base base prm) us vs).
  Lemma mul_rep : forall u v x y, u ~= x -> v ~= y -> mul u v ~= (x*y)%F.
  Proof.
    autounfold; unfold mul; intuition.
    {
      apply reduce_length.
      rewrite BaseSystem.mul_length, extended_base_length.
      omega.
    } {
      rewrite ZToField_mod, reduce_rep, <-ZToField_mod.
      rewrite BaseSystem.mul_rep by
        (apply ExtBaseVector || rewrite extended_base_length; omega).
      subst.
      do 2 rewrite decode_short by auto.
      apply ZToField_mul.
    }
  Qed.

  Definition add_to_nth n (x:Z) xs :=
    set_nth n (x + nth_default 0 xs n) xs.
  Hint Unfold add_to_nth.

  (* i must be in the domain of base *)
  Definition cap i := 
    if eq_nat_dec i (pred (length base))
    then (2^k) / nth_default 0 base i
    else nth_default 0 base (S i) / nth_default 0 base i.

  Definition carry_simple i := fun us =>
    let di := nth_default 0 us      i in
    let us' := set_nth i (di mod cap i) us in
    add_to_nth (S i) (      (di / cap i)) us'.

  Definition carry_and_reduce i := fun us =>
    let di := nth_default 0 us      i in
    let us' := set_nth i (di mod cap i) us in
    add_to_nth   0   (c * (di / cap i)) us'.

  Definition carry i : T -> T := 
    if eq_nat_dec i (pred (length base))
    then carry_and_reduce i
    else carry_simple i.

  (* TODO: move to BaseSystemProofs *)
  Lemma decode'_splice : forall xs ys bs,
    BaseSystem.decode' bs (xs ++ ys) = 
    BaseSystem.decode' (firstn (length xs) bs) xs + 
    BaseSystem.decode'  (skipn (length xs) bs) ys.
  Proof.
    unfold BaseSystem.decode'.
    induction xs; destruct ys, bs; boring.
    + rewrite combine_truncate_r.
      do 2 rewrite Z.add_0_r; auto.
    + unfold BaseSystem.accumulate.
      apply Z.add_assoc.
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
      do 2 rewrite BaseSystem.decode_base_nil.
      ring_simplify; auto.
    } {
      rewrite (skipn_nth_default n base 0) by omega.
      do 2 rewrite BaseSystem.decode'_cons.
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

  Lemma base_length_lt_pred : (pred (length base) < length base)%nat.
  Proof.
    pose proof (base_length_nonzero base); omega.
  Qed.
  Hint Resolve base_length_lt_pred.

  Lemma cap_positive: forall i, (i < length base)%nat -> cap i > 0.
  Proof.
    unfold cap; intros; break_if. {
      apply div_positive_gt_0; try (subst; apply base_tail_matches_modulus). {
        rewrite <- two_p_equiv.
        apply two_p_gt_ZERO.
        apply k_nonneg.
      } {
        apply nth_default_base_positive; subst; auto.
      }
    } {
      apply div_positive_gt_0; try (apply base_succ; omega); 
        try (apply nth_default_base_positive; omega).
    }
  Qed.

  Lemma cap_div_mod : forall us i, (i < (pred (length base)))%nat ->
    let di := nth_default 0 us i in
    (di - (di mod cap i)) * nth_default 0 base i = 
    (di / cap i)          * nth_default 0 base (S i).
  Proof.
    intros.
    rewrite (Z_div_mod_eq di (cap i)) at 1 by (apply cap_positive; omega);
      ring_simplify.
    unfold cap; break_if; intuition.
    rewrite base_succ_div_mult at 4 by omega; ring.
  Qed.

  Lemma carry_simple_decode_eq : forall i us,
    (length us = length base) ->
    (i < (pred (length base)))%nat ->
    BaseSystem.decode base (carry_simple i us) = BaseSystem.decode base us.
  Proof.
    unfold carry_simple. intros.
    rewrite add_to_nth_sum by (rewrite length_set_nth; omega).
    rewrite set_nth_sum by omega.
    rewrite <- cap_div_mod by auto; ring_simplify; auto.
  Qed.

  Lemma two_k_div_mul_last :
     2 ^ k = nth_default 0 base (pred (length base)) *
    (2 ^ k / nth_default 0 base (pred (length base))).
  Proof.
    intros.
    pose proof base_tail_matches_modulus.
    rewrite (Z_div_mod_eq (2 ^ k) (nth_default 0 base (pred (length base)))) at 1 by
      (apply nth_default_base_positive; auto); omega.
  Qed.
 
  Lemma cap_div_mod_reduce : forall us,
    let i  := pred (length base) in
    let di := nth_default 0 us i in
    (di - (di mod cap i)) * nth_default 0 base i =
    (di / cap i)          * 2 ^ k.
  Proof.
    intros.
    rewrite (Z_div_mod_eq di (cap i)) at 1 by
      (apply cap_positive; auto); ring_simplify.
    unfold cap; break_if; intuition.
    rewrite Z.mul_comm, Z.mul_assoc.
    subst i; rewrite <- two_k_div_mul_last; ring.
  Qed.

  Lemma carry_decode_eq_reduce : forall us,
    (length us = length base) ->
    BaseSystem.decode base (carry_and_reduce (pred (length base)) us) mod modulus
    = BaseSystem.decode base us mod modulus.
  Proof.
    unfold carry_and_reduce; intros.
    pose proof (base_length_nonzero base).
    rewrite add_to_nth_sum by (rewrite length_set_nth; omega).
    rewrite set_nth_sum by omega.
    rewrite Zplus_comm, <- Z.mul_assoc.
    rewrite <- pseudomersenne_add.
    rewrite BaseSystem.b0_1.
    rewrite (Z.mul_comm (2 ^ k)).
    rewrite <- Zred_factor0.
    rewrite <- cap_div_mod_reduce by auto.
    do 2 rewrite Zmult_minus_distr_r.
    f_equal.
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

  Definition carry_sequence is us := fold_right carry us is.

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
End PseudoMersenneBase.
