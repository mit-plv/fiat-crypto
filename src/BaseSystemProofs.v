Require Import Coq.Lists.List Coq.micromega.Psatz.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.BaseSystem.
Require Import Crypto.Util.Notations.
Local Open Scope Z.

Local Infix ".+" := add.

Local Hint Extern 1 (@eq Z _ _) => ring.

Section BaseSystemProofs.
  Context `(base_vector : BaseVector).

  Lemma decode'_truncate : forall bs us, decode' bs us = decode' bs (firstn (length bs) us).
  Proof.
    unfold decode'; intros; f_equal; apply combine_truncate_l.
  Qed.

  Lemma decode'_splice : forall xs ys bs,
    decode' bs (xs ++ ys) =
    decode' (firstn (length xs) bs) xs + decode'  (skipn (length xs) bs) ys.
  Proof.
    unfold decode'.
    induction xs; destruct ys, bs; boring.
    + rewrite combine_truncate_r.
      do 2 rewrite Z.add_0_r; auto.
    + unfold accumulate.
      apply Z.add_assoc.
  Qed.

  Lemma add_rep : forall bs us vs, decode' bs (add us vs) = decode' bs us + decode' bs vs.
  Proof.
    unfold decode', accumulate; induction bs; destruct us, vs; boring; ring.
  Qed.

  Lemma decode_nil : forall bs, decode' bs nil = 0.
    auto.
  Qed.
  Hint Rewrite decode_nil.

  Lemma decode_base_nil : forall us, decode' nil us = 0.
  Proof.
    intros; rewrite decode'_truncate; auto.
  Qed.
  Hint Rewrite decode_base_nil.

  Lemma mul_each_rep : forall bs u vs,
    decode' bs (mul_each u vs) = u * decode' bs vs.
  Proof.
    unfold decode', accumulate; induction bs; destruct vs; boring; ring.
  Qed.

  Lemma base_eq_1cons: base = 1 :: skipn 1 base.
  Proof.
    pose proof (b0_1 0) as H.
    destruct base; compute in H; try discriminate; boring.
  Qed.

  Lemma decode'_cons : forall x1 x2 xs1 xs2,
    decode' (x1 :: xs1) (x2 :: xs2) = x1 * x2 + decode' xs1 xs2.
  Proof.
    unfold decode', accumulate; boring; ring.
  Qed.
  Hint Rewrite decode'_cons.

  Lemma decode_cons : forall x us,
    decode base (x :: us) = x + decode base (0 :: us).
  Proof.
    unfold decode; intros.
    rewrite base_eq_1cons.
    autorewrite with core; ring_simplify; auto.
  Qed.

  Lemma decode'_map_mul : forall v xs bs,
    decode' (map (Z.mul v) bs) xs =
    Z.mul v (decode' bs xs).
  Proof.
    unfold decode'.
    induction xs; destruct bs; boring.
    unfold accumulate; simpl; nia.
  Qed.

  Lemma decode_map_mul : forall v xs,
    decode (map (Z.mul v) base) xs =
    Z.mul v (decode base xs).
  Proof.
    unfold decode; intros; apply decode'_map_mul.
  Qed.

  Lemma sub_rep : forall bs us vs, decode' bs (sub us vs) = decode' bs us - decode' bs vs.
  Proof.
    induction bs; destruct us; destruct vs; boring; ring.
  Qed.

  Lemma nth_default_base_nonzero : forall d, d <> 0 ->
    forall i, nth_default d base i <> 0.
  Proof.
    intros.
    rewrite nth_default_eq.
    destruct (nth_in_or_default i base d).
    + auto using Z.positive_is_nonzero, base_positive.
    + congruence.
  Qed.

  Lemma nth_default_base_pos : forall d, 0 < d ->
    forall i,  0 < nth_default d base i.
  Proof.
    intros.
    rewrite nth_default_eq.
    destruct (nth_in_or_default i base d).
    + apply Z.gt_lt; auto using base_positive.
    + congruence.
  Qed.

  Lemma mul_each_base : forall us bs c,
      decode' bs (mul_each c us) = decode' (mul_each c bs) us.
  Proof.
    induction us; destruct bs; boring; ring.
  Qed.

  Hint Rewrite (@nth_default_nil Z).
  Hint Rewrite (@firstn_nil Z).
  Hint Rewrite (@skipn_nil Z).

  Lemma base_app : forall us low high,
      decode' (low ++ high) us = decode' low (firstn (length low) us) + decode' high (skipn (length low) us).
  Proof.
    induction us; destruct low; boring.
  Qed.

  Lemma base_mul_app : forall low c us,
      decode' (low ++ mul_each c low) us = decode' low (firstn (length low) us) +
      c * decode' low (skipn (length low) us).
  Proof.
    intros.
    rewrite base_app; f_equal.
    rewrite <- mul_each_rep.
    rewrite mul_each_base.
    reflexivity.
  Qed.

  Lemma zeros_rep : forall bs n, decode' bs (zeros n) = 0.
    induction bs; destruct n; boring.
  Qed.
  Lemma length_zeros : forall n, length (zeros n) = n.
    induction n; boring.
  Qed.
  Hint Rewrite length_zeros.

  Lemma app_zeros_zeros : forall n m, zeros n ++ zeros m = zeros (n + m)%nat.
  Proof.
    induction n; boring.
  Qed.
  Hint Rewrite app_zeros_zeros.

  Lemma zeros_app0 : forall m, zeros m ++ 0 :: nil = zeros (S m).
  Proof.
    induction m; boring.
  Qed.
  Hint Rewrite zeros_app0.

  Lemma nth_default_zeros : forall n i, nth_default 0 (BaseSystem.zeros n) i = 0.
  Proof.
    induction n; intros; [ cbv [BaseSystem.zeros]; apply nth_default_nil | ].
    rewrite <-zeros_app0, nth_default_app.
    rewrite length_zeros.
    destruct (lt_dec i n); auto.
    destruct (eq_nat_dec i n); subst.
    + rewrite Nat.sub_diag; apply nth_default_cons.
    + apply nth_default_out_of_bounds.
      cbv [length]; omega.
  Qed.

  Lemma rev_zeros : forall n, rev (zeros n) = zeros n.
  Proof.
    induction n; boring.
  Qed.
  Hint Rewrite rev_zeros.

  Hint Unfold nth_default.

  Lemma decode_single : forall n bs x,
    decode' bs (zeros n ++ x :: nil) = nth_default 0 bs n * x.
  Proof.
    induction n; destruct bs; boring.
  Qed.
  Hint Rewrite decode_single.

  Lemma peel_decode : forall xs ys x y, decode' (x::xs) (y::ys) = x*y + decode' xs ys.
  Proof.
    boring.
  Qed.
  Hint Rewrite zeros_rep peel_decode.

  Lemma decode_highzeros : forall xs bs n, decode' bs (xs ++ zeros n) = decode' bs xs.
  Proof.
    induction xs; destruct bs; boring.
  Qed.

  Lemma mul_bi'_zeros : forall n m, mul_bi' base n (zeros m) = zeros m.
    induction m; boring.
  Qed.
  Hint Rewrite mul_bi'_zeros.

  Lemma nth_error_base_nonzero : forall n x,
    nth_error base n = Some x -> x <> 0.
  Proof.
    eauto using (@nth_error_value_In Z), Z.gt0_neq0, base_positive.
  Qed.

  Hint Rewrite plus_0_r.

  Lemma mul_bi_single : forall m n x,
    (n + m < length base)%nat ->
    decode base (mul_bi base n (zeros m ++ x :: nil)) = nth_default 0 base m * x * nth_default 0 base n.
  Proof.
    unfold mul_bi, decode.
    destruct m; simpl; simpl_list; simpl; intros. {
      pose proof nth_error_base_nonzero as nth_nonzero.
      case_eq base; [intros; boring | intros z l base_eq].
      specialize (b0_1 0); intro b0_1'.
      rewrite base_eq in *.
      rewrite nth_default_cons in b0_1'.
      rewrite b0_1' in *.
      unfold crosscoef.
      autounfold; autorewrite with core.
      unfold nth_default.
      nth_tac.
      rewrite Z.mul_1_r.
      rewrite Z_div_same_full.
      destruct x; ring.
      eapply nth_nonzero; eauto.
    } {
      ssimpl_list.
      autorewrite with core.
      rewrite app_assoc.
      autorewrite with core.
      unfold crosscoef; simpl; ring_simplify.
      rewrite Nat.add_1_r.
      rewrite base_good by auto.
      rewrite Z_div_mult by (apply base_positive; rewrite nth_default_eq; apply nth_In; auto).
      rewrite <- Z.mul_assoc.
      rewrite <- Z.mul_comm.
      rewrite <- Z.mul_assoc.
      rewrite <- Z.mul_assoc.
      destruct (Z.eq_dec x 0); subst; try ring.
      rewrite Z.mul_cancel_l by auto.
      rewrite <- base_good by auto.
      ring.
      }
  Qed.

  Lemma set_higher' : forall vs x, vs++x::nil = vs .+ (zeros (length vs) ++ x :: nil).
    induction vs; boring; f_equal; ring.
  Qed.

  Lemma set_higher : forall bs vs x,
    decode' bs (vs++x::nil) = decode' bs vs + nth_default 0 bs (length vs) * x.
  Proof.
    intros.
    rewrite set_higher'.
    rewrite add_rep.
    f_equal.
    apply decode_single.
  Qed.

  Lemma zeros_plus_zeros : forall n, zeros n = zeros n .+ zeros n.
    induction n; auto.
    simpl; f_equal; auto.
  Qed.

  Lemma mul_bi'_n_nil : forall n, mul_bi' base n nil = nil.
  Proof.
    unfold mul_bi; auto.
  Qed.
  Hint Rewrite mul_bi'_n_nil.

  Lemma add_nil_l : forall us, nil .+ us = us.
    induction us; auto.
  Qed.
  Hint Rewrite add_nil_l.

  Lemma add_nil_r : forall us, us .+ nil = us.
    induction us; auto.
  Qed.
  Hint Rewrite add_nil_r.

  Lemma add_first_terms : forall us vs a b,
    (a :: us) .+ (b :: vs) = (a + b) :: (us .+ vs).
    auto.
  Qed.
  Hint Rewrite add_first_terms.

  Lemma mul_bi'_cons : forall n x us,
    mul_bi' base n (x :: us) = x * crosscoef base n (length us) :: mul_bi' base n us.
  Proof.
    unfold mul_bi'; auto.
  Qed.

  Lemma add_same_length : forall us vs l, (length us = l) -> (length vs = l) ->
    length (us .+ vs) = l.
  Proof.
    induction us, vs; boring.
    erewrite (IHus vs (pred l)); boring.
  Qed.

  Hint Rewrite app_nil_l.
  Hint Rewrite app_nil_r.

  Lemma add_snoc_same_length : forall l us vs a b,
    (length us = l) -> (length vs = l) ->
    (us ++ a :: nil) .+ (vs ++ b :: nil) = (us .+ vs) ++ (a + b) :: nil.
  Proof.
    induction l, us, vs; boring; discriminate.
  Qed.

  Lemma mul_bi'_add : forall us n vs l
    (Hlus: length us = l)
    (Hlvs: length vs = l),
    mul_bi' base n (rev (us .+ vs)) =
    mul_bi' base n (rev us) .+ mul_bi' base n (rev vs).
  Proof.
    (* TODO(adamc): please help prettify this *)
    induction us using rev_ind;
      try solve [destruct vs; boring; congruence].
    destruct vs using rev_ind; boring; clear IHvs; simpl_list.
    erewrite (add_snoc_same_length (pred l) us vs _ _); simpl_list.
    repeat rewrite mul_bi'_cons; rewrite add_first_terms; simpl_list.
    rewrite (IHus n vs (pred l)).
    replace (length us) with (pred l).
    replace (length vs) with (pred l).
    rewrite (add_same_length us vs (pred l)).
    f_equal; ring.

    erewrite length_snoc; eauto.
    erewrite length_snoc; eauto.
    erewrite length_snoc; eauto.
    erewrite length_snoc; eauto.
    erewrite length_snoc; eauto.
    erewrite length_snoc; eauto.
    erewrite length_snoc; eauto.
    erewrite length_snoc; eauto.
   Qed.

  Lemma zeros_cons0 : forall n, 0 :: zeros n = zeros (S n).
    auto.
  Qed.

  Lemma add_leading_zeros : forall n us vs,
    (zeros n ++ us) .+ (zeros n ++ vs) = zeros n ++ (us .+ vs).
  Proof.
    induction n; boring.
  Qed.

  Lemma rev_add_rev : forall us vs l, (length us = l) -> (length vs = l) ->
    (rev us) .+ (rev vs) = rev (us .+ vs).
  Proof.
    induction us, vs; boring; try solve [subst; discriminate].
    rewrite (add_snoc_same_length (pred l) _ _ _ _) by (subst; simpl_list; omega).
    rewrite (IHus vs (pred l)) by omega; auto.
  Qed.
  Hint Rewrite rev_add_rev.

  Lemma mul_bi'_length : forall us n, length (mul_bi' base n us) = length us.
  Proof.
    induction us, n; boring.
  Qed.
  Hint Rewrite mul_bi'_length.

  Lemma add_comm : forall us vs, us .+ vs = vs .+ us.
  Proof.
    induction us, vs; boring; f_equal; auto.
  Qed.

  Hint Rewrite rev_length.

  Lemma mul_bi_add_same_length : forall n us vs l,
    (length us = l) -> (length vs = l) ->
    mul_bi base n (us .+ vs) = mul_bi base n us .+ mul_bi base n vs.
  Proof.
    unfold mul_bi; boring.
    rewrite add_leading_zeros.
    erewrite mul_bi'_add; boring.
    erewrite rev_add_rev; boring.
  Qed.

  Lemma add_zeros_same_length : forall us, us .+ (zeros (length us)) = us.
  Proof.
    induction us; boring; f_equal; omega.
  Qed.

  Hint Rewrite add_zeros_same_length.
  Hint Rewrite minus_diag.

  Lemma add_trailing_zeros : forall us vs, (length us >= length vs)%nat ->
    us .+ vs = us .+ (vs ++ (zeros (length us - length vs)%nat)).
  Proof.
    induction us, vs; boring; f_equal; boring.
  Qed.

  Lemma length_add_ge : forall us vs, (length us >= length vs)%nat ->
    (length (us .+ vs) <= length us)%nat.
  Proof.
    intros.
    rewrite add_trailing_zeros by trivial.
    erewrite add_same_length by (pose proof app_length; boring); omega.
  Qed.

  Lemma add_length_le_max : forall us vs,
      (length (us .+ vs) <= max (length us) (length vs))%nat.
  Proof.
    intros; case_max; (rewrite add_comm; apply length_add_ge; omega) ||
                                        (apply length_add_ge; omega) .
  Qed.

  Lemma sub_nil_length: forall us : digits, length (sub nil us) = length us.
  Proof.
     induction us; boring.
  Qed.

  Lemma sub_length : forall us vs,
      (length (sub us vs) = max (length us) (length vs))%nat.
  Proof.
    induction us, vs; boring.
    rewrite sub_nil_length; auto.
  Qed.

  Lemma mul_bi_length : forall us n, length (mul_bi base n us) = (length us + n)%nat.
  Proof.
    pose proof mul_bi'_length; unfold mul_bi.
    destruct us; repeat progress (simpl_list; boring).
  Qed.
  Hint Rewrite mul_bi_length.

  Lemma mul_bi_trailing_zeros : forall m n us,
    mul_bi base n us ++ zeros m = mul_bi base n (us ++ zeros m).
  Proof.
    unfold mul_bi.
    induction m; intros; try solve [boring].
    rewrite <- zeros_app0.
    rewrite app_assoc.
    repeat progress (boring; rewrite rev_app_distr).
  Qed.

  Lemma mul_bi_add_longer : forall n us vs,
    (length us >= length vs)%nat ->
    mul_bi base n (us .+ vs) = mul_bi base n us .+ mul_bi base n vs.
  Proof.
    boring.
    rewrite add_trailing_zeros by auto.
    rewrite (add_trailing_zeros (mul_bi base n us) (mul_bi base n vs))
      by (repeat (rewrite mul_bi_length); omega).
    erewrite mul_bi_add_same_length by
      (eauto; simpl_list; rewrite length_zeros; omega).
    rewrite mul_bi_trailing_zeros.
    repeat (f_equal; boring).
  Qed.

  Lemma mul_bi_add : forall n us vs,
    mul_bi base n (us .+ vs) = (mul_bi base n  us) .+ (mul_bi base n vs).
  Proof.
    intros; pose proof mul_bi_add_longer.
    destruct (le_ge_dec (length us) (length vs)). {
      rewrite add_comm.
      rewrite (add_comm (mul_bi base n us)).
      boring.
    } {
      boring.
    }
  Qed.

  Lemma mul_bi_rep : forall i vs,
    (i + length vs < length base)%nat ->
    decode base (mul_bi base i vs) = decode base vs * nth_default 0 base i.
  Proof.
    unfold decode.
    induction vs using rev_ind; intros; try solve [unfold mul_bi; boring].
    assert (i + length vs < length base)%nat by
      (rewrite app_length in *; boring).

    rewrite set_higher.
    ring_simplify.
    rewrite <- IHvs by auto; clear IHvs.
    rewrite <- mul_bi_single by auto.
    rewrite <- add_rep.
    rewrite <- mul_bi_add.
    rewrite set_higher'.
    auto.
  Qed.

  Local Notation mul' := (mul' base).
  Local Notation mul := (mul base).

  Lemma mul'_rep : forall us vs,
    (length us + length vs <= length base)%nat ->
    decode base (mul' (rev us) vs) = decode base us * decode base vs.
  Proof.
    unfold decode.
    induction us using rev_ind; boring.

    assert (length us + length vs < length base)%nat by
      (rewrite app_length in *; boring).

    ssimpl_list.
    rewrite add_rep.
    boring.
    rewrite set_higher.
    rewrite mul_each_rep.
    rewrite mul_bi_rep by auto.
    unfold decode; ring.
  Qed.

  Lemma mul_rep : forall us vs,
    (length us + length vs <= length base)%nat ->
    decode base (mul us vs) = decode base us * decode base vs.
  Proof.
    exact mul'_rep.
  Qed.

  Lemma mul'_length: forall us vs,
      (length (mul' us vs) <= length us + length vs)%nat.
  Proof.
    pose proof add_length_le_max.
    induction us; boring.
    unfold mul_each.
    simpl_list; case_max; boring; omega.
  Qed.

  Lemma mul_length: forall us vs,
      (length (mul us vs) <= length us + length vs)%nat.
  Proof.
    intros; unfold BaseSystem.mul.
    rewrite mul'_length.
    rewrite rev_length; omega.
  Qed.

  Lemma add_length_exact : forall us vs,
      length (us .+ vs) = max (length us) (length vs).
  Proof.
    induction us; destruct vs; boring.
  Qed.

  Hint Rewrite add_length_exact : distr_length.

  Lemma mul'_length_exact_full: forall us vs,
      (length (mul' us vs) = match length us with
                             | 0 => 0%nat
                             | _ => pred (length us + length vs)
                             end)%nat.
  Proof.
    induction us; intros; try solve [boring].
    unfold BaseSystem.mul'; fold mul'.
    unfold mul_each.
    rewrite add_length_exact, map_length, mul_bi_length, length_cons.
    destruct us.
    + rewrite Max.max_0_r. simpl; omega.
    + rewrite Max.max_l; [ omega | ].
      rewrite IHus by ( congruence || simpl in *; omega).
      simpl; omega.
  Qed.

  Hint Rewrite mul'_length_exact_full : distr_length.

  (* TODO(@jadephilipoom, from jgross): one of these conditions isn't
  needed.  Should it be dropped, or was there a reason to keep it? *)
  Lemma mul'_length_exact: forall us vs,
      (length us <= length vs)%nat -> us <> nil ->
      (length (mul' us vs) = pred (length us + length vs))%nat.
  Proof.
    intros; rewrite mul'_length_exact_full; destruct us; simpl; congruence.
  Qed.

  Lemma mul_length_exact_full: forall us vs,
      (length (mul us vs) = match length us with
                            | 0 => 0
                            | _ => pred (length us + length vs)
                            end)%nat.
  Proof.
    intros; unfold BaseSystem.mul; autorewrite with distr_length; reflexivity.
  Qed.

  Hint Rewrite mul_length_exact_full : distr_length.

  (* TODO(@jadephilipoom, from jgross): one of these conditions isn't
  needed.  Should it be dropped, or was there a reason to keep it? *)
  Lemma mul_length_exact: forall us vs,
      (length us <= length vs)%nat -> us <> nil ->
      (length (mul us vs) = pred (length us + length vs))%nat.
  Proof.
    intros; unfold BaseSystem.mul.
    rewrite mul'_length_exact; rewrite ?rev_length; try omega.
    intro rev_nil.
    match goal with H : us <> nil |- _ => apply H end.
    apply length0_nil; rewrite <-rev_length, rev_nil.
    reflexivity.
  Qed.
  Definition encode'_zero z max  : encode' base z max 0%nat = nil := eq_refl.
  Definition encode'_succ z max i : encode' base z max (S i) =
    encode' base z max i ++ ((z mod (nth_default max base (S i))) / (nth_default max base i)) :: nil := eq_refl.
  Opaque encode'.
  Hint Resolve encode'_zero encode'_succ.

  Lemma encode'_length : forall z max i, length (encode' base z max i) = i.
  Proof.
    induction i; auto.
    rewrite encode'_succ, app_length, IHi.
    cbv [length].
    omega.
  Qed.

  (* States that each element of the base is a positive integer multiple of the previous
     element, and that max is a positive integer multiple of the last element. Ideally this
     would have a better name. *)
  Definition base_max_succ_divide max := forall i, (S i <= length base)%nat ->
    Z.divide (nth_default max base i) (nth_default max base (S i)).

  Lemma encode'_spec : forall z max, 0 < max ->
    base_max_succ_divide max -> forall i, (i <= length base)%nat ->
    decode' base (encode' base z max i) = z mod (nth_default max base i).
  Proof.
    induction i; intros.
    + rewrite encode'_zero, b0_1, Z.mod_1_r.
      apply decode_nil.
    + rewrite encode'_succ, set_higher.
      rewrite IHi by omega.
      rewrite encode'_length, (Z.add_comm (z mod nth_default max base i)).
      replace (nth_default 0 base i) with (nth_default max base i) by
        (rewrite !nth_default_eq; apply nth_indep; omega).
      match goal with H1 : base_max_succ_divide _, H2 : (S i <= length base)%nat, H3 : 0 < max |- _ =>
        specialize (H1 i H2);
        rewrite (Znumtheory.Zmod_div_mod _ _ _ (nth_default_base_pos _ H _)
                                               (nth_default_base_pos _ H _) H0) end.
      rewrite <-Z.div_mod by (apply Z.positive_is_nonzero, Z.lt_gt; auto using nth_default_base_pos).
      reflexivity.
  Qed.

  Lemma encode_rep : forall z max, 0 <= z < max ->
    base_max_succ_divide max -> decode base (encode base z max) = z.
  Proof.
    unfold encode; intros.
    rewrite encode'_spec, nth_default_out_of_bounds by (omega || auto).
    apply Z.mod_small; omega.
  Qed.

End BaseSystemProofs.

Hint Rewrite @add_length_exact @mul'_length_exact_full @mul_length_exact_full @encode'_length @sub_length : distr_length.

Section MultiBaseSystemProofs.
  Context base0 (base_vector0 : @BaseVector base0) base1 (base_vector1 : @BaseVector base1).

  Lemma decode_short_initial : forall (us : digits),
      (firstn (length us) base0 = firstn (length us) base1)
      -> decode base0 us = decode base1 us.
  Proof.
    intros us H.
    unfold decode, decode'.
    rewrite (combine_truncate_r us base0), (combine_truncate_r us base1), H.
    reflexivity.
  Qed.

  Lemma mul_rep_two_base : forall (us vs : digits),
      (length us + length vs <= length base1)%nat
      -> firstn (length us) base0 = firstn (length us) base1
      -> firstn (length vs) base0 = firstn (length vs) base1
      -> (decode base0 us) * (decode base0 vs) = decode base1 (mul base1 us vs).
  Proof.
      intros.
      rewrite mul_rep by trivial.
      apply f_equal2; apply decode_short_initial; assumption.
  Qed.

End MultiBaseSystemProofs.
