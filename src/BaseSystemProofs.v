Require Import List.
Require Import Util.ListUtil Util.CaseUtil Util.ZUtil.
Require Import ZArith.ZArith ZArith.Zdiv.
Require Import Omega NPeano Arith.
Require Import Crypto.BaseSystem.
Local Open Scope Z.

Local Infix ".+" := add (at level 50).

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

  Lemma sub_rep : forall bs us vs, decode' bs (sub us vs) = decode' bs us - decode' bs vs.
  Proof.
    induction bs; destruct us; destruct vs; boring; ring.
  Qed.

  Lemma encode_rep : forall z, decode base (encode z) = z.
  Proof.
    pose proof base_eq_1cons.
    unfold decode, encode; destruct z; boring.
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
    eauto using (@nth_error_value_In Z), Zgt0_neq0, base_positive.
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

  Lemma sub_length_le_max : forall us vs,
      (length (sub us vs) <= max (length us) (length vs))%nat.
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

  (* mul' is multiplication with the FIRST ARGUMENT REVERSED *)
  Fixpoint mul' (usr vs:digits) : digits :=
    match usr with
      | u::usr' =>
        mul_each u (mul_bi base (length usr') vs) .+ mul' usr' vs
      | _ => nil
    end.
  Definition mul us := mul' (rev us).

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
    intros; unfold mul.
    rewrite mul'_length.
    rewrite rev_length; omega.
  Qed.


End BaseSystemProofs.
