Require Import List.
Require Import Util.ListUtil.
Require Import ZArith.ZArith ZArith.Zdiv.
Require Import Omega NPeano Arith.

Local Open Scope Z.

Lemma pos_pow_nat_pos : forall x n, 
  Z.pos x ^ Z.of_nat n > 0.
  do 2 (intros; induction n; subst; simpl in *; auto with zarith).
  rewrite <- Pos.add_1_r, Zpower_pos_is_exp.
  apply Zmult_gt_0_compat; auto; reflexivity.
Qed.

Module Type BaseCoefs.
  (** [BaseCoefs] represent the weights of each digit in a positional number system, with the weight of least significant digit presented first. The following requirements on the base are preconditions for using it with BaseSystem. *)
  Parameter base : list Z.
  Axiom base_positive : forall b, In b base -> b > 0. (* nonzero would probably work too... *)
  Axiom b0_1 : forall x, nth_default x base 0 = 1.
  Axiom base_good :
    forall i j, (i+j < length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
End BaseCoefs.

Module BaseSystem (Import B:BaseCoefs).
  (** [BaseSystem] implements an constrained positional number system.
      A wide variety of bases are supported: the base coefficients are not
      required to be powers of 2, and it is NOT necessarily the case that
      $b_{i+j} = b_i b_j$. Implementations of addition and multiplication are
      provided, with focus on near-optimal multiplication performance on
      non-trivial but small operands: maybe 10 32-bit integers or so. This
      module does not handle carries automatically: if no restrictions are put
      on the use of a [BaseSystem], each digit is unbounded. This has nothing
      to do with modular arithmetic either.
  *)
  Definition digits : Type := list Z.

  Definition accumulate p acc := fst p * snd p + acc.
  Definition decode' bs u  := fold_right accumulate 0 (combine u bs).
  Definition decode := decode' base.
  Hint Unfold accumulate.
  (* Does not carry; z becomes the lowest and only digit. *)
  Definition encode (z : Z) := z :: nil.

  Lemma decode'_truncate : forall bs us, decode' bs us = decode' bs (firstn (length bs) us).
  Proof.
    unfold decode, decode'; intros; f_equal; apply combine_truncate_l.
  Qed.
  
  Fixpoint add (us vs:digits) : digits :=
    match us,vs with
      | u::us', v::vs' => u+v :: add us' vs'
      | _, nil => us
      | _, _ => vs
    end.
  Infix ".+" := add (at level 50).

  Hint Extern 1 (@eq Z _ _) => ring.

  Lemma add_rep : forall bs us vs, decode' bs (add us vs) = decode' bs us + decode' bs vs.
  Proof.
    unfold decode, decode'; induction bs; destruct us; destruct vs; boring.
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

  Definition mul_each u := map (Z.mul u).
  Lemma mul_each_rep : forall bs u vs,
    decode' bs (mul_each u vs) = u * decode' bs vs.
  Proof.
    unfold decode'; induction bs; destruct vs; boring.
  Qed.

  Lemma decode'_cons : forall x1 x2 xs1 xs2,
    decode' (x1 :: xs1) (x2 :: xs2) = x1 * x2 + decode' xs1 xs2.
  Proof.
    unfold decode'; boring.
  Qed.
  Hint Rewrite decode'_cons.

  Fixpoint sub (us vs:digits) : digits :=
    match us,vs with
      | u::us', v::vs' => u-v :: sub us' vs'
      | _, nil => us
      | nil, v::vs' => (0-v)::sub nil vs'
    end.

  Lemma sub_rep : forall bs us vs, decode' bs (sub us vs) = decode' bs us - decode' bs vs.
  Proof.
    induction bs; destruct us; destruct vs; boring.
  Qed.

  Lemma base_eq_1cons: base = 1 :: skipn 1 base.
  Proof.
    pose proof (b0_1 0) as H.
    destruct base; compute in H; try discriminate; boring.
  Qed.

  Lemma encode_rep : forall z, decode (encode z) = z.
  Proof.
    pose proof base_eq_1cons.
    unfold decode, encode; destruct z; boring.
  Qed.

  Lemma mul_each_base : forall us bs c, 
      decode' bs (mul_each c us) = decode' (mul_each c bs) us.
  Proof.
    induction us; destruct bs; boring.
  Qed.

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

  Definition crosscoef i j : Z := 
    let b := nth_default 0 base in
    (b(i) * b(j)) / b(i+j)%nat.
  Hint Unfold crosscoef.

  Fixpoint zeros n := match n with O => nil | S n' => 0::zeros n' end.
  Lemma zeros_rep : forall bs n, decode' bs (zeros n) = 0.
    induction bs; destruct n; boring.
  Qed.
  Lemma length_zeros : forall n, length (zeros n) = n.
    induction n; boring.
  Qed.
  Hint Rewrite length_zeros.

  Lemma app_zeros_zeros : forall n m, zeros n ++ zeros m = zeros (n + m).
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

  (* mul' is multiplication with the SECOND ARGUMENT REVERSED and OUTPUT REVERSED *)
  Fixpoint mul_bi' (i:nat) (vsr:digits) := 
    match vsr with
    | v::vsr' => v * crosscoef i (length vsr') :: mul_bi' i vsr'
    | nil => nil
    end.
  Definition mul_bi (i:nat) (vs:digits) : digits :=
    zeros i ++ rev (mul_bi' i (rev vs)).

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

  Lemma mul_bi'_zeros : forall n m, mul_bi' n (zeros m) = zeros m.
    induction m; boring.
  Qed.
  Hint Rewrite mul_bi'_zeros.

  Lemma Z_div_mul' : forall a b : Z, b <> 0 -> (b * a) / b = a.
    intros. rewrite Z.mul_comm. apply Z.div_mul; auto.
  Qed.

  Lemma Zgt0_neq0 : forall x, x > 0 -> x <> 0.
    boring.
  Qed.

  Lemma nth_error_base_nonzero : forall n x,
    nth_error base n = Some x -> x <> 0.
  Proof.
    eauto using (@nth_error_value_In Z), Zgt0_neq0, base_positive.
  Qed.

  Hint Rewrite plus_0_r.

  Lemma mul_bi_single : forall m n x,
    (n + m < length base)%nat ->
    decode (mul_bi n (zeros m ++ x :: nil)) = nth_default 0 base m * x * nth_default 0 base n.
  Proof.
    unfold mul_bi, decode.
    destruct m; simpl; simpl_list; simpl; intros. {
      pose proof nth_error_base_nonzero.
      boring; destruct base; nth_tac.
      rewrite Z_div_mul'; eauto.
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

  Lemma mul_bi'_n_nil : forall n, mul_bi' n nil = nil.
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
    mul_bi' n (x :: us) = x * crosscoef n (length us) :: mul_bi' n us.
  Proof.
    unfold mul_bi'; auto.
  Qed.

  Lemma cons_length : forall A (xs : list A) a, length (a :: xs) = S (length xs).
  Proof.
    auto.
  Qed.

  Lemma add_same_length : forall us vs l, (length us = l) -> (length vs = l) ->
    length (us .+ vs) = l.
  Proof.
    induction us, vs; boring.
    erewrite (IHus vs (pred l)); boring.
  Qed.

  Lemma length0_nil : forall {A} (xs : list A), length xs = 0%nat -> xs = nil.
  Proof.
    induction xs; boring; discriminate.
  Qed.

  Hint Rewrite app_nil_l.

  Lemma add_snoc_same_length : forall l us vs a b, 
    (length us = l) -> (length vs = l) ->
    (us ++ a :: nil) .+ (vs ++ b :: nil) = (us .+ vs) ++ (a + b) :: nil.
  Proof.
    induction l, us, vs; boring; discriminate.
  Qed.

  Lemma length_snoc : forall {T} xs (x:T),
    length xs = pred (length (xs++x::nil)).
  Proof.
    boring; simpl_list; boring.
  Qed.

  Lemma mul_bi'_add : forall us n vs l
    (Hlus: length us = l)
    (Hlvs: length vs = l),
    mul_bi' n (rev (us .+ vs)) = 
    mul_bi' n (rev us) .+ mul_bi' n (rev vs).
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
    induction us; intros. {
      rewrite add_nil_l.
      rewrite add_nil_l; auto.
    } {
      destruct vs. {
        elimtype False.
        replace (length nil) with 0%nat in H0 by auto.
        rewrite cons_length in H.
        assert (0 <> l)%nat by (rewrite <- H; apply O_S).
        contradiction.
      } {
        rewrite add_first_terms.
        simpl.
        assert (length us = pred l).
        rewrite cons_length in H.
        rewrite <- H; auto.
        assert (length vs = pred l).
        rewrite cons_length in H0.
        rewrite <- H0; auto.
        rewrite (add_app_same_length (pred l) _ _ _ _); try (rewrite rev_length; auto).
        rewrite (IHus vs (pred l)); auto.
      }
    }
  Qed.

  Lemma mul_bi'_length : forall us n, length (mul_bi' n us) = length us.
  Proof.
    induction us; intros; auto.
    rewrite mul_bi'_cons.
    rewrite cons_length.
    rewrite cons_length.
    replace (length (mul_bi' n us)) with (length us); auto.
  Qed.

  Lemma add_comm : forall us vs, us .+ vs = vs .+ us.
  Proof.
    induction us; intros. {
      rewrite add_nil_l.
      rewrite add_nil_r.
      auto.
   } {
     destruct vs. {
       rewrite add_nil_l.
       rewrite add_nil_r; auto.
     } {
       rewrite add_first_terms.
       rewrite add_first_terms.
       rewrite IHus; f_equal; omega.
    } 
  }
  Qed.

  Lemma mul_bi_add_same_length : forall n us vs l, (length us = l) -> (length vs = l) ->
    mul_bi n (us .+ vs) = mul_bi n us .+ mul_bi n vs.
  Proof.
    intros.
    unfold mul_bi; simpl.
    rewrite add_leading_zeros.
    rewrite (mul_bi'_add us n vs l); auto.
    rewrite (rev_add_rev _ _ l).
    rewrite add_comm; f_equal.
    rewrite mul_bi'_length; rewrite rev_length.
    apply H.
    rewrite mul_bi'_length; rewrite rev_length.
    apply H0.
  Qed.

  Lemma add_zeros_same_length : forall us, us .+ (zeros (length us)) = us.
  Proof.
    induction us; auto; simpl.
    rewrite IHus; f_equal; ring.
  Qed.

  Lemma add_trailing_zeros : forall us vs, (length us >= length vs)%nat ->
    us .+ vs = us .+ (vs ++ (zeros (length us - length vs))).
  Proof.
    induction us; intros. {
      rewrite add_nil_l.
      rewrite add_nil_l.
      simpl in *.
      assert (length vs = 0%nat) by omega.
      simpl_list; auto.
    } {
      destruct vs. {
        rewrite add_nil_r.
        rewrite app_nil_l.
        simpl.
        f_equal; try ring.
        symmetry.
        apply add_zeros_same_length.
      } {
        rewrite add_first_terms; simpl.
        f_equal.
        apply IHus.
        rewrite cons_length in H.
        rewrite cons_length in H.
        intuition.
      }
    }
  Qed.

  Lemma length_add_ge : forall us vs, (length us >= length vs)%nat ->
    (length (us .+ vs) <= length us)%nat.
  Proof.
    intros.
    rewrite add_trailing_zeros; auto.
    rewrite (add_same_length _ _ (length us)); try omega.
    rewrite app_length.
    rewrite length_zeros.
    omega.
  Qed.

  Lemma add_length_le_max : forall us vs,
      (length (us .+ vs) <= max (length us) (length vs))%nat.
  Proof.
    intros.
    destruct (ge_dec (length us) (length vs)). {
      rewrite Max.max_l by omega.
      rewrite length_add_ge; auto.
    } {
      rewrite add_comm.
      rewrite Max.max_r by omega.
      apply length_add_ge; omega.
    }
  Qed.

  Lemma mul_bi_length : forall us n, length (mul_bi n us) = (length us + n)%nat.
  Proof.
    induction us; intros; simpl. {
      unfold mul_bi; simpl; simpl_list.
      apply length_zeros.
    } {
      unfold mul_bi; simpl; simpl_list.
      rewrite length_zeros.
      rewrite mul_bi'_length; simpl_list; simpl.
      omega.
    }
  Qed.

  Lemma mul_bi_trailing_zeros : forall m n us, mul_bi n us ++ zeros m = mul_bi n (us ++ zeros m).
  Proof.
    unfold mul_bi.
    induction m; intros; simpl_list; auto.
    rewrite <- zeros_app0.
    rewrite app_assoc.
    rewrite IHm; clear IHm.
    simpl.
    repeat (rewrite rev_app_distr).
    simpl.
    repeat (rewrite rev_zeros).
    rewrite app_assoc.
    auto.
  Qed.

  Lemma mul_bi_add_longer : forall n us vs, (length us >= length vs)%nat ->
    mul_bi n (us .+ vs) = mul_bi n us .+ mul_bi n vs.
  Proof.
      intros.
      rewrite add_trailing_zeros by auto.
      rewrite (add_trailing_zeros (mul_bi n us) (mul_bi n vs)) by (repeat (rewrite mul_bi_length); omega).
      erewrite mul_bi_add_same_length by (eauto; simpl_list; rewrite length_zeros; omega).
      f_equal.
      rewrite mul_bi_trailing_zeros.
      repeat (rewrite mul_bi_length).
      f_equal. f_equal. f_equal.
      omega.
  Qed.

  Lemma mul_bi_add : forall n us vs,
    mul_bi n (us .+ vs) = (mul_bi n  us) .+ (mul_bi n vs).
  Proof.
    intros.
    destruct (le_ge_dec (length us) (length vs)). {
      assert (length vs >= length us)%nat by auto.
      rewrite add_comm.
      replace (mul_bi n us .+ mul_bi n vs) with (mul_bi n vs .+ mul_bi n us) by (apply add_comm).
      apply (mul_bi_add_longer n vs us); auto.
    } {
      apply mul_bi_add_longer; auto.
    }
  Qed.

  Lemma mul_bi_rep : forall i vs,
    (i + length vs < length base)%nat ->
    decode (mul_bi i vs) = decode vs * nth_default 0 base i.
  Proof.
    unfold decode.
    induction vs using rev_ind; intros; simpl. {
      unfold mul_bi, decode.
      ssimpl_list; rewrite zeros_rep; simpl.
      unfold decode'; simpl.
      ring.
    } {
      assert (i + length vs < length base)%nat as inbounds. {
        rewrite app_length in *; simpl in *.
        rewrite NPeano.Nat.add_1_r, <- plus_n_Sm in *.
        etransitivity; eauto.
      }

      rewrite set_higher.
      ring_simplify.
      rewrite <- IHvs by auto; clear IHvs.
      simpl in *.
      rewrite <- mul_bi_single by auto.
      rewrite <- add_rep.
      rewrite <- mul_bi_add.
      rewrite set_higher'.
      auto.
    }
  Qed.

  (* mul' is multiplication with the FIRST ARGUMENT REVERSED *)
  Fixpoint mul' (usr vs:digits) : digits :=
    match usr with
      | u::usr' => 
        mul_each u (mul_bi (length usr') vs) .+ mul' usr' vs
      | _ => nil
    end.
  Definition mul us := mul' (rev us).

  Lemma mul'_rep : forall us vs,
    (length us + length vs <= length base)%nat ->
    decode (mul' (rev us) vs) = decode us * decode vs.
  Proof.
    unfold decode.
    induction us using rev_ind; intros; simpl; try apply decode_nil.

    assert (length us + length vs < length base)%nat as inbounds. {
      rewrite app_length in *; simpl in *.
      rewrite plus_comm in *.
      rewrite NPeano.Nat.add_1_r, <- plus_n_Sm in *.
      auto.
    }

    ssimpl_list.
    rewrite add_rep.
    rewrite IHus by (rewrite le_trans; eauto); clear IHus.
    rewrite set_higher.
    rewrite mul_each_rep.
    rewrite mul_bi_rep by auto; unfold decode.
    ring.
  Qed.

  Lemma mul_rep : forall us vs,
    (length us + length vs <= length base)%nat ->
    decode (mul us vs) = decode us * decode vs.
  Proof.
    exact mul'_rep.
  Qed.

  Ltac case_max :=
    match goal with [ |- context[max ?x ?y] ] =>
        destruct (le_dec x y); try ( rewrite Max.max_l by omega
                              || rewrite Max.max_r by omega)
    end.

  Lemma mul'_length: forall us vs,
      (length (mul' us vs) <= length us + length vs)%nat.
  Proof.
    induction us; intros; simpl; try omega.
    rewrite add_length_le_max.
    unfold mul_each; rewrite map_length; rewrite mul_bi_length.
    case_max. {
      rewrite Max.max_l by (rewrite plus_comm; eauto); omega.
    } {
      omega.
    }
  Qed.

  Lemma mul_length: forall us vs,
      (length (mul us vs) <= length us + length vs)%nat.
  Proof.
    intros; unfold mul.
    rewrite mul'_length.
    rewrite rev_length; omega.
  Qed.

(* Print Assumptions mul_rep. *)

End BaseSystem.

Module Type PolynomialBaseParams.
  Parameter b1 : positive. (* the value at which the polynomial is evaluated *)
  Parameter baseLength : nat. (* 1 + degree of the polynomial *)
  Axiom baseLengthNonzero : NPeano.ltb 0 baseLength = true.
End PolynomialBaseParams.

Module PolynomialBaseCoefs (Import P:PolynomialBaseParams) <: BaseCoefs.
  (** PolynomialBaseCoeffs generates base vectors for [BaseSystem] using the extra assumption that $b_{i+j} = b_j b_j$. *)
  Definition bi i := (Zpos b1)^(Z.of_nat i).
  Definition base := map bi (seq 0 baseLength).

  Lemma b0_1 : forall x, nth_default x base 0 = 1.
    unfold base, bi, nth_default.
    case_eq baseLength; intros. {
      assert ((0 < baseLength)%nat) by
        (rewrite <-NPeano.ltb_lt; apply baseLengthNonzero).
      subst; omega.
    }
    auto.
  Qed.

  Lemma base_positive : forall b, In b base -> b > 0.
  Proof.
    unfold base.
    intros until 0; intro H.
    rewrite in_map_iff in *.
    destruct H; destruct H.
    subst.
    apply pos_pow_nat_pos.
  Qed.

  Lemma base_good:
    forall i j, (i + j < length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
  Proof.
    unfold base, nth_default; nth_tac.

    clear.
    unfold bi.
    rewrite Nat2Z.inj_add, Zpower_exp by
      (replace 0 with (Z.of_nat 0) by auto; rewrite <- Nat2Z.inj_ge; omega).
    rewrite Z_div_same_full; try ring.
    rewrite <- Z.neq_mul_0.
    split; apply Z.pow_nonzero; try apply Zle_0_nat; try solve [intro H; inversion H].
  Qed.
End PolynomialBaseCoefs.

Module BasePoly2Degree32Params <: PolynomialBaseParams.
  Definition b1 := 2%positive.
  Definition baseLength := 32%nat.
  Lemma baseLengthNonzero : NPeano.ltb 0 baseLength = true.
    compute; reflexivity.
  Qed.
End BasePoly2Degree32Params.

Import ListNotations.

Module BaseSystemExample.
  Module BasePoly2Degree32Coefs := PolynomialBaseCoefs BasePoly2Degree32Params.
  Module BasePoly2Degree32 := BaseSystem BasePoly2Degree32Coefs.
  Import BasePoly2Degree32.

  Example three_times_two : mul [1;1;0] [0;1;0] = [0;1;1;0;0].
  Proof.
    reflexivity.
  Qed.

  (* python -c "e = lambda x: '['+''.join(reversed(bin(x)[2:])).replace('1','1;').replace('0','0;')[:-1]+']'; print(e(19259)); print(e(41781))" *)
  Definition a := [1;1;0;1;1;1;0;0;1;1;0;1;0;0;1].
  Definition b := [1;0;1;0;1;1;0;0;1;1;0;0;0;1;0;1].
  Example da : decode a = 19259.
  Proof.
    reflexivity.
  Qed.
  Example db : decode b = 41781.
  Proof.
    reflexivity.
  Qed.
  Example encoded_ab :
    mul a b =[1;1;1;2;2;4;2;2;4;5;3;3;3;6;4;2;5;3;4;3;2;1;2;2;2;0;1;1;0;1].
  Proof.
    reflexivity.
  Qed.
  Example dab : decode (mul a b) = 804660279.
  Proof.
    reflexivity.
  Qed.
End BaseSystemExample.
