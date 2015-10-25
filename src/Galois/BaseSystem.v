Require Import List.
Require Import ZArith.ZArith ZArith.Zdiv.

Local Open Scope Z.

Module Type BaseCoefs.
  (* lists coefficients of digits and the digits themselves always have the
  * LEAST significant position first. *)
  Definition coefs : Type := list Z.

  Parameter base : coefs.
  Axiom bs_good :
    forall i j,
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
End BaseCoefs.

Module BaseSystem (Import B:BaseCoefs).
  Definition digits : Type := list Z.

  Definition accumulate p acc := fst p * snd p + acc.
  Definition decode bs u  := fold_right accumulate 0 (combine u bs).
  Hint Unfold decode accumulate.

	Fixpoint add (us vs:digits) : digits :=
		match us,vs with
			| u::us', v::vs' => (u+v)::(add us' vs')
			| _, nil => us
			| _, _ => vs
		end.
  Local Infix ".+" := add (at level 50).

  Lemma add_rep : forall bs us vs, decode bs (add us vs) = decode bs us + decode bs vs.
  Proof.
    unfold decode, accumulate.
    induction bs; destruct us; destruct vs; auto; simpl; try rewrite IHbs; ring.
  Qed.

  Lemma decode_nil : forall bs, decode bs nil = 0.
    auto.
  Qed.

  (* mul_geomseq is a valid multiplication algorithm if b_i = b_1^i *)
  Fixpoint mul_geomseq (us vs:digits) : digits :=
		match us,vs with
			| u::us', v::vs' => u*v :: map (Z.mul u) vs' .+ mul_geomseq us' vs
			| _, _ => nil
		end.

  Definition mul_each u := map (Z.mul u).
  Lemma mul_each_rep : forall bs u vs, decode bs (mul_each u vs) = u * decode bs vs.
  Proof.
    unfold decode, accumulate.
    induction bs; destruct vs; auto; simpl; try rewrite IHbs; ring.
  Qed.

  Definition crosscoef i j : Z := 
    let b := nth_default 0 base in
    (b(i) * b(j)) / b(i+j)%nat.

  Fixpoint zeros n := match n with O => nil | S n' => 0::zeros n' end.
  Lemma zeros_rep : forall bs n, decode bs (zeros n) = 0.
    unfold decode, accumulate.
    induction bs; destruct n; auto; simpl; try rewrite IHbs; ring.
  Qed.
  Lemma length_zeros : forall n, length (zeros n) = n.
    induction n; simpl; auto.
  Qed.

  Lemma app_zeros_zeros : forall n m, (zeros n ++ zeros m) = zeros (n + m).
  Proof.
    intros; 
    induction n; simpl; auto.
    rewrite IHn; auto.
  Qed.

  Lemma zeros_app0 : forall m, (zeros m ++ 0 :: nil) = zeros (S m).
  Proof.
    intros.
    assert (0 :: nil = zeros 1) by auto.
    rewrite H.
    rewrite app_zeros_zeros.
    rewrite NPeano.Nat.add_1_r; auto.
  Qed.

  Lemma rev_zeros : forall n, rev (zeros n) = zeros n.
  Proof.
    intros.
    induction n. {
      unfold zeros; auto.
    } {
      replace (rev (zeros (S n))) with (rev (zeros n) ++ 0 :: nil) by auto.
      rewrite IHn.
      rewrite zeros_app0; auto.
    }
  Qed.

  Lemma app_cons_app_app : forall T xs (y:T) ys, xs ++ y :: ys = (xs ++ (y::nil)) ++ ys.
  Proof.
    intros.
    rewrite app_assoc_reverse.
    replace ((y :: nil) ++ ys) with (y :: ys); auto.
  Qed.

  (* mul' is multiplication with the SECOND ARGUMENT REVERSED and OUTPUT REVERSED *)
  Fixpoint mul_bi' (i:nat) (vsr:digits) := 
    match vsr with
    | v::vsr' => v * crosscoef i (length vsr') :: mul_bi' i vsr'
    | nil => nil
    end.
  Definition mul_bi (i:nat) (vs:digits) : digits :=
    zeros i ++ rev (mul_bi' i (rev vs)).

  (*
  Definition mul_bi (i:nat) (vs:digits) : digits :=
    let mkEntry := (fun (p:(nat*Z)) => let (j, v) := p in v * crosscoef i j) in
    zeros i ++ map mkEntry (@enumerate Z vs).
  *)

  Lemma decode_single : forall n bs x,
    decode bs (zeros n ++ x :: nil) = nth_default 0 bs n * x.
  Proof.
    induction n; intros; simpl.
    destruct bs; auto; unfold decode, accumulate, nth_default; simpl; ring.
    destruct bs; simpl; auto.
    unfold decode, accumulate, nth_default in *; simpl in *; auto.
  Qed.

  Lemma peel_decode : forall xs ys x y, decode (x::xs) (y::ys) = x*y + decode xs ys.
    intros.
    unfold decode, accumulate, nth_default in *; simpl in *; ring_simplify; auto.
  Qed.

  Lemma decode_highzeros : forall xs bs n, decode bs (xs ++ zeros n) = decode bs xs.
    induction xs; intros; simpl; try rewrite zeros_rep; auto.
    destruct bs; simpl; auto.
    repeat (rewrite peel_decode).
    rewrite IHxs; auto.
  Qed.

  Lemma mul_bi_single : forall m n x,
    decode base (mul_bi n (zeros m ++ x :: nil)) = nth_default 0 base m * x * nth_default 0 base n.
  Proof.
    unfold mul_bi.
    destruct m; simpl; ssimpl_list; simpl; intros.
    rewrite decode_single.
    unfold crosscoef; simpl.
    rewrite plus_0_r.
    ring_simplify.
    replace (nth_default 0 base n * nth_default 0 base 0) with (nth_default 0 base 0 * nth_default 0 base n) by ring.
    SearchAbout Z.div.
    rewrite Z_div_mult; try ring.

    assert (nth_default 0 base n > 0) by admit; auto.

    intros; simpl; ssimpl_list; simpl.
    replace (mul_bi' n (rev (zeros m) ++ 0 :: nil)) with (zeros (S m)) by admit.
    intros; simpl; ssimpl_list; simpl.
    rewrite length_zeros.
    rewrite app_cons_app_app.
    rewrite rev_zeros.
    intros; simpl; ssimpl_list; simpl.
    rewrite zeros_app0.
    rewrite app_assoc.
    rewrite app_zeros_zeros.
    rewrite decode_single.
    unfold crosscoef; simpl; ring_simplify.
    rewrite NPeano.Nat.add_1_r.
    rewrite bs_good.
    rewrite Z_div_mult.
    rewrite <- Z.mul_assoc.
    rewrite <- Z.mul_comm.
    rewrite <- Z.mul_assoc.
    rewrite <- Z.mul_assoc.
    destruct (Z.eq_dec x 0); subst; try ring.
    rewrite Z.mul_cancel_l by auto.
    rewrite <- bs_good.
    ring.

    assert (nth_default 0 base (n + S m) > 0) by admit; auto.
  Qed.

  Lemma set_higher' : forall vs x, vs++x::nil = vs .+ (zeros (length vs) ++ x :: nil).
    induction vs; auto.
    intros; simpl; rewrite IHvs; f_equal; ring.
  Qed.
  
  Lemma set_higher : forall bs vs x,
    decode bs (vs++x::nil) = decode bs vs + nth_default 0 bs (length vs) * x.
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

  (* TODO: add this to preconditions for base *)
  Lemma b0_1 : forall bs, nth_default 0 bs 0 = 1.
  Admitted.

  (* TODO: add this to preconditions for base *)
  Lemma bn_nonzero : forall n bs, nth_default 0 bs n <> 0.
  Admitted.

  Lemma crosscoef_0_n : forall n, crosscoef 0 n = 1.
    induction n; unfold crosscoef.
    rewrite Z_div_mult_full.
    apply b0_1.
    rewrite plus_O_n.
    rewrite b0_1; intuition.
    simpl.
    rewrite Z_div_mult_full.
    apply b0_1.
    apply bn_nonzero.
  Qed.

  Lemma mul_bi'_0_us : forall us, mul_bi' 0 us = us.
  Proof.
    intros.
    induction us; simpl; auto.
    rewrite IHus.
    rewrite crosscoef_0_n.
    rewrite <- Zred_factor0; auto.
  Qed.

  Lemma mul_bi'_n_nil : forall n, mul_bi' n nil = nil.
  Proof.
    intros.
    unfold mul_bi; auto.
  Qed.

  Lemma add_nil_l : forall us, nil .+ us = us.
    induction us; auto.
  Qed.

  Lemma mul_bi_0_us : forall us, mul_bi 0 us = us.
  Proof.
    intros.
    unfold mul_bi; simpl.
    rewrite mul_bi'_0_us.
    rewrite rev_involutive; auto.
  Qed.

  Lemma mul_bi'_app : forall n x us,
    mul_bi' n (x :: us) = x * crosscoef n (length us) :: mul_bi' n us.
  Proof.
    unfold mul_bi'; auto.
  Qed.

  Lemma mul_bi'_add : forall n us vs,
    mul_bi' n (us .+ vs) = mul_bi' n us .+ mul_bi' n vs.
  Proof.
    intros.
    (* induction us. {
      rewrite mul_bi'_n_nil.
      rewrite add_nil_l.
      rewrite add_nil_l; auto.
    } {
      induction vs; auto.
      rewrite mul_bi'_app.
      apply IHus.
    }

    induction n. {
      rewrite mul_bi'_0_us.
      replace (mul_bi' 0 us) with us by (rewrite mul_bi'_0_us; auto).
      replace (mul_bi' 0 vs) with vs by (rewrite mul_bi'_0_us; auto).
      auto.
    } {
      unfold mul_bi'; simpl.
      simpl. *)
   Admitted.

  Lemma add_leading_zeroes : forall n us vs,
    (zeros n ++ us) .+ (zeros n ++ vs) = zeros n ++ (us .+ vs).
  Admitted.

  Lemma rev_add : forall us vs,
    rev(us .+ vs) = rev us .+ rev vs.
  Admitted.

  Lemma mul_bi_add : forall n us vs,
    mul_bi n (us .+ vs) = mul_bi n us .+ mul_bi n vs.
  Proof.
    intros.
    unfold mul_bi; simpl.
    replace (rev (us .+ vs)) with (rev us .+ rev vs).
    rewrite mul_bi'_add.
    rewrite add_leading_zeroes.
    rewrite rev_add; auto.
    rewrite <- rev_add; auto.
  Qed.

  Lemma mul_bi_rep : forall i vs, decode base (mul_bi i vs) = decode base vs * nth_default 0 base i.
    induction vs using rev_ind; intros; simpl. {
      unfold mul_bi.
      ssimpl_list; rewrite zeros_rep; simpl.
      unfold decode; simpl.
      ring.
    } {
      rewrite set_higher.
      ring_simplify.
      rewrite <- IHvs; clear IHvs.
      rewrite <- mul_bi_single.
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
  Local Infix "#*" := mul (at level 40).

  Lemma mul'_rep : forall us vs, decode base (mul' (rev us) vs) = decode base us * decode base vs.
    induction us using rev_ind; intros; simpl; try apply decode_nil.
    ssimpl_list.
    rewrite add_rep.
    rewrite IHus; clear IHus.
    rewrite set_higher.
    rewrite mul_each_rep.
    rewrite mul_bi_rep.
    ring.
  Qed.

  Lemma mul_rep : forall us vs, decode base (us #* vs) = decode base us * decode base vs.
    apply mul'_rep.
  Qed.
End BaseSystem.
