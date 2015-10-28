Require Import List.
Require Import ZArith.ZArith ZArith.Zdiv.
  Require Import Omega.

Lemma nth_error_map : forall A B (f:A->B) xs i y,
  nth_error (map f xs) i = Some y ->
  exists x, nth_error xs i = Some x /\ f x = y.
Admitted.

Lemma nth_error_seq : forall start len i,
  nth_error (seq start len) i =
  if lt_dec i len
  then Some (start + i)
  else None.
Admitted.

Lemma nth_error_length_error : forall A (xs:list A) i, nth_error xs i = None ->
  i >= length xs.
Admitted.

Local Open Scope Z.

Lemma pos_pow_nat_pos : forall x n, 
  Z.pos x ^ Z.of_nat n > 0.
Admitted.

Module Type BaseCoefs.
  (** [BaseCoefs] represent the weights of each digit in a positional number system, with the weight of least significant digit presented first. The following requirements on the base are preconditions for using it with BaseSystem. *)
  Parameter base : list Z.
  Axiom b0_1 : nth_default 0 base 0 = 1.
  Axiom base_positive : forall b, In b base -> b > 0. (* nonzero would probably work too... *)
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
      $b_{i+j} = b_j b_j$. Implementations of addition and multiplication are
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
  Hint Unfold decode' accumulate.

	Fixpoint add (us vs:digits) : digits :=
		match us,vs with
			| u::us', v::vs' => (u+v)::(add us' vs')
			| _, nil => us
			| _, _ => vs
		end.
  Infix ".+" := add (at level 50).

  Lemma add_rep : forall bs us vs, decode' bs (add us vs) = decode' bs us + decode' bs vs.
  Proof.
    unfold decode', accumulate.
    induction bs; destruct us; destruct vs; auto; simpl; try rewrite IHbs; ring.
  Qed.

  Lemma decode_nil : forall bs, decode' bs nil = 0.
    auto.
  Qed.

  (* mul_geomseq is a valid multiplication algorithm if b_i = b_1^i *)
  Fixpoint mul_geomseq (us vs:digits) : digits :=
		match us,vs with
			| u::us', v::vs' => u*v :: map (Z.mul u) vs' .+ mul_geomseq us' vs
			| _, _ => nil
		end.

  Definition mul_each u := map (Z.mul u).
  Lemma mul_each_rep : forall bs u vs, decode' bs (mul_each u vs) = u * decode' bs vs.
  Proof.
    unfold decode', accumulate.
    induction bs; destruct vs; auto; simpl; try rewrite IHbs; ring.
  Qed.

  Definition crosscoef i j : Z := 
    let b := nth_default 0 base in
    (b(i) * b(j)) / b(i+j)%nat.

  Fixpoint zeros n := match n with O => nil | S n' => 0::zeros n' end.
  Lemma zeros_rep : forall bs n, decode' bs (zeros n) = 0.
    unfold decode', accumulate.
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
    decode' bs (zeros n ++ x :: nil) = nth_default 0 bs n * x.
  Proof.
    induction n; intros; simpl.
    destruct bs; auto; unfold decode', accumulate, nth_default; simpl; ring.
    destruct bs; simpl; auto.
    unfold decode', accumulate, nth_default in *; simpl in *; auto.
  Qed.

  Lemma peel_decode : forall xs ys x y, decode' (x::xs) (y::ys) = x*y + decode' xs ys.
    intros.
    unfold decode', accumulate, nth_default in *; simpl in *; ring_simplify; auto.
  Qed.

  Lemma decode_highzeros : forall xs bs n, decode' bs (xs ++ zeros n) = decode' bs xs.
    induction xs; intros; simpl; try rewrite zeros_rep; auto.
    destruct bs; simpl; auto.
    repeat (rewrite peel_decode).
    rewrite IHxs; auto.
  Qed.

  Lemma mul_bi'_zeros : forall n m, mul_bi' n (zeros m) = zeros m.
    induction m; intros; auto.
    simpl; f_equal; apply IHm.
  Qed.

  Lemma mul_bi_single : forall m n x,
    (n + m < length base)%nat ->
    decode (mul_bi n (zeros m ++ x :: nil)) = nth_default 0 base m * x * nth_default 0 base n.
  Proof.
    unfold mul_bi, decode.
    destruct m; simpl; ssimpl_list; simpl; intros. {
      rewrite decode_single.
      unfold crosscoef; simpl.
      rewrite plus_0_r.
      ring_simplify.
      replace (nth_default 0 base n * nth_default 0 base 0) with (nth_default 0 base 0 * nth_default 0 base n) by ring.
      rewrite Z_div_mult; try ring.

      apply base_positive.
      rewrite nth_default_eq.
      apply nth_In.
      rewrite plus_0_r in *.
      auto.
    } {
      simpl; ssimpl_list; simpl.
      rewrite rev_zeros.
      rewrite zeros_app0.
      rewrite mul_bi'_zeros.
      simpl; ssimpl_list; simpl.
      rewrite length_zeros.
      rewrite app_cons_app_app.
      rewrite rev_zeros.
      simpl; ssimpl_list; simpl.
      rewrite zeros_app0.
      rewrite app_assoc.
      rewrite app_zeros_zeros.
      rewrite decode_single.
      unfold crosscoef; simpl; ring_simplify.
      rewrite NPeano.Nat.add_1_r.
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
    induction vs; auto.
    intros; simpl; rewrite IHvs; f_equal; ring.
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
    intros.
    unfold mul_bi; auto.
  Qed.

  Lemma add_nil_l : forall us, nil .+ us = us.
    induction us; auto.
  Qed.

  Lemma add_nil_r : forall us, us .+ nil = us.
    induction us; auto.
  Qed.
  
  Lemma add_first_terms : forall us vs a b,
    (a :: us) .+ (b :: vs) = (a + b) :: (us .+ vs).
    auto.
  Qed.
 
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
    induction us; intros. {
      rewrite add_nil_l.
      apply H0.
    } {
      destruct vs. {
        rewrite add_nil_r; apply H.
      } {
        rewrite add_first_terms.
        rewrite cons_length.
        rewrite (IHus vs (pred l)).
        apply NPeano.Nat.succ_pred_pos.
        replace l with (length (a :: us)) by (apply H).
        rewrite cons_length; simpl.
        apply gt_Sn_O.
        replace l with (length (a :: us)) by (apply H).
        rewrite cons_length; simpl; auto.
        replace l with (length (z :: vs)) by (apply H).
        rewrite cons_length; simpl; auto.
      }
    }
  Qed.

  Lemma length0_nil : forall A (xs : list A), length xs = 0%nat -> xs = nil.
  Proof.
    induction xs; intros; auto.
    elimtype False.
    assert (0 <> length (a :: xs))%nat.
    rewrite cons_length.
    apply O_S.
    contradiction H0.
    rewrite H; auto.
  Qed.

  Lemma add_app_same_length : forall l us vs a b, 
    (length us = l) -> (length vs = l) ->
    (us ++ a :: nil) .+ (vs ++ b :: nil) = (us .+ vs) ++ (a + b) :: nil.
  Proof.
    induction l; intros. {
      assert (us = nil) by (apply length0_nil; apply H).
      assert (vs = nil) by (apply length0_nil; apply H0).
      rewrite H1; rewrite app_nil_l.
      rewrite H2; rewrite app_nil_l.
      rewrite add_nil_l.
      rewrite app_nil_l.
      auto.
    } {
      destruct us. {
        rewrite app_nil_l.
        rewrite add_nil_l.
        destruct vs. {
          rewrite app_nil_l.
          rewrite app_nil_l.
          auto.
        } {
          elimtype False.
          replace (length nil) with (0%nat) in H by auto.
          assert (0 <> S l)%nat.
          apply O_S.
          contradiction H1.
        }
      } {
        destruct vs. {
          elimtype False.
          replace (length nil) with (0%nat) in H0 by auto.
          assert (0 <> S l)%nat.
          apply O_S.
          contradiction H1.
        } {
          rewrite add_first_terms.
          rewrite <- app_comm_cons.
          rewrite <- app_comm_cons.
          rewrite add_first_terms.
          rewrite <- app_comm_cons.
          rewrite IHl; f_equal.
          assert (length (z :: us) = S (length us)) by (apply cons_length).
          assert (S (length us) = S l) by auto.
          auto.
          assert (length (z0 :: vs) = S (length vs)) by (apply cons_length).
          assert (S (length vs) = S l) by auto.
          auto.
        }
      }
  }
  Qed.

  Lemma mul_bi'_add : forall us n vs l, (length us = l) -> (length vs = l) ->
    mul_bi' n (rev (us .+ vs)) = 
    mul_bi' n (rev us) .+ mul_bi' n (rev vs).
  Proof.
    induction us using rev_ind; intros. {
      rewrite add_nil_l.
      rewrite mul_bi'_n_nil.
      rewrite add_nil_l; auto.
   } {
      destruct vs using rev_ind. {
        rewrite add_nil_r.
        rewrite mul_bi'_n_nil.
        rewrite add_nil_r; auto.
      } {
        simpl in *.
        simpl_list.
        rewrite (add_app_same_length (pred l) us vs x x0); auto.
        rewrite rev_unit.
        rewrite mul_bi'_cons.
        rewrite mul_bi'_cons.
        rewrite mul_bi'_cons.
        rewrite add_first_terms.
        rewrite rev_length.
        rewrite rev_length.
        rewrite rev_length.
        assert (length us = pred l).
        replace l with (length (us ++ x :: nil)) by (apply H).
        rewrite app_length; simpl; omega.
        assert (length vs = pred l).
        replace l with (length (vs ++ x0 :: nil)) by (apply H0).
        rewrite app_length; simpl; omega.
        rewrite (IHus n vs (pred l)).
        replace (length us) with (pred l) by (apply H).
        replace (length vs) with (pred l) by (apply H).
        rewrite (add_same_length us vs (pred l)).
        f_equal; ring.
        apply H1. apply H2. apply H1. apply H2.
        assert (length (us ++ x :: nil) = S (length us)).
        rewrite app_length.
        replace (length (x :: nil)) with 1%nat by auto; omega.
        assert (S (length us) = l).
        rewrite <- H1. apply H.
        replace l with (S (length us)) by apply H2. auto.
        assert (length (vs ++ x0 :: nil) = S (length vs)).
        rewrite app_length.
        replace (length (x0 :: nil)) with 1%nat by auto; omega.
        assert (S (length vs) = l).
        rewrite <- H1. apply H0.
        replace l with (S (length vs)) by apply H2. auto.
       }
     }
     Qed.

  Lemma zeros_cons0 : forall n, 0 :: zeros n = zeros (S n).
    auto.
  Qed.

  Lemma add_leading_zeros : forall n us vs,
    (zeros n ++ us) .+ (zeros n ++ vs) = zeros n ++ (us .+ vs).
    induction n; intros; auto.
    rewrite <- zeros_cons0; simpl.
    rewrite IHn; auto.
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
    mul_bi n (us .+ vs) = mul_bi n us .+ mul_bi n vs.
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
  Infix "#*" := mul (at level 40).

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
    decode (us #* vs) = decode us * decode vs.
  Proof.
    exact mul'_rep.
  Qed.
Print Assumptions mul_rep.
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

  Lemma b0_1 : nth_default 0 base 0 = 1.
    unfold base, bi, nth_default.
    case_eq baseLength; intros. {
      assert ((0 < baseLength)%nat) by
        (rewrite <-NPeano.ltb_lt; apply baseLengthNonzero).
      subst; omega.
    }
    auto.
  Qed.

  Lemma base_positive : forall b, In b base -> b > 0.
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
    unfold base, nth_default.
    intros; repeat progress (match goal with
      | [  |- context[match nth_error ?xs ?i with Some _ => _ | None => _ end ] ] => case_eq (nth_error xs i); intros
      | [ H: nth_error (map _ _) _ = Some _ |- _ ] => destruct (nth_error_map _ _ _ _ _ _ H); clear H
      | [ H: _ /\ _ |- _ ] => destruct H
      | [ H: nth_error (seq _ _) _ = Some _ |- _ ] => rewrite nth_error_seq in H
      | [ H: context[if lt_dec ?a ?b then _ else _] |- _ ] => destruct (lt_dec a b)
      | [ H: Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
      | [ H: None = Some _  |- _ ] => inversion H
      | [ H: Some _ = None |- _ ] => inversion H
      | [H: nth_error _ _ = None |- _ ] => specialize (nth_error_length_error _ _ _ H); intro; clear H
    end); autorewrite with list in *; try omega.

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

  Example three_times_two : [1;1;0] #* [0;1;0] = [0;1;1;0;0].
    compute; reflexivity.
  Qed.

  (* python -c "e = lambda x: '['+''.join(reversed(bin(x)[2:])).replace('1','1;').replace('0','0;')[:-1]+']'; print(e(19259)); print(e(41781))" *)
  Definition a := [1;1;0;1;1;1;0;0;1;1;0;1;0;0;1].
  Definition b := [1;0;1;0;1;1;0;0;1;1;0;0;0;1;0;1].
  Example da : decode a = 19259.
    compute. reflexivity.
  Qed.
  Example db : decode b = 41781.
    compute. reflexivity.
  Qed.
  Example encoded_ab :
    a #*b =[1;1;1;2;2;4;2;2;4;5;3;3;3;6;4;2;5;3;4;3;2;1;2;2;2;0;1;1;0;1].
    compute. reflexivity.
  Qed.
  Example dab : decode (a #* b) = 804660279.
    compute. reflexivity.
  Qed.
End BaseSystemExample.
