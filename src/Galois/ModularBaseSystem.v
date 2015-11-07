Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Galois.BaseSystem Crypto.Galois.GaloisTheory.
Require Import Util.ListUtil.
Open Scope Z_scope.

Module Type PseudoMersenneBaseParams (Import B:BaseCoefs) (Import M:Modulus).
  (* TODO: do we actually want B and M "up there" in the type parameters? I was
  * imagining writing something like "Paramter Module M : Modulus". *)

  Parameter k : Z.
  Parameter c : Z.
  Axiom modulus_pseudomersenne : primeToZ modulus = 2^k - c.

  Axiom base_matches_modulus :
    forall i j,
    (i   <  length base)%nat ->
    (j   <  length base)%nat ->
    (i+j >= length base)%nat->
    let b := nth_default 0 base in
    let r := (b i * b j)  /  (2^k * b (i+j-length base)%nat) in
              b i * b j = r * 2^k * b (i+j-length base)%nat.

  Axiom b0_1 : nth_default 0 base 0 = 1.

  (* Probably implied by modulus_pseudomersenne. *)
  Axiom k_pos : 0 <= k.

End PseudoMersenneBaseParams.

Module Type GFrep (Import M:Modulus).
  Module Import GF := GaloisTheory M.
  (* TODO: could GF notation be in Galois, not GaloisTheory *)
  Parameter T : Type.
  Parameter fromGF : GF -> T.
  Parameter toGF : T -> GF.

  Parameter rep : T -> GF -> Prop.
  Local Notation "u '~=' x" := (rep u x) (at level 70).
  Axiom fromGF_rep : forall x, fromGF x ~= x.
  Axiom rep_toGF : forall u x, u ~= x -> toGF u = x.

  Parameter add : T -> T -> T.
  Axiom add_rep : forall u v x y, u ~= x -> v ~= y -> add u v ~= (x+y)%GF.

  Parameter sub : T -> T -> T.
  Axiom sub_rep : forall u v x y, u ~= x -> v ~= y -> sub u v ~= (x-y)%GF.
  (* TBD: sub may need to be in BaseSystem as well *)

  Parameter mul : T -> T -> T.
  Axiom mul_rep : forall u v x y, u ~= x -> v ~= y -> mul u v ~= (x*y)%GF.

  Parameter square : T -> T.
  Axiom square_rep : forall u x, u ~= x -> square u ~= (x^2)%GF.
  (* we will want a non-trivial implementation later, currently square x = mul x x *)
End GFrep.

Module GFPseudoMersenneBase (BC:BaseCoefs) (M:Modulus) (P:PseudoMersenneBaseParams BC M) (* TODO(jadep): "<: GFrep M" *).
  Module Import GF := GaloisTheory M.
  Module EC <: BaseCoefs.
    Definition base := BC.base ++ (map (Z.mul (2^(P.k))) BC.base).
    
    Lemma base_positive : forall b, In b base -> b > 0.
    Proof.
      unfold base. intros.
      rewrite in_app_iff in H.
      destruct H. {
        apply BC.base_positive; auto.
      } {
        specialize BC.base_positive.
        induction BC.base; intros. {
          simpl in H; intuition.
        } {
          simpl in H.
          destruct H; subst.
          replace 0 with (2 ^ P.k * 0) by auto.
          apply (Zmult_gt_compat_l a 0 (2 ^ P.k)).
          rewrite Z.gt_lt_iff.
          apply Z.pow_pos_nonneg; intuition.
          apply P.k_pos.
          apply H0; left; auto.
          apply IHl; auto.
          intros. apply H0; auto. right; auto.
        }
      }
    Qed.

    Lemma map_nth_default_base_high : forall n, (n < (length BC.base))%nat -> 
      nth_default 0 (map (Z.mul (2 ^ P.k)) BC.base) n =
      (2 ^ P.k) * (nth_default 0 BC.base n).
    Proof.
      intros.
      erewrite map_nth_default; auto.
    Qed.

    Lemma base_good :
      forall i j, (i+j < length base)%nat ->
      let b := nth_default 0 base in
      let r := (b i * b j) / b (i+j)%nat in
      b i * b j = r * b (i+j)%nat.
    Proof.
      intros.
      subst b. subst r.
      unfold base in *.
      rewrite app_length in H; rewrite map_length in H.
      repeat rewrite nth_default_app.
      destruct (lt_dec i (length BC.base)); destruct (lt_dec j (length BC.base)); destruct (lt_dec (i + j) (length BC.base)); try omega.
      {
        (* i < length BC.base, j < length BC.base, i + j < length BC.base *)
        apply BC.base_good; auto.
      } {
        (* i < length BC.base, j < length BC.base, i + j >= length BC.base *)
        admit.
      } {
        (* i < length BC.base, j >= length BC.base, i + j >= length BC.base *)
        do 2 rewrite map_nth_default_base_high by omega.
        remember (nth_default 0 BC.base) as b.
        remember (j - length BC.base)%nat as j'.
        admit.
      } {
        (* i >= length BC.base, j < length BC.base, i + j >= length BC.base *)
        admit.
      }
    Qed.
  End EC.

  Module E := BaseSystem EC.
  Module B := BaseSystem BC.

  (* TODO: move to ListUtil *)
  Lemma firstn_app : forall {A} n (xs ys : list A), (n <= length xs)%nat ->
      firstn n xs = firstn n (xs ++ ys).
  Proof.
    induction n; destruct xs; destruct ys; simpl_list; boring; try omega.
    rewrite (IHn xs (a0 :: ys)) by omega; auto.
  Qed.
    
  Lemma decode_short : forall (us : B.digits), 
    (length us <= length BC.base)%nat -> B.decode us = E.decode us.
  Proof.
    intros.
    unfold B.decode, B.decode', E.decode, E.decode'.
    rewrite combine_truncate_r.
    rewrite (combine_truncate_r us EC.base).
    f_equal; f_equal.
    unfold EC.base.
    rewrite (firstn_app _ _  (map (Z.mul (2 ^ P.k)) BC.base)); auto.
  Qed.


  Lemma mul_rep_extended : forall (us vs : B.digits),
      (length us <= length BC.base)%nat -> 
      (length vs <= length BC.base)%nat ->
      B.decode us * B.decode vs = E.decode (E.mul us vs).
  Proof.
      intros. 
      rewrite E.mul_rep by (unfold EC.base; simpl_list; omega).
      f_equal; rewrite decode_short; auto.
  Qed.

  (* Converts from length of E.base to length of B.base by reduction modulo M.*)
  Definition reduce (us : E.digits) : B.digits :=
    let high := skipn (length BC.base) us in
    let low := firstn (length BC.base) us in
    let wrap := map (Z.mul P.c) high in
    B.add low wrap.

  Lemma Prime_nonzero: forall (p : Prime), primeToZ p <> 0.
  Proof.
    unfold Prime. intros.
    destruct p.
    simpl. intro.
    subst.
    apply Znumtheory.not_prime_0; auto.
  Qed.

  Lemma mod_mult_plus: forall a b c, (b <> 0) -> (a * b + c) mod b = c mod b.
  Proof.
    intros.
    rewrite Zplus_mod.
    rewrite Z.mod_mul; auto; simpl.
    rewrite Zmod_mod; auto.
  Qed.

  (* a = r + s(2^k) = r + s(2^k - c + c) = r + s(2^k - c) + cs = r + cs *) 
  Lemma pseudomersenne_add: forall x y, (x + ((2^P.k) * y)) mod modulus = (x + (P.c * y)) mod modulus.
  Proof.
    intros.
    replace (2^P.k) with (((2^P.k) - P.c) + P.c) by auto.
    rewrite Z.mul_add_distr_r.
    rewrite Zplus_mod.
    rewrite <- P.modulus_pseudomersenne.
    rewrite Z.mul_comm.
    rewrite mod_mult_plus; try apply Prime_nonzero.
    rewrite <- Zplus_mod; auto.
  Qed.

  Lemma extended_shiftadd: forall (us : E.digits), E.decode us =
      B.decode (firstn (length BC.base) us) +
      (2^P.k * B.decode (skipn (length BC.base) us)).
  Proof.
    intros.
    unfold B.decode, E.decode; rewrite <- B.mul_each_rep.
    replace B.decode' with E.decode' by auto.
    unfold EC.base.
    replace (map (Z.mul (2 ^ P.k)) BC.base) with (E.mul_each (2 ^ P.k) BC.base) by auto.
    rewrite E.base_mul_app.
    rewrite <- E.mul_each_rep; auto.
  Qed.

  Lemma reduce_rep : forall us, B.decode (reduce us) mod modulus = (E.decode us) mod modulus.
  Proof.
    intros.
    rewrite extended_shiftadd.
    rewrite pseudomersenne_add.
    unfold reduce.
    remember (firstn (length BC.base) us) as low.
    remember (skipn (length BC.base) us) as high.
    unfold B.decode.
    rewrite B.add_rep.
    replace (map (Z.mul P.c) high) with (B.mul_each P.c high) by auto.
    rewrite B.mul_each_rep; auto.
  Qed.

  Definition add := B.add.
  Definition mul us vs := reduce (E.mul us vs).
  Definition square x := mul x x.

End GFPseudoMersenneBase.
