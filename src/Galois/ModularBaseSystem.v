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

  Axiom b0_1 : nth_default 0 base 1 = 1.
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

Module GFPseudoMersenneBase (BC:BaseCoefs) (M:Modulus) (P:PseudoMersenneBaseParams BC M) <: GFrep M.
  Module Import GF := GaloisTheory M.
  Module EC <: BaseCoefs.
    Definition base := BC.base ++ (map (Z.mul (2^(P.k))) BC.base).
    
    Lemma base_positive : forall b, In b base -> b > 0.
    Proof.
    Admitted.

    Lemma base_good :
      forall i j, (i+j < length base)%nat ->
      let b := nth_default 0 base in
      let r := (b i * b j) / b (i+j)%nat in
      b i * b j = r * b (i+j)%nat. 
    Admitted.

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
    rewrite combine_truncate.
    rewrite (combine_truncate us EC.base).
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
  Fixpoint reduce (us : E.digits) : B.digits :=
    let high := skipn (length BC.base) us in
    let low := firstn (length BC.base) us in
    let wrap := map (Z.mul P.c) high in
    B.add low wrap.

  (* TODO: move this somewhere more appropriate/improve strategy? *)
  Lemma Prime_nonzero: forall (p : Prime), primeToZ p <> 0.
  Admitted.

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
    rewrite decode_short; try (rewrite firstn_length; rewrite Min.le_min_l; auto).
  Admitted.

  (* TODO: definition of reduce, but isn't unfolding and solving automatically. *)
  Lemma reduce_defn : forall (us : E.digits), reduce us =
      B.add (firstn (length BC.base) us) (map (Z.mul P.c) (skipn (length BC.base) us)).
  Proof.
  Admitted.

  (* TODO: add in preconditions for B *)
  Lemma base_bounds : forall us, 0 <= B.decode us < modulus.
  Admitted.

  Lemma decode_mod : forall us, B.decode us = B.decode us mod modulus.
  Proof.
      intros; rewrite Zmod_small; auto.
      apply base_bounds.
  Qed.

  Lemma reduce_rep : forall us, B.decode (reduce us) = (E.decode us) mod modulus.
  Proof.
    intros.
    rewrite decode_mod.
    rewrite extended_shiftadd.
    rewrite pseudomersenne_add.
    remember (firstn (length BC.base) us) as low.
    remember (skipn (length BC.base) us) as high.
    replace (reduce us) with (B.add low (map (Z.mul P.c) high)) by (rewrite reduce_defn; rewrite Heqlow; rewrite Heqhigh; auto).
    unfold B.decode.
    rewrite B.add_rep.
    replace (map (Z.mul P.c) high) with (B.mul_each P.c high) by auto.
    rewrite B.mul_each_rep; auto.
  Qed.

Print Assumptions reduce_rep.

End GFPseudoMersenneBase.
