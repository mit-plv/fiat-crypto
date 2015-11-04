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

  (* a = r + s(2^k) = r + s(2^k - c + c) = r + s(2^k - c) + cs = r + cs *) 
  (* Fixpoint reduce (us : unreduced_digits) : digits := *)
      

End GFPseudoMersenneBase.
