Require Import Galois GaloisTheory Galois.BaseSystem Galois.ModularBaseSystem.
Require Import List Util.ListUtil.
Import ListNotations.
Require Import ZArith.ZArith Zpower ZArith Znumtheory.
Require Import QArith.QArith QArith.Qround.
Require Import VerdiTactics.
Close Scope Q.

Module Base25Point5_10limbs <: BaseCoefs.
  Local Open Scope Z_scope.
  Definition base := map (fun i => two_p (Qceiling (Z_of_nat i *255 # 10))) (seq 0 10).
  Lemma base_positive : forall b, In b base -> b > 0.
  Proof.
    compute; intros; repeat break_or_hyp; intuition.
  Qed.

  Lemma b0_1 : forall x, nth_default x base 0 = 1.
  Proof.
    reflexivity.
  Qed.

  Lemma base_good :
    forall i j, (i+j < length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
  Proof.
    intros.
    assert (In i (seq 0 (length base))) by nth_tac.
    assert (In j (seq 0 (length base))) by nth_tac.
    subst b; subst r; simpl in *.
    repeat break_or_hyp; try omega; vm_compute; reflexivity.
  Qed.
End Base25Point5_10limbs.

Module Modulus25519 <: Modulus.
  Local Open Scope Z_scope.
  Definition two_255_19 := two_p 255 - 19.
  Lemma two_255_19_prime : prime two_255_19. Admitted.
  Definition prime25519 := exist _ two_255_19 two_255_19_prime.
  Definition modulus := prime25519.
End Modulus25519.

Module GF25519Base25Point5Params <: PseudoMersenneBaseParams Base25Point5_10limbs Modulus25519.
  Import Base25Point5_10limbs.
  Import Modulus25519.
  Local Open Scope Z_scope.
  (* TODO: do we actually want B and M "up there" in the type parameters? I was
  * imagining writing something like "Paramter Module M : Modulus". *)

  Definition k := 255.
  Definition c := 19.
  Lemma modulus_pseudomersenne :
    primeToZ modulus = 2^k - c.
  Proof.
    reflexivity.
  Qed.

  Lemma base_matches_modulus :
    forall i j,
    (i   <  length base)%nat ->
    (j   <  length base)%nat ->
    (i+j >= length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j)  /   (2^k * b (i+j-length base)%nat) in
              b i * b j = r * (2^k * b (i+j-length base)%nat).
  Proof.
    intros.
    assert (In i (seq 0 (length base))) by nth_tac.
    assert (In j (seq 0 (length base))) by nth_tac.
    subst b; subst r; simpl in *.
    repeat break_or_hyp; try omega; vm_compute; reflexivity.
  Qed.

  Lemma base_succ : forall i, ((S i) < length base)%nat -> 
    let b := nth_default 0 base in
    b (S i) mod b i = 0.
  Proof.
    intros.
    assert (In i (seq 0 (length base))) by nth_tac.
    assert (In (S i) (seq 0 (length base))) by nth_tac.
    subst b; simpl in *.
    repeat break_or_hyp; try omega; vm_compute; reflexivity.
  Qed.

  Lemma base_tail_matches_modulus:
    2^k mod nth_default 0 base (pred (length base)) = 0.
  Proof.
    nth_tac.
  Qed.

  Lemma b0_1 : forall x, nth_default x base 0 = 1.
  Proof.
    reflexivity.
  Qed.

  Lemma k_nonneg : 0 <= k.
  Proof.
    rewrite Zle_is_le_bool; reflexivity.
  Qed.
End GF25519Base25Point5Params.

Module GF25519Base25Point5 := GFPseudoMersenneBase Base25Point5_10limbs Modulus25519 GF25519Base25Point5Params.

Ltac expand_list f :=
  assert ((length f < 100)%nat) as _ by (simpl length in *; omega);
    repeat progress (
    let n := fresh f in
    destruct f as [ | n ];
    try solve [simpl length in *; try discriminate]).

Lemma GF25519Base25Point5_mul_expr_example :
  forall (f g:list Z)
  (Hf: length f = 10)
  (Hg: length g = 10)
  h (Heqh : h = GF25519Base25Point5.mul f g)
  r (Heqr : r = GF25519Base25Point5.carry_sequence [0;1;2;3;4;5;6;7;8;9;0] h),
  GF25519Base25Point5.B.digits.
Proof.
  intros.
  expand_list f; clear Hf.
  expand_list g; clear Hg.
  unfold
    GF25519Base25Point5.mul,
    GF25519Base25Point5.B.add,
    GF25519Base25Point5.E.mul,
    GF25519Base25Point5.E.mul',
    GF25519Base25Point5.E.mul_bi,
    GF25519Base25Point5.E.mul_bi',
    GF25519Base25Point5.E.mul_each,
    GF25519Base25Point5.E.add,
    GF25519Base25Point5.B.digits,
    GF25519Base25Point5.E.digits,
    Base25Point5_10limbs.base,
    GF25519Base25Point5.E.crosscoef,
    nth_default
  in Heqh; simpl in Heqh.

  unfold
    two_power_pos,
    shift_pos
  in Heqh; simpl in Heqh.

  (* unfoldZ.div in Heqh; simpl in Heqh. *) (* THIS TAKES TOO LONG *)
  repeat rewrite Z_div_same_full in Heqh by (apply Zeq_bool_neq; reflexivity).
  repeat match goal with [ Heqh : context[ (?a / ?b)%Z ]  |- _ ] =>
    replace (a / b)%Z with 2%Z in Heqh by
      (symmetry; erewrite <- Z.div_unique_exact; try apply Zeq_bool_neq; reflexivity)
  end.

  Hint Rewrite
    Z.mul_0_l
    Z.mul_0_r
    Z.mul_1_l
    Z.mul_1_r
    Z.add_0_l
    Z.add_0_r
    : Z_identities.
  autorewrite with Z_identities in Heqh.

  cbv beta iota zeta delta [GF25519Base25Point5.reduce Base25Point5_10limbs.base] in Heqh.
  remember GF25519Base25Point5Params.c as c in Heqh; unfold GF25519Base25Point5Params.c in Heqc.
  simpl in Heqh.

  repeat rewrite (Z.mul_add_distr_l c) in Heqh.
  repeat rewrite (Z.mul_assoc _ _ 2) in Heqh.
  repeat rewrite (Z.mul_comm _ 2) in Heqh.
  repeat rewrite (Z.mul_assoc 2 c) in Heqh.

  remember (2 * c)%Z as TwoC in Heqh; subst c; simpl in HeqTwoC; subst TwoC.
  repeat rewrite Z.add_assoc in Heqh.
  repeat rewrite Z.mul_assoc in Heqh.
  (* pretty-print: sh -c "tr -d '\n' | tr ';' '\n' | sed 's: *\* *:\*:g' | column -t" *)
  (* output:
  [(f0*g0  +  38*f9*g1  +  19*f8*g2  +  38*f7*g3  +  19*f6*g4  +  38*f5*g5  +  19*f4*g6  +  38*f3*g7  +  19*f2*g8  +  38*f1*g9)%Z
  (f1*g0   +  f0*g1     +  19*f9*g2  +  19*f8*g3  +  19*f7*g4  +  19*f6*g5  +  19*f5*g6  +  19*f4*g7  +  19*f3*g8  +  19*f2*g9)%Z
  (f2*g0   +  2*f1*g1   +  f0*g2     +  38*f9*g3  +  19*f8*g4  +  38*f7*g5  +  19*f6*g6  +  38*f5*g7  +  19*f4*g8  +  38*f3*g9)%Z
  (f3*g0   +  f2*g1     +  f1*g2     +  f0*g3     +  19*f9*g4  +  19*f8*g5  +  19*f7*g6  +  19*f6*g7  +  19*f5*g8  +  19*f4*g9)%Z
  (f4*g0   +  2*f3*g1   +  f2*g2     +  2*f1*g3   +  f0*g4     +  38*f9*g5  +  19*f8*g6  +  38*f7*g7  +  19*f6*g8  +  38*f5*g9)%Z
  (f5*g0   +  f4*g1     +  f3*g2     +  f2*g3     +  f1*g4     +  f0*g5     +  19*f9*g6  +  19*f8*g7  +  19*f7*g8  +  19*f6*g9)%Z
  (f6*g0   +  2*f5*g1   +  f4*g2     +  2*f3*g3   +  f2*g4     +  2*f1*g5   +  f0*g6     +  38*f9*g7  +  19*f8*g8  +  38*f7*g9)%Z
  (f7*g0   +  f6*g1     +  f5*g2     +  f4*g3     +  f3*g4     +  f2*g5     +  f1*g6     +  f0*g7     +  19*f9*g8  +  19*f8*g9)%Z
  (f8*g0   +  2*f7*g1   +  f6*g2     +  2*f5*g3   +  f4*g4     +  2*f3*g5   +  f2*g6     +  2*f1*g7   +  f0*g8     +  38*f9*g9)%Z
  (f9*g0   +  f8*g1     +  f7*g2     +  f6*g3     +  f5*g4     +  f4*g5     +  f3*g6     +  f2*g7     +  f1*g8     +  f0*g9)%Z]
  *)

  (* TODO: implement carry as a function from i to a function from digits to digits. 
  * The branch should happen *before* taking the digits as an argument*)
  (*
  simpl in Heqr.
  repeat match goal with [ Heqr : context[GF25519Base25Point5.carry ?i ?xs] |- _ ] =>
      let cr := fresh "cr" in
      remember (GF25519Base25Point5.carry i) as cr
  end.
  cbv beta iota delta [GF25519Base25Point5.carry] in *.
  simpl eq_nat_dec in *.

  remember (cr h) as crh.
  rewrite Heqcr in Heqcrh.
  cbv iota beta delta [nth_default nth_error value set_nth] in Heqcrh.
  *)

  exact h.
Qed.
