Require Import BinInt BinNat ZArith Znumtheory.
Require Import BoolEq Field_theory.
Require Export Crypto.Galois.Galois Crypto.Galois.GaloisTheory.
Require Import Crypto.Tactics.VerdiTactics.

(* This file is for the actual field tactics and some specialized
 * morphisms that help field operate.
 *
 * When you want a Galois Field, this is the /only module/ you
 * should import, because it automatically pulls in everything
 * from Galois and the Modulus.
 *)
Module GaloisField (M: Modulus).
  Module G := Galois M.
  Module T := GaloisTheory M.
  Export M G T.

  (* Define a "ring morphism" between GF and Z, i.e. an equivalence
   * between 'inject (ZFunction (X))' and 'GFFunction (inject (X))'.
   *
   * Doing this allows us to do our coefficient manipulations in Z
   * rather than GF, because we know it's equivalent to inject the
   * result afterward.
   *)
  Lemma GFring_morph:
      ring_morph GFzero GFone GFplus GFmult GFminus GFopp eq
                 0%Z    1%Z   Zplus  Zmult  Zminus  Zopp  Zeq_bool
                 inject.
  Proof.
    constructor; intros; try galois;
      try (apply gf_eq; simpl; intuition).

    apply Zmod_small; destruct modulus; simpl;
      apply prime_ge_2 in p; intuition.

    replace (- (x mod modulus)) with (0 - (x mod modulus));
      try rewrite Zminus_mod_idemp_r; trivial.

    replace x with y; intuition.
      symmetry; apply Zeq_bool_eq; trivial.
  Qed.

  (* Redefine our division theory under the ring morphism *)
  Lemma GFmorph_div_theory: 
      div_theory eq Zplus Zmult inject Z.quotrem.
  Proof.
    constructor; intros; intuition.
    replace (Z.quotrem a b) with (Z.quot a b, Z.rem a b);
      try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).

    eq_remove_proofs; demod;
      rewrite <- (Z.quot_rem' a b);
      destruct a; simpl; trivial.
  Qed.

  (* Some simple utility lemmas *)
  Lemma injectZeroIsGFZero :
    GFzero = inject 0.
  Proof.
    apply gf_eq; simpl; trivial.
  Qed.

  Lemma injectOneIsGFOne :
    GFone = inject 1.
  Proof.
    apply gf_eq; simpl; intuition.
    symmetry; apply Zmod_small; destruct modulus; simpl;
      apply prime_ge_2 in p; intuition.
  Qed.

  Lemma exist_neq: forall A (P: A -> Prop) x y Px Py, x <> y -> exist P x Px <> exist P y Py.
  Proof.
    intuition; solve_by_inversion.
  Qed.

  (* Change all GFones to (inject 1) and GFzeros to (inject 0) so that
   * we can use our ring morphism to simplify them
   *)
  Ltac GFpreprocess :=
    repeat rewrite injectZeroIsGFZero;
    repeat rewrite injectOneIsGFOne.

  (* Split up the equation (because field likes /\, then
   * change back all of our GFones and GFzeros.
   *
   * TODO (adamc): what causes it to generate these subproofs?
   *)
  Ltac GFpostprocess :=
    repeat split;
		repeat match goal with [ |- context[exist ?a ?b (inject_subproof ?x)] ] =>
			replace (exist a b (inject_subproof x)) with (inject x%Z) by reflexivity
		end;
    repeat rewrite <- injectZeroIsGFZero;
    repeat rewrite <- injectOneIsGFOne.

  (* Tactic to passively convert from GF to Z in special circumstances *)
  Ltac GFconstant t :=
    match t with
    | inject ?x => x
    | _ => NotConstant
    end.

  (* Add our ring with all the fixin's *)
  Add Ring GFring_Z : GFring_theory
    (morphism GFring_morph,
     constants [GFconstant],
     div GFmorph_div_theory,
     power_tac GFpower_theory [GFexp_tac]). 

  (* Add our field with all the fixin's *)
  Add Field GFfield_Z : GFfield_theory
    (morphism GFring_morph,
     preprocess [GFpreprocess],
     postprocess [GFpostprocess],
     constants [GFconstant],
     div GFmorph_div_theory,
     power_tac GFpower_theory [GFexp_tac]). 

  Local Open Scope GF_scope.

  Lemma GF_mul_eq : forall x y z, z <> 0 -> x * z = y * z -> x = y.
  Proof.
    intros ? ? ? z_nonzero mul_z_eq.
    replace x with (x * 1) by field.
    rewrite <- (GF_multiplicative_inverse z_nonzero).
    replace (x * (GFinv z * z)) with ((x * z) * GFinv z) by ring.
    rewrite mul_z_eq.
    replace (y * z * GFinv z) with (y * (GFinv z * z)) by ring.
    rewrite GF_multiplicative_inverse; auto; field.
  Qed.

  Lemma GF_mul_0_l : forall x, 0 * x = 0.
  Proof.
    intros; field.
  Qed.

  Lemma GF_mul_0_r : forall x, x * 0 = 0.
  Proof.
    intros; field.
  Qed.

  Definition GF_eq_dec : forall x y : GF, {x = y} + {x <> y}.
    intros.
    assert (H := Z.eq_dec (inject x) (inject y)).

    destruct H.
    
    - left; galois; intuition.

    - right; intuition.
      rewrite H in n.
      assert (y = y); intuition.
  Qed.

    Lemma mul_nonzero_l : forall a b, a*b <> 0 -> a <> 0.
    intros; intuition; subst.
    assert (0 * b = 0) by field; intuition.
  Qed.

  Lemma mul_nonzero_r : forall a b, a*b <> 0 -> b <> 0.
    intros; intuition; subst.
    assert (a * 0 = 0) by field; intuition.
  Qed.

  Lemma mul_zero_why : forall a b, a*b = 0 -> a = 0 \/ b = 0.
    intros.
    assert (Z := GF_eq_dec a 0); destruct Z.

    - left; intuition.

    - assert (a * b / a = 0) by
        ( rewrite H; field; intuition ).

      field_simplify in H0.
      replace (b/1) with b in H0 by (field; intuition).
      right; intuition.
      apply n in H0; intuition.
  Qed.

  Lemma mul_nonzero_nonzero : forall a b, a <> 0 -> b <> 0 -> a*b <> 0.
    intros; intuition; subst.
    apply mul_zero_why in H1.
    destruct H1; subst; intuition.
  Qed.
  Hint Resolve mul_nonzero_nonzero.

  Lemma GFexp_distr_mul : forall x y z, (0 <= z)%N ->
    (x ^ z) * (y ^ z) = (x * y) ^ z.
  Proof.
    intros.
    replace z with (Z.to_N (Z.of_N z)) by apply N2Z.id.
    apply natlike_ind with (x := Z.of_N z); simpl; [ field | | 
      replace 0%Z with (Z.of_N 0%N) by auto; apply N2Z.inj_le; auto].
    intros z' z'_nonneg IHz'.
    rewrite Z2N.inj_succ by auto.
    rewrite (GFexp_pred x) by apply N.neq_succ_0.
    rewrite (GFexp_pred y) by apply N.neq_succ_0.
    rewrite (GFexp_pred (x * y)) by apply N.neq_succ_0.
    rewrite N.pred_succ.
    rewrite <- IHz'.
    field.
  Qed.

  Lemma GF_square_mul : forall x y z, (y <> 0) ->
    x ^ 2 = z * y ^ 2 -> exists sqrt_z, sqrt_z ^ 2 = z.
  Proof.
    intros ? ? ? y_nonzero A.
    exists (x / y).
    assert ((x / y) ^ 2 = x ^ 2 / y ^ 2) as square_distr_div. {
      unfold GFdiv, GFexp, GFexp'.
      replace (GFinv (y * y)) with (GFinv y * GFinv y); try ring.
      unfold GFinv.
      destruct (N.eq_dec (N.pred (totientToN totient)) 0) as [ eq_zero | neq_zero ];
        [ rewrite eq_zero | rewrite GFexp_distr_mul ]; try field.
      simpl.
      do 2 rewrite <- Z2N.inj_pred.
      replace 0%N with (Z.to_N 0%Z) by auto.
      apply Z2N.inj_le; modulus_bound.
    }
    assert (y ^ 2 <> 0) as y2_nonzero by (apply mul_nonzero_nonzero; auto).
    rewrite (GF_mul_eq _ z (y ^ 2)); auto.
    unfold GFdiv.
    rewrite <- A.
    field; auto.
  Qed.

  Lemma sqrt_solutions : forall x y, y ^ 2 = x ^ 2 -> y = x \/ y = GFopp x.
  Proof.
    intros.
    (* TODO(jadep) *)
  Admitted.

  Lemma GFopp_swap : forall x y, GFopp x = y <-> x = GFopp y.
  Proof.
    split; intro; subst; field.
  Qed.

  Lemma GFopp_involutive : forall x, GFopp (GFopp x) = x.
  Proof.
    intros; field.
  Qed.

End GaloisField.
