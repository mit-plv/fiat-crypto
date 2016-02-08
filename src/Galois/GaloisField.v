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

  Lemma divOneIsX :
    forall (x: GF), (x / 1)%GF = x.
  Proof.
    intros; unfold GFdiv.

    replace (GFinv 1)%GF with 1%GF by (
      replace (GFinv 1)%GF with (GFinv 1 * 1)%GF by ring;
      rewrite GF_multiplicative_inverse; intuition).

    ring.
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

    repeat match goal with
    | [ |- context[exist ?a ?b (inject_subproof ?x)] ] =>
      replace (exist a b (inject_subproof x)) with (inject x%Z) by reflexivity
    end;

    repeat rewrite <- injectZeroIsGFZero;
    repeat rewrite <- injectOneIsGFOne;
    repeat rewrite divOneIsX.

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

End GaloisField.
