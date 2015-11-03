
Require Import BinInt BinNat ZArith Znumtheory.
Require Import BoolEq Field_theory.
Require Import Galois GaloisTheory.

Module ZGaloisField (M: Modulus).
  Module G := Galois M.
  Module T := GaloisTheory M.
  Export M G T.

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

  Ltac GFpreprocess :=
    repeat rewrite injectZeroIsGFZero;
    repeat rewrite injectOneIsGFOne.

  Ltac GFpostprocess :=
    repeat rewrite <- injectZeroIsGFZero;
    repeat rewrite <- injectOneIsGFOne.

  Ltac GFconstant t :=
    match t with
    | inject ?x => x
    | _ => NotConstant
    end.

  Add Ring GFring_Z : GFring_theory
    (morphism GFring_morph,
     constants [GFconstant],
     div GFmorph_div_theory,
     power_tac GFpower_theory [GFexp_tac]).

  Add Field GFfield_Z : GFfield_theory
    (morphism GFring_morph,
     preprocess [GFpreprocess],
     postprocess [GFpostprocess],
     constants [GFconstant],
     div GFmorph_div_theory,
     power_tac GFpower_theory [GFexp_tac]). 

End ZGaloisField.

