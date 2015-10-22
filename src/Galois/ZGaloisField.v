
Require Import BinInt BinNat ZArith Znumtheory.
Require Import BoolEq.
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

  Add Ring GFring_Z : GFring_theory
    (morphism GFring_morph,
     power_tac GFpower_theory [GFexp_tac]).

  Add Field GFfield_Z : GFfield_theory
    (morphism GFring_morph,
     power_tac GFpower_theory [GFexp_tac]).

End ZGaloisField.

