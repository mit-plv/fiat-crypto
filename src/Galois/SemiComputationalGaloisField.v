
Require Import BinInt BinNat ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import Tactics.VerdiTactics.
Require Import Galois GaloisTheory.

Module ComputationalGaloisField (M: Modulus).
  Module G := Galois M.
  Module T := GaloisTheory M.
  Export M G T.

  (* Useful small-number lemmas *)
  Definition isSmall (x: Z) := x <? SMALL_THRESH.

  Lemma small_prop: forall x: Z, isSmall x = true <-> x < SMALL_THRESH.
  Proof.
    intros; unfold isSmall; apply (Z.ltb_lt x SMALL_THRESH).
  Qed.

  Lemma small_neg_prop: forall x: Z, isSmall x = false <-> SMALL_THRESH <= x.
  Proof.
    intros; unfold isSmall; apply (Z.ltb_ge x SMALL_THRESH).
  Qed.

  Lemma small_dec: forall x: Z, {isSmall x = true} + {isSmall x = false}.
  Proof.
    intros; induction (isSmall x); intuition.
  Qed.

  Lemma double_small_dec: forall x y: Z,
      {isSmall x = true  /\ isSmall y = true}
    + {isSmall x = false \/ isSmall y = false}.
  Proof.
    intros; destruct (small_dec x), (small_dec y).
    - left; intuition.
    - right; intuition.
    - right; intuition.
    - right; intuition.
  Qed.

  Lemma GF_ge_zero: forall x: GF, x >= 0.
  Proof.
    intros; destruct x; simpl; rewrite e.
    assert (modulus > 0);
      destruct modulus; destruct a;
      assert (Z := prime_ge_2 x0); simpl; intuition.
    assert (A := Z_mod_lt x x0).
    intuition.
  Qed.

  Lemma small_plus: forall x y: GF,
    isSmall x = true -> isSmall y = true ->
      x + y = (x + y) mod modulus.
  Proof.
    intros. rewrite Zmod_small; trivial.
    rewrite small_prop in H, H0.
    assert (Hx := GF_ge_zero x).
    assert (Hy := GF_ge_zero y).
    split; try intuition.

    destruct modulus; simpl in *.
    destruct a.
    assert (x0 > SMALL_THRESH * SMALL_THRESH); intuition.
    assert (SMALL_THRESH * SMALL_THRESH > SMALL_THRESH + SMALL_THRESH);
      simpl; intuition.
  Qed.

  Lemma small_minus: forall x y: GF,
    isSmall x = true -> isSmall y = true -> x >= y ->
      x - y = (x - y) mod modulus.
  Proof.
    intros. rewrite Zmod_small; trivial.
    rewrite small_prop in H, H0.
    assert (Hx := GF_ge_zero x).
    assert (Hy := GF_ge_zero y).
    split; try intuition.

    destruct modulus; simpl in *.
    destruct a.
    assert (x0 > SMALL_THRESH * SMALL_THRESH); intuition.
    assert (SMALL_THRESH * SMALL_THRESH > SMALL_THRESH + SMALL_THRESH);
      simpl; intuition.
  Qed.

  Lemma small_mult: forall x y: GF,
    isSmall x = true -> isSmall y = true ->
      x * y = (x * y) mod modulus.
  Proof.
    intros. rewrite Zmod_small; trivial.
    rewrite small_prop in H, H0.
    assert (Hx := GF_ge_zero x).
    assert (Hy := GF_ge_zero y).
    split; try intuition.

    destruct x, y; simpl in *.
    destruct modulus; simpl in *.
    destruct a.
    assert (x1 > SMALL_THRESH * SMALL_THRESH); intuition.
    assert (x * x0 <= SMALL_THRESH * SMALL_THRESH); intuition.
    left.
  Qed.

  Ltac isModulusConstant :=
    let hnfModulus := eval hnf in (proj1_sig modulus)
    in match (isZcst hnfModulus) with
    | NotConstant => NotConstant
    | _ => match hnfModulus with
      | Z.pos _ => true
      | _ => false
      end
    end.

  Ltac isGFconstant t :=
    match t with
    | GFzero => true
    | GFone => true
    | ZToGF _ => isModulusConstant
    | exist _ ?z _ => match (isZcst z) with
      | NotConstant => NotConstant
      | _ => isModulusConstant
      end
    | _ => NotConstant
    end.

  Ltac GFconstants t :=
    match isGFconstant t with
    | NotConstant => NotConstant
    | _ => t
    end.

  Definition GFplus'(x y: GF): GF.
    destruct (double_small_dec x y).
    exists (x + y).
      (* Admitted *)

    exists ((x + y) mod modulus);
    abstract (rewrite Zmod_mod; trivial).
  Defined.

  Definition GFminus'(x y: GF): GF.
    destruct (double_small_dec x y).
    exists (x - y).
      (* Admitted *)

    exists ((x - y) mod modulus).
    abstract (rewrite Zmod_mod; trivial).
  Defined.

  Definition GFmult'(x y: GF): GF.
    destruct (double_small_dec x y).
    exists (x * y).
      (* Admitted *)

    exists ((x * y) mod modulus).
    abstract (rewrite Zmod_mod; trivial).
  Defined.

  Definition GFopp'(x: GF): GF := GFminus' GFzero x.

  Definition GFsemicomp_field_theory : field_theory GFzero GFone GFplus' GFmult' GFminus' GFopp' GFdiv GFinv eq.
  Proof.
    constructor; auto.
  Qed.

  Add Field GFfield_semi : GFsemicomp_field_theory
    (decidable GFdecidable,
     completeness GFcomplete,
     constants [GFconstants],
     div GFdiv_theory,
     power_tac GFpower_theory [GFexp_tac]).

End ComputationalGaloisField.
