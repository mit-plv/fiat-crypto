
Require Import BinInt BinNat ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import Tactics.VerdiTactics.

Section GaloisPreliminaries.
  Definition SMALL_THRESH: Z := 128.
  Definition MIN_PRIME: Z := SMALL_THRESH * SMALL_THRESH.

  Definition Prime := {x: Z | prime x /\ x > MIN_PRIME}.

  Definition primeToZ(x: Prime) := proj1_sig x.
  Coercion primeToZ: Prime >-> Z.
End GaloisPreliminaries.

Module Type Modulus.
  Parameter modulus: Prime.
End Modulus.

Module GaloisField (M: Modulus).
  Import M.

  Definition GF := {x: Z | x = x mod modulus}.
  Definition GFToZ(x: GF) := proj1_sig x.
  Coercion GFToZ: GF >-> Z.

  Definition ZToGF (x: Z) : if ((0 <=? x) && (x <? modulus))%bool then GF else True.
    break_if; [|trivial].
    exists x.
    destruct (Bool.andb_true_eq _ _ (eq_sym Heqb)); clear Heqb.
    erewrite Zmod_small; [trivial|].
    intuition.
    - rewrite <- Z.leb_le; auto.
    - rewrite <- Z.ltb_lt; auto.
  Defined.

  Theorem gf_eq: forall (x y: GF), x = y <-> GFToZ x = GFToZ y.
  Proof.
    destruct x, y; intuition; simpl in *; try congruence.
    subst x.
    f_equal.
    apply UIP_dec.
    apply Z.eq_dec.
  Qed.

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

  (* Elementary operations *)
  Definition GFzero: GF.
    exists 0.
    abstract trivial.
  Defined.

  Definition GFone: GF.
    exists 1.
    abstract (symmetry; apply Zmod_small; intuition;
              destruct modulus; simpl; destruct a;
              apply prime_ge_2 in H; intuition).
  Defined.

  Definition GFplus(x y: GF): GF.
    destruct (double_small_dec x y).

    exists (x + y).
      rewrite Zmod_small; trivial.
      destruct modulus.
      destruct a.
      assert (0 <= x + y).
        auto with arith.
      assert (x + y < SMALL_THRESH + SMALL_THRESH).
      unfold isSmall, SMALL_THRESH in *.
      intuition.

    exists ((x + y) mod modulus);
      abstract (rewrite Zmod_mod; trivial).

  Defined.

  Definition GFminus(x y: GF): GF.
    exists ((x - y) mod modulus).
    abstract (rewrite Zmod_mod; trivial).
  Defined.

  Definition GFmult(x y: GF): GF.
    exists ((x * y) mod modulus).
    abstract (rewrite Zmod_mod; trivial).
  Defined.

  Definition GFopp(x: GF): GF := GFminus GFzero x.

  (* Totient Preliminaries *)
  Fixpoint GFexp' (x: GF) (power: positive) :=
    match power with
    | xH => x
    | xO power' => GFexp' (GFmult x x) power'
    | xI power' => GFmult x (GFexp' (GFmult x x) power')
    end.

  Definition GFexp (x: GF) (power: N): GF :=
    match power with
    | N0 => GFone
    | Npos power' => GFexp' x power'
    end.

  (* Inverses + division derived from the existence of a totient *)
  Definition isTotient(e: N) := N.gt e 0 /\ forall g: GF, g <> GFzero ->
    GFexp g e = GFone.

  Definition Totient := {e: N | isTotient e}.

  Theorem fermat_little_theorem: isTotient (N.pred (Z.to_N modulus)).
  Admitted.

  Definition totient : Totient.
    exists (N.pred (Z.to_N modulus)).
    exact fermat_little_theorem.
  Defined.

  Definition totientToN(x: Totient) := proj1_sig x.
  Coercion totientToN: Totient >-> N.

  Definition GFinv(x: GF): GF := GFexp x (N.pred totient).

  Definition GFdiv(x y: GF): GF := GFmult x (GFinv y).

End GaloisField.
