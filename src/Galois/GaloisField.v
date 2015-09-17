
Require Import BinInt BinNat ZArith Znumtheory.
Require Import ProofIrrelevance.

Section GaloisPreliminaries.
  Definition Prime := {x: Z | prime x}.

  Definition primeToZ(x: Prime) := proj1_sig x.
  Coercion primeToZ: Prime >-> Z.

  Theorem exist_eq: forall (x y: Z) P e1 e2, x = y <-> exist P x e1 = exist P y e2.
    intros. split.
      intro H. apply subset_eq_compat; trivial.
      intro H.
      assert (proj1_sig (exist P x e1) = proj1_sig (exist P y e2)).
        rewrite H. trivial.
      simpl in H0. rewrite H0. trivial.
  Qed.
End GaloisPreliminaries.

Module Type Modulus.
  Parameter modulus: Prime.
End Modulus.

Module GaloisField (M: Modulus).
  Import M.

  Definition GF := {x: Z | exists y, x = y mod modulus}.
  Definition GFToZ(x: GF) := proj1_sig x.
  Coercion GFToZ: GF >-> Z.

  Theorem gf_eq: forall (x y: GF), x = y <-> GFToZ x = GFToZ y.
    intros x y. destruct x, y. split; apply exist_eq.
  Qed.

  (* Elementary operations *)
  Definition GFzero: GF.
    exists 0, 0.
    abstract trivial.
  Defined.

  Definition GFone: GF.
    exists 1, 1.
    abstract (symmetry; apply Zmod_small; intuition; destruct modulus; simpl;
              apply prime_ge_2 in p; intuition).
  Defined.

  Definition GFplus(x y: GF): GF.
    exists ((x + y) mod modulus), (x + y).
    abstract trivial.
  Defined.

  Definition GFminus(x y: GF): GF.
    exists ((x - y) mod modulus), (x - y).
    abstract trivial.
  Defined.

  Definition GFmult(x y: GF): GF.
    exists ((x * y) mod modulus), (x * y).
    abstract trivial.
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
  Definition isTotient(e: N) := N.gt e 0 /\ forall g, GFexp g e = GFone.

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
