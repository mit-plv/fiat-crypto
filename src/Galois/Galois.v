
Require Import BinInt BinNat ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import Tactics.VerdiTactics.

(* This file is for the high-level type definitions of
 * GF, Primes, Moduli, etc. and their notations and essential
 * operations.
 *
 * The lemmas required for the ring and field theories are
 * in GaloisTheory.v and the actual tactic implementations
 * for the field are in GaloisField.v. An introduction to the
 * use of our implementation of the Galois field is in
 * GaloisTutorial.v
 *)

Section GaloisPreliminaries.
  (* The core prime modulus type, relying on Znumtheory's prime *)
  Definition Prime := {x: Z | prime x}.

  (* Automagically coerce primes to Z *)
  Definition primeToZ(x: Prime) := proj1_sig x.
  Coercion primeToZ: Prime >-> Z.
End GaloisPreliminaries.

(* A module to hold the field's modulus, which will be an argument to
 * all of our Galois modules.
 *)
Module Type Modulus.
  Parameter modulus: Prime.
End Modulus.

(* The core Galois Field model *)
Module Galois (M: Modulus).
  Import M.

  (* The sigma definition of an element of the field: we have
   * an element corresponding to the values in Z which can be
   * produced by a 'mod' operation.
   *)
  Definition GF := {x: Z | x = x mod modulus}.

  Delimit Scope GF_scope with GF.
  Local Open Scope GF_scope.

  (* Automagically convert GF to Z when needed *)
  Definition GFToZ(x: GF) := proj1_sig x.
  Coercion GFToZ: GF >-> Z.

  (* Automagically convert Z to GF when needed *)
  Definition inject(x: Z):  GF.
    exists (x mod modulus).
    abstract (rewrite Zmod_mod; trivial).
  Defined.

  Coercion inject : Z >-> GF.

  (* Convert Z to GF without a mod operation, for when the modulus is opaque *)
  Definition ZToGF (x: Z) : if ((0 <=? x) && (x <? modulus))%bool then GF else True.
    break_if; [|trivial].
    exists x.
    destruct (Bool.andb_true_eq _ _ (eq_sym Heqb)); clear Heqb.
    erewrite Zmod_small; [trivial|].
    intuition.
    - rewrite <- Z.leb_le; auto.
    - rewrite <- Z.ltb_lt; auto.
  Defined.

  (* Core lemma: equality in GF implies equality in Z *)
  Theorem gf_eq: forall (x y: GF), x = y <-> GFToZ x = GFToZ y.
  Proof.
    destruct x, y; intuition; simpl in *; try congruence.
    subst x.
    f_equal.
    apply UIP_dec.
    apply Z.eq_dec.
  Qed.

  (* Core values: One and Zero *)
  Definition GFzero: GF.
    exists 0.
    abstract trivial.
  Defined.

  Definition GFone: GF.
    exists 1.
    abstract( symmetry; apply Zmod_small; intuition;
              destruct modulus; simpl;
              apply prime_ge_2 in p; intuition).
  Defined.

  Lemma GFone_nonzero : GFone <> GFzero.
  Proof.
    unfold GFone, GFzero.
    intuition; solve_by_inversion.
  Qed.
  Hint Resolve GFone_nonzero.

  (* Elementary operations: +, -, * *)
  Definition GFplus(x y: GF): GF.
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

  (* Modular exponentiation *)
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

  (* Preliminaries to inversion in a prime field *)
  Definition isTotient(e: N) := N.gt e 0 /\ forall g: GF, g <> GFzero ->
    GFexp g e = GFone.

  Definition Totient := {e: N | isTotient e}.

  (* Get a totient via Fermat's little theorem *)
  Theorem fermat_little_theorem: isTotient (N.pred (Z.to_N modulus)).
  Admitted.

  Definition totient : Totient.
    exists (N.pred (Z.to_N modulus)).
    exact fermat_little_theorem.
  Defined.

  Definition totientToN(x: Totient) := proj1_sig x.
  Coercion totientToN: Totient >-> N.

  (* Define inversion and division *)
  Definition GFinv(x: GF): GF := GFexp x (N.pred totient).

  Definition GFdiv(x y: GF): GF := GFmult x (GFinv y).

  (* Notations for all of the operations we just made *)
  Notation "1" := GFone : GF_scope.
  Notation "0" := GFzero : GF_scope.
  Infix "+"    := GFplus : GF_scope.
  Infix "-"    := GFminus : GF_scope.
  Infix "*"    := GFmult : GF_scope.
  Infix "/"    := GFdiv : GF_scope.
  Infix "^"    := GFexp : GF_scope.

End Galois.
