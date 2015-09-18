
Require Import Crypto.Galois.GaloisField Crypto.Galois.GaloisFieldTheory.
Require Import Tactics.VerdiTactics.

(** Theory of elliptic curves over prime fields for cryptographic applications,
with focus on the curves in <https://tools.ietf.org/html/draft-ladd-safecurves-04> *)
Module PointFormats (M: Modulus).
  Module Field := GaloisField M.
  Module Theory := GaloisFieldTheory M.
  Import M Field Theory.
  Local Open Scope GF_scope.
  Local Notation "2" := (1+1).
  Local Notation "3" := (1+1+1).
  Local Notation "27" := (3*3*3).

  (** [weierstrass] represents a point on an elliptic curve using Weierstrass
  * coordinates (<http://cs.ucsb.edu/~koc/ccs130h/2013/EllipticHyperelliptic-CohenFrey.pdf>) definition 13.1*)
  Record weierstrass := mkWeierstrass {weierstrassX : GF; weierstrassY : GF}.
  Definition weierstrassOnCurve (a1 a2 a3 a4 a5 a6:GF) (P : weierstrass) : Prop :=
    let x := weierstrassX P in
    let y := weierstrassY P in
    y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6.

  (** [montgomery] represents a point on an elliptic curve using Montgomery
  * coordinates (see <https://en.wikipedia.org/wiki/Montgomery_curve>) *)
  Record montgomery := mkMontgomery {montgomeryX : GF; montgomeryY : GF}.
  Definition montgomeryOnCurve (B A:GF) (P : montgomery) : Prop :=
    let x := montgomeryX P in
    let y := montgomeryY P in
    B*y^2 = x^3 + A*x^2 + x.

  (** see <http://cs.ucsb.edu/~koc/ccs130h/2013/EllipticHyperelliptic-CohenFrey.pdf> section 13.2.3.c and <https://en.wikipedia.org/wiki/Montgomery_curve#Equivalence_with_Weierstrass_curves> *)
  Definition montgomeryToWeierstrass (B A:GF) (P : montgomery) : weierstrass :=
    let x := montgomeryX P in
    let y := montgomeryY P in
    mkWeierstrass (x/B + A/(3*B)) (y/B).

  Lemma montgomeryToWeierstrassOnCurve : forall (B A:GF) (P:montgomery), 
    let a4 := 1/B^2 - A^2/(3*B^2) in
    let a6 := 0- A^3/(27*B^3) - a4*A/(3*B) in
    let P' := montgomeryToWeierstrass B A P in
    montgomeryOnCurve B A P -> weierstrassOnCurve 0 0 0 a4 0 a6 P'.
  Proof.
    intros.
    unfold montgomeryToWeierstrass, montgomeryOnCurve, weierstrassOnCurve in *.
    remember (weierstrassY P') as y in *.
    remember (weierstrassX P') as x in *.
    remember (montgomeryX P) as u in *.
    remember (montgomeryY P) as v in *.
    field_simplify.
    subst P'; simpl in Heqy, Heqx.
    clear P Hequ Heqv.
    (* This is not currently important and makes field run out of memory. Maybe
    * because I transcribed it incorrectly... *)
  Abort.

  (** [montgomeryxFrac] represents a point on an elliptic curve using Montgomery x
  * coordinate stored as fraction as in
  * <http://cr.yp.to/ecdh/curve25519-20060209.pdf> appendix B. *)
  Record montgomeryXFrac := mkMontgomeryXFrac {montgomeryXFracX : GF; montgomeryXFracZ : GF}.
  Definition montgomeryToMontgomeryXFrac P := mkMontgomeryXFrac (montgomeryX P) 1.
  Definition montgomeryXFracToMontgomeryX P : GF := (montgomeryXFracX P) / (montgomeryXFracZ P).

  (** [twisted] represents a point on an elliptic curve using twisted Edwards
  * coordinates (see <https://www.hyperelliptic.org/EFD/g1p/auto-twisted.html>
  * <https://eprint.iacr.org/2008/013.pdf>, and <http://ed25519.cr.yp.to/ed25519-20110926.pdf>) *)
  Record twisted := mkTwisted {twistedX : GF; twistedY : GF}.
  Definition twistedOnCurve (a d:GF) (P : twisted) : Prop :=
    let x := twistedX P in
    let y := twistedY P in
    a*x^2 + y^2 = 1 + d*x^2*y^2.

  (* <https://eprint.iacr.org/2008/013.pdf> Theorem 3.2. *)
  (* TODO: exceptional points *)
  Definition twistedToMontfomery (a d:GF) (P : twisted) : montgomery := 
    let x := twistedX P in
    let y := twistedY P in
    mkMontgomery ((1+y)/(1-y)) ((1+y)/((1-y)*x)).
  Definition montgomeryToTwisted (B A:GF) (P : montgomery) : twisted :=
    let X := montgomeryX P in
    let Y := montgomeryY P in
    mkTwisted (X/Y) ((X-1)/(X+1)).

  (** [projective] represents a point on an elliptic curve using projective
  * Edwards coordinates for twisted edwards curves with a=-1 (see
  * <https://hyperelliptic.org/EFD/g1p/auto-edwards-projective.html>
  * <https://en.wikipedia.org/wiki/Edwards_curve#Projective_homogeneous_coordinates>) *)
  Record projective := mkProjective {projectiveX : GF; projectiveY : GF; projectiveZ : GF}.
  Definition twistedToProjective (P : twisted) : projective :=
    let x := twistedX P in
    let y := twistedY P in
    mkProjective x y 1.

  Definition projectiveToTwisted (P : projective) : twisted :=
    let X := projectiveX P in
    let Y := projectiveY P in
    let Z := projectiveZ P in
    mkTwisted (X/Z) (Y/Z).

  (** [extended] represents a point on an elliptic curve using extended projective
  * Edwards coordinates with twist a=-1 (see <https://eprint.iacr.org/2008/522.pdf>). *)
  Record extended := mkExtended {extendedToProjective : projective; extendedT : GF}.
  Definition extendedValid (P : extended) : Prop :=
    let pP := extendedToProjective P in
    let X := projectiveX pP in
    let Y := projectiveY pP in
    let Z := projectiveZ pP in
    let T := extendedT P in
    X*Y = Z*T.

  Definition twistedToExtended (P : twisted) : extended :=
    let x := twistedX P in
    let y := twistedY P in
    mkExtended (mkProjective x y 1) (x*y).

  Definition extendedToTwisted (P : extended) : twisted :=
    projectiveToTwisted (extendedToProjective P).

  (** [precomputed] represents a point on an elliptic curve using "precomputed"
  * Edwards coordinates, as used for fixed-base scalar multiplication
  * (see <http://ed25519.cr.yp.to/ed25519-20110926.pdf> section 4: addition). *)
  Record precomputed := mkPrecomputed {precomputedSum : GF;
                                       precomputedDifference : GF;
                                       precomputed2dxy : GF}.
  Definition twistedToPrecomputed (d:GF) (P : twisted) : precomputed :=
    let x := twistedX P in
    let y := twistedY P in
    mkPrecomputed (y+x) (y-x) (2*d*x*y).


  (** <https://www.hyperelliptic.org/EFD/g1p/auto-twisted.html> *)
  Definition twistedAdd (a d:GF) (P1 P2 : twisted) : twisted :=
    let x1 := twistedX P1 in
    let y1 := twistedY P1 in
    let x2 := twistedX P2 in
    let y2 := twistedY P2 in
    mkTwisted
      ((x1*y2 +   y1*x2)/(1 + 2*d*x1*x2*y1*y2))
      ((y1*y2 - a*x1*x2)/(1 - 2*d*x1*x2*y1*y2))
  .

  (** From <https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-03> *)
  Definition extendedM1Add (d:GF) (P1 P2 : extended) : extended :=
    let pP1 := extendedToProjective P1 in
    let X1 := projectiveX pP1 in
    let Y1 := projectiveY pP1 in
    let Z1 := projectiveZ pP1 in
    let T1 := extendedT P1 in
    let pP2 := extendedToProjective P2 in
    let X2 := projectiveX pP2 in
    let Y2 := projectiveY pP2 in
    let Z2 := projectiveZ pP2 in
    let T2 := extendedT P2 in
    let  A := (Y1-X1)*(Y2-X2) in
    let  B := (Y1+X1)*(Y2+X2) in
    let  C := T1*2*d*T2 in
    let  D := Z1*2*Z2 in
    let  E := B-A in
    let  F := D-C in
    let  G := D+C in
    let  H := B-A in
    let X3 := E*F in
    let Y3 := G*H in
    let T3 := E*H in
    let Z3 := F*G in
    mkExtended (mkProjective X3 Y3 Z3) T3.

  Lemma extendeM1dAddCon : forall (d:GF)
    (P1 P2 P3 : extended) (HeqP3 : P3 = extendedM1Add d P1 P2),
    extendedValid P3.
  Proof.
    intros.
    destruct P1 as [[X1 Y1 Z1] T1].
    destruct P2 as [[X2 Y2 Z2] T2].
    destruct P3 as [[X3 Y3 Z3] T3].
    unfold extendedValid, extendedToProjective, projectiveToTwisted, twistedX, twistedY in *.
    invcs HeqP3.

    field.
  Qed.

  Lemma extendedM1AddRep : forall (d:GF) (P1 P2 : extended) (tP1 tP2 : twisted)
    (P1con : extendedValid P1) (P1rep : extendedToTwisted P1 = tP1)
    (P2con : extendedValid P2) (P2rep : extendedToTwisted P2 = tP2),
    twistedAdd (0-1) d tP1 tP2 = extendedToTwisted (extendedM1Add d P1 P2).
  Proof.
    intros.
    destruct P1 as [[X1 Y1 Z1] T1]; destruct P2 as [[X2 Y2 Z2] T2].
    unfold extendedValid, twistedAdd, extendedToTwisted, extendedToProjective, projectiveToTwisted, twistedX, twistedY in *.
    break_let; break_let.
    invcs P1rep; invcs P2rep.

    f_equal.

    assert (T1 = X1 * Y1 / Z1).

    (*
    FIXME:
    In nested Ltac calls to "field" and
    "field_lookup PackField ltac:FIELD [  ] G" (expanded to
    "field_lookup <dynamic [value]> [  ] (T1 = X1 * Y2 / Z2)"), last call failed.
    Error: cannot find a declared field structure over "GF"
    *)

    Abort.

End PointFormats.
