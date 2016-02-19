Require BinInt Znumtheory.

Require Crypto.CompleteEdwardsCurve.Pre.

Require Import Crypto.Spec.ModularArithmetic.
Local Open Scope F_scope.

Class TwistedEdwardsParams := {
  q : BinInt.Z;
  a : F q;
  d : F q;
  prime_q : Znumtheory.prime q;
  two_lt_q : BinInt.Z.lt 2 q;
  nonzero_a : a <> 0;
  square_a : exists sqrt_a, sqrt_a^2 = a;
  nonsquare_d : forall x, x^2 <> d
}.

Section TwistedEdwardsCurves.
  Context {prm:TwistedEdwardsParams}.

  (* Twisted Edwards curves with complete addition laws. References:
  * <https://eprint.iacr.org/2008/013.pdf>
  * <http://ed25519.cr.yp.to/ed25519-20110926.pdf>
  * <https://eprint.iacr.org/2015/677.pdf>
  *)
  Definition onCurve P := let '(x,y) := P in a*x^2 + y^2 = 1 + d*x^2*y^2.
  Definition point := { P | onCurve P}.
  Definition mkPoint (xy:F q * F q) (pf:onCurve xy) : point := exist onCurve xy pf.

  Definition zero : point := mkPoint (0, 1) (@Pre.zeroOnCurve _ _ _ prime_q).
  
  Definition unifiedAdd' P1' P2' :=
    let '(x1, y1) := P1' in
    let '(x2, y2) := P2' in
      (((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2)) , ((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2))).

  Definition unifiedAdd (P1 P2 : point) : point :=
    let 'exist P1' pf1 := P1 in
    let 'exist P2' pf2 := P2 in
    mkPoint (unifiedAdd' P1' P2')
      (@Pre.unifiedAdd'_onCurve _ _ _ prime_q two_lt_q nonzero_a square_a nonsquare_d _ _ pf1 pf2).

  Fixpoint scalarMult (n:nat) (P : point) : point :=
    match n with
    | O => zero
    | S n' => unifiedAdd P (scalarMult n' P)
    end.
End TwistedEdwardsCurves.

Delimit Scope E_scope with E.
Infix "+" := unifiedAdd : E_scope.
Infix "*" := scalarMult : E_scope.