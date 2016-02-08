Require BinInt Znumtheory.

Require Crypto.CompleteEwardsCurve.Pre.

Require Import Crypto.Spec.ModularArithmetic.
Local Open Scope F_scope.

Class TwistedEdwardsParams := {
  p : BinInt.Z;
  a : F p;
  d : F p;
  modulus_prime : Znumtheory.prime p;
  a_nonzero : a <> 0;
  a_square : exists sqrt_a, sqrt_a^2 = a;
  d_nonsquare : forall x, x^2 <> d
}.

Section TwistedEdwardsCurves.
  Context `{prm:TwistedEdwardsParams}.
  (* Twisted Edwards curves with complete addition laws. References:
  * <https://eprint.iacr.org/2008/013.pdf>
  * <http://ed25519.cr.yp.to/ed25519-20110926.pdf>
  * <https://eprint.iacr.org/2015/677.pdf>
  *)
  Definition onCurve P := let '(x,y) := P in a*x^2 + y^2 = 1 + d*x^2*y^2.
  Definition point := { P | onCurve P}.
  Definition mkPoint xy proof : point := exist onCurve xy proof.
  Definition projX (P:point) : F p := fst (proj1_sig P).
  Definition projY (P:point) : F p:= snd (proj1_sig P).

  Definition zero : point := mkPoint (0, 1) Pre.zeroOnCurve.
  
  (* NOTE: the two matches on P1 can probably be merged, not sure whether good idea... *)
  Definition unifiedAdd (P1 P2 : point) : point :=
    let 'exist P1' pf1 := P1 in
    let 'exist P2' pf2 := P2 in
    mkPoint
      ( let '(x1, y1) := P1' in
        let '(x2, y2) := P2' in
        (((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2)) , ((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2))))
      (Pre.unifiedAdd'_onCurve _ _ pf1 pf2).
  Local Infix "+" := unifiedAdd.

  Fixpoint scalarMult (n:nat) (P : point) : point :=
    match n with
    | O => zero
    | S n' => P + scalarMult n' P
    end.
End TwistedEdwardsCurves.