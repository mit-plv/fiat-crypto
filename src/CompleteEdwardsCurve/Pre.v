Require Import Coq.Classes.Morphisms. Require Coq.Setoids.Setoid.
Require Import Crypto.Algebra Crypto.Algebra.
Require Import Crypto.Util.Notations Crypto.Util.Decidable Crypto.Util.Tactics.

Section Pre.
  Context {F eq zero one opp add sub mul inv div}
          {field:@Algebra.field F eq zero one opp add sub mul inv div}
          {eq_dec:DecidableRel eq}.
  Add Field EdwardsCurveField : (Field.field_theory_for_stdlib_tactic (T:=F)).

  Local Infix "=" := eq. Local Notation "a <> b" := (not (a = b)).
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := zero.  Local Notation "1" := one.
  Local Infix "+" := add. Local Infix "*" := mul.
  Local Infix "-" := sub. Local Infix "/" := div.
  Local Notation "x ^ 2" := (x*x).

  Context (a:F) (a_nonzero : a<>0) (a_square : exists sqrt_a, sqrt_a^2 = a).
  Context (d:F) (d_nonsquare : forall sqrt_d, sqrt_d^2 <> d).
  Context (char_gt_2 : 1+1 <> 0).

  Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2).
  Lemma zeroOnCurve : onCurve 0 1. nsatz. Qed.

  Section Addition.
    Context (x1 y1:F) (P1onCurve: onCurve x1 y1).
    Context (x2 y2:F) (P2onCurve: onCurve x2 y2).
    Lemma denominator_nonzero : (d*x1*x2*y1*y2)^2 <> 1.
    Proof.
      destruct a_square as [sqrt_a], (dec(sqrt_a*x2+y2 = 0)), (dec(sqrt_a*x2-y2 = 0));
        try match goal with [H: ?f (sqrt_a * x2) y2 <> 0 |- _ ]
            => specialize (d_nonsquare ((f (sqrt_a * x1) (d * x1 * x2 * y1 * y2 * y1))
                                       /(f (sqrt_a * x2) y2     *   x1 * y1        )))
            end; field_nsatz.
    Qed.

    Lemma add_onCurve : onCurve ((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2)) ((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2)).
    Proof. pose proof denominator_nonzero; field_nsatz. Qed.
  End Addition.
End Pre.