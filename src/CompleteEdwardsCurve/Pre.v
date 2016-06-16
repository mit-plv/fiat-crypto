Require Import Coq.Classes.Morphisms. Require Coq.Setoids.Setoid.
Require Import Crypto.Algebra.

Generalizable All Variables.
Section Pre.
  Context {F eq zero one opp add sub mul inv div} `{field F eq zero one opp add sub mul inv div}.
  Local Infix "=" := eq. Local Notation "a <> b" := (not (a = b)).
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := zero.  Local Notation "1" := one.
  Local Infix "+" := add. Local Infix "*" := mul.
  Local Infix "-" := sub. Local Infix "/" := div.
  Local Notation "x '^' 2" := (x*x) (at level 30).

  Add Field EdwardsCurveField : (Field.field_theory_for_stdlib_tactic (T:=F)).

  Context {a:F} {a_nonzero : a<>0} {a_square : exists sqrt_a, sqrt_a^2 = a}.
  Context {d:F} {d_nonsquare : forall sqrt_d, sqrt_d^2 <> d}.
  Context {char_gt_2 : 1+1 <> 0}.
  
  (* the canonical definitions are in Spec *)
  Definition onCurve (P:F*F) := let (x, y) := P in a*x^2 + y^2 = 1 + d*x^2*y^2.
  Definition unifiedAdd' (P1' P2':F*F) : F*F :=
    let (x1, y1) := P1' in
    let (x2, y2) := P2' in
    pair (((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2))) (((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2))).
  
  Ltac use_sqrt_a := destruct a_square as [sqrt_a a_square']; rewrite <-a_square' in *.

  Lemma edwardsAddComplete' x1 y1 x2 y2 :
    onCurve (pair x1 y1) ->
    onCurve (pair x2 y2) ->
    (d*x1*x2*y1*y2)^2 <> 1.
  Proof.
    unfold onCurve, not; use_sqrt_a; intros.
    destruct (eq_dec (sqrt_a*x2 + y2) 0); destruct (eq_dec (sqrt_a*x2 - y2) 0);
      lazymatch goal with
      | [H: not (eq (?f (sqrt_a * x2)  y2) 0) |- _ ]
        => apply d_nonsquare with (sqrt_d:= (f (sqrt_a * x1) (d * x1 * x2 * y1 * y2 * y1))
                                           /(f (sqrt_a * x2) y2   *   x1 * y1           ))
      | _ => apply a_nonzero
      end; field_algebra; auto using Ring.opp_nonzero_nonzero.
  Qed.

  Lemma edwardsAddCompletePlus x1 y1 x2 y2 :
    onCurve (x1, y1) -> onCurve (x2, y2) -> (1 + d*x1*x2*y1*y2) <> 0.
  Proof. intros H1 H2 ?. apply (edwardsAddComplete' _ _ _ _ H1 H2); field_algebra. Qed.
  
  Lemma edwardsAddCompleteMinus x1 y1 x2 y2 :
    onCurve (x1, y1) -> onCurve (x2, y2) -> (1 - d*x1*x2*y1*y2) <> 0.
  Proof. intros H1 H2 ?. apply (edwardsAddComplete' _ _ _ _ H1 H2); field_algebra. Qed.
  
  Lemma zeroOnCurve : onCurve (0, 1). Proof. simpl. field_algebra. Qed.
  
  Lemma unifiedAdd'_onCurve : forall P1 P2,
    onCurve P1 -> onCurve P2 -> onCurve (unifiedAdd' P1 P2).
  Proof.
    unfold onCurve, unifiedAdd'; intros [x1 y1] [x2 y2] H1 H2.
    field_algebra; auto using edwardsAddCompleteMinus, edwardsAddCompletePlus.
  Qed.
End Pre.