Require Import Coq.Classes.Morphisms. Require Coq.Setoids.Setoid.
Close Scope nat_scope. Close Scope type_scope. Close Scope core_scope.
Require Import Crypto.SaneField.

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
  Context {d:F} {d_nonsquare : forall x, x^2 <> d}.
  Context {char_gt_2 : 1+1 <> 0}.
  
  (* the canonical definitions are in Spec *)
  Definition onCurve (P:F*F) := let (x, y) := P in a*x^2 + y^2 = 1 + d*x^2*y^2.
  Definition unifiedAdd' (P1' P2':F*F) : F*F :=
    let (x1, y1) := P1' in
    let (x2, y2) := P2' in
    pair (((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2))) (((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2))).

  Ltac admit_nonzero := abstract (repeat split; match goal with |- not (eq _ 0) => admit end).

  Lemma edwardsAddComplete' x1 y1 x2 y2 :
    onCurve (pair x1 y1) ->
    onCurve (pair x2 y2) ->
    (d*x1*x2*y1*y2)^2 <> 1.
  Proof.
    unfold onCurve, not; intros.
    assert (d * x1 ^2 * y1 ^2 * (a * x2 ^2 + y2 ^2) = a * x1 ^2 + y1 ^2) as Heqt by nsatz.
    destruct a_square as [sqrt_a a_square']; rewrite <-a_square' in *.
    destruct (eq_dec (sqrt_a*x2 + y2) 0); destruct (eq_dec (sqrt_a*x2 - y2) 0);
      lazymatch goal with
      | [H: not (eq (?f (sqrt_a * x2)  y2) 0) |- _ ]
        => eapply (d_nonsquare ((f (sqrt_a * x1) (d * x1 * x2 * y1 * y2 * y1)) / (x1 * y1 * (f (sqrt_a * x2)  y2))  ));
             nsatz; admit_nonzero
      | _ => apply a_nonzero; (do 2 nsatz) (* TODO: why does it not win on the first call? *)
      end.
  Qed.

  Lemma edwardsAddCompletePlus x1 y1 x2 y2 :
    onCurve (x1, y1) ->
    onCurve (x2, y2) ->
    (1 + d*x1*x2*y1*y2) <> 0.
  Proof.
    intros Hc1 Hc2; simpl in Hc1, Hc2.
    intros; destruct (F_eq_dec (d*x1*x2*y1*y2) (0-1)) as [H|H].
    - assert ((d*x1*x2*y1*y2)^2 = 1) by (rewriteAny; field). destruct (edwardsAddComplete' x1 y1 x2 y2); auto.
    - replace (d * x1 * x2 * y1 * y2) with (1+d * x1 * x2 * y1 * y2-1) in H by field.
      intro Hz; rewrite Hz in H; intuition.
  Qed.
  
  Lemma edwardsAddCompleteMinus x1 y1 x2 y2 :
    onCurve (x1, y1) ->
    onCurve (x2, y2) ->
    (1 - d*x1*x2*y1*y2) <> 0.
  Proof.
    intros Hc1 Hc2. destruct (F_eq_dec (d*x1*x2*y1*y2) 1) as [H|H].
    - assert ((d*x1*x2*y1*y2)^2 = 1) by (rewriteAny; field). destruct (edwardsAddComplete' x1 y1 x2 y2); auto.
    - replace (d * x1 * x2 * y1 * y2) with ((1-(1-d * x1 * x2 * y1 * y2))) in H by field.
      intro Hz; rewrite Hz in H; apply H; field.
  Qed.
  
  Definition zeroOnCurve : onCurve (0, 1).
    simpl. field.
  Qed.
  
  Lemma unifiedAdd'_onCurve' x1 y1 x2 y2 x3 y3
    (H: (x3, y3) = unifiedAdd' (x1, y1) (x2, y2)) :
    onCurve (x1, y1) -> onCurve (x2, y2) -> onCurve (x3, y3).
  Proof.
    (* https://eprint.iacr.org/2007/286.pdf Theorem 3.1;
      * c=1 and an extra a in front of x^2 *) 
  
    injection H; clear H; intros.
  
    Ltac t x1 y1 x2 y2 :=
      assert ((a*x2^2 + y2^2)*d*x1^2*y1^2
             = (1 + d*x2^2*y2^2) * d*x1^2*y1^2) by (rewriteAny; auto);
      assert (a*x1^2 + y1^2 - (a*x2^2 + y2^2)*d*x1^2*y1^2
             = 1 - d^2*x1^2*x2^2*y1^2*y2^2) by (repeat rewriteAny; field).
    t x1 y1 x2 y2; t x2 y2 x1 y1.
  
    remember ((a*x1^2 + y1^2 - (a*x2^2+y2^2)*d*x1^2*y1^2)*(a*x2^2 + y2^2 -
      (a*x1^2 + y1^2)*d*x2^2*y2^2)) as T.
    assert (HT1: T = (1 - d^2*x1^2*x2^2*y1^2*y2^2)^2) by (repeat rewriteAny; field).
    assert (HT2: T = (a * ((x1 * y2 + y1 * x2) * (1 - d * x1 * x2 * y1 * y2)) ^ 2 +(
    (y1 * y2 - a * x1 * x2) * (1 + d * x1 * x2 * y1 * y2)) ^ 2 -d * ((x1 *
     y2 + y1 * x2)* (y1 * y2 - a * x1 * x2))^2)) by (subst; field).
    replace (1:F q) with (a*x3^2 + y3^2 -d*x3^2*y3^2); [field|]; subst x3 y3.
  
    match goal with [ |- ?x = 1 ] => replace x with
    ((a * ((x1 * y2 + y1 * x2) * (1 - d * x1 * x2 * y1 * y2)) ^ 2 +
     ((y1 * y2 - a * x1 * x2) * (1 + d * x1 * x2 * y1 * y2)) ^ 2 -
      d*((x1 * y2 + y1 * x2) * (y1 * y2 - a * x1 * x2)) ^ 2)/
    ((1-d^2*x1^2*x2^2*y1^2*y2^2)^2)) end.
    - rewrite <-HT1, <-HT2; field; rewrite HT1.
      replace ((1 - d ^ 2 * x1 ^ 2 * x2 ^ 2 * y1 ^ 2 * y2 ^ 2))
      with ((1 - d*x1*x2*y1*y2)*(1 + d*x1*x2*y1*y2)) by field.
      auto using Fq_pow_nonzero, Fq_mul_nonzero_nonzero,
        edwardsAddCompleteMinus, edwardsAddCompletePlus.
    - field; replace (1 - (d * x1 * x2 * y1 * y2) ^ 2)
         with ((1 - d*x1*x2*y1*y2)*(1 + d*x1*x2*y1*y2))
           by field;
      auto using Fq_pow_nonzero, Fq_mul_nonzero_nonzero,
        edwardsAddCompleteMinus, edwardsAddCompletePlus.
  Qed.
  
  Lemma unifiedAdd'_onCurve : forall P1 P2, onCurve P1 -> onCurve P2 ->
    onCurve (unifiedAdd' P1 P2).
  Proof.
    intros; destruct P1, P2.
    remember (unifiedAdd' (f, f0) (f1, f2)) as r; destruct r.
    eapply unifiedAdd'_onCurve'; eauto.
  Qed.
End Pre.