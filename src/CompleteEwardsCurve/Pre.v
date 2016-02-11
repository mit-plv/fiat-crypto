Require Import BinInt Znumtheory VerdiTactics.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Local Open Scope F_scope.
  
Section Pre.
  Context {q : BinInt.Z}.
  Context {a : F q}.
  Context {d : F q}.
  Context {prime_q : Znumtheory.prime q}.
  Context {two_lt_q : 2 < q}.
  Context {a_nonzero : a <> 0}.
  Context {a_square : exists sqrt_a, sqrt_a^2 = a}.
  Context {d_nonsquare : forall x, x^2 <> d}.

  Add Field Ffield_Z : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 
  
  (* the canonical definitions are in Spec *)
  Local Notation onCurve P := (let '(x, y) := P in a*x^2 + y^2 = 1 + d*x^2*y^2).
  Local Notation unifiedAdd' P1' P2' := (
    let '(x1, y1) := P1' in
    let '(x2, y2) := P2' in
    (((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2)) , ((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2)))
  ).
  
  Lemma char_gt_2 : ZToField 2 <> (0: F q).
    intro; find_injection.
    pose proof two_lt_q.
    rewrite (Z.mod_small 2 q), Z.mod_0_l in *; omega.
  Qed.
  
  (*
  Ltac whatsNotZero :=
    repeat match goal with
    | [H: ?lhs = ?rhs |- _ ] =>
        match goal with [Ha: lhs <> 0 |- _ ] => fail 1 | _ => idtac end;
        assert (lhs <> 0) by (rewrite H; auto)
    | [H: ?lhs = ?rhs |- _ ] =>
        match goal with [Ha: rhs <> 0 |- _ ] => fail 1 | _ => idtac end;
        assert (rhs <> 0) by (rewrite H; auto)
    | [H: (?a^?p)%F <> 0 |- _ ] =>
        match goal with [Ha: a <> 0 |- _ ] => fail 1 | _ => idtac end;
        let Y:=fresh in let Z:=fresh in try (
          assert (p <> 0%N) as Z by (intro Y; inversion Y);
          assert (a <> 0) by (eapply root_nonzero; eauto);
          clear Z)
    | [H: (?a*?b)%F <> 0 |- _ ] =>
        match goal with [Ha: a <> 0 |- _ ] => fail 1 | _ => idtac end;
        assert (a <> 0) by (eapply mul_nonzero_l; eauto)
    | [H: (?a*?b)%F <> 0 |- _ ] =>
        match goal with [Ha: b <> 0 |- _ ] => fail 1 | _ => idtac end;
        assert (b <> 0) by (eapply mul_nonzero_r; eauto)
    end.
  *)
  
  Lemma edwardsAddComplete' x1 y1 x2 y2 :
    onCurve (x1, y1) ->
    onCurve (x2, y2) ->
    (d*x1*x2*y1*y2)^2 <> 1.
  Proof. (*
    intuition; whatsNotZero.
  
    pose proof char_gt_2. pose proof a_nonzero as Ha_nonzero. 
    destruct a_square as [sqrt_a a_square].
    rewrite <-a_square in *.
  
    (* Furthermore... *)
    pose proof (eq_refl (d*x1^2*y1^2*(sqrt_a^2*x2^2 + y2^2))) as Heqt.
    rewrite H0 in Heqt at 2.
    replace (d * x1 ^ 2 * y1 ^ 2 * (1 + d * x2 ^ 2 * y2 ^ 2))
       with (d*x1^2*y1^2 + (d*x1*x2*y1*y2)^2) in Heqt by field.
    rewrite H1 in Heqt.
    replace (d * x1 ^ 2 * y1 ^ 2 + 1) with (1 + d * x1 ^ 2 * y1 ^ 2) in Heqt by field.
    rewrite <-H in Heqt.
  
    (* main equation for both potentially nonzero denominators *)
    case_eq_GF (sqrt_a*x2 + y2) 0; case_eq_GF (sqrt_a*x2 - y2) 0;
      try match goal with [H: ?f (sqrt_a * x2)  y2 <> 0 |- _ ] =>
        assert ((f (sqrt_a*x1) (d * x1 * x2 * y1 * y2*y1))^2 =
                 f ((sqrt_a^2)*x1^2 + (d * x1 * x2 * y1 * y2)^2*y1^2)
                   (d * x1 * x2 * y1 * y2*sqrt_a*(inject 2)*x1*y1)) as Heqw1 by field;
        rewrite H1 in *;
        replace (1 * y1^2) with (y1^2) in * by field;
        rewrite <- Heqt in *;
        assert (d = (f (sqrt_a * x1) (d * x1 * x2 * y1 * y2 * y1))^2 /
                                 (x1 * y1 * (f (sqrt_a * x2)  y2))^2)
                                 by (rewriteAny; field; auto);
        match goal with [H: d = (?n^2)/(?l^2) |- _ ] =>
            destruct (d_nonsquare (n/l)); (remember n; rewriteAny; field; auto)
        end
      end.
  
    assert (Hc: (sqrt_a * x2 + y2) + (sqrt_a * x2 - y2) = 0) by (repeat rewriteAny; field).
  
    replace (sqrt_a * x2 + y2 + (sqrt_a * x2 - y2)) with (inject 2 * sqrt_a * x2) in Hc by field.
  
    (* contradiction: product of nonzero things is zero *)
    destruct (mul_zero_why _ _ Hc) as [Hcc|Hcc]; subst; intuition.
    destruct (mul_zero_why _ _ Hcc) as [Hccc|Hccc]; subst; intuition.
    apply Ha_nonzero; field.
  Qed
  *) Admitted.
  Lemma edwardsAddCompletePlus x1 y1 x2 y2 :
    onCurve (x1, y1) ->
    onCurve (x2, y2) ->
    (1 + d*x1*x2*y1*y2) <> 0.
  Proof. (*
    intros; case_eq_GF (d*x1*x2*y1*y2) (0-1)%GF.
    - assert ((d*x1*x2*y1*y2)^2 = 1) by (rewriteAny; field). destruct (edwardsAddComplete' x1 y1 x2 y2); auto.
    - replace (d * x1 * x2 * y1 * y2) with (1+d * x1 * x2 * y1 * y2-1) in H1 by field.
      intro; rewrite H2 in H1; intuition.
  Qed.
  *) Admitted.
  
  Lemma edwardsAddCompleteMinus x1 y1 x2 y2 :
    onCurve (x1, y1) ->
    onCurve (x2, y2) ->
    (1 - d*x1*x2*y1*y2) <> 0.
  Proof. (*
    unfold onCurve; intros; case_eq_GF (d*x1*x2*y1*y2) (1)%GF.
    - assert ((d*x1*x2*y1*y2)^2 = 1) by (rewriteAny; field). destruct (edwardsAddComplete' x1 y1 x2 y2); auto.
    - replace (d * x1 * x2 * y1 * y2) with ((1-(1-d * x1 * x2 * y1 * y2))) in H1 by field.
      intro; rewrite H2 in H1; apply H1; field.
  Qed.
  *) Admitted.
  
  Definition zeroOnCurve : onCurve (0, 1).
  Admitted. (* field. *)
  
  Lemma unifiedAdd'_onCurve' x1 y1 x2 y2 x3 y3
    (H: (x3, y3) = unifiedAdd' (x1, y1) (x2, y2)) :
    onCurve (x1, y1) -> onCurve (x2, y2) -> onCurve (x3, y3).
  Proof. (*
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
    replace 1 with (a*x3^2 + y3^2 -d*x3^2*y3^2); [field|]; subst x3 y3.
  
    match goal with [ |- ?x = 1 ] => replace x with
    ((a * ((x1 * y2 + y1 * x2) * (1 - d * x1 * x2 * y1 * y2)) ^ 2 +
     ((y1 * y2 - a * x1 * x2) * (1 + d * x1 * x2 * y1 * y2)) ^ 2 -
      d*((x1 * y2 + y1 * x2) * (y1 * y2 - a * x1 * x2)) ^ 2)/
    ((1-d^2*x1^2*x2^2*y1^2*y2^2)^2)) end; try field; auto.
    - rewrite <-HT1, <-HT2; field; rewrite HT1.
      replace ((1 - d ^ 2 * x1 ^ 2 * x2 ^ 2 * y1 ^ 2 * y2 ^ 2))
         with ((1 - d*x1*x2*y1*y2)*(1 + d*x1*x2*y1*y2))
           by field; simpl; auto.
    - replace (1 - (d * x1 * x2 * y1 * y2) ^ 2)
         with ((1 - d*x1*x2*y1*y2)*(1 + d*x1*x2*y1*y2))
           by field; auto.
  Qed.
  *) Admitted.
  
  Lemma unifiedAdd'_onCurve : forall P1 P2, onCurve P1 -> onCurve P2 ->
    onCurve (unifiedAdd' P1 P2).
  Proof.
    intros; destruct P1, P2.
    remember (unifiedAdd' (f, f0) (f1, f2)) as r; destruct r.
    eapply unifiedAdd'_onCurve'; eauto.
  Qed.
End Pre.