Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.ModularArithmetic.FField.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.

Section CompleteEdwardsCurveTheorems.
  Context {prm:TwistedEdwardsParams}.
  Local Opaque q a d prime_q two_lt_q nonzero_a square_a nonsquare_d. (* [F_field] calls [compute] *)
  Existing Instance prime_q.

  Add Field Ffield_p' : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess; try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 

  Add Field Ffield_notConstant : (OpaqueFieldTheory q)
    (constants [notConstant]). 


  Lemma point_eq : forall p1 p2, p1 = p2 -> forall pf1 pf2,
    mkPoint p1 pf1 = mkPoint p2 pf2.
  Proof.
    destruct p1, p2; intros; find_injection; intros; subst; apply f_equal.
    apply UIP_dec, F_eq_dec. (* this is a hack. We actually don't care about the equality of the proofs. However, we *can* prove it, and knowing it lets us use the universal equality instead of a type-specific equivalence, which makes many things nicer. *) 
  Qed.
  Hint Resolve point_eq.

  Ltac Edefn := unfold unifiedAdd, unifiedAdd', zero; intros;
                  repeat match goal with
                         | [ p : point |- _ ] =>
                           let x := fresh "x" p in
                           let y := fresh "y" p in
                           let pf := fresh "pf" p in
                           destruct p as [[x y] pf]; unfold onCurve in pf
                  | _ => eapply point_eq, (f_equal2 pair)
                  | _ => eapply point_eq
  end.
  Lemma twistedAddComm : forall A B, (A+B = B+A)%E.
  Proof.
    Edefn; apply (f_equal2 div); ring.
  Qed.

  Lemma twistedAddAssoc : forall A B C, (A+(B+C) = (A+B)+C)%E.
  Proof.
    intros; Edefn; F_field_simplify_eq.
    - (* nsatz. *) (* requires IntegralDomain (F q), then gives stack overflow *)
      admit. (*sage -c "
R.<d,a,xA,yA,xB,yB,xC,yC> = PolynomialRing(QQ,8,order='invlex')
I = R.ideal([
  (a * (xA * xA) + yA * yA) - (1 + d * (xA * xA) * (yA * yA)),
  (a * (xB * xB) + yB * yB) - (1 + d * (xB * xB) * (yB * yB)),
  (a * (xC * xC) + yC * yC) - (1 + d * (xC * xC) * (yC * yC))
])

print ((- xA * xA * xA * yB * yB * yB * yB * yC * yC * xB * xB * xB * xC * d * d * d * yA * yA -
    xA * xA * xA * yB * yB * yB * yC * yC * yC * a * xB * xB * xC * xC * d * d +
    xA * xA * xA * yB * yB * yB * yC * a * xB * xB * xB * xB * xC * xC * d * d * d * yA * yA -
    xA * xA * xA * yB * yB * yB * yC * xB * xB * d * d * yA * yA +
    xA * xA * xA * yB * yB * yC * yC * a * a * xB * xB * xB * xC * xC * xC * d * d -
    xA * xA * xA * yB * yB * yC * yC * a * xB * xC * d +
    xA * xA * xA * yB * yB * a * xB * xB * xB * xC * d * d * yA * yA +
    xA * xA * xA * yB * yC * a * a * xB * xB * xC * xC * d +
    xA * xA * yB * yB * yB * yB * yC * yC * yC * xB * xC * xC * d * d * yA +
    xA * xA * yB * yB * yB * yB * yC * xB * xB * xB * xC * xC * d * d * d * yA * yA * yA +
    xA * xA * yB * yB * yB * yC * yC * xB * xB * xB * xB * xC * d * d * d * yA * yA * yA +
    xA * xA * yB * yB * yB * yC * yC * xC * d * yA -
    xA * xA * yB * yB * yB * xB * xB * xC * d * d * yA * yA * yA -
    (1 + 1) * xA * xA * yB * yB * yC * a * xB * xC * xC * d * yA -
    xA * xA * yB * yB * yC * xB * xB * xB * d * d * yA * yA * yA +
    xA * xA * yB * yC * yC * a * a * xB * xB * xB * xB * xC * xC * xC * d * d * yA -
    (1 + 1) * xA * xA * yB * yC * yC * a * xB * xB * xC * d * yA +
    xA * xA * yC * a * a * xB * xB * xB * xC * xC * d * yA -
    xA * yB * yB * yB * yB * yC * yC * xB * xC * xC * xC * d * d * yA * yA +
    xA * yB * yB * yB * yC * xC * xC * d * yA * yA +
    xA * yB * yB * yC * yC * xB * xC * d + (1 + 1) * xA * yB * yB * yC * yC * xB * xC * d * yA * yA +
    xA * yB * yC * yC * yC * a * xB * xB * xB * xB * xC * xC * d * d * yA * yA -
    xA * yB * yC * a * xB * xB * xC * xC * d - (1 + 1) * xA * yB * yC * a * xB * xB * xC * xC * d * yA * yA +
    xA * yB * yC - xA * yC * yC * a * xB * xB * xB * xC * d * yA * yA -
    xA * a * xB * xC - yB * yB * yB * yC * yC * xB * xB * xC * xC * xC * d * d * yA * yA * yA -
    yB * yB * yC * yC * yC * xB * xB * xB * xC * xC * d * d * yA * yA * yA -
    yB * yB * yC * xB * xC * xC * d * yA + yB * yB * yC * xB * xC * xC * d * yA * yA * yA -
                                           yB * yC * yC * xB * xB * xC * d * yA + yB * yC * yC * xB * xB * xC * d * yA * yA * yA +
    yB * xC * yA + yC * xB * yA - (
    - xA * xA * xA * yB * yB * yB * yB * yC * yC * xB * xC * d * d * yA * yA -
    xA * xA * xA * yB * yB * yB * yC * yC * yC * xB * xB * d * d * yA * yA +
    xA * xA * xA * yB * yB * a * a * xB * xB * xB * xC * xC * xC * d * d * yA * yA +
    xA * xA * xA * yB * yC * a * a * xB * xB * xB * xB * xC * xC * d * d * yA * yA +
    xA * xA * yB * yB * yB * yB * yC * yC * yC * xB * xB * xB * xC * xC * d * d * d * yA +
    xA * xA * yB * yB * yB * yB * yC * xB * xC * xC * d * d * yA * yA * yA +
    xA * xA * yB * yB * yB * yC * yC * a * xB * xB * xB * xB * xC * xC * xC * d * d * d * yA +
    xA * xA * yB * yB * yB * yC * yC * xC * d * yA -
    xA * xA * yB * yB * yB * a * xB * xB * xC * xC * xC * d * d * yA * yA * yA -
    xA * xA * yB * yB * yC * yC * yC * xB * xB * xB * d * d * yA * yA * yA +
    xA * xA * yB * yB * yC * yC * yC * xB * d * yA -
    (1 + 1) * xA * xA * yB * yB * yC * a * xB * xC * xC * d * yA -
    xA * xA * yB * yB * yC * xB * d * yA +
    xA * xA * yB * yC * yC * a * xB * xB * xB * xB * xC * d * d * yA * yA * yA -
    (1 + 1) * xA * xA * yB * yC * yC * a * xB * xB * xC * d * yA +
    xA * xA * yB * a * a * xB * xB * xC * xC * xC * d * yA -
    xA * xA * yB * a * xB * xB * xC * d * yA + xA * xA * yC * a * a * xB * xB * xB * xC * xC * d * yA -
                                               xA * yB * yB * yB * yB * yC * yC * xB * xB * xB * xC * xC * xC * d * d * d * yA * yA +
    xA * yB * yB * yB * yC * yC * yC * xB * xB * xB * xB * xC * xC * d * d * d * yA * yA -
    xA * yB * yB * yB * yC * yC * yC * xB * xB * xC * xC * d * d +
    xA * yB * yB * yB * yC * xC * xC * d * yA * yA +
    xA * yB * yB * yC * yC * a * xB * xB * xB * xC * xC * xC * d * d +
    (1 + 1) * xA * yB * yB * yC * yC * xB * xC * d * yA * yA -
    xA * yB * yB * a * xB * xC * xC * xC * d * yA * yA +
    xA * yB * yB * xB * xC * d * yA * yA + xA * yB * yC * yC * yC * xB * xB * d * yA * yA -
                                           (1 + 1) * xA * yB * yC * a * xB * xB * xC * xC * d * yA * yA -
                                           xA * yB * yC * xB * xB * d * yA * yA + xA * yB * yC -
                                                                                  xA * yC * yC * a * xB * xB * xB * xC * d * yA * yA -
                                                                                  xA * a * xB * xC - yB * yB * yB * yC * yC * xB * xB * xC * xC * xC * d * d * yA -
                                                                                  yB * yB * yC * yC * yC * xB * xB * xB * xC * xC * d * d * yA +
    yB * xC * yA + yC * xB * yA))
    in I)"*)
    - admit. (* nonzero demonimator conditions, to be resolved as in ExtendedCoordinates.v *)
    - (* nsatz. *) (* requires IntegralDomain (F q), then gives stack overflow *)
      admit. (* sage -c "
R.<d,a,xA,yA,xB,yB,xC,yC> = PolynomialRing(QQ,8,order='invlex')
I = R.ideal([
  (a * (xA * xA) + yA * yA) - (1 + d * (xA * xA) * (yA * yA)),
  (a * (xB * xB) + yB * yB) - (1 + d * (xB * xB) * (yB * yB)),
  (a * (xC * xC) + yC * yC) - (1 + d * (xC * xC) * (yC * yC))
])

print (((- yA * yA * yA * yB * yB * yB * yB * yC * yC * xB * xB * xB * xC * 1 * d * d * d * xA * xA -
    yA * yA * yA * yB * yB * yB * yC * yC * yC * xB * xB * xC * xC * d * d +
    yA * yA * yA * yB * yB * yB * yC * a * xB * xB * xB * xB * xC * xC * 1 * d * d * d * xA * xA -
    yA * yA * yA * yB * yB * yB * yC * xB * xB * 1 * 1 * d * d * xA * xA +
    yA * yA * yA * yB * yB * yC * yC * a * xB * xB * xB * xC * xC * xC * d * d -
    yA * yA * yA * yB * yB * yC * yC * xB * xC * 1 * d +
    yA * yA * yA * yB * yB * a * xB * xB * xB * xC * 1 * 1 * d * d * xA * xA +
    yA * yA * yA * yB * yC * a * xB * xB * xC * xC * 1 * d -
    yA * yA * yB * yB * yB * yB * yC * yC * yC * xB * xC * xC * d * d * xA -
    yA * yA * yB * yB * yB * yB * yC * a * xB * xB * xB * xC * xC * 1 * d * d * d * xA * xA * xA -
    yA * yA * yB * yB * yB * yC * yC * a * xB * xB * xB * xB * xC * 1 * d * d * d * xA * xA * xA -
    yA * yA * yB * yB * yB * yC * yC * xC * 1 * d * xA +
    yA * yA * yB * yB * yB * a * xB * xB * xC * 1 * 1 * d * d * xA * xA * xA +
    yA * yA * yB * yB * yC * a * xB * xB * xB * 1 * 1 * d * d * xA * xA * xA +
    (1 + 1) * yA * yA * yB * yB * yC * a * xB * xC * xC * 1 * d * xA -
    yA * yA * yB * yC * yC * a * a * xB * xB * xB * xB * xC * xC * xC * d * d * xA +
    (1 + 1) * yA * yA * yB * yC * yC * a * xB * xB * xC * 1 * d * xA -
    yA * yA * yC * a * a * xB * xB * xB * xC * xC * 1 * d * xA -
    yA * yB * yB * yB * yB * yC * yC * a * xB * xC * xC * xC * d * d * xA * xA +
    yA * yB * yB * yB * yC * a * xC * xC * 1 * d * xA * xA +
    (1 + 1) * yA * yB * yB * yC * yC * a * xB * xC * 1 * d * xA * xA +
    yA * yB * yB * yC * yC * xB * xC * 1 * 1 * 1 * d +
    yA * yB * yC * yC * yC * a * a * xB * xB * xB * xB * xC * xC * d * d * xA * xA -
    (1 + 1) * yA * yB * yC * a * a * xB * xB * xC * xC * 1 * d * xA * xA -
    yA * yB * yC * a * xB * xB * xC * xC * 1 * 1 * 1 * d + 
    yA * yB * yC * 1 * 1 * 1 * 1 - yA * yC * yC * a * a * xB * xB * xB * xC * 1 * d * xA * xA -
    yA * a * xB * xC * 1 * 1 * 1 * 1 +
    yB * yB * yB * yC * yC * a * a * xB * xB * xC * xC * xC * d * d * xA * xA * xA +
    yB * yB * yC * yC * yC * a * a * xB * xB * xB * xC * xC * d * d * xA * xA * xA -
    yB * yB * yC * a * a * xB * xC * xC * 1 * d * xA * xA * xA +
    yB * yB * yC * a * xB * xC * xC * 1 * 1 * 1 * d * xA -
    yB * yC * yC * a * a * xB * xB * xC * 1 * d * xA * xA * xA +
    yB * yC * yC * a * xB * xB * xC * 1 * 1 * 1 * d * xA - 
    yB * a * xC * 1 * 1 * 1 * 1 * xA - yC * a * xB * 1 * 1 * 1 * 1 * xA) -
   (- yA * yA * yA * yB * yB * yB * yB * yC * yC * xB * xC * d * d * xA * xA -
    yA * yA * yA * yB * yB * yB * yC * yC * yC * xB * xB * d * d * xA * xA +
    yA * yA * yA * yB * yB * a * a * xB * xB * xB * xC * xC * xC * d * d * xA * xA +
    yA * yA * yA * yB * yC * a * a * xB * xB * xB * xB * xC * xC * d * d * xA * xA -
    yA * yA * yB * yB * yB * yB * yC * yC * yC * xB * xB * xB * xC * xC * 1 * d * d * d * xA -
    yA * yA * yB * yB * yB * yB * yC * a * xB * xC * xC * d * d * xA * xA * xA -
    yA * yA * yB * yB * yB * yC * yC * a * xB * xB * xB * xB * xC * xC * xC * 1 * d * d * d * xA -
    yA * yA * yB * yB * yB * yC * yC * xC * 1 * d * xA +
    yA * yA * yB * yB * yB * a * a * xB * xB * xC * xC * xC * d * d * xA * xA * xA +
    yA * yA * yB * yB * yC * yC * yC * a * xB * xB * xB * d * d * xA * xA * xA -
    yA * yA * yB * yB * yC * yC * yC * xB * 1 * d * xA +
    (1 + 1) * yA * yA * yB * yB * yC * a * xB * xC * xC * 1 * d * xA +
    yA * yA * yB * yB * yC * xB * 1 * 1 * 1 * d * xA -
    yA * yA * yB * yC * yC * a * a * xB * xB * xB * xB * xC * d * d * xA * xA * xA +
    (1 + 1) * yA * yA * yB * yC * yC * a * xB * xB * xC * 1 * d * xA -
    yA * yA * yB * a * a * xB * xB * xC * xC * xC * 1 * d * xA +
    yA * yA * yB * a * xB * xB * xC * 1 * 1 * 1 * d * xA -
    yA * yA * yC * a * a * xB * xB * xB * xC * xC * 1 * d * xA -
    yA * yB * yB * yB * yB * yC * yC * a * xB * xB * xB * xC * xC * xC * 1 * d * d * d * xA * xA +
    yA * yB * yB * yB * yC * yC * yC * a * xB * xB * xB * xB * xC * xC * 1 * d * d * d * xA * xA -
    yA * yB * yB * yB * yC * yC * yC * xB * xB * xC * xC * 1 * 1 * d * d +
    yA * yB * yB * yB * yC * a * xC * xC * 1 * d * xA * xA +
    yA * yB * yB * yC * yC * a * xB * xB * xB * xC * xC * xC * 1 * 1 * d * d +
    (1 + 1) * yA * yB * yB * yC * yC * a * xB * xC * 1 * d * xA * xA -
    yA * yB * yB * a * a * xB * xC * xC * xC * 1 * d * xA * xA +
    yA * yB * yB * a * xB * xC * 1 * 1 * 1 * d * xA * xA +
    yA * yB * yC * yC * yC * a * xB * xB * 1 * d * xA * xA -
    (1 + 1) * yA * yB * yC * a * a * xB * xB * xC * xC * 1 * d * xA * xA -
    yA * yB * yC * a * xB * xB * 1 * 1 * 1 * d * xA * xA + 
    yA * yB * yC * 1 * 1 * 1 * 1 - yA * yC * yC * a * a * xB * xB * xB * xC * 1 * d * xA * xA -
    yA * a * xB * xC * 1 * 1 * 1 * 1 +
    yB * yB * yB * yC * yC * a * xB * xB * xC * xC * xC * 1 * 1 * d * d * xA +
    yB * yB * yC * yC * yC * a * xB * xB * xB * xC * xC * 1 * 1 * d * d * xA -
    yB * a * xC * 1 * 1 * 1 * 1 * xA - yC * a * xB * 1 * 1 * 1 * 1 * xA)) in I)"
*)
    - admit. (* nonzero demonimator conditions, to be resolved as in ExtendedCoordinates.v *)
  Admitted.

  Lemma zeroIsIdentity : forall P, (P + zero = P)%E.
  Proof.
    Edefn; repeat rewrite ?F_add_0_r, ?F_add_0_l, ?F_sub_0_l, ?F_sub_0_r,
           ?F_mul_0_r, ?F_mul_0_l, ?F_mul_1_l, ?F_mul_1_r, ?F_div_1_r; exact eq_refl.
  Qed.

  (* solve for x ^ 2 *)
  Definition solve_for_x2 (y : F q) := ((y ^ 2 - 1) / (d * (y ^ 2) - a))%F.

  Lemma d_y2_a_nonzero : (forall y, 0 <> d * y ^ 2 - a)%F.
    intros ? eq_zero.
    pose proof prime_q.
    destruct square_a as [sqrt_a sqrt_a_id].
    rewrite <- sqrt_a_id in eq_zero.
    destruct (Fq_square_mul_sub _ _ _ eq_zero) as [ [sqrt_d sqrt_d_id] | a_zero].
    + pose proof (nonsquare_d sqrt_d); auto.
    + subst.
      rewrite Fq_pow_zero in sqrt_a_id by congruence.
      auto using nonzero_a.
  Qed.

  Lemma a_d_y2_nonzero : (forall y, a - d * y ^ 2 <> 0)%F.
  Proof.
    intros y eq_zero.
    pose proof prime_q.
    eapply F_minus_swap in eq_zero.
    eauto using (d_y2_a_nonzero y).
  Qed.

  Lemma solve_correct : forall x y, onCurve (x, y) <->
    (x ^ 2 = solve_for_x2 y)%F.
  Proof.
    split.
    + intro onCurve_x_y.
      pose proof prime_q.
      unfold onCurve in onCurve_x_y.
      eapply F_div_mul; auto using (d_y2_a_nonzero y).
      replace (x ^ 2 * (d * y ^ 2 - a))%F with ((d * x ^ 2 * y ^ 2) - (a * x ^ 2))%F by ring.
      rewrite F_sub_add_swap.
      replace (y ^ 2 + a * x ^ 2)%F with (a * x ^ 2 + y ^ 2)%F by ring.
      rewrite onCurve_x_y.
      ring.
    + intro x2_eq.
      unfold onCurve, solve_for_x2 in *.
      rewrite x2_eq.
      field.
      auto using d_y2_a_nonzero.
  Qed.

End CompleteEdwardsCurveTheorems.
