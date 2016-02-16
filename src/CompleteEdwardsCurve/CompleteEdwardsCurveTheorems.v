Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.

Section CompleteEdwardsCurveTheorems.
  Context {prm:TwistedEdwardsParams}.
  Existing Instance prime_q.
  Add Field Ffield_Z : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [idtac],
     postprocess [try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 

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
    Edefn; apply f_equal2; ring.
  Qed.

  Lemma twistedAddAssoc : forall A B C, (A+(B+C) = (A+B)+C)%E.
  Proof.
    (* http://math.rice.edu/~friedl/papers/AAELLIPTIC.PDF *)
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

  (* TODO : move to ModularArithmeticTheorems? *)
  Definition sqrt_valid (a : F q) := ((sqrt_mod_q a) ^ 2 = a)%F.

  Lemma solve_sqrt_valid : forall (p : point),
    sqrt_valid (solve_for_x2 (snd (proj1_sig p))).
  Admitted.

  Lemma solve_onCurve: forall (y : F q), sqrt_valid (solve_for_x2 y) ->
    onCurve (sqrt_mod_q (solve_for_x2 y), y).
  Proof.
    intros.
    unfold sqrt_valid in *.
    apply solve_correct; auto.
  Qed.

  Lemma solve_opp_onCurve: forall (y : F q), sqrt_valid (solve_for_x2 y) ->
    onCurve (opp (sqrt_mod_q (solve_for_x2 y)), y).
  Proof.
    intros y sqrt_valid_x2.
    unfold sqrt_valid in *.
    apply solve_correct.
    rewrite <- sqrt_valid_x2 at 2.
    ring.
  Qed.

End CompleteEdwardsCurveTheorems.
