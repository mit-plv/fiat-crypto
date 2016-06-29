Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.Algebra.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.

Module E.
  Import Group Ring Field CompleteEdwardsCurve.E.
  Section CompleteEdwardsCurveTheorems.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a d}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {prm:@twisted_edwards_params F Feq Fzero Fone Fadd Fmul a d}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).
    Local Notation point := (@point F Feq Fone Fadd Fmul a d).
    Local Notation onCurve := (@onCurve F Feq Fone Fadd Fmul a d).

    Add Field _edwards_curve_theorems_field : (field_theory_for_stdlib_tactic (H:=field)).

    Definition eq (P Q:point) := fieldwise (n:=2) Feq (coordinates P) (coordinates Q).
    Infix "=" := eq : E_scope.

    Ltac destruct_points :=
      repeat match goal with
             | [ p : point |- _ ] =>
               let x := fresh "x" p in
               let y := fresh "y" p in
               let pf := fresh "pf" p in
               destruct p as [[x y] pf]
             end.

    Local Hint Resolve char_gt_2.
    Local Hint Resolve nonzero_a.
    Local Hint Resolve square_a.
    Local Hint Resolve nonsquare_d.
    Local Hint Resolve @edwardsAddCompletePlus.
    Local Hint Resolve @edwardsAddCompleteMinus.

    Local Obligation Tactic := intros; destruct_points; simpl; super_nsatz.
    Program Definition opp (P:point) : point :=
      exist _ (let '(x, y) := coordinates P in (Fopp x, y) ) _.

    Ltac bash_step :=
      match goal with
      | |- _ => progress intros
      | [H: _ /\ _ |- _ ] => destruct H
      | |- _  => typeclasses eauto
      | |- _ => progress destruct_points
      | [A:Feq (a*_^2+_^2) (1 + d*_^2*_^2),  B:Feq (a*_^2+_^2) (1 + d*_^2*_^2) |- _] =>
        unique pose proof (edwardsAddCompletePlus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a) _ _ _ _ A B);
        unique pose proof (edwardsAddCompleteMinus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a) _ _ _ _ A B)
      | [A:Feq (a*_^2+_^2) (1 + d*_^2*_^2) |- _] =>
        unique pose proof (edwardsAddCompletePlus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a) _ _ _ _ A (proj2_sig zero));
        unique pose proof (edwardsAddCompletePlus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a) _ _ _ _ A A);
        unique pose proof (edwardsAddCompletePlus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a) _ _ _ _ (proj2_sig zero) A);
        unique pose proof (edwardsAddCompleteMinus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a) _ _ _ _ A (proj2_sig zero));
        unique pose proof (edwardsAddCompleteMinus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a) _ _ _ _ (proj2_sig zero) A);
        unique pose proof (edwardsAddCompleteMinus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a) _ _ _ _ A A)
      | |- _ => progress cbv [fst snd coordinates proj1_sig eq fieldwise fieldwise' add zero opp] in *
      | |- _ => split
      | |- Feq _ _ => super_nsatz
      end.

    Ltac bash := repeat bash_step.

    Global Instance Equivalence_eq : Equivalence eq. Proof. bash. Qed.
    Global Instance Proper_add : Proper (eq==>eq==>eq) add. Proof. bash. Qed.
    Global Instance Proper_opp : Proper (eq==>eq) opp. Proof. bash. Qed.
    Global Instance Proper_coordinates : Proper (eq==>fieldwise (n:=2) Feq) coordinates. Proof. bash. Qed.

    Global Instance edwards_acurve_abelian_group : abelian_group (eq:=eq)(op:=add)(id:=zero)(inv:=opp).
    Proof.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      bash_step.
      { conservative_common_denominator.
        nsatz.
        admit.
        admit.
        admit.
        admit. }
      {
        conservative_common_denominator.
        nsatz.
        admit.
        admit.
        admit.
        admit. }
      bash.
      bash.
      bash.
      bash.
      bash.
      bash.
      bash.
      bash.
      bash.
    Admitted.

    Global Instance Proper_mul : Proper (Logic.eq==>eq==>eq) mul.
    Proof.
      intros n m Hnm P Q HPQ. rewrite <-Hnm; clear Hnm m.
      induction n; simpl; rewrite ?IHn, ?HPQ; reflexivity.
    Qed.

    Global Instance mul_is_scalarmult : @is_scalarmult point eq add zero mul.
    Proof. split; intros; reflexivity || typeclasses eauto. Qed.

    Section PointCompression.
      Local Notation "x ^ 2" := (x*x).
      Definition solve_for_x2 (y : F) := ((y^2 - 1) / (d * (y^2) - a)).

      Lemma a_d_y2_nonzero : forall y, d * y^2 - a <> 0.
      Proof.
        intros ? eq_zero.
        destruct square_a as [sqrt_a sqrt_a_id]; rewrite <- sqrt_a_id in eq_zero.
        destruct (eq_dec y 0); [apply nonzero_a|apply nonsquare_d with (sqrt_a/y)]; super_nsatz.
      Qed.

      Lemma solve_correct : forall x y, onCurve (x, y) <-> (x^2 = solve_for_x2 y).
      Proof.
        unfold solve_for_x2; simpl; split; intros;
          (conservative_common_denominator_all; [nsatz | eapply a_d_y2_nonzero; eauto]).
      Qed.
    End PointCompression.
  End CompleteEdwardsCurveTheorems.

  Section Homomorphism.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv Fa Fd}
            {fieldF:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Fprm:@twisted_edwards_params F Feq Fzero Fone Fadd Fmul Fa Fd}.
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv Ka Kd}
            {fieldK:@field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {Kprm:@twisted_edwards_params K Keq Kzero Kone Kadd Kmul Ka Kd}.
    Context {phi:F->K} {Hphi:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                                   K Keq Kone Kadd Kmul phi}.
    Context {Ha:Keq (phi Fa) Ka} {Hd:Keq (phi Fd) Kd}.
    Local Notation Fpoint := (@point F Feq Fone Fadd Fmul Fa Fd).
    Local Notation Kpoint := (@point K Keq Kone Kadd Kmul Ka Kd).

    Create HintDb field_homomorphism discriminated.
    Hint Rewrite <-
         homomorphism_one
         homomorphism_add
         homomorphism_sub
         homomorphism_mul
         homomorphism_div
         Ha
         Hd
      : field_homomorphism.

    Program Definition ref_phi (P:Fpoint) : Kpoint := exist _ (
      let (x, y) := coordinates P in (phi x, phi y)) _.
    Next Obligation.
      destruct P as [[? ?] ?]; simpl.
      rewrite_strat bottomup hints field_homomorphism.
      eauto using is_homomorphism_phi_proper; assumption.
    Qed.

    Context {point_phi:Fpoint->Kpoint}
            {point_phi_Proper:Proper (eq==>eq) point_phi}
            {point_phi_correct: forall (P:Fpoint), eq (point_phi P) (ref_phi P)}.

    Lemma lift_homomorphism : @Group.is_homomorphism Fpoint eq add Kpoint eq add point_phi.
    Proof.
      repeat match goal with
             | |- Group.is_homomorphism => split
             | |- _ => intro
             | |-  _ /\ _ => split
             | [H: _ /\ _ |- _ ] => destruct H
             | [p: point |- _ ] => destruct p as [[??]?]
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | |- _ => progress cbv [fst snd coordinates proj1_sig eq fieldwise fieldwise' add zero opp ref_phi] in *
             | |- Keq ?x ?x => reflexivity
             | |- Keq ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | [ H : Feq _ _ |- Keq (phi _) (phi _)] => solve [f_equiv; intuition]
             end.
      Qed.
  End Homomorphism.
End E.
