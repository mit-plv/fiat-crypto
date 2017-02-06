Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.Algebra Crypto.Algebra Crypto.Util.Decidable.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tuple Crypto.Util.Notations Crypto.Util.Tactics.
Require Export Crypto.Util.FixCoqMistakes.

Module E.
  Import Group ScalarMult Ring Field CompleteEdwardsCurve.E.
  Section CompleteEdwardsCurveTheorems.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a d}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {prm:@twisted_edwards_params F Feq Fzero Fone Fadd Fmul a d}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).
    Local Notation point := (@point F Feq Fone Fadd Fmul a d).
    Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2).

    Add Field _edwards_curve_theorems_field : (field_theory_for_stdlib_tactic (H:=field)).

    Definition eq (P Q:point) := fieldwise (n:=2) Feq (coordinates P) (coordinates Q).
    Infix "=" := eq : E_scope.

    Ltac destruct_points :=
      repeat match goal with
             | [ p : point |- _ ] =>
               let x := fresh "x" p in
               let y := fresh "y" p in
               let pf := fresh "pf" p in
               destruct p as [ [x y] pf]
             end.

    Local Obligation Tactic := intros; destruct_points; simpl; super_nsatz.
    Program Definition opp (P:point) : point :=
      exist _ (let '(x, y) := coordinates P in (Fopp x, y) ) _.

    (* all nonzero-denominator goals here require proofs that are not
    trivially implied by field axioms. Posing all such proofs at once
    and then solving the nonzero-denominator goal using [super_nsatz]
    is too slow because the context contains many assumed nonzero
    expressions and the product of all of them is a very large
    polynomial. However, we never need to use more than one
    nonzero-ness assumption for a given nonzero-denominator goal, so
    we can try them separately one-by-one. *)

    Ltac apply_field_nonzero H :=
      match goal with |- not (Feq _ 0) => idtac | _ => fail "not a nonzero goal" end;
      try solve [exact H];
      let Hx := fresh "H" in
      intro Hx;
      apply H;
      try common_denominator;
      [rewrite <-Hx; ring | ..].

    Ltac bash_step :=
      let addCompletePlus := constr:(edwardsAddCompletePlus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a)) in
      let addCompleteMinus := constr:(edwardsAddCompleteMinus(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a)) in
      let addOnCurve := constr:(unifiedAdd'_onCurve(char_gt_2:=char_gt_2)(d_nonsquare:=nonsquare_d)(a_square:=square_a)(a_nonzero:=nonzero_a)) in
      match goal with
      | |- _ => progress intros
      | [H: _ /\ _ |- _ ] => destruct H
      | [H: ?a = ?b |- _ ] => is_var a; is_var b; repeat rewrite <-H in *; clear H b (* fast path *)
      | |- _ => progress destruct_points
      | |- _ => progress cbv [fst snd coordinates proj1_sig eq fieldwise fieldwise' add zero opp] in *
      | |- _ => split
      | [H:Feq (a*_^2+_^2) (1 + d*_^2*_^2) |- _ <> 0]
        => apply_field_nonzero (addCompletePlus _ _ _ _ H H) ||
           apply_field_nonzero (addCompleteMinus _ _ _ _ H H)
      | [A:Feq (a*_^2+_^2) (1 + d*_^2*_^2),
           B:Feq (a*_^2+_^2) (1 + d*_^2*_^2) |- _ <> 0]
        => apply_field_nonzero (addCompletePlus _ _ _ _ A B) ||
           apply_field_nonzero (addCompleteMinus _ _ _ _ A B)
      | [A:Feq (a*_^2+_^2) (1 + d*_^2*_^2),
           B:Feq (a*_^2+_^2) (1 + d*_^2*_^2),
             C:Feq (a*_^2+_^2) (1 + d*_^2*_^2) |- _ <> 0]
        => apply_field_nonzero (addCompleteMinus _ _ _ _ A (addOnCurve (_, _) (_, _) B C)) ||
           apply_field_nonzero (addCompletePlus _ _ _ _ A (addOnCurve (_, _) (_, _) B C))
      | |- ?x <> 0 => let H := fresh "H" in assert (x = 1) as H by ring; rewrite H; exact one_neq_zero
      | |- Feq _ _ => progress common_denominator
      | |- Feq _ _ => nsatz
      | |- _ => exact _ (* typeclass instances *)
      end.

    Ltac bash := repeat bash_step.

    Global Instance Proper_add : Proper (eq==>eq==>eq) add. Proof. bash. Qed.
    Global Instance Proper_opp : Proper (eq==>eq) opp. Proof. bash. Qed.
    Global Instance Proper_coordinates : Proper (eq==>fieldwise (n:=2) Feq) coordinates. Proof. bash. Qed.
    Global Instance edwards_acurve_abelian_group : abelian_group (eq:=eq)(op:=add)(id:=zero)(inv:=opp).
    Proof.
      bash.
    Qed.

    Global Instance Proper_mul : Proper (Logic.eq==>eq==>eq) mul.
    Proof.
      intros n n'; repeat intro; subst n'.
      induction n; (reflexivity || eapply Proper_add; eauto).
    Qed.

    Global Instance mul_is_scalarmult : @is_scalarmult point eq add zero mul.
    Proof. unfold mul; split; intros; (reflexivity || exact _). Qed.

    Section PointCompression.
      Local Notation "x ^ 2" := (x*x).
      Definition solve_for_x2 (y : F) := ((y^2 - 1) / (d * (y^2) - a)).

      Lemma a_d_y2_nonzero : forall y, d * y^2 - a <> 0.
      Proof.
        intros ? eq_zero.
        destruct square_a as [sqrt_a sqrt_a_id]; rewrite <- sqrt_a_id in eq_zero.
        destruct (dec (y=0)); [apply nonzero_a | apply nonsquare_d with (sqrt_a/y)]; super_nsatz.
      Qed.

      Lemma solve_correct : forall x y, onCurve x y <-> (x^2 = solve_for_x2 y).
      Proof.
        unfold solve_for_x2; simpl; split; intros;
          (common_denominator_all; [nsatz | auto using a_d_y2_nonzero]).
      Qed.
    End PointCompression.
  End CompleteEdwardsCurveTheorems.
  Section Homomorphism.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv Fa Fd}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Fprm:@twisted_edwards_params F Feq Fzero Fone Fadd Fmul Fa Fd}
            {Feq_dec:DecidableRel Feq}.
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv Ka Kd}
            {fieldK: @Algebra.field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {Kprm:@twisted_edwards_params K Keq Kzero Kone Kadd Kmul Ka Kd}
            {Keq_dec:DecidableRel Keq}.
    Context {phi:F->K} {Hphi:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                                   K Keq Kone Kadd Kmul phi}.
    Context {Ha:Keq (phi Fa) Ka} {Hd:Keq (phi Fd) Kd}.
    Local Notation Fpoint := (@E.point F Feq Fone Fadd Fmul Fa Fd).
    Local Notation Kpoint := (@E.point K Keq Kone Kadd Kmul Ka Kd).
    Local Notation FonCurve := (@onCurve F Feq Fone Fadd Fmul Fa Fd).
    Local Notation KonCurve := (@onCurve K Keq Kone Kadd Kmul Ka Kd).

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

    Obligation Tactic := idtac.
    Program Definition ref_phi (P:Fpoint) : Kpoint := exist _ (
      let (x, y) := coordinates P in (phi x, phi y)) _.
    Next Obligation.
      destruct P as [ [? ?] ?]; simpl.
      rewrite_strat bottomup hints field_homomorphism.
      eauto using Monoid.is_homomorphism_phi_proper; assumption.
    Qed.

    Context {point_phi:Fpoint->Kpoint}
            {point_phi_Proper:Proper (eq==>eq) point_phi}
            {point_phi_correct: forall (P:point), eq (point_phi P) (ref_phi P)}.

    Lemma lift_homomorphism : @Monoid.is_homomorphism Fpoint eq add Kpoint eq add point_phi.
    Proof.
      repeat match goal with
             | |- Monoid.is_homomorphism => split
             | |- _ => intro
             | |-  _ /\ _ => split
             | [H: _ /\ _ |- _ ] => destruct H
             | [p: point |- _ ] => destruct p as [ [??]?]
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | |- _ => progress cbv [fst snd coordinates proj1_sig eq fieldwise fieldwise' add zero opp ref_phi] in *
             | |- Keq ?x ?x => reflexivity
             | |- Keq ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | [ H : Feq _ _ |- Keq (phi _) (phi _)] => solve [f_equiv; intuition]
             end;
        assert (FonCurve (f1,f2)) as FonCurve1 by assumption;
        assert (FonCurve (f,f0)) as FonCurve2 by assumption;
        [ eapply (@edwardsAddCompleteMinus F) with (x1 := f1); destruct Fprm; eauto
        | eapply (@edwardsAddCompletePlus  F) with (x1 := f1); destruct Fprm; eauto].
      Qed.
  End Homomorphism.
End E.
