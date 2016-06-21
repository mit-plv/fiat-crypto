Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.Algebra Crypto.Tactics.Nsatz.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.
Require Import Crypto.Util.Tuple.

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
    Local Notation "x ^2" := (x*x) (at level 30).
    Local Notation point := (@point F Feq Fone Fadd Fmul a d).
    Local Notation onCurve := (@onCurve F Feq Fone Fadd Fmul a d).

    Add Field _edwards_curve_theorems_field : (field_theory_for_stdlib_tactic (H:=field)).

    Definition eq (P Q:point) := fieldwise (n:=2) Feq (coordinates P) (coordinates Q).
    Infix "=" := eq : E_scope.

    (* TODO: decide whether we still want something like this, then port
    Local Ltac t :=
      unfold point_eqb;
        repeat match goal with
        | _ => progress intros
        | _ => progress simpl in *
        | _ => progress subst
        | [P:E.point |- _ ] => destruct P
        | [x: (F q * F q)%type |- _ ] => destruct x
        | [H: _ /\ _ |- _ ] => destruct H
        | [H: _ |- _ ] => rewrite Bool.andb_true_iff in H
        | [H: _ |- _ ] => apply F_eqb_eq in H
        | _ => rewrite F_eqb_refl
        end; eauto.

    Lemma point_eqb_sound : forall p1 p2, point_eqb p1 p2 = true -> p1 = p2.
    Proof.
      t.
    Qed.

    Lemma point_eqb_complete : forall p1 p2, p1 = p2 -> point_eqb p1 p2 = true.
    Proof.
      t.
    Qed.

    Lemma point_eqb_neq : forall p1 p2, point_eqb p1 p2 = false -> p1 <> p2.
    Proof.
      intros. destruct (point_eqb p1 p2) eqn:Hneq; intuition.
      apply point_eqb_complete in H0; congruence.
    Qed.

    Lemma point_eqb_neq_complete : forall p1 p2, p1 <> p2 -> point_eqb p1 p2 = false.
    Proof.
      intros. destruct (point_eqb p1 p2) eqn:Hneq; intuition.
      apply point_eqb_sound in Hneq. congruence.
    Qed.

    Lemma point_eqb_refl : forall p, point_eqb p p = true.
    Proof.
      t.
    Qed.

    Definition point_eq_dec (p1 p2:E.point) : {p1 = p2} + {p1 <> p2}.
      destruct (point_eqb p1 p2) eqn:H; match goal with
                                        | [ H: _ |- _ ] => apply point_eqb_sound in H
                                        | [ H: _ |- _ ] => apply point_eqb_neq in H
                                        end; eauto.
    Qed.

    Lemma point_eqb_correct : forall p1 p2, point_eqb p1 p2 = if point_eq_dec p1 p2 then true else false.
    Proof.
      intros. destruct (point_eq_dec p1 p2); eauto using point_eqb_complete, point_eqb_neq_complete.
    Qed.
    *)

    (* TODO: move to util *)
    Lemma decide_and  : forall P Q, {P}+{not P} -> {Q}+{not Q} -> {P/\Q}+{not(P/\Q)}.
    Proof. intros; repeat match goal with [H:{_}+{_}|-_] => destruct H end; intuition. Qed.

    Ltac destruct_points :=
      repeat match goal with
             | [ p : point |- _ ] =>
               let x := fresh "x" p in
               let y := fresh "y" p in
               let pf := fresh "pf" p in
               destruct p as [[x y] pf]
             end.

    Ltac expand_opp :=
      rewrite ?mul_opp_r, ?mul_opp_l, ?ring_sub_definition, ?inv_inv, <-?ring_sub_definition.

    Local Hint Resolve char_gt_2.
    Local Hint Resolve nonzero_a.
    Local Hint Resolve square_a.
    Local Hint Resolve nonsquare_d.
    Local Hint Resolve @edwardsAddCompletePlus.
    Local Hint Resolve @edwardsAddCompleteMinus.

    Local Obligation Tactic := intros; destruct_points; simpl; field_algebra.
    Program Definition opp (P:point) : point :=
      exist _ (let '(x, y) := coordinates P in (Fopp x, y) ) _.

    Ltac bash :=
      repeat match goal with
             | |- _ => progress intros
             | [H: _ /\ _ |- _ ] => destruct H
             | |- _ => progress destruct_points
             | |- _ => progress cbv [fst snd coordinates proj1_sig eq fieldwise fieldwise' add zero opp] in *
             | |- _ => split
             | |- Feq _ _ => field_algebra
             | |- _ <> 0 => expand_opp; solve [nsatz_nonzero|eauto]
             | |- {_}+{_} => eauto 15 using decide_and, @eq_dec with typeclass_instances
             end.

    Global Instance Proper_add : Proper (eq==>eq==>eq) add. Proof. bash. Qed.
    Global Instance Proper_opp : Proper (eq==>eq) opp. Proof. bash. Qed.
    Global Instance Proper_coordinates : Proper (eq==>fieldwise (n:=2) Feq) coordinates. Proof. bash. Qed.

    Global Instance edwards_acurve_abelian_group : abelian_group (eq:=eq)(op:=add)(id:=zero)(inv:=opp).
    Proof.
      bash.
      (* TODO: port denominator-nonzero proofs for associativity *)
      match goal with | |- _ <> 0 => admit end.
      match goal with | |- _ <> 0 => admit end.
      match goal with | |- _ <> 0 => admit end.
      match goal with | |- _ <> 0 => admit end.
    Qed.

    (* TODO: move to [Group] and [AbelianGroup] as appropriate *)
    Lemma mul_0_l : forall P, (0 * P = zero)%E.
    Proof. intros; reflexivity. Qed.
    Lemma mul_S_l : forall n P, (S n * P = P + n * P)%E.
    Proof. intros; reflexivity. Qed.
    Lemma mul_add_l : forall (n m:nat) (P:point), ((n + m)%nat * P = n * P + m * P)%E.
    Proof.
      induction n; intros;
        rewrite ?plus_Sn_m, ?plus_O_n, ?mul_S_l, ?left_identity, <-?associative, <-?IHn; reflexivity.
    Qed.
    Lemma mul_assoc : forall (n m : nat) P, (n * (m * P) = (n * m)%nat * P)%E.
    Proof.
      induction n; intros; [reflexivity|].
      rewrite ?mul_S_l, ?Mult.mult_succ_l, ?mul_add_l, ?IHn, commutative; reflexivity.
    Qed.
    Lemma mul_zero_r : forall m, (m * E.zero = E.zero)%E.
    Proof. induction m; rewrite ?mul_S_l, ?left_identity, ?IHm; try reflexivity. Qed.
    Lemma opp_mul : forall n P, (opp (n * P) = n * (opp P))%E.
    Admitted.

    Section PointCompression.
      Local Notation "x ^2" := (x*x).
      Definition solve_for_x2 (y : F) := ((y^2 - 1) / (d * (y^2) - a)).

      Lemma a_d_y2_nonzero : forall y, d * y^2 - a <> 0.
      Proof.
        intros ? eq_zero.
        destruct square_a as [sqrt_a sqrt_a_id]; rewrite <- sqrt_a_id in eq_zero.
        destruct (eq_dec y 0); [apply nonzero_a|apply nonsquare_d with (sqrt_a/y)]; field_algebra.
      Qed.

      Lemma solve_correct : forall x y, onCurve (x, y) <-> (x^2 = solve_for_x2 y).
      Proof.
        unfold solve_for_x2; simpl; split; intros; field_algebra; auto using a_d_y2_nonzero.
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