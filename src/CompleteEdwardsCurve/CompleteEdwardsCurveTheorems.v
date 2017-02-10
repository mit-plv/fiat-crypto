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

  Notation onCurve_zero := Pre.onCurve_zero.
  Notation denominator_nonzero := Pre.denominator_nonzero.
  Notation denominator_nonzero_x := denominator_nonzero_x.
  Notation denominator_nonzero_y := Pre.denominator_nonzero_y.
  Notation onCurve_add := Pre.onCurve_add.

  (* used in Theorems and Homomorphism *)
  Ltac _gather_nonzeros :=
    match goal with
      |- context[?t] =>
      match type of t with
        ?T =>
        match type of T with
          Prop =>
          let T := (eval simpl in T) in
          match T with
            not (_ _ _) => unique pose proof (t:T)
          end
        end
      end
    end.

  Section CompleteEdwardsCurveTheorems.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a d}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {prm:@twisted_edwards_params F Feq Fzero Fmul a d}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).
    Local Notation point := (@point F Feq Fone Fadd Fmul a d).
    Definition onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2).
    (* TODO: remove uses of this defnition, then make it a local notation *)
    Definition eq := @E.eq F Feq Fone Fadd Fmul a d.

    Ltac t_step :=
      match goal with
      | _ => exact _
      | _ => intro
      | |- Equivalence _ => split
      | |- abelian_group => split | |- group => split | |- monoid => split
      | |- is_associative => split | |- is_commutative => split 
      | |- is_left_inverse => split | |- is_right_inverse => split
      | |- is_left_identity => split | |- is_right_identity => split
      | _ => progress destruct_head' @E.point
      | _ => progress destruct_head' prod
      | _ => progress destruct_head' and
      | _ => progress cbv [onCurve eq E.eq E.add E.coordinates proj1_sig] in *
      (* [_gather_nonzeros] must run before [fst_pair] or [simpl] but after splitting E.eq and unfolding [E.add] *)
      | _ => _gather_nonzeros
      | _ => progress simpl in *
      | |- _ /\ _ => split | |- _ <-> _ => split
      | _ => solve [fsatz]
      end.
    Ltac t := repeat t_step.

    Program Definition opp (P:point) : point := (Fopp (fst P), (snd P)).
    Next Obligation. t. Qed.

    Global Instance associative_add : is_associative(eq:=E.eq)(op:=add).
    Proof.
      do 17 t_step.
      (*
       Ltac debuglevel ::= constr:(1%nat).
       all: goal_to_field_equality field.
       all: inequalities_to_inverses field.
       all: divisions_to_inverses field.
       nsatz. (* runs out of 6GB of stack space *)
      *)
      Add Field EdwardsCurveField : (Field.field_theory_for_stdlib_tactic (T:=F)).
      all:repeat common_denominator_equality_inequality_all; try nsatz.
      { revert H5; intro. fsatz. }
      { revert H1; intro. fsatz. }
      { revert H6; intro. fsatz. }
      { revert H2; intro. fsatz. }
    Qed.

    Global Instance edwards_curve_abelian_group : abelian_group (eq:=E.eq)(op:=add)(id:=zero)(inv:=opp).
    Proof. t. Qed.

    Global Instance Proper_coordinates : Proper (eq==>fieldwise (n:=2) Feq) coordinates. Proof. t. Qed.

    Global Instance Proper_mul : Proper (Logic.eq==>eq==>eq) mul.
    Proof.
      intros n n'; repeat intro; subst n'.
      induction n; (reflexivity || eapply (_:Proper (eq==>eq==>eq) add); eauto).
    Qed.

    Global Instance mul_is_scalarmult : @is_scalarmult point eq add zero mul.
    Proof. split; intros; (reflexivity || exact _). Qed.

    Section PointCompression.
      Local Notation "x ^ 2" := (x*x).
      Definition solve_for_x2 (y : F) := ((y^2 - 1) / (d * (y^2) - a)).

      Lemma a_d_y2_nonzero y : d * y^2 - a <> 0.
      Proof.
        destruct square_a as [sqrt_a], (dec (y=0));
          pose proof nonzero_a; pose proof (nonsquare_d (sqrt_a/y)); fsatz.
      Qed.

      Lemma solve_correct : forall x y, onCurve x y <-> (x^2 = solve_for_x2 y).
      Proof. pose proof a_d_y2_nonzero; cbv [solve_for_x2]; t. Qed.
    End PointCompression.
  End CompleteEdwardsCurveTheorems.
  Section Homomorphism.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv Fa Fd}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Fprm:@twisted_edwards_params F Feq Fzero Fmul Fa Fd}
            {Feq_dec:DecidableRel Feq}.
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv Ka Kd}
            {fieldK: @Algebra.field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {Kprm:@twisted_edwards_params K Keq Kzero Kmul Ka Kd}
            {Keq_dec:DecidableRel Keq}.
    Context {phi:F->K} {Hphi:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                                   K Keq Kone Kadd Kmul phi}.
    Context {Ha:Keq (phi Fa) Ka} {Hd:Keq (phi Fd) Kd}.
    Local Notation Fpoint := (@E.point F Feq Fone Fadd Fmul Fa Fd).
    Local Notation Kpoint := (@E.point K Keq Kone Kadd Kmul Ka Kd).

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
             | |- _ => intro
             | |- Monoid.is_homomorphism => split
             | _ => progress destruct_head' @E.point
             | _ => progress destruct_head' prod
             | _ => progress destruct_head' and
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | _ => progress cbv [ref_phi eq E.eq CompleteEdwardsCurve.E.eq E.add E.coordinates proj1_sig] in *
             (* [_gather_nonzeros] must run before [fst_pair] or [simpl] but after splitting E.eq and unfolding [E.add] *)
             | _ => _gather_nonzeros
             | _ => progress simpl in *
             | |- _ ?x ?x => reflexivity
             | |- _ ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | |- _ /\ _ => split
             | _ => solve [fsatz | repeat (f_equiv; auto) ]
             end.
      Qed.
  End Homomorphism.
End E.
