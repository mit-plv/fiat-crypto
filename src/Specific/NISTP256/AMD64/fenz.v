Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.Core. Import B.
Require Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Import Crypto.Specific.NISTP256.AMD64.MontgomeryP256.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Import ListNotations.

Require Import Crypto.Specific.Framework.IntegrationTestTemporaryMiscCommon.

Require Import Crypto.Compilers.Z.Bounds.Pipeline.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let bound1 : zrange
    := Eval compute in
        {| lower := 0 ; upper := r-1 |}.
  Let bounds : Tuple.tuple zrange sz
    := Eval compute in
        Tuple.repeat bound1 sz.

  Let lgbitwidth := Eval compute in (Z.to_nat (Z.log2_up (Z.log2_up r))).
  Let bitwidth := Eval compute in (2^lgbitwidth)%nat.
  Let feZ : Type := tuple Z sz.
  Let feW : Type := tuple (wordT lgbitwidth) sz.
  Let feBW : Type := BoundedWord sz bitwidth bounds.
  Let eval : feBW -> Z :=
    fun x => MontgomeryAPI.eval (Z.pos r) (BoundedWordToZ _ _ _ x).
  Let feBW_small : Type := { v : feBW | eval v < MontgomeryAPI.eval (n:=sz) (Z.pos r) p256 }.
  Let feBW_of_feBW_small : feBW_small -> feBW := @proj1_sig _ _.
  Local Coercion feBW_of_feBW_small : feBW_small >-> feBW.
  Let phi : feBW -> F m :=
    fun x => montgomery_to_F (eval x).

  Local Ltac op_sig_side_conditions_t _ :=
    try (hnf; rewrite <- (is_bounded_by_None_repeat_In_iff_lt _ _ _)); destruct_head_hnf' sig; try assumption.

  (* TODO : change this to field once field isomorphism happens *)
  Definition nonzero
    : { nonzero : feBW_small -> BoundedWord  1 bitwidth bound1
      | forall A, (BoundedWordToZ _ _ _ (nonzero A) =? 0) = (if Decidable.dec (phi A = F.of_Z m 0) then true else false) }.
  Proof.
    apply_lift_sig; intros; eexists_sig_etransitivity.
    all:cbv [feBW_of_feBW_small phi eval].
    refine (_ : (if Decidable.dec (_ = 0) then true else false) = _).
    lazymatch goal with
    | [ |- (if Decidable.dec ?x then _ else _) = (if Decidable.dec ?y then _ else _) ]
      => cut (x <-> y);
           [ destruct (Decidable.dec x), (Decidable.dec y); try reflexivity; intros [? ?];
             generalize dependent x; generalize dependent y; solve [ intuition congruence ]
           | ]
    end.
    etransitivity; [ | eapply (proj2_sig nonzero) ];
      [ | solve [ op_sig_side_conditions_t () ].. ].
    reflexivity.
    let decP := lazymatch goal with |- { c | _ = if Decidable.dec (?decP = 0) then _ else _ } => decP end in
    apply (@proj2_sig_map _ (fun c => BoundedWordToZ 1 _ _ c = decP) _).
    { intros a' H'; rewrite H'.
      let H := fresh in
      lazymatch goal with |- context[Decidable.dec ?x] => destruct (Decidable.dec x) as [H|H]; try rewrite H end.
      { reflexivity. }
      { let H := fresh in
        lazymatch goal with |- context[?x =? 0] => destruct (x =? 0) eqn:? end;
          try reflexivity.
        Z.ltb_to_lt; congruence. } }
    eexists_sig_etransitivity.
    do_set_sig nonzero.
    cbv_runtime.
    reflexivity.
    sig_dlet_in_rhs_to_context.
    cbv [proj1_sig].
    match goal with
    | [ H : feBW_small |- _ ] => destruct H as [? _]
    end.
    (* jgross start here! *)
    Set Ltac Profiling.
    (*     Set Ltac Profiling.
    Print Ltac ReflectiveTactics.solve_side_conditions.
    Ltac ReflectiveTactics.solve_side_conditions ::= idtac.
    Time refine_reflectively128_with_uint8_with anf. (* Finished transaction in 212.693 secs (212.576u,0.184s) (successful) *)
    { Time ReflectiveTactics.do_reify. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Require Import CNotations.
      Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_rhs_reflexivity. }
  { Time ReflectiveTactics.unify_abstract_renamify_rhs_reflexivity. }
  { Time SubstLet.subst_let; clear; abstract vm_cast_no_check eq_refl. }
  { Time SubstLet.subst_let; clear; vm_compute; reflexivity. }
  { Time UnifyAbstractReflexivity.unify_abstract_compute_rhs_reflexivity. }
  { Time ReflectiveTactics.unify_abstract_cbv_interp_rhs_reflexivity. }
  { Time abstract ReflectiveTactics.handle_bounds_from_hyps. }
  { Time ReflectiveTactics.handle_boundedness_side_condition. } *)
    Time refine_reflectively_with_uint8_with anf. (* Finished transaction in 212.693 secs (212.576u,0.184s) (successful) *)
    Show Ltac Profile.
  Time Defined. (* Finished transaction in 21.291 secs (21.231u,0.032s) (successful) *)

Time End BoundedField25p5. (* Finished transaction in 14.666 secs (14.556u,0.111s) (successful) *)

Print Assumptions nonzero.
