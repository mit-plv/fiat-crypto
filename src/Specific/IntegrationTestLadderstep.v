Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.ArithmeticSynthesisTest.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.ETransitivity.
Require Import Crypto.Curves.Montgomery.XZ.
Import ListNotations.

Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.

Require Import Crypto.Compilers.Z.Bounds.Pipeline.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz)).
  Let length_lw := Eval compute in List.length limb_widths.

  Local Notation b_of exp := {| lower := 0 ; upper := 2^exp + 2^(exp-3) |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
  (* The definition [bounds_exp] is a tuple-version of the
     limb-widths, which are the [exp] argument in [b_of] above, i.e.,
     the approximate base-2 exponent of the bounds on the limb in that
     position. *)
  Let bounds_exp : Tuple.tuple Z length_lw
    := Eval compute in
        Tuple.from_list length_lw limb_widths eq_refl.
  Let bounds : Tuple.tuple zrange length_lw
    := Eval compute in
        Tuple.map (fun e => b_of e) bounds_exp.

  Let lgbitwidth := Eval compute in (Z.to_nat (Z.log2_up (List.fold_right Z.max 0 limb_widths))).
  Let bitwidth := Eval compute in (2^lgbitwidth)%nat.
  Let feZ : Type := tuple Z sz.
  Let feW : Type := tuple (wordT lgbitwidth) sz.
  Let feW_bounded : feW -> Prop
    := fun w => is_bounded_by None bounds (map wordToZ w).
  Let feBW : Type := BoundedWord sz bitwidth bounds.
  Let phi : feBW -> F m :=
    fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x).

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition FMxzladderstep := @M.xzladderstep (F m) F.add F.sub F.mul.

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition Mxzladderstep_sig
    : { xzladderstep : tuple Z sz -> tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz * (tuple Z sz * tuple Z sz)
      | forall a24 x1 Q Q', let eval := B.Positional.Fdecode wt in Tuple.map (n:=2) (Tuple.map (n:=2) eval) (xzladderstep a24 x1 Q Q') = FMxzladderstep (eval a24) (eval x1) (Tuple.map (n:=2) eval Q) (Tuple.map (n:=2) eval Q') }.
  Proof.
    exists (@M.xzladderstep _ (proj1_sig add_sig) (proj1_sig sub_sig) (fun x y => proj1_sig carry_sig (proj1_sig mul_sig x y))).
    intros.
    cbv [FMxzladderstep M.xzladderstep].
    destruct Q, Q'; cbv [map map' fst snd Let_In eval].
    repeat rewrite ?(proj2_sig add_sig), ?(proj2_sig mul_sig), ?(proj2_sig sub_sig), ?(proj2_sig carry_sig).
    reflexivity.
  Defined.

  (* TODO : change this to field once field isomorphism happens *)
  Local Notation xzladderstepP a24 x1 Q Q'
    := (fun xz : feW * feW * (feW * feW)
        => feW_bounded a24
           -> feW_bounded x1
           -> feW_bounded (fst Q) /\ feW_bounded (snd Q)
           -> feW_bounded (fst Q') /\ feW_bounded (snd Q')
           -> (feW_bounded (fst (fst xz)) /\ feW_bounded (snd (fst xz)))
              /\ (feW_bounded (fst (snd xz)) /\ feW_bounded (snd (snd xz))))
         (only parsing).
  Definition xzladderstep :
    { xzladderstep : { xzladderstep : feW -> feW -> feW * feW -> feW * feW -> feW * feW * (feW * feW)
                     | forall a24 x1 Q Q', xzladderstepP a24 x1 Q Q' (xzladderstep a24 x1 Q Q') }
    | forall a24v x1v Qv Q'v,
        let v := proj1_sig xzladderstep a24v x1v Qv Q'v in
        let pf : xzladderstepP a24v x1v Qv Q'v v := proj2_sig xzladderstep a24v x1v Qv Q'v in
        forall a24p x1p Qp Q'p,
          let a24 := exist _ a24v a24p in
          let x1 := exist _ x1v x1p in
          let Q := (exist _ (fst Qv) (proj1 Qp), exist _ (snd Qv) (proj2 Qp)) in
          let Q' := (exist _ (fst Q'v) (proj1 Q'p), exist _ (snd Q'v) (proj2 Q'p)) in
          let pf := pf a24p x1p Qp Q'p in
          let xzladderstep := ((exist _ (fst (fst v)) (proj1 (proj1 pf)),
                                exist _ (snd (fst v)) (proj2 (proj1 pf))),
                               (exist _ (fst (snd v)) (proj1 (proj2 pf)),
                                exist _ (snd (snd v)) (proj2 (proj2 pf)))) in
          Tuple.map (n:=2) (Tuple.map (n:=2) phi) xzladderstep = FMxzladderstep (phi a24) (phi x1) (Tuple.map (n:=2) phi Q) (Tuple.map (n:=2) phi Q') }.
  Proof.
    lazymatch goal with
    | [ |- { op | forall (a:?A) (b:?B) (c:?C) (d:?D),
               let v := proj1_sig op a b c d in
               let pf := proj2_sig op a b c d in
               @?P a b c d v pf } ]
      => refine (@lift4_sig_sig A B C D _ _ P _)
    end.
    intros; cbv beta iota zeta.
    eexists_sig_etransitivity_R (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq))));
      cbv [pointwise_relation].
    intros. all:cbv [phi].
    { set_evars.
      rewrite <- !(Tuple.map_map (B.Positional.Fdecode wt) (BoundedWordToZ sz bitwidth bounds)).
      rewrite <- (proj2_sig Mxzladderstep_sig).
      etransitivity_rev.
      { apply f_equal.
        cbv [proj1_sig]; cbv [Mxzladderstep_sig].
        context_to_dlet_in_rhs (@M.xzladderstep _ _ _ _).
        set (k := @M.xzladderstep _ _ _ _); context_to_dlet_in_rhs k; subst k.
        cbv [M.xzladderstep].
        lazymatch goal with
        | [ |- context[@proj1_sig ?a ?b carry_sig] ]
          => context_to_dlet_in_rhs (@proj1_sig a b carry_sig)
        end.
        lazymatch goal with
        | [ |- context[@proj1_sig ?a ?b mul_sig] ]
          => context_to_dlet_in_rhs (@proj1_sig a b mul_sig)
        end.
        lazymatch goal with
        | [ |- context[@proj1_sig ?a ?b add_sig] ]
          => context_to_dlet_in_rhs (@proj1_sig a b add_sig)
        end.
        lazymatch goal with
        | [ |- context[@proj1_sig ?a ?b sub_sig] ]
          => context_to_dlet_in_rhs (@proj1_sig a b sub_sig)
        end.
        cbv beta iota delta [proj1_sig mul_sig add_sig sub_sig carry_sig runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz]; cbn [fst snd].
        reflexivity. }
      subst_evars.
      reflexivity. }
    eexists_sig_etransitivity_for_rewrite_fun_R (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq))));
      cbv [pointwise_relation].
    { intros.
      subst feBW.
      set_evars.
      do 2 lazymatch goal with
           | [ |- context[Tuple.map (n:=?n) (fun x => ?f (?g x))] ]
             => rewrite <- (Tuple.map_map (n:=n) f g : pointwise_relation _ eq _ _)
           end.
      subst_evars.
      reflexivity. }
    cbv beta.
    refine (proj2_sig_map _ _).
    { intros ? p x y z w; apply f_equal; revert x y z w.
      lazymatch type of p with ?e ?v => pattern v end.
      eexact p. }
    subst feW feW_bounded; cbv beta.
    (* jgross start here! *)
    Set Ltac Profiling.
    (*
    Time Glue.refine_to_reflective_glue (64::128::nil)%nat%list.
    Time ReflectiveTactics.refine_with_pipeline_correct.
    { Time ReflectiveTactics.do_reify. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_rhs_reflexivity. }
    { Time ReflectiveTactics.unify_abstract_renamify_rhs_reflexivity. }
    { Time SubstLet.subst_let; clear; abstract vm_cast_no_check (eq_refl true). }
    { Time SubstLet.subst_let; clear; vm_compute; reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_compute_rhs_reflexivity. }
    { Time ReflectiveTactics.unify_abstract_cbv_interp_rhs_reflexivity. }
    { Time abstract ReflectiveTactics.handle_bounds_from_hyps. }
     *)
    Time refine_reflectively.
    Show Ltac Profile.
  Time Defined.

Time End BoundedField25p5.
