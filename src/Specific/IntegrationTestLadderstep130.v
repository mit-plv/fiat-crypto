Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.ArithmeticSynthesisTest130.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
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
  Let phi : feW -> F m :=
    fun x => B.Positional.Fdecode wt (Tuple.map wordToZ x).

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition FMxzladderstep := @M.xzladderstep (F m) F.add F.sub F.mul.

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition Mxzladderstep_sig
    : { xzladderstep : tuple Z sz -> tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz * (tuple Z sz * tuple Z sz)
      | forall a24 x1 Q Q', let eval := B.Positional.Fdecode wt in Tuple.map (n:=2) (Tuple.map (n:=2) eval) (xzladderstep a24 x1 Q Q') = FMxzladderstep (eval a24) (eval x1) (Tuple.map (n:=2) eval Q) (Tuple.map (n:=2) eval Q') }.
  Proof.
    exists (@M.xzladderstep _ (proj1_sig add_sig) (proj1_sig sub_sig) (fun x y => proj1_sig carry_sig (proj1_sig mul_sig x y))).
    intros a24 x1 Q Q' eval.
    cbv [FMxzladderstep M.xzladderstep].
    destruct Q, Q'; cbv [map map' fst snd Let_In eval].
    repeat rewrite ?(proj2_sig add_sig), ?(proj2_sig mul_sig), ?(proj2_sig sub_sig), ?(proj2_sig carry_sig).
    reflexivity.
  Defined.

  (* TODO : change this to field once field isomorphism happens *)
  Definition xzladderstep :
    { xzladderstep : feW -> feW * feW -> feW * feW -> feW * feW * (feW * feW)
    | forall x1 Q Q',
        let xz := xzladderstep x1 Q Q' in
        let eval := B.Positional.Fdecode wt in
        feW_bounded x1
        -> feW_bounded (fst Q) /\ feW_bounded (snd Q)
        -> feW_bounded (fst Q') /\ feW_bounded (snd Q')
        -> ((feW_bounded (fst (fst xz)) /\ feW_bounded (snd (fst xz)))
            /\ (feW_bounded (fst (snd xz)) /\ feW_bounded (snd (snd xz))))
           /\ Tuple.map (n:=2) (Tuple.map (n:=2) phi) xz = FMxzladderstep (eval (proj1_sig a24_sig)) (phi x1) (Tuple.map (n:=2) phi Q) (Tuple.map (n:=2) phi Q') }.
  Proof.
    apply_lift_sig.
    intros a b c; cbv beta iota zeta.
    lazymatch goal with
    | [ |- { e | ?A -> ?B -> ?C -> @?E e } ]
      => refine (proj2_sig_map (P:=fun e => A -> B -> C -> (_:Prop)) _ _)
    end.
    { intros ? FINAL.
      repeat let H := fresh in intro H; specialize (FINAL H).
      cbv [phi].
      split; [ refine (proj1 FINAL); shelve | ].
      do 4 match goal with
           | [ |- context[Tuple.map (n:=?N) (fun x : ?T => ?f (?g x))] ]
             => rewrite <- (Tuple.map_map (n:=N) f g
                            : pointwise_relation _ eq _ (Tuple.map (n:=N) (fun x : T => f (g x))))
           end.
      rewrite <- (proj2_sig Mxzladderstep_sig).
      apply f_equal.
      cbv [proj1_sig]; cbv [Mxzladderstep_sig].
      context_to_dlet_in_rhs (@M.xzladderstep _ _ _ _ _).
      cbv [M.xzladderstep a24_sig].
      repeat lazymatch goal with
             | [ |- context[@proj1_sig ?a ?b ?f_sig _] ]
               => context_to_dlet_in_rhs (@proj1_sig a b f_sig)
             end.
      cbv beta iota delta [proj1_sig mul_sig add_sig sub_sig carry_sig].
      cbv_runtime.
      refine (proj2 FINAL). }
    subst feW feW_bounded; cbv beta.
    (* jgross start here! *)
    Set Ltac Profiling.
    (*
    Time Glue.refine_to_reflective_glue (128::256::nil)%nat%list.
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
    Time refine_reflectively128.
    Show Ltac Profile.
  Time Defined.

Time End BoundedField25p5.
