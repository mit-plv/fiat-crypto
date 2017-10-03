Require Import Coq.Classes.Morphisms.

Require Import Crypto.Specific.X25519.C64.ReificationTypes.
Require Import Crypto.Specific.X25519.C64.ArithmeticSynthesisTest.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.

Require Import Crypto.Util.FixedWordSizes.
Require Import Coq.ZArith.BinIntDef.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.ETransitivity.
Require Import Crypto.Util.Notations.

(** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
Definition FMxzladderstep := @M.donnaladderstep (F m) F.add F.sub F.mul.

Section with_notations.
  Local Infix "+" := (proj1_sig add_sig).
  Local Notation "a * b" := (proj1_sig carry_sig (proj1_sig mul_sig a b)).
  Local Notation "x ^ 2" := (proj1_sig carry_sig (proj1_sig square_sig x)).
  Local Infix "-" := (proj1_sig sub_sig).
  Definition Mxzladderstep a24 x1 Q Q'
    := match Q, Q' with
       | (x, z), (x', z') =>
         dlet origx := x in
         dlet x := x + z in
         dlet z := origx - z in
         dlet origx' := x' in
         dlet x' := x' + z' in
         dlet z' := origx' - z' in
         dlet xx' := x' * z in
         dlet zz' := x * z' in
         dlet origx' := xx' in
         dlet xx' := xx' + zz' in
         dlet zz' := origx' - zz' in
         dlet x3 := xx'^2 in
         dlet zzz' := zz'^2 in
         dlet z3 := zzz' * x1 in
         dlet xx := x^2 in
         dlet zz := z^2 in
         dlet x2 := xx * zz in
         dlet zz := xx - zz in
         dlet zzz := zz * a24 in
         dlet zzz := zzz + xx in
         dlet z2 := zz * zzz in
         ((x2, z2), (x3, z3))%core
       end.
End with_notations.


(** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
Definition Mxzladderstep_sig
  : { xzladderstep : tuple Z sz -> tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz * (tuple Z sz * tuple Z sz)
    | forall a24 x1 Q Q', let eval := B.Positional.Fdecode wt in Tuple.map (n:=2) (Tuple.map (n:=2) eval) (xzladderstep a24 x1 Q Q') = FMxzladderstep (eval a24) (eval x1) (Tuple.map (n:=2) eval Q) (Tuple.map (n:=2) eval Q') }.
Proof.
  exists Mxzladderstep.
  intros a24 x1 Q Q' eval.
  cbv [Mxzladderstep FMxzladderstep M.donnaladderstep].
  destruct Q, Q'; cbv [map map' fst snd Let_In eval].
  repeat rewrite ?(proj2_sig add_sig), ?(proj2_sig mul_sig), ?(proj2_sig square_sig), ?(proj2_sig sub_sig), ?(proj2_sig carry_sig).
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
         /\ Tuple.map (n:=2) (Tuple.map (n:=2) phiW) xz = FMxzladderstep (eval (proj1_sig a24_sig)) (phiW x1) (Tuple.map (n:=2) phiW Q) (Tuple.map (n:=2) phiW Q') }.
Proof.
  start_preglue.
  unmap_map_tuple ().
  do_rewrite_with_sig_1arg Mxzladderstep_sig.
  cbv [Mxzladderstep M.xzladderstep a24_sig]; cbn [proj1_sig].
  do_set_sigs ().
  cbv_runtime.
  all:finish_conjoined_preglue ().
  (* jgross start here! *)
  Set Ltac Profiling.
  (*
  Time Glue.refine_to_reflective_glue P.allowable_bit_widths.
  Time ReflectiveTactics.refine_with_pipeline_correct default.
  { Time ReflectiveTactics.do_reify. }
  { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
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
  { Time abstract ReflectiveTactics.handle_boundedness_side_condition. }
   *)
  Time refine_reflectively_gen P.allowable_bit_widths default.
  Show Ltac Profile.
Time Defined.
