Require Export Crypto.SpecificGen.GF2519_32Reflective.Common.
Require Import Crypto.SpecificGen.GF2519_32BoundedCommon.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Util.Tactics.

Local Opaque Interp.
Lemma ExprUnOpFEToZ_correct_and_bounded
      ropW op (ropZ_sig : rexpr_unop_FEToZ_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall x
                   (x := eta_fe2519_32W x)
                   (Hx : is_bounded (fe2519_32WToZ x) = true),
          let args := unop_args_to_bounded x Hx in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWordW.interp_op) (MapInterp BoundedWordW.of_wordW ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall x
                   (x := eta_fe2519_32W x)
                   (Hx : is_bounded (fe2519_32WToZ x) = true),
          let args := unop_args_to_bounded x Hx in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWordW.BoundedWordToBounds) args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_wordW ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => unopFEToZ_bounds_good bounds = true
          | None => False
          end)
  : unop_FEToZ_correct (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x Hx.
  pose x as x'.
  hnf in x; destruct_head' prod.
  specialize (H0 x' Hx).
  specialize (H1 x' Hx).
  let args := constr:(unop_args_to_bounded x' Hx) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.
