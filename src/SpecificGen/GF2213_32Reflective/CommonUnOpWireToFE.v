Require Export Crypto.SpecificGen.GF2213_32Reflective.Common.
Require Import Crypto.SpecificGen.GF2213_32BoundedCommon.
Require Import Crypto.Reflection.Z.Interpretations.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Util.Tactics.

Local Opaque Interp.
Lemma ExprUnOpWireToFE_correct_and_bounded
      ropW op (ropZ_sig : rexpr_unop_WireToFE_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall x
                   (x := eta_wire_digitsW x)
                   (Hx : wire_digits_is_bounded (wire_digitsWToZ x) = true),
          let args := unopWireToFE_args_to_bounded x Hx in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall x
                   (x := eta_wire_digitsW x)
                   (Hx : wire_digits_is_bounded (wire_digitsWToZ x) = true),
          let args := unopWireToFE_args_to_bounded x Hx in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWord64.BoundedWordToBounds) args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => unopWireToFE_bounds_good bounds = true
          | None => False
          end)
  : unop_WireToFE_correct_and_bounded (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x Hx.
  pose x as x'.
  hnf in x; destruct_head' prod.
  specialize (H0 x' Hx).
  specialize (H1 x' Hx).
  let args := constr:(unopWireToFE_args_to_bounded x' Hx) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.
