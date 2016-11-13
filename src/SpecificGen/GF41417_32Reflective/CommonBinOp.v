Require Export Crypto.SpecificGen.GF41417_32Reflective.Common.
Require Import Crypto.SpecificGen.GF41417_32BoundedCommon.
Require Import Crypto.Reflection.Z.Interpretations.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Util.Tactics.

Local Opaque Interp.
Lemma ExprBinOp_correct_and_bounded
      ropW op (ropZ_sig : rexpr_binop_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall xy
                   (xy := (eta_fe41417_32W (fst xy), eta_fe41417_32W (snd xy)))
                   (Hxy : is_bounded (fe41417_32WToZ (fst xy)) = true
                          /\ is_bounded (fe41417_32WToZ (snd xy)) = true),
          let Hx := let (Hx, Hy) := Hxy in Hx in
          let Hy := let (Hx, Hy) := Hxy in Hy in
          let args := binop_args_to_bounded xy Hx Hy in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall xy
                   (xy := (eta_fe41417_32W (fst xy), eta_fe41417_32W (snd xy)))
                   (Hxy : is_bounded (fe41417_32WToZ (fst xy)) = true
                          /\ is_bounded (fe41417_32WToZ (snd xy)) = true),
          let Hx := let (Hx, Hy) := Hxy in Hx in
          let Hy := let (Hx, Hy) := Hxy in Hy in
          let args := binop_args_to_bounded (fst xy, snd xy) Hx Hy in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWord64.BoundedWordToBounds) args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => binop_bounds_good bounds = true
          | None => False
          end)
  : binop_correct_and_bounded (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x y Hx Hy.
  pose x as x'; pose y as y'.
  hnf in x, y; destruct_head' prod.
  specialize (H0 (x', y') (conj Hx Hy)).
  specialize (H1 (x', y') (conj Hx Hy)).
  let args := constr:(binop_args_to_bounded (x', y') Hx Hy) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.
