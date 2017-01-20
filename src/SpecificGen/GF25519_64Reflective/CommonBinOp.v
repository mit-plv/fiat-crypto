Require Export Crypto.SpecificGen.GF25519_64Reflective.Common.
Require Import Crypto.SpecificGen.GF25519_64BoundedCommon.
Require Import Crypto.Reflection.Z.Interpretations128.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Util.Tactics.

Local Opaque Interp.
Lemma ExprBinOp_correct_and_bounded
      ropW op (ropZ_sig : rexpr_binop_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall xy
                   (xy := (eta_fe25519_64W (fst xy), eta_fe25519_64W (snd xy)))
                   (Hxy : is_bounded (fe25519_64WToZ (fst xy)) = true
                          /\ is_bounded (fe25519_64WToZ (snd xy)) = true),
          let Hx := let (Hx, Hy) := Hxy in Hx in
          let Hy := let (Hx, Hy) := Hxy in Hy in
          let args := binop_args_to_bounded xy Hx Hy in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWordW.interp_op) ropW)
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall xy
                   (xy := (eta_fe25519_64W (fst xy), eta_fe25519_64W (snd xy)))
                   (Hxy : is_bounded (fe25519_64WToZ (fst xy)) = true
                          /\ is_bounded (fe25519_64WToZ (snd xy)) = true),
          let Hx := let (Hx, Hy) := Hxy in Hx in
          let Hy := let (Hx, Hy) := Hxy in Hy in
          let args := binop_args_to_bounded (fst xy, snd xy) Hx Hy in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWordW.BoundedWordToBounds) args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) ropW) (LiftOption.to' (Some x')))
          with
          | Some bounds => binop_bounds_good bounds = true
          | None => False
          end)
  : binop_correct_and_bounded ropW op.
Proof.
  intros x y Hx Hy.
  pose x as x'; pose y as y'.
  hnf in x, y; destruct_head' prod.
  specialize (H0 (x', y') (conj Hx Hy)).
  specialize (H1 (x', y') (conj Hx Hy)).
  let args := constr:(binop_args_to_bounded (x', y') Hx Hy) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.
