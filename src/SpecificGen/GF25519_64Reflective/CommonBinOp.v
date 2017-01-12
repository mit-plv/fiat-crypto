Require Export Crypto.SpecificGen.GF25519_64Reflective.Common.
Require Import Crypto.SpecificGen.GF25519_64BoundedCommon.
Require Import Crypto.Reflection.Z.Interpretations128.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
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
                  (Interp (@BoundedWordW.interp_op) ropW
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
                  (Interp (@ZBounds.interp_op) ropW (LiftOption.to' (Some x')))
          with
          | Some bounds => binop_bounds_good bounds = true
          | None => False
          end)
  : binop_correct_and_bounded ropW op.
Proof.
  intros xy HxHy.
  pose xy as xy'.
  compute in xy; destruct_head' prod.
  specialize (H0 xy' HxHy).
  specialize (H1 xy' HxHy).
  destruct HxHy as [Hx Hy].
  let args := constr:(binop_args_to_bounded xy' Hx Hy) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.
