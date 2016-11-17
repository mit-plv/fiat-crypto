Require Export Crypto.Specific.GF25519Reflective.Common.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Util.Tactics.

Local Opaque Interp.
Local Notation eta_and x := (let (a, b) := x in a, let (a, b) := x in b) (only parsing).
Lemma Expr9_4Op_correct_and_bounded
      ropW op (ropZ_sig : rexpr_9_4op_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall x012345678
                   (x012345678
                    := (eta_fe25519W (fst (fst (fst (fst (fst (fst (fst (fst x012345678)))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst (fst x012345678)))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst x012345678))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst x012345678)))))),
                        eta_fe25519W (snd (fst (fst (fst (fst x012345678))))),
                        eta_fe25519W (snd (fst (fst (fst x012345678)))),
                        eta_fe25519W (snd (fst (fst x012345678))),
                        eta_fe25519W (snd (fst x012345678)),
                        eta_fe25519W (snd x012345678)))
                   (Hx012345678
                    : is_bounded (fe25519WToZ (fst (fst (fst (fst (fst (fst (fst (fst x012345678))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst (fst x012345678))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst x012345678)))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst x012345678))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst x012345678)))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst x012345678))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst x012345678)))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst x012345678))) = true
                      /\ is_bounded (fe25519WToZ (snd x012345678)) = true),
          let (Hx0, Hx12345678) := (eta_and Hx012345678) in
          let (Hx1, Hx2345678) := (eta_and Hx12345678) in
          let (Hx2, Hx345678) := (eta_and Hx2345678) in
          let (Hx3, Hx45678) := (eta_and Hx345678) in
          let (Hx4, Hx5678) := (eta_and Hx45678) in
          let (Hx5, Hx678) := (eta_and Hx5678) in
          let (Hx6, Hx78) := (eta_and Hx678) in
          let (Hx7, Hx8) := (eta_and Hx78) in
          let args := op9_args_to_bounded x012345678 Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWordW.interp_op) (MapInterp BoundedWordW.of_wordW ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall x012345678
                   (x012345678
                    := (eta_fe25519W (fst (fst (fst (fst (fst (fst (fst (fst x012345678)))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst (fst x012345678)))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst x012345678))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst x012345678)))))),
                        eta_fe25519W (snd (fst (fst (fst (fst x012345678))))),
                        eta_fe25519W (snd (fst (fst (fst x012345678)))),
                        eta_fe25519W (snd (fst (fst x012345678))),
                        eta_fe25519W (snd (fst x012345678)),
                        eta_fe25519W (snd x012345678)))
                   (Hx012345678
                    : is_bounded (fe25519WToZ (fst (fst (fst (fst (fst (fst (fst (fst x012345678))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst (fst x012345678))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst x012345678)))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst x012345678))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst x012345678)))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst x012345678))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst x012345678)))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst x012345678))) = true
                      /\ is_bounded (fe25519WToZ (snd x012345678)) = true),
          let (Hx0, Hx12345678) := (eta_and Hx012345678) in
          let (Hx1, Hx2345678) := (eta_and Hx12345678) in
          let (Hx2, Hx345678) := (eta_and Hx2345678) in
          let (Hx3, Hx45678) := (eta_and Hx345678) in
          let (Hx4, Hx5678) := (eta_and Hx45678) in
          let (Hx5, Hx678) := (eta_and Hx5678) in
          let (Hx6, Hx78) := (eta_and Hx678) in
          let (Hx7, Hx8) := (eta_and Hx78) in
          let args := op9_args_to_bounded x012345678 Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWordW.BoundedWordToBounds) args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_wordW ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => op9_4_bounds_good bounds = true
          | None => False
          end)
  : op9_4_correct_and_bounded (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x0 x1 x2 x3 x4 x5 x6 x7 x8.
  intros Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8.
  pose x0 as x0'.
  pose x1 as x1'.
  pose x2 as x2'.
  pose x3 as x3'.
  pose x4 as x4'.
  pose x5 as x5'.
  pose x6 as x6'.
  pose x7 as x7'.
  pose x8 as x8'.
  hnf in x0, x1, x2, x3, x4, x5, x6, x7, x8; destruct_head' prod.
  specialize (H0 (x0', x1', x2', x3', x4', x5', x6', x7', x8')
                 (conj Hx0 (conj Hx1 (conj Hx2 (conj Hx3 (conj Hx4 (conj Hx5 (conj Hx6 (conj Hx7 Hx8))))))))).
  specialize (H1 (x0', x1', x2', x3', x4', x5', x6', x7', x8')
                 (conj Hx0 (conj Hx1 (conj Hx2 (conj Hx3 (conj Hx4 (conj Hx5 (conj Hx6 (conj Hx7 Hx8))))))))).
  let args := constr:(op9_args_to_bounded (x0', x1', x2', x3', x4', x5', x6', x7', x8') Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.
