Require Export Crypto.Specific.GF25519Reflective.Common.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Util.Tactics.

Local Opaque Interp.
Local Notation eta_and x := (let (a, b) := x in a, let (a, b) := x in b) (only parsing).
Lemma Expr10_4Op_correct_and_bounded
      ropW op (ropZ_sig : rexpr_10_4op_sig op)
      (Hbounds : correct_and_bounded_genT ropW ropZ_sig)
      (H0 : forall x0123456789
                   (x0123456789
                    := (eta_fe25519W (fst (fst (fst (fst (fst (fst (fst (fst (fst x0123456789))))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst (fst (fst x0123456789))))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst (fst x0123456789)))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst x0123456789))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst x0123456789)))))),
                        eta_fe25519W (snd (fst (fst (fst (fst x0123456789))))),
                        eta_fe25519W (snd (fst (fst (fst x0123456789)))),
                        eta_fe25519W (snd (fst (fst x0123456789))),
                        eta_fe25519W (snd (fst x0123456789)),
                        eta_fe25519W (snd x0123456789)))
                   (Hx0123456789
                    : is_bounded (fe25519WToZ (fst (fst (fst (fst (fst (fst (fst (fst (fst x0123456789)))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst (fst (fst x0123456789)))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst (fst x0123456789))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst x0123456789)))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst x0123456789))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst x0123456789)))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst x0123456789))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst x0123456789)))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst x0123456789))) = true
                      /\ is_bounded (fe25519WToZ (snd x0123456789)) = true),
          let (Hx0, Hx123456789) := (eta_and Hx0123456789) in
          let (Hx1, Hx23456789) := (eta_and Hx123456789) in
          let (Hx2, Hx3456789) := (eta_and Hx23456789) in
          let (Hx3, Hx456789) := (eta_and Hx3456789) in
          let (Hx4, Hx56789) := (eta_and Hx456789) in
          let (Hx5, Hx6789) := (eta_and Hx56789) in
          let (Hx6, Hx789) := (eta_and Hx6789) in
          let (Hx7, Hx89) := (eta_and Hx789) in
          let (Hx8, Hx9) := (eta_and Hx89) in
          let args := op10_args_to_bounded x0123456789 Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 Hx9 in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWordW.interp_op) (MapInterp BoundedWordW.of_wordW ropW))
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall x0123456789
                   (x0123456789
                    := (eta_fe25519W (fst (fst (fst (fst (fst (fst (fst (fst (fst x0123456789))))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst (fst (fst x0123456789))))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst (fst x0123456789)))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst (fst x0123456789))))))),
                        eta_fe25519W (snd (fst (fst (fst (fst (fst x0123456789)))))),
                        eta_fe25519W (snd (fst (fst (fst (fst x0123456789))))),
                        eta_fe25519W (snd (fst (fst (fst x0123456789)))),
                        eta_fe25519W (snd (fst (fst x0123456789))),
                        eta_fe25519W (snd (fst x0123456789)),
                        eta_fe25519W (snd x0123456789)))
                   (Hx0123456789
                    : is_bounded (fe25519WToZ (fst (fst (fst (fst (fst (fst (fst (fst (fst x0123456789)))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst (fst (fst x0123456789)))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst (fst x0123456789))))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst (fst x0123456789)))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst (fst x0123456789))))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst (fst x0123456789)))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst (fst x0123456789))))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst (fst x0123456789)))) = true
                      /\ is_bounded (fe25519WToZ (snd (fst x0123456789))) = true
                      /\ is_bounded (fe25519WToZ (snd x0123456789)) = true),
          let (Hx0, Hx123456789) := (eta_and Hx0123456789) in
          let (Hx1, Hx23456789) := (eta_and Hx123456789) in
          let (Hx2, Hx3456789) := (eta_and Hx23456789) in
          let (Hx3, Hx456789) := (eta_and Hx3456789) in
          let (Hx4, Hx56789) := (eta_and Hx456789) in
          let (Hx5, Hx6789) := (eta_and Hx56789) in
          let (Hx6, Hx789) := (eta_and Hx6789) in
          let (Hx7, Hx89) := (eta_and Hx789) in
          let (Hx8, Hx9) := (eta_and Hx89) in
          let args := op10_args_to_bounded x0123456789 Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 Hx9 in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWordW.BoundedWordToBounds) args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_wordW ropW)) (LiftOption.to' (Some x')))
          with
          | Some bounds => op10_4_bounds_good bounds = true
          | None => False
          end)
  : op10_4_correct_and_bounded (MapInterp (fun _ x => x) ropW) op.
Proof.
  intros x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
  intros Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 Hx9.
  pose x0 as x0'.
  pose x1 as x1'.
  pose x2 as x2'.
  pose x3 as x3'.
  pose x4 as x4'.
  pose x5 as x5'.
  pose x6 as x6'.
  pose x7 as x7'.
  pose x8 as x8'.
  pose x9 as x9'.
  hnf in x0, x1, x2, x3, x4, x5, x6, x7, x8, x9; destruct_head' prod.
  specialize (H0 (x0', x1', x2', x3', x4', x5', x6', x7', x8', x9')
                 (conj Hx0 (conj Hx1 (conj Hx2 (conj Hx3 (conj Hx4 (conj Hx5 (conj Hx6 (conj Hx7 (conj Hx8 Hx9)))))))))).
  specialize (H1 (x0', x1', x2', x3', x4', x5', x6', x7', x8', x9')
                 (conj Hx0 (conj Hx1 (conj Hx2 (conj Hx3 (conj Hx4 (conj Hx5 (conj Hx6 (conj Hx7 (conj Hx8 Hx9)))))))))).
  Time let args := constr:(op10_args_to_bounded (x0', x1', x2', x3', x4', x5', x6', x7', x8', x9') Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 Hx9) in
       admit; t_correct_and_bounded ropZ_sig Hbounds H0 H1 args. (* On 8.6beta1, with ~2 GB RAM, Finished transaction in 46.56 secs (46.372u,0.14s) (successful) *)
Admitted. (*Time Qed. (* On 8.6beta1, with ~4.3 GB RAM, Finished transaction in 67.652 secs (66.932u,0.64s) (successful) *)*)
