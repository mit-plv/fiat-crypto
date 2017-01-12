Require Export Crypto.Specific.GF25519Reflective.Common.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
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
                  (Interp (@BoundedWordW.interp_op) ropW
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
                  (Interp (@ZBounds.interp_op) ropW (LiftOption.to' (Some x')))
          with
          | Some bounds => op9_4_bounds_good bounds = true
          | None => False
          end)
  : op9_4_correct_and_bounded ropW op.
Proof.
  intros xs Hxs.
  pose xs as xs'.
  compute in xs.
  destruct_head' prod.
  cbv [Tuple.map Tuple.on_tuple Tuple.to_list Tuple.to_list' fst snd List.map Tuple.from_list Tuple.from_list' HList.hlistP HList.hlistP'] in Hxs.
  pose Hxs as Hxs'.
  destruct Hxs as [ [ [ [ [ [ [ [ Hx0 Hx1 ] Hx2 ] Hx3 ] Hx4 ] Hx5 ] Hx6 ] Hx7 ] Hx8 ].
  specialize (H0 xs'
                 (conj Hx0 (conj Hx1 (conj Hx2 (conj Hx3 (conj Hx4 (conj Hx5 (conj Hx6 (conj Hx7 Hx8))))))))).
  specialize (H1 xs'
                 (conj Hx0 (conj Hx1 (conj Hx2 (conj Hx3 (conj Hx4 (conj Hx5 (conj Hx6 (conj Hx7 Hx8))))))))).
  Time let args := constr:(op9_args_to_bounded xs' Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8) in
       admit; t_correct_and_bounded ropZ_sig Hbounds H0 H1 args. (* On 8.6beta1, with ~2 GB RAM, Finished transaction in 46.56 secs (46.372u,0.14s) (successful) *)
Admitted. (*Time Qed. (* On 8.6beta1, with ~4.3 GB RAM, Finished transaction in 67.652 secs (66.932u,0.64s) (successful) *)*)
