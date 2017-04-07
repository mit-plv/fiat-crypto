Require Import Coq.omega.Omega.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.NatUtil.

Notation round_up_monotone_T round_up
  := (forall x y,
         (x <= y)%nat
         -> match round_up x, round_up y with
            | Some x', Some y' => (x' <= y')%nat
            | None, None => True
            | Some _, None => True
            | None, Some _ => False
            end)
       (only parsing).

Lemma round_up_to_in_list_monotone (allowable_lgsz : list nat)
  : round_up_monotone_T (Bounds.round_up_to_in_list allowable_lgsz).
Proof.
  intros x y H.
  induction allowable_lgsz as [|s ss].
  { constructor. }
  { unfold Bounds.round_up_to_in_list in *.
    repeat match goal with
           | _ => solve [ trivial ]
           | _ => progress simpl in *
           | _ => progress break_innermost_match_step
           | _ => progress break_innermost_match_hyps_step
           | [ H : ?leb _ _ = true |- _ ] => apply NPeano.Nat.leb_le in H
           | [ H : ?leb _ _ = false |- _ ] => apply NPeano.Nat.leb_gt in H
           | _ => omega *
           end. }
Qed.
