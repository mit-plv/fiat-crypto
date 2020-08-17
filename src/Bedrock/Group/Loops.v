Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Crypto.Util.Loops.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.

(** Helper lemmas for proving equivalence between different loop formats
    (e.g. rupicola's [downto] and Util/Loops.v's [while] **)

Section DownToWhile.
  Lemma downto'_while
        {state} (count : nat)
        (step : state -> nat -> state) :
    forall start init,
      downto' init start count step =
      fst (while (fun '(_, i) => (i >=? Z.of_nat start)%Z)
                 (fun '(s, i) => (step s (Z.to_nat i), Z.pred i))
               count (init, Z.pred (Z.of_nat count))).
  Proof.
    induction count; intros.
    { destruct start; [ reflexivity | ].
      cbn; autorewrite with push_skipn; reflexivity. }
    { rewrite Nat2Z.inj_succ, Z.pred_succ.
      cbn [while]; break_match;
        LtbToLt.Z.ltb_to_lt;
        match goal with
        | H : (Z.of_nat _ < Z.of_nat _)%Z |- _ =>
          apply Nat2Z.inj_lt in H
        | H : (Z.of_nat _ >= Z.of_nat _)%Z |- _ =>
          apply Nat2Z.inj_ge in H
        end; [ | ].
      { rewrite <-IHcount, Nat2Z.id.
        cbv [downto']. rewrite seq_snoc.
        autorewrite with natsimplify push_skipn distr_length.
        rewrite rev_app_distr, fold_left_app.
        reflexivity. }
      { cbv [downto']. autorewrite with push_skipn.
        reflexivity. } }
  Qed.

  Lemma downto_while
        {state} (count : nat)
        (step : state -> nat -> state) :
    forall init : state,
      downto init count step =
      fst (while (fun '(_, i) => (i >=? 0)%Z)
                 (fun '(s, i) => (step s (Z.to_nat i), Z.pred i))
               count (init, Z.pred (Z.of_nat count))).
  Proof. apply downto'_while. Qed.
End DownToWhile.
