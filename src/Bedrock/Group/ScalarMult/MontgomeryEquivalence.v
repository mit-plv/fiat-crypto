Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import bedrock2.Semantics.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Group.Loops.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Curves.Montgomery.XZProofs.
Require Import Crypto.Util.Loops.

Section Equivalence.
  Context {prime_field_parameters : PrimeFieldParameters}.

  (*TODO: which of ladderstep_gallina and M.xzladderstep should we change? either?*)
  Definition reorder_pairs {A B C D} (p : \<<A , B , C , D\>>) : (A*B)*(C*D) :=
    (P2.car p, P2.car (P2.cdr p),((P2.car (P2.cdr (P2.cdr p))),(P2.cdr (P2.cdr (P2.cdr p))))).

  (* TODO: should M.montladder change to accomodate this? *)
  Definition to_pair {A B} p : A*B := (P2.car p, P2.cdr p).

  Lemma invert_reorder_pairs {A B C D} (p : \<<A , B , C , D\>>) w x y z
    : reorder_pairs p = (w,x, (y,z)) <-> p = \<w,x,y,z\>.
  Proof.
    destruct p as [? [? [? ?]]].
    cbv.
    intuition congruence.
  Qed.
  
  Lemma ladderstep_gallina_equiv X1 P1 P2 :
    reorder_pairs (ladderstep_gallina _ a24 X1 (fst P1) (snd P1) (fst P2) (snd P2)) =
    @M.xzladderstep
      _ F.add F.sub F.mul a24 X1 P1 P2.
  Proof.
    intros. cbv [ladderstep_gallina M.xzladderstep].
    destruct P1 as [x1 z1]. destruct P2 as [x2 z2].
    cbv [Rewriter.Util.LetIn.Let_In nlet]. cbn [fst snd].
    rewrite !F.pow_2_r; trivial.
  Qed.

  Lemma montladder_gallina_equiv scalarbits n point :
    montladder_gallina _ a24 scalarbits n point =
    @M.montladder _ F.zero F.one F.add F.sub F.mul F.inv
      a24 (fun b x y => to_pair (cswap b x y)) (Z.of_nat scalarbits) (Z.testbit n) point.
  Proof.
    cbv [montladder_gallina M.montladder Rewriter.Util.LetIn.Let_In stack].
    do 5 (unfold nlet at 1); cbn [fst snd P2.car P2.cdr].
    rewrite downto_while.
    match goal with
    | |- ?lhs = ?rhs =>
      match lhs with context [while ?ltest ?lbody ?fuel ?linit] =>
      match rhs with context [while ?rtest ?rbody ?fuel ?rinit] =>
      rewrite (while.preservation ltest lbody rtest rbody
        (fun s1 s2 => s1 = let '(x2, z2, x3, z3, swap, i) := s2 in
        (\<x2, z2, x3, z3, swap\>, i))) with (init2:=rinit)
    end end end.
    { rewrite !Nat2Z.id. destruct (while _ _ _ _) eqn:? at 1 2.
      destruct_products; reflexivity. }
    { intros. destruct_products. congruence. }
    { intros. destruct_products. Prod.inversion_prod. LtbToLt.Z.ltb_to_lt. subst.
      rewrite !Z2Nat.id by lia.
      cbv [nlet].
      repeat match goal with
             | H : (_,_) = (_,_) |- _ => inversion H; subst; clear H
             | _ => progress BreakMatch.break_match
             | _ => progress BreakMatch.break_match_hyps
             end. 
      rewrite <- ladderstep_gallina_equiv, invert_reorder_pairs  in Heqp2.
      cbn [fst snd] in Heqp2.
      unfold to_pair in Heqp0;
      inversion Heqp0; subst; clear Heqp0.
      unfold to_pair in Heqp1;
        inversion Heqp1; subst; clear Heqp1.
      set (ladderstep_gallina _ _ _ _ _ _ _) in *.
      rewrite Heqp2. reflexivity. }
    { reflexivity. }
  Qed.

End Equivalence.
