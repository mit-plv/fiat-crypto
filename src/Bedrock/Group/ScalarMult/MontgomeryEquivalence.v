Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import bedrock2.Semantics.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Group.Loops.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Curves.Montgomery.XZProofs.
Require Import Crypto.Util.Loops.

Section Equivalence.
  Context {field_parameters : FieldParameters}.

  (*TODO: which of ladderstep_gallina and M.xzladderstep should we change? either?*)
  Definition reorder_pairs {A B C D} (p : \<<A , B , C , D\>>) : (A*B)*(C*D) :=
    (P2.car p, P2.car (P2.cdr p),((P2.car (P2.cdr (P2.cdr p))),(P2.cdr (P2.cdr (P2.cdr p))))).

  Lemma invert_reorder_pairs {A B C D} (p : \<<A , B , C , D\>>) w x y z
    : reorder_pairs p = (w,x, (y,z)) <-> p = \<w,x,y,z\>.
  Proof.
    destruct p as [? [? [? ?]]].
    cbv.
    intuition congruence.
  Qed.
  
  Lemma ladderstep_gallina_equiv X1 P1 P2 :
    reorder_pairs (ladderstep_gallina X1 (fst P1) (snd P1) (fst P2) (snd P2)) =
    @M.xzladderstep
      _ F.add F.sub F.mul a24 X1 P1 P2.
  Proof.
    intros. cbv [ladderstep_gallina M.xzladderstep].
    destruct P1 as [x1 z1]. destruct P2 as [x2 z2].
    cbv [Rewriter.Util.LetIn.Let_In Notations.nlet]. cbn [fst snd].
    rewrite !F.pow_2_r; trivial.
  Qed.

  (*TODO: account for reorder_pairs*)
  Lemma montladder_gallina_equiv
        n scalarbits testb point :
    (forall i, testb i = Z.testbit n (Z.of_nat i)) ->
    (0 <= scalarbits)%Z ->
    montladder_gallina scalarbits testb point =
    @M.montladder
      _ F.zero F.one F.add F.sub F.mul F.inv
      a24 cswap scalarbits (Z.testbit n) point.
  Proof.
    intros. cbv [montladder_gallina M.montladder].
    cbv [Rewriter.Util.LetIn.Let_In Notations.nlet]. cbn [fst snd P2.car P2.cdr].
    rewrite downto_while.
    unfold Alloc.stack.
    match goal with
    | |- ?lhs = ?rhs =>
      match lhs with
        | context [while ?ltest ?lbody ?fuel ?linit] =>
        match rhs with
          | context [while ?rtest ?rbody ?fuel ?rinit] =>
            rewrite (while.preservation
                       ltest lbody rtest rbody
                       (fun s1 s2 =>
                          s1 =
                          let '(x2, z2, x3, z3, swap, i) := s2 in
                          (\<x2, z2, x3, z3, swap\>, i)))
              with (init2:=rinit);
              [ remember (while rtest rbody fuel rinit) | .. ]
        end end end.

    (* first, finish proving post-loop equivalence *)
    { destruct_products; cbn [fst snd]. reflexivity. }

    (* then, prove loop-equivalence preconditions *)
    { intros. destruct_products. congruence. }
    { intros. destruct_products. LtbToLt.Z.ltb_to_lt.
      repeat match goal with
             | _ => progress rewrite Z2Nat.id by lia
             | _ => progress cbn [fst snd]
             | _ => rewrite cswap_pair
             | _ => rewrite ladderstep_gallina_equiv
             | _ => rewrite <-surjective_pairing
             | H : forall i : nat, _ i = Z.testbit _ _ |- _ =>
               rewrite H
             | H : (_,_) = (_,_) |- _ => inversion H; subst; clear H
             | H : context [match ?e with | pair _ _ => _ end] |- _ =>
               destr e
             | |- context [match ?e with | pair _ _ => _ end] =>
               destr e
             | _ => reflexivity
             end. 

      rewrite <- ladderstep_gallina_equiv in E2.
      rewrite invert_reorder_pairs in E2.
      simpl in E2.
      rewrite E2.
      reflexivity.
    }
    { rewrite Z2Nat.id by lia. reflexivity. }
  Qed.

End Equivalence.
