Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
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
  Context {semantics : Semantics.parameters}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  Lemma ladderstep_gallina_equiv X1 P1 P2 :
    ladderstep_gallina X1 P1 P2 =
    @M.xzladderstep
      _ F.add F.sub F.mul a24 X1 P1 P2.
  Proof.
    intros. cbv [ladderstep_gallina M.xzladderstep].
    destruct P1 as [x1 z1]. destruct P2 as [x2 z2].
    cbv [Rewriter.Util.LetIn.Let_In Notations.nlet]. cbn [fst snd].
    rewrite !F.pow_2_r; trivial.
  Qed.

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
    cbv [Rewriter.Util.LetIn.Let_In Notations.nlet]. cbn [fst snd].
    rewrite downto_while.
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
                          (x2, z2, (x3, z3), swap, i)))
              with (init2:=rinit);
              [ remember (while rtest rbody fuel rinit) | .. ]
        end end end.

    (* first, finish proving post-loop equivalence *)
    { destruct_products; cbn [fst snd]. rewrite cswap_pair. cbn [fst snd].
      repeat match goal with
             | |- context [match ?e with | pair _ _ => _ end] =>
               destr e
             end.
      reflexivity. }

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

             (* fixup added during merge without investigation: *)
             setoid_rewrite <-E; setoid_rewrite E3; trivial.
    }
    { rewrite Z2Nat.id by lia. reflexivity. }
  Qed.
End Equivalence.
