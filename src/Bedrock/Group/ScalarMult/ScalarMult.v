Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import bedrock2.Syntax.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.Loops.
Require Import Crypto.Bedrock.Group.Point.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.ScalarField.
Require Import Crypto.Bedrock.Specs.Group.
Require Import Crypto.Curves.Montgomery.AffineInstances.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Curves.Montgomery.XZProofs.
Require Import Crypto.Spec.MontgomeryCurve.
Require Import Crypto.Util.Loops.

Instance montgomery_xz_parameters
         {field_parameters : FieldParameters}
         (M_prime : Znumtheory.prime M) (* TODO: move to field_parameters_ok or something *)
         (char_ge_3 : Ring.char_ge 3)
         (a b : F M_pos)
         (b_nonzero : b <> F.zero)
         (scmul : string)
  : GroupParameters :=
  { G := @M.point (F M_pos) Logic.eq F.add F.mul a b;
    eq := @M.eq (F M_pos) Logic.eq F.add F.mul a b;
    add := @M.add _ _ _ _ _ _ _ _ _ _ (@F.field_modulo M_pos M_prime) F.eq_dec char_ge_3 a b b_nonzero;
    zero := @M.zero (F M_pos) Logic.eq F.add F.mul a b;
    opp := @Affine.M.opp _ _ _ _ _ _ _ _ _ _ (@F.field_modulo M_pos M_prime) F.eq_dec a b b_nonzero;
    scalarmult :=
      @scalarmult_ref _ (M.add (b_nonzero:=b_nonzero))
                      M.zero
                      (Affine.M.opp (b_nonzero:=b_nonzero));
    scmul := scmul;
    }.

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
    cbv [Rewriter.Util.LetIn.Let_In dlet.dlet]. cbn [fst snd].
    rewrite !F.pow_2_r. reflexivity.
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
    cbv [Rewriter.Util.LetIn.Let_In dlet.dlet]. cbn [fst snd].
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
    { destruct_products. rewrite cswap_pair. cbn [fst snd].
      repeat match goal with
             | |- context [match ?e with | pair _ _ => _ end] =>
               destr e
             end.
      reflexivity. }

    (* then, prove loop-equivalence preconditions *)
    { intros. destruct_products. congruence. }
    { intros. destruct_products. LtbToLt.Z.ltb_to_lt.
      rewrite ladderstep_gallina_equiv.
      repeat match goal with
             | _ => progress rewrite Z2Nat.id by lia
             | _ => progress cbn [fst snd]
             | _ => rewrite cswap_pair
             | _ => rewrite <-surjective_pairing
             | H : forall i : nat, _ i = Z.testbit _ _ |- _ =>
               rewrite H
             | H : (_,_) = (_,_) |- _ => inversion H; subst; clear H
             | H : context [match ?e with | pair _ _ => _ end] |- _ =>
               destr e
             | |- context [match ?e with | pair _ _ => _ end] =>
               destr e
             | _ => reflexivity
             end. }
    { rewrite Z2Nat.id by lia. reflexivity. }
  Qed.
End Equivalence.
