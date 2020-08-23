Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import bedrock2.Syntax.
Require Import coqutil.Byte.
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

Module M.
  Section __.
    Context {semantics : Semantics.parameters}
            {semantics_ok : Semantics.parameters_ok _}
            {field_parameters : FieldParameters}
            {field_parameters_ok : FieldParameters_ok}
            {field_representation : FieldRepresentation}
            {field_representation_ok : FieldRepresentation_ok}.
    Context (char_ge_3 :
               @Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add
                             F.sub F.mul 3)
            (char_ge_12 :
               @Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add
                              F.sub F.mul 12)
            (char_ge_28 :
               @Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add
                             F.sub F.mul 28)
            (a b : F M_pos) (b_nonzero : b <> F.zero)
            (discriminant_nonzero : (a * a - (1 + 1 + 1 + 1) <> 0)%F)
            (scmul : string).
    Local Notation to_xz := (M.to_xz (F:=F M_pos) (Feq:=Logic.eq)
                                     (Fzero:=F.zero) (Fone:=F.one)
                                     (Fadd:=F.add) (Fmul:=F.mul)
                                     (a:=a) (b:=b)).
    Local Notation to_x := (M.to_x (F:=F M_pos) (Feq:=Logic.eq)
                                   (Fzero:=F.zero) (Fdiv:=F.div)
                                   (Feq_dec:=F.eq_dec)).

    Global Instance group_parameters
      : GroupParameters :=
      { G := @M.point (F M_pos) Logic.eq F.add F.mul a b;
        eq := @M.eq (F M_pos) Logic.eq F.add F.mul a b;
        add := @M.add (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub
                      F.mul F.inv F.div (@F.field_modulo M_pos M_prime)
                      F.eq_dec char_ge_3 a b b_nonzero;
        zero := @M.zero (F M_pos) Logic.eq F.add F.mul a b;
        opp := @Affine.M.opp _ _ _ _ _ _ _ _ _ _ (@F.field_modulo M_pos M_prime) F.eq_dec a b b_nonzero;
        scalarmult :=
          @scalarmult_ref _
                          (M.add
                             (field := @F.field_modulo M_pos M_prime)
                             (char_ge_3 := char_ge_3)
                             (b_nonzero := b_nonzero))
                          M.zero
                          (Affine.M.opp
                             (field := @F.field_modulo M_pos M_prime)
                             (b_nonzero := b_nonzero));
        scmul := scmul;
      }.

    Global Instance group_parameters_ok : GroupParameters_ok.
    Proof.
      constructor.
      { apply M.MontgomeryWeierstrassIsomorphism; auto. }
      { apply @scalarmult_ref_is_scalarmult.
        apply M.MontgomeryWeierstrassIsomorphism; auto. }
    Qed.

    Definition xrepresents (x : list byte) (P : G) : Prop :=
      feval_bytes x = to_x (to_xz P).

    Global Instance x_representation : GroupRepresentation :=
      { gelem := list byte; (* x only, as bytes *)
        grepresents := xrepresents;
        GElem := FElemBytes;
      }.

    Section Implementation.
      Context {scalar_field_parameters : ScalarFieldParameters}
              {scalar_field_parameters_ok : ScalarFieldParameters_ok}
              {scalar_field_representation : ScalarRepresentation}.
      Existing Instance spec_of_montladder.

      (* redeclaration plugs in implicits so [enter] works *)
      Definition spec_of_scmul : spec_of scmul :=
        Eval cbv [spec_of_scmul] in
          (@spec_of_scmul semantics scalar_field_parameters
                          scalar_field_representation group_parameters
                          x_representation).
      Definition spec_of_from_bytes : spec_of from_bytes :=
        spec_of_from_bytes.
      Existing Instances spec_of_scmul spec_of_from_bytes.

      (* TODO: make rupicola and stack allocation play nicer together so
         Montgomery ladder doesn't need so many arguments *)
      Definition scmul_func : Syntax.func :=
        let n := felem_size_in_bytes in
        (scmul, (["out"; "x_bytes"; "k"], [],
                 cmd.stackalloc
                   "X1" n
                   (cmd.stackalloc
                      "Z1" n
                      (cmd.stackalloc
                         "X2" n
                         (cmd.stackalloc
                            "Z2" n
                            (cmd.stackalloc
                               "A" n
                               (cmd.stackalloc
                                  "AA" n
                                  (cmd.stackalloc
                                     "B" n
                                     (cmd.stackalloc
                                        "BB" n
                                        (cmd.stackalloc
                                           "E" n
                                           (cmd.stackalloc
                                              "C" n
                                              (cmd.stackalloc
                                                 "D" n
                                                 (cmd.stackalloc
                                                    "DA" n
                                                    (cmd.stackalloc
                                                       "CB" n
                                                       (cmd.stackalloc
                                                          "x" n
                                                          (cmd.seq
                                                             (cmd.call [] from_bytes [expr.var "x_bytes"; expr.var "x"])
                                                             (cmd.call [] "montladder" [expr.var "out"; expr.var "k"; expr.var "x"; expr.var "X1"; expr.var "Z1"; expr.var "X2"; expr.var "Z2"; expr.var "A"; expr.var "AA"; expr.var "B"; expr.var "BB"; expr.var "E"; expr.var "C"; expr.var "D"; expr.var "DA"; expr.var "CB"]))))))))))))))))).

      (* speedier proof if straightline doesn't try to compute the stack
         allocation sizes *)
      Local Opaque felem_size_in_bytes.
      Lemma scmul_func_correct :
        program_logic_goal_for_function! scmul_func.
      Proof.
        (* straightline doesn't work properly for setup, so the first step
           is inlined and changed here *)
        Fail straightline.
        cbv [program_logic_goal_for].
        enter scmul_func. intros.
        WeakestPrecondition.unfold1_call_goal.
        (cbv beta match delta [WeakestPrecondition.call_body]).
        lazymatch goal with
        | |- if ?test then ?T else _ =>
          replace test with true by (rewrite String.eqb_refl; reflexivity);
            change_no_check T
        end; (cbv beta match delta [WeakestPrecondition.func]).

        cbv [GElem x_representation] in *. sepsimpl.
        (* plain straightline should do this but doesn't (because locals
           representation is abstract?); using enhanced version from
           rupicola (straightline') *)
        repeat lazymatch goal with
               | |- (felem_size_in_bytes mod _ = 0)%Z /\ _ =>
                 split; [ solve [apply felem_size_in_bytes_mod] | ]
               | Hb : Memory.anybytes ?p ?n ?mS,
                      Hs : map.split ?mC ?m ?mS,
                           Hm : ?P ?m |- _ =>
                 let H := fresh in
                 let bs := fresh "bs" in
                 pose proof (anybytes_to_array_1 _ _ _ Hb) as H;
                   destruct H as [bs [? ?]];
                   assert (sep P (array ptsto (word.of_Z 1) p bs) mC)
                     by (remember P; cbv [sep]; exists m, mS;
                         ssplit; solve [eauto]);
                   clear Hb Hs
               | _ => clear_old_seps; straightline'
               end.

        straightline_call.
        { ssplit.
          { admit. (* needs bytes <-> bignum lemma *) }
          { admit. (* needs bytes <-> bignum lemma *) } }
        { split.
          Print handle_call.
          ecancel_assum
        { ssplit.
          (* TODO: next steps are
             - prove bytes <-> bignum lemmas (from Field/Synthesis/Generic/Bignum.v)
             - change placeholder to Memory.anybytes *)
      Abort.
    End Implementation.
  End __.
End M.

