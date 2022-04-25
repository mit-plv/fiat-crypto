(* NOTE: broken, fix after Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder. *)
Require Import Rupicola.Lib.Api. (* for helpful tactics + notations *)
Require Import coqutil.Byte.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryEquivalence.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Specs.Group.
Require Import Crypto.Curves.Montgomery.AffineInstances.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Curves.Montgomery.XZProofs.
Require Import Crypto.Spec.MontgomeryCurve.

Module M.
  Section __.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
    Context {locals: map.map String.string word}.
    Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
    Context {ext_spec: bedrock2.Semantics.ExtSpec}.
    Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
    Context {locals_ok : map.ok locals}.
    Context {env_ok : map.ok env}.
    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
    Context {prime_field_parameters : PrimeFieldParameters}
            {prime_field_parameters_ok : PrimeFieldParameters_ok}.

    Local Instance field_parameters : FieldParameters := PrimeField.prime_field_parameters.
    Context {field_representation : FieldRepresentation}
            {field_representation_ok : FieldRepresentation_ok}
            {scalarbits : nat}.

    Let F := F.F.

    Context (char_ge_3 :
               @Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add
                             F.sub F.mul 3)
            (char_ge_5 :
               @Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add
                             F.sub F.mul 5)
            (char_ge_12 :
               @Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add
                              F.sub F.mul 12)
            (char_ge_28 :
               @Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add
                             F.sub F.mul 28)
            (a b : F M_pos) (scmul : string).
    Context
      (b_nonzero : b <> F.zero)
      (discriminant_nonzero : (a * a - (1 + 1 + 1 + 1) <> 0)%F)
      (a24_correct : ((1 + 1 + 1 + 1) * a24)%F = (a - (1 + 1))%F)
      (a2m4_nonsquare :
         forall r : F M_pos,
           (r * r)%F <> (a * a - (1 + 1 + 1 + 1))%F).

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
      feval_bytes x = to_x (to_xz P) /\ bytes_in_bounds x.

    Global Instance x_representation : GroupRepresentation :=
      { gelem := list byte; (* x only, as bytes *)
        grepresents := xrepresents;
        GElem := FElemBytes;
      }.

    Section Implementation.
      Local Instance spec_of_montladder : spec_of "montladder" := spec_of_montladder scalarbits.

      (* redeclaration plugs in implicits so [enter] works *)
      Definition spec_of_scmul : spec_of scmul :=
        Eval cbv [spec_of_scmul] in
          (@spec_of_scmul _ _ _ _ _ _  group_parameters x_representation (Nat.div_up scalarbits 8)).
      Definition spec_of_from_bytes : spec_of from_bytes := spec_of_from_bytes.
      Definition spec_of_to_bytes : spec_of to_bytes := spec_of_to_bytes.
      Existing Instances spec_of_scmul spec_of_from_bytes spec_of_to_bytes.

      Fixpoint repeat_stackalloc
               (size : Z) (names : list string)
        : cmd.cmd -> cmd.cmd :=
        match names with
        | [] => fun post => post
        | n :: names' =>
          fun post =>
            cmd.stackalloc n size (repeat_stackalloc size names' post)
        end.

      (* TODO: make rupicola and stack allocation play nicer together so
         Montgomery ladder doesn't need so many arguments *)
      Definition scmul_func : Syntax.func :=
        (scmul, (["out"; "x_bytes"; "k"], [],
                 repeat_stackalloc
                   felem_size_in_bytes
                   ["X1"; "Z1"; "X2"; "Z2"; "A"; "AA"; "B"; "BB"; "E"; "C"; "D"; "DA"; "CB"; "x"; "r"]
                   (cmd.seq
                      (cmd.call [] from_bytes [expr.var "x"; expr.var "x_bytes"])
                      (cmd.seq
                         (cmd.call [] "montladder"
                                   [expr.var "r"; expr.var "k"; expr.var "x"; expr.var "X1";
                                      expr.var "Z1"; expr.var "X2"; expr.var "Z2"; expr.var "A";
                                        expr.var "AA"; expr.var "B"; expr.var "BB"; expr.var "E";
                                          expr.var "C"; expr.var "D"; expr.var "DA"; expr.var "CB"])
                         (cmd.call [] to_bytes [expr.var "out"; expr.var "r"]))))).

      Lemma and_iff1_l (X : Prop) (P : mem -> Prop) :
        X ->
        Lift1Prop.iff1 (fun m => X /\ P m) P.
      Proof.
        repeat intro.
        split; intros; sepsimpl; eauto.
      Qed.

      (* TODO: generalize this tactic and upstream to bedrock2 *)
      Ltac extract_pred' pred P :=
        lazymatch P with
        | (pred ?X * ?Q)%sep => constr:(pair X Q)
        | (?Q * pred ?X)%sep => constr:(pair X Q)
        | (?P * ?Q)%sep =>
          lazymatch P with
          | context [pred] =>
            match extract_pred' pred P with
            | pair ?X ?P' => constr:(pair X (P' * Q)%sep)
            end
          | _ => lazymatch Q with
                 | context [pred] =>
                   match extract_pred' pred Q with
                   | pair ?X ?Q' => constr:(pair X (P * Q')%sep)
                   end
                 | _ => fail "No emp found in" P Q
                 end
          end
        | _ => fail "expected a separation-logic conjunct with at least 2 terms, got" P
        end.
      Ltac extract_pred pred :=
        match goal with
        | |- context [pred] =>
          match goal with
          | |- sep ?P ?Q ?m =>
            let r := extract_pred' pred (sep P Q) in
            match r with
            | pair ?X ?Y =>
              let H := fresh in
              assert (sep (pred X) Y m) as H;
              [ | clear - H; ecancel_assumption ]
            end
          end
        end.
      Ltac extract_emp :=
        let pred := constr:(emp (map:=mem)) in
        extract_pred pred.
      Ltac extract_ex1 :=
        lazymatch goal with
        | |- context [@Lift1Prop.ex1 ?A ?B] =>
            let pred := constr:(@Lift1Prop.ex1 A B) in
            extract_pred pred
        | _ => fail "extract_ex1 : no ex1 found in goal!"
        end.

      Ltac prove_anybytes_postcondition :=
        repeat lazymatch goal with
               | |- exists m mS,
                   Memory.anybytes ?p ?n mS
                   /\ map.split ?mC m mS
                   /\ ?K =>
                 let H := fresh in
                 let mp := fresh in
                 let mq := fresh in
                 assert (sep (fun m => K) (Placeholder p) mC) as H;
                 [ | clear - H; cbv [sep] in H; cbv [Placeholder];
                     destruct H as [mp [mq [? [? ?]]]];
                     exists mp, mq; ssplit; solve [eauto] ]
               | |- sep (fun mC =>
                           exists m mS,
                             Memory.anybytes ?p ?n mS
                             /\ map.split mC m mS
                             /\ ?K) ?Q ?mem =>
                 let H := fresh in
                 let H' := fresh in
                 let mp := fresh in
                 let mq := fresh in
                 let mp2 := fresh in
                 let mq2 := fresh in
                 assert (sep (sep (fun m => K) (Placeholder p)) Q mem) as H;
                 [ eapply sep_assoc
                 | clear - H; cbv [sep] in H; cbv [Placeholder];
                   destruct H as [mp [mq [? [H' ?] ] ] ];
                   exists mp, mq; ssplit; eauto; [ ];
                   destruct H' as [mp2 [mq2 [? [? ?] ] ] ];
                   exists mp2, mq2; ssplit; solve [eauto] ]
               end.

      (* speedier proof if straightline doesn't try to compute the stack
         allocation sizes *)
      Local Opaque felem_size_in_bytes.
      Lemma scmul_func_correct :
        program_logic_goal_for_function! scmul_func.
      Proof.
        (* straightline doesn't work properly for setup, so the first step
           is inlined and changed here *)
        (* Fail straightline. *)
        cbv [program_logic_goal_for scmul_func spec_of_scmul]; intros.
        WeakestPrecondition.unfold1_call_goal.
        (cbv beta match delta [WeakestPrecondition.call_body]).
        lazymatch goal with
        | |- if ?test then ?T else _ =>
          replace test with true by (rewrite String.eqb_refl; reflexivity);
            change_no_check T
        end; (cbv beta match delta [WeakestPrecondition.func]).

        cbv [GElem x_representation grepresents xrepresents] in *.
        sepsimpl.
        (* plain straightline should do this but doesn't (because locals
           representation is abstract?); using enhanced version from
           rupicola (straightline') *)
        repeat lazymatch goal with
               | |- (felem_size_in_bytes mod _ = 0)%Z /\ _ =>
                 split; [ solve [apply felem_size_in_bytes_mod] | ]
               | Hb : Memory.anybytes ?p ?n ?mS,
                      Hs : map.split ?mC ?m ?mS,
                           Hm : ?P ?m |- _ =>
                   assert (sep P (Placeholder p) mC)
                     by (remember P; cbv [sep]; exists m, mS;
                         ssplit; solve [eauto]);
                   clear Hb Hs
               | _ => clear_old_seps; straightline'
               end.

(* NOTE: broken, fix after Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder. *)
(*
        (* call from_bytes *)
        handle_call; [ solve [eauto] .. | ].
        sepsimpl; repeat straightline'.

        (* call montladder *)
        handle_call; [ solve [eauto] .. | ].
        sepsimpl; repeat straightline'.

        (* clean up *)
        cbv [MontLadderResult] in *.
        clear_old_seps. sepsimpl.

        (* call to_bytes *)
        handle_call; [ solve [eauto] .. | ].
        sepsimpl; subst. clear_old_seps.

        (* prove postcondition, including dealloc *)
        repeat straightline'.
        prove_anybytes_postcondition.
        cbn [WeakestPrecondition.list_map
               WeakestPrecondition.list_map_body].
        seprewrite and_iff1_l; [ reflexivity | ].
        sepsimpl; [ reflexivity .. | ].
        lift_eexists; sepsimpl.

        extract_emp.

        extract_emp.

        sepsimpl; [ | | ].
        {
          pose proof scalarbits_pos.
          match goal with
          | H : context [montladder_gallina] |- _ =>
            erewrite montladder_gallina_equiv in H
              by (reflexivity || lia)
          end.
          cbv [grepresents xrepresents] in *.
          cbn [scalarmult group_parameters].
          match goal with
          | H : M.montladder _ _ _ = feval ?x
            |- feval_bytes ?y = _ =>
            let H' := fresh in
            assert (feval x = feval_bytes y) as H' by eauto;
              rewrite <-H', <-H; clear H H'
          end.
          apply @M.montladder_correct with (Feq := Logic.eq);
            eauto using F.inv_0, sceval_range with lia; try congruence. }
        { eauto. }
        { repeat match goal with
                 | H : context [FElem ?p] |- context [Placeholder ?p] =>
                   seprewrite (FElem_from_bytes p)
                 end.
          sepsimpl. lift_eexists.
          ecancel_assumption. }
      Qed.
 *)
      Abort.
    End Implementation.
  End __.
End M.
