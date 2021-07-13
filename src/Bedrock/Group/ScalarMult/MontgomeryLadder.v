(* NOTE: the plan is to completely redo montladder after ladderstep is updated to use stackalloc *)

Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation.
Require Import Crypto.Bedrock.Group.Point.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.ScalarField.Interface.Compilation.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.ScalarField.
Require Import Crypto.Util.NumTheoryUtil.
Local Open Scope Z_scope.

Section __.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {scalar_field_parameters : ScalarFieldParameters}.
  Context {scalar_field_parameters_ok : ScalarFieldParameters_ok}.
  Context {field_representaton : FieldRepresentation}
          {scalar_representation : ScalarRepresentation}.
  Context {field_representation_ok : FieldRepresentation_ok}.
  Hint Resolve @relax_bounds : compiler.

  Section Gallina.
    Local Open Scope F_scope.

    Definition montladder_gallina
               (scalarbits : Z) (testbit:nat ->bool) (u:F M_pos)
      : F M_pos :=
      let/n P1 := (1, 0) in
      let/n P2 := (u, 1) in
      let/n swap := false in
      let/n count := scalarbits in
      let '(P1, P2, swap) :=
         downto
           (P1, P2, swap) (* initial state *)
           (Z.to_nat count)
           (fun state i =>
              let '(P1, P2, swap) := state in
              let/n s_i := testbit i in
              let/n swap := xorb swap s_i in
              let/n (P1, P2) := cswap swap P1 P2 in
              let/n (P1, P2) := ladderstep_gallina u P1 P2 in
              let/n swap := s_i in
              (P1, P2, swap)
           ) in
      let/n (P1, P2) := cswap swap P1 P2 in
      let '(x, z) := P1 in
      let/n r := F.inv z in
      let/n r := (x * r) in
      r.
  End Gallina.

  Section MontLadder.
    Context (scalarbits_small : word.wrap scalarbits = scalarbits).

    Instance spec_of_montladder : spec_of "montladder" :=
      fnspec! "montladder"
            (pOUT pK pU pX1 pZ1 pX2 pZ2
                  pA pAA pB pBB pE pC pD pDA pCB : Semantics.word)
            / (K : scalar) (U : felem) (* inputs *)
            OUT X1 Z1 X2 Z2 A AA B BB E C D DA CB (* intermediates *)
            R,
      { requires tr mem :=
           bounded_by tight_bounds U
           /\ (FElem pOUT OUT * Scalar pK K * FElem pU U
               * FElem pX1 X1 * FElem pZ1 Z1
               * FElem pX2 X2 * FElem pZ2 Z2
               * FElem pA A * FElem pAA AA
               * FElem pB B * FElem pBB BB
               * FElem pE E * FElem pC C
               * FElem pD D * FElem pDA DA
               * FElem pCB CB * R)%sep mem;
        ensures tr' mem' :=
          tr' = tr
          /\ (exists OUT X1 Z1 X2 Z2
                     A AA B BB E C D DA CB : felem,
                 feval OUT = montladder_gallina
                               scalarbits
                               (fun i =>
                                  Z.testbit (F.to_Z (sceval K))
                                            (Z.of_nat i))
                               (feval U)
            /\ bounded_by tight_bounds OUT
            /\ (FElem pOUT OUT * Scalar pK K * FElem pU U
                * FElem pX1 X1 * FElem pZ1 Z1
                * FElem pX2 X2 * FElem pZ2 Z2
                * FElem pA A * FElem pAA AA
                * FElem pB B * FElem pBB BB
                * FElem pE E * FElem pC C
                * FElem pD D * FElem pDA DA
                * FElem pCB CB * R)%sep mem) }.

    Ltac apply_compile_cswap_nocopy :=
      simple eapply compile_cswap_nocopy with
        (Data :=
           fun p (X : F _) =>
             (Lift1Prop.ex1
                (fun x =>
                   (emp (feval x = X) * FElem p x)%sep)))
        (tmp:="tmp");
      [ lazymatch goal with
        | |- sep _ _ _ =>
          repeat lazymatch goal with
                 | |- Lift1Prop.ex1 _ _ => eexists
                 | |- feval _ = _ => eassumption
                 | _ => progress sepsimpl
                 end; ecancel_assumption
        | _ => idtac
        end .. | ];
      [ repeat compile_step .. | ];
      [ try congruence .. | ].

    Ltac compile_custom ::=
      simple apply compile_nlet_as_nlet_eq;
      first [ simple eapply compile_downto
            | simple eapply compile_sctestbit
            | simple eapply compile_point_assign
            | simple eapply compile_felem_small_literal
            | simple eapply compile_felem_copy
            | simple eapply compile_cswap_pair
            | apply_compile_cswap_nocopy ].

    (* TODO: make a new loop invariant, drop the sep-local stuff *)
    (*
    Definition downto_inv
               swap_var X1_var Z1_var X2_var Z2_var K_var
               K K_ptr X1_ptr Z1_ptr X2_ptr Z2_ptr Rl
               A_ptr AA_ptr B_ptr BB_ptr E_ptr C_ptr D_ptr DA_ptr CB_ptr
               (locals : Semantics.locals)
               (_ : nat)
               (gst : bool)
               (st : point * point * bool)
               (_ : list word)
      : Semantics.mem -> Prop :=
      let P1 := fst (fst st) in
      let P2 := snd (fst st) in
      let swap := snd st in
      let x1 := fst P1 in
      let z1 := snd P1 in
      let x2 := fst P2 in
      let z2 := snd P2 in
      let swapped := gst in
      liftexists X1_ptr' Z1_ptr' X2_ptr' Z2_ptr'
                 X1 Z1 X2 Z2,
        (emp (bounded_by tight_bounds X1
              /\ bounded_by tight_bounds Z1
              /\ bounded_by tight_bounds X2
              /\ bounded_by tight_bounds Z2
              /\ feval X1 = x1
              /\ feval Z1 = z1
              /\ feval X2 = x2
              /\ feval Z2 = z2
              /\ (if swapped
                  then (X1_ptr' = X2_ptr
                        /\ Z1_ptr' = Z2_ptr
                        /\ X2_ptr' = X1_ptr
                        /\ Z2_ptr' = Z1_ptr)
                  else (X1_ptr' = X1_ptr
                        /\ Z1_ptr' = Z1_ptr
                        /\ X2_ptr' = X2_ptr
                        /\ Z2_ptr' = Z2_ptr))
              /\ (Var swap_var (word.of_Z (Z.b2z swap)) * Var K_var K_ptr
                  * Var X1_var X1_ptr' * Var Z1_var Z1_ptr'
                  * Var X2_var X2_ptr' * Var Z2_var Z2_ptr'
                  * Rl)%sep locals)
         * (Scalar K_ptr K * FElem X1_ptr' X1 * FElem Z1_ptr' Z1
            * FElem X2_ptr' X2 * FElem Z2_ptr' Z2
            * Placeholder A_ptr * Placeholder AA_ptr
            * Placeholder B_ptr * Placeholder BB_ptr
            * Placeholder E_ptr * Placeholder C_ptr
            * Placeholder D_ptr * Placeholder DA_ptr
            * Placeholder CB_ptr))%sep.
*)
    Definition downto_ghost_step
               (K : scalar) (st : point * point * bool)
               (gst : bool) (i : nat) :=
      let swap := snd st in
      let swap := xorb swap (Z.testbit (F.to_Z (sceval K)) (Z.of_nat i)) in
      xorb gst swap.

    Ltac setup_downto_inv_init :=
      lift_eexists; sepsimpl;
      (* first fill in any map.get goals where we know the variable names *)
      lazymatch goal with
      | |- map.get _ ?x = Some _ =>
        tryif is_evar x then idtac
        else (autorewrite with mapsimpl; reflexivity)
      | _ => idtac
      end;
      lazymatch goal with
      | |- (_ * _)%sep _ => ecancel_assumption
      | _ => idtac
      end.

    Ltac solve_downto_inv_subgoals :=
      lazymatch goal with
      | |- map.get _ _ = _ => subst_lets_in_goal; solve_map_get_goal
      | |- bounded_by _ _ => solve [ auto ]
      | |- feval _ = _ =>
        subst_lets_in_goal; first [ reflexivity | assumption ]
      | |- ?x = ?x => reflexivity
      | |- ?x => fail "unrecognized side condition" x
      end.

    Lemma feval_fst_cswap s a b A B :
      feval a = A -> feval b = B ->
      feval (fst (cswap s a b)) = fst (cswap s A B).
    Proof. destruct s; cbn; auto. Qed.

    Lemma feval_snd_cswap s a b A B :
      feval a = A -> feval b = B ->
      feval (snd (cswap s a b)) = snd (cswap s A B).
    Proof. destruct s; cbn; auto. Qed.

    (* Adding word.unsigned_of_Z_1 and word.unsigned_of_Z_0 as hints to
       compiler doesn't work, presumably because of the typeclass
       preconditions. This is a hacky workaround. *)
    (* TODO: figure out a cleaner way to do this *)
    Lemma unsigned_of_Z_1 : word.unsigned (@word.of_Z _ Semantics.word 1) = 1.
    Proof. exact word.unsigned_of_Z_1. Qed.
    Lemma unsigned_of_Z_0 : word.unsigned (@word.of_Z _ Semantics.word 0) = 0.
    Proof. exact word.unsigned_of_Z_0. Qed.
    Hint Resolve unsigned_of_Z_0 unsigned_of_Z_1 : compiler.

    Ltac safe_compile_step :=
      compile_step;
      (* first pass fills in some evars *)
      [ repeat compile_step .. | idtac ];
      (* second pass must solve *)
      [ first [ solve [repeat compile_step]
              | solve [straightline_map_solver_locals] ] .. | idtac ].

    Ltac solve_field_subgoals_with_cswap :=
      lazymatch goal with
      | |- map.get _ _ = Some _ =>
        solve [subst_lets_in_goal; solve_map_get_goal]
      | |- feval _ = _ =>
        solve [eauto using feval_fst_cswap, feval_snd_cswap]
      | |- bounded_by _ (fst (cswap _ _ _)) =>
        apply cswap_cases_fst; solve [auto]
      | |- bounded_by _ (snd (cswap _ _ _)) =>
        apply cswap_cases_snd; solve [auto]
      | _ => idtac
      end; solve [eauto].

    (* create a new evar to take on the second swap clause *)
    Ltac rewrite_cswap_iff1_with_evar_frame :=
      match goal with
        |- (?P * ?R)%sep _ =>
        match P with context [cswap] => idtac end;
        is_evar R;
        let R1 := fresh "R" in
        let R2 := fresh "R" in
        evar (R1 : Semantics.mem -> Prop);
        evar (R2 : Semantics.mem -> Prop);
        unify R (sep R1 R2);
        seprewrite (cswap_iff1 FElem)
      end.

    Ltac safe_field_compile_step :=
      field_compile_step;
      lazymatch goal with
      | |- sep _ ?R _ =>
        tryif is_evar R
        then (repeat rewrite_cswap_iff1_with_evar_frame)
        else (repeat seprewrite (cswap_iff1 FElem));
        ecancel_assumption
      | _ => idtac
      end;
      lazymatch goal with
      | |- context [WeakestPrecondition.cmd] => idtac
      | _ => solve_field_subgoals_with_cswap
      end.

    Existing Instance spec_of_sctestbit.

    Derive montladder_body SuchThat
           (let args := ["OUT"; "K"; "U"; "X1"; "Z1"; "X2"; "Z2";
                           "A"; "AA"; "B"; "BB"; "E"; "C"; "D"; "DA"; "CB"] in
            let montladder : Syntax.func :=
                ("montladder", (args, [], montladder_body)) in
          ltac:(
            let goal := Rupicola.Lib.Tactics.program_logic_goal_for_function
                          montladder [felem_small_literal; felem_copy;
                                        sctestbit; "ladderstep"; inv; mul] in
            exact (__rupicola_program_marker montladder_gallina -> goal)))
         As montladder_correct.
    Proof.
(* NOTE: the plan is to completely redo montladder after ladderstep is updated to use stackalloc *)
    Abort.
(*
      pose proof scalarbits_pos.
      compile_setup.
      repeat compile_step.
      (* need to update point compilation lemmas! Point.v *)

      (* compile constants *)

      cbv [program_logic_goal_for spec_of_montladder].
      setup. cbv [F.one F.zero]. (* expose F.of_Z *)

      (* prevent things from getting stored in pOUT *)
      hide pOUT.

      repeat safe_compile_step.

      let i_var := gen_sym_fetch "v" in (* last used variable name *)
      let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
      remember locals as L;
      evar (l : map.rep (map:=Semantics.locals));
        let Hl := fresh in
        assert (map.remove L i_var = l) as Hl by
              (subst L; push_map_remove; subst_lets_in_goal; reflexivity);
          subst l;
          match type of Hl with
          | _ = ?l =>
            sep_from_literal_locals l;
              match goal with H : sep _ _ l |- _ =>
                              rewrite <-Hl in H; clear Hl
              end
          end.

      let tmp_var := constr:("tmp") in
      let x1_var := constr:("X1") in
      let z1_var := constr:("Z1") in
      let x2_var := constr:("X2") in
      let z2_var := constr:("Z2") in
      let counter_var := gen_sym_fetch "v" in
      let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
        simple eapply compile_downto with
            (wcount := word.of_Z scalarbits)
            (ginit := false)
            (i_var := counter_var)
            (ghost_step := downto_ghost_step K)
            (Inv :=
               downto_inv
                 _ x1_var z1_var x2_var z2_var _
                 _ pK pX1 pZ1 pX2 pZ2
                 _ pA pAA pB pBB pE pC pD pDA pCB);
          [ .. | subst L | subst L ].
      { cbv [downto_inv].
        setup_downto_inv_init.
        all:solve_downto_inv_subgoals. }
      { subst. autorewrite with mapsimpl.
        reflexivity. }
      { rewrite word.unsigned_of_Z, Z2Nat.id by lia;
          solve [eauto using scalarbits_small]. }
      { subst_lets_in_goal. lia. }
      { (* loop body *)
        intros. clear_old_seps.
        match goal with gst' := downto_ghost_step _ _ _ _ |- _ =>
                                subst gst' end.
        destruct_products.
        cbv [downto_inv] in * |-. sepsimpl_hyps.
        eexists; intros.

        (* convert locals back to literal map using the separation-logic
           condition; an alternative would be to have all lemmas play nice with
           locals in separation logic *)
        match goal with H : sep _ _ (map.remove _ ?i_var)
                        |- context [map.get _ ?i_var = Some ?wi] =>
                        eapply Var_put_remove with (v:=wi) in H;
                          eapply sep_assoc in H
        end.
        literal_locals_from_sep.

        repeat safe_compile_step.

        simple eapply compile_ladderstep.
        (* first, resolve evars *)
        all:lazymatch goal with
            | |- feval _ = _ =>
              solve [eauto using feval_fst_cswap, feval_snd_cswap]
            | _ => idtac
            end.
        (* *after* evar resolution *)
        all:lazymatch goal with
            | |- sep _ _ _ =>
              repeat seprewrite (cswap_iff1 FElem);
                ecancel_assumption
            | |- context [WeakestPrecondition.cmd] => idtac
            | _ => solve_field_subgoals_with_cswap
            end.

        repeat safe_compile_step.

        (* TODO: use nlet to do this rename automatically *)
        let locals := lazymatch goal with
                      | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
        let b := lazymatch goal with x := xorb ?b _ |- _ => b end in
        let swap_var := lazymatch locals with
                          context [map.put _ ?x (word.of_Z (Z.b2z b))] => x end in
        eapply compile_rename_bool with (var := swap_var);
          [ solve [repeat compile_step] .. | ].
        intro.

        (* unset loop-local variables *)
        repeat remove_unused_var.

        compile_done.
        { (* prove locals postcondition *)
          autorewrite with mapsimpl.
          ssplit; [ | reflexivity ].
          subst_lets_in_goal. reflexivity. }
        { (* prove loop invariant held *)
          cbv [downto_inv downto_ghost_step].
          cbv [LadderStepResult] in *.
          cleanup; sepsimpl_hyps.
          repeat match goal with
                 | H : ?x = (_, _) |- context [fst ?x] =>
                   rewrite H; progress cbn [fst snd]
                 end.
          clear_old_seps.
          lift_eexists. sepsimpl.
          (* first, resolve evars *)
          all:lazymatch goal with
              | |- @sep _ _ Semantics.mem _ _ _ =>
                repeat seprewrite FElem_from_bytes;
                repeat (sepsimpl; lift_eexists);
                ecancel_assumption
              | |- @sep _ _ Semantics.locals _ _ ?locals =>
                subst_lets_in_goal; push_map_remove;
                  let locals := match goal with |- ?P ?l => l end in
                  sep_from_literal_locals locals;
                    ecancel_assumption
              | _ => idtac
              end.
          (* now solve other subgoals *)
          all:subst_lets_in_goal; eauto.
          match goal with
          | H : if ?gst then _ else _ |-
            if xorb ?gst ?x then _ else _ =>
            destr gst; cleanup; subst;
              cbn [xorb]; destr x
          end.
          all:cbn [cswap fst snd]; ssplit; reflexivity. } }
      { (* loop done; rest of function *)
        intros. destruct_products.
        cbv [downto_inv downto_inv] in *.
        sepsimpl_hyps.

        (* convert locals back to literal map using the separation-logic
           condition; an alternative would be to have all lemmas play nice with
           locals in separation logic *)
        match goal with H : sep _ _ (map.remove _ ?i_var),
                            Hget : map.get _ ?i_var = Some ?wi |- _ =>
                        eapply Var_put_remove with (v:=wi) in H;
                          eapply sep_assoc in H;
                          rewrite map.put_noop in H by assumption
        end.
        literal_locals_from_sep.

        repeat safe_compile_step. (cbv match zeta beta).

        subst_lets_in_goal. erewrite <-!feval_fst_cswap by eauto.
        safe_field_compile_step. safe_compile_step.

        (* the output of this last operation needs to be stored in the pointer
           for the output, so we guide the automation to the right pointer *)
        clear_old_seps.
        repeat lazymatch goal with
               | H : sep _ _ _ |- _ =>
                 seprewrite_in FElem_from_bytes H
               end.
        sepsimpl.
        unhide pOUT.

        safe_field_compile_step.
        repeat safe_compile_step.
        compile_done. cbv [MontLadderResult].
        (* destruct the hypothesis identifying the new pointers as some swapping
           of the original ones *)
        destruct_one_match_hyp_of_type bool.
        all:cleanup; subst.
        all:lift_eexists.
        all:sepsimpl; [ solve [eauto] .. | ].
        all:repeat seprewrite FElem_from_bytes.
        all:repeat (sepsimpl; lift_eexists).
        all:ecancel_assumption. }
    Qed.
 *)

  End MontLadder.
End __.

Local Coercion expr.var : string >-> Syntax.expr.
Local Unset Printing Coercions.
(*
Redirect "Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.montladder_body" Print montladder_body.
*)
