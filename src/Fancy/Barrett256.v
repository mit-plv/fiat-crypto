(* TODO: prune all these dependencies *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.HexString.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.SubsetoidRing.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Tactics.GetGoal.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.CC.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Arithmetic.
Require Import Crypto.Fancy.PrintingNotations.
Require Import Crypto.Fancy.Prod.
Require Import Crypto.Fancy.Spec.
Require Import Crypto.Fancy.Translation.
Require Crypto.Language.
Require Crypto.UnderLets.
Require Crypto.AbstractInterpretation.
Require Crypto.AbstractInterpretationProofs.
Require Crypto.Rewriter.
Require Crypto.MiscCompilerPasses.
Require Crypto.CStringification.
Require Export Crypto.PushButtonSynthesis.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import Associational Positional.

Import
  Crypto.Language
  Crypto.UnderLets
  Crypto.AbstractInterpretation
  Crypto.AbstractInterpretationProofs
  Crypto.Rewriter
  Crypto.MiscCompilerPasses
  Crypto.CStringification.

Import
  Language.Compilers
  UnderLets.Compilers
  AbstractInterpretation.Compilers
  AbstractInterpretationProofs.Compilers
  Rewriter.Compilers
  MiscCompilerPasses.Compilers
  CStringification.Compilers.

Import Compilers.defaults.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.

Import Spec.Fancy.
Import ProdEquiv.

Module Barrett256.
  Import LanguageWf.Compilers.

  Definition M := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition machine_wordsize := 256.

  Derive barrett_red256
         SuchThat (BarrettReduction.rbarrett_red_correctT M machine_wordsize barrett_red256)
         As barrett_red256_correct.
  Proof. Time solve_rbarrett_red_nocache machine_wordsize. Time Qed.

  Definition muLow := Eval lazy in (2 ^ (2 * machine_wordsize) / M) mod (2^machine_wordsize).

  Lemma barrett_reduce_correct_specialized :
    forall (xLow xHigh : Z),
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      BarrettReduction.barrett_reduce machine_wordsize M muLow 2 2 xLow xHigh = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof.
    intros.
    apply BarrettReduction.barrett_reduce_correct; cbv [machine_wordsize M muLow] in *;
      try omega;
      try match goal with
          | |- context [weight] => intros; cbv [weight]; autorewrite with zsimplify; auto using Z.pow_mul_r with omega
          end; lazy; try split; congruence.
  Qed.

  (*
  (* TODO: delete if unneeded *)
  (* Note: If this is not factored out, then for some reason Qed takes forever in barrett_red256_correct_full. *)
  Lemma barrett_red256_correct_proj2 :
    forall x y,
      ZRange.type.option.is_bounded_by
        (t:=base.type.prod base.type.Z base.type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        (x, y) = true ->
      type.app_curried
          (expr.Interp (@ident.gen_interp ident.cast_outside_of_range)
             barrett_red256) (x, (y, tt)) =
        BarrettReduction.barrett_reduce machine_wordsize M
             ((2 ^ (2 * machine_wordsize) / M)
              mod 2 ^ machine_wordsize) 2 2 x y.
  Proof.
    intros.
    destruct ((proj1 barrett_red256_correct) (x, (y, tt)) (x, (y, tt))).
    { cbn; tauto. }
    { cbn in *. rewrite andb_true_r. auto. }
    { auto. }
  Qed.
  Lemma barrett_red256_correct_proj2' :
    forall x y,
      ZRange.type.option.is_bounded_by
        (t:=base.type.prod base.type.Z base.type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        (x, y) = true ->
      expr.Interp (@ident.interp) barrett_red256 x y =
        BarrettReduction.barrett_reduce machine_wordsize M
             ((2 ^ (2 * machine_wordsize) / M)
              mod 2 ^ machine_wordsize) 2 2 x y.
  Proof.
    intros.
    erewrite <-barrett_red256_correct_proj2 by assumption.
    unfold type.app_curried. exact eq_refl.
  Qed.
*)
  Strategy -100 [type.app_curried].
  Local Arguments is_bounded_by_bool / .
  Lemma barrett_red256_correct_full  :
    forall (xLow xHigh : Z),
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      expr.Interp (@ident.interp) barrett_red256 xLow xHigh = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof.
    intros.
    rewrite <-barrett_reduce_correct_specialized by assumption.
    destruct (proj1 barrett_red256_correct (xLow, (xHigh, tt)) (xLow, (xHigh, tt))) as [H1 H2].
    { repeat split. }
    { cbn -[Z.pow].
      rewrite !andb_true_iff.
      assert (M < 2^machine_wordsize) by (vm_compute; reflexivity).
      repeat apply conj; Z.ltb_to_lt; trivial; omega. }
    { etransitivity; [ eapply H2 | ]. (* need Strategy -100 [type.app_curried]. for this to be fast *)
      generalize BarrettReduction.barrett_reduce; vm_compute; reflexivity. }
  Qed.

  Definition barrett_red256_fancy' (xLow xHigh RegMuLow RegMod RegZero error : positive) :=
    of_Expr 6%positive
            (make_consts [(RegMuLow, muLow); (RegMod, M); (RegZero, 0)])
            barrett_red256
            (xLow, (xHigh, tt))
            error.
  Derive barrett_red256_fancy
         SuchThat (forall xLow xHigh RegMuLow RegMod RegZero,
                      barrett_red256_fancy xLow xHigh RegMuLow RegMod RegZero = barrett_red256_fancy' xLow xHigh RegMuLow RegMod RegZero)
         As barrett_red256_fancy_eq.
  Proof.
    intros.
    lazy - [Fancy.ADD Fancy.ADDC Fancy.SUB Fancy.SUBC
                      Fancy.MUL128LL Fancy.MUL128LU Fancy.MUL128UL Fancy.MUL128UU
                      Fancy.RSHI Fancy.SELC Fancy.SELM Fancy.SELL Fancy.ADDM].
    reflexivity.
  Qed.

  Local Ltac wf_subgoal :=
    repeat match goal with
           | _ => progress cbn [fst snd]
           | |- LanguageWf.Compilers.expr.wf _ _ _ =>
             econstructor; try solve [econstructor]; [ ]
           | |- LanguageWf.Compilers.expr.wf _ _ _ =>
             solve [econstructor]
           | |- In _ _ => auto 50 using in_eq, in_cons
           end.
  Local Ltac valid_expr_subgoal :=
    repeat match goal with
           | _ => progress intros
           | |- context [valid_ident] => econstructor
           | |- context[valid_scalar] => econstructor
           | |- context [valid_carry] => econstructor
           | _ => reflexivity
           | |- _ <> None => cbn; congruence
           | |- of_prefancy_scalar _ _ _ _ = _ => cbn; solve [eauto]
           end.

  (* TODO: don't rely on the C, M, and L flags *)
  Lemma barrett_red256_fancy_correct :
    forall xLow xHigh error,
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      let RegZero := 1%positive in
      let RegMod := 2%positive in
      let RegMuLow := 3%positive in
      let RegxHigh := 4%positive in
      let RegxLow := 5%positive in
      let consts_list := [(RegMuLow, muLow); (RegMod, M); (RegZero, 0)] in
      let arg_list := [(RegxHigh, xHigh); (RegxLow, xLow)] in
      let ctx := make_ctx (consts_list ++ arg_list) in
      let carry_flag := false in (* TODO: don't rely on this value, given it's unused *)
      let last_wrote := (fun x : Fancy.CC.code =>
                           match x with
                           | Fancy.CC.C => RegZero
                           | _ => RegxHigh (* xHigh needs to have written M; others unused *)
                           end) in
      let cc := make_cc last_wrote ctx carry_flag in
      interp Pos.eqb wordmax Fancy.cc_spec (barrett_red256_fancy RegxLow RegxHigh RegMuLow RegMod RegZero error) cc ctx = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof.
    intros.
    rewrite barrett_red256_fancy_eq.
    cbv [barrett_red256_fancy'].
    rewrite <-barrett_red256_correct_full by auto.
    eapply of_Expr_correct with (x2 := (xLow, (xHigh, tt))).
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      intuition; Prod.inversion_prod; subst; cbv. break_innermost_match; congruence. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      intuition; Prod.inversion_prod; subst; cbv; congruence. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow. tauto. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      intuition; Prod.inversion_prod; subst; cbv; congruence. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      match goal with |- context [_ mod ?m] => change m with (2 ^ machine_wordsize) end.
      assert (M < 2 ^ machine_wordsize) by (cbv; congruence).
      assert (0 <= muLow < 2 ^ machine_wordsize) by (split; cbv; congruence).
      intuition; Prod.inversion_prod; subst; apply Z.mod_small; omega. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      match goal with |- context [_ mod ?m] => change m with (2 ^ machine_wordsize) end.
      assert (M < 2 ^ machine_wordsize) by (cbv; congruence).
      assert (0 <= muLow < 2 ^ machine_wordsize) by (split; cbv; congruence).
      intuition; Prod.inversion_prod; subst; apply Z.mod_small; omega. }
    { cbn.
      repeat match goal with
             | _ => apply expr.WfLetIn
             | _ => progress wf_subgoal 
             | _ => econstructor
             end. }
    { cbn. cbv [muLow M].
      repeat (econstructor; [ solve [valid_expr_subgoal] | intros ]).
      econstructor. valid_expr_subgoal. }
    { cbn - [barrett_red256]. cbv [id].
      f_equal.
      (* TODO(jgross): switch out casts *)
      (* might need to use CheckCasts.interp_eqv_without_casts? *)
      replace (@ident.gen_interp cast_oor) with (@ident.interp) by admit.
      reflexivity. }
  Admitted.

  Import Fancy.Registers.

  Definition barrett_red256_alloc' xLow xHigh RegMuLow :=
    fun errorP errorR =>
      allocate register
               positive Pos.eqb
               errorR
               (barrett_red256_fancy 1000%positive 1001%positive 1002%positive 1003%positive 1004%positive errorP)
               [r2;r3;r4;r5;r6;r7;r8;r9;r10;r5;r11;r6;r12;r13;r14;r15;r16;r17;r18;r19;r20;r21;r22;r23;r24;r25;r26;r27;r28;r29]
               (fun n => if n =? 1000 then xLow
                         else if n =? 1001 then xHigh
                              else if n =? 1002 then RegMuLow
                                   else if n =? 1003 then RegMod
                                        else if n =? 1004 then RegZero
                                             else errorR).
  Derive barrett_red256_alloc
         SuchThat (barrett_red256_alloc = barrett_red256_alloc')
         As barrett_red256_alloc_eq.
  Proof.
    intros.
    cbv [barrett_red256_alloc' barrett_red256_fancy].
    cbn. subst barrett_red256_alloc.
    reflexivity.
  Qed.

  Local Ltac solve_bounds :=
    match goal with
    | H : ?a = ?b mod ?c |- 0 <= ?a < ?c => rewrite H; apply Z.mod_pos_bound; omega
    | _ => assumption
    end.

  Lemma barrett_red256_alloc_equivalent errorP errorR cc_start_state start_context :
    forall x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 extra_reg,
      NoDup [x; xHigh; RegMuLow; scratchp1; scratchp2; scratchp3; scratchp4; scratchp5; extra_reg; RegMod; RegZero] ->
      0 <= start_context x < 2^machine_wordsize ->
      0 <= start_context xHigh < 2^machine_wordsize ->
      0 <= start_context RegMuLow < 2^machine_wordsize ->
      ProdEquiv.interp256 (barrett_red256_alloc r0 r1 r30 errorP errorR) cc_start_state
                          (fun r => if reg_eqb r r0
                                    then start_context x
                                    else if reg_eqb r r1
                                         then start_context xHigh
                                         else if reg_eqb r r30
                                              then start_context RegMuLow
                                              else start_context r)
    = ProdEquiv.interp256 (Prod.MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5) cc_start_state start_context.
  Proof.
    intros.
    let r := eval compute in (2^machine_wordsize) in
        replace (2^machine_wordsize) with r in * by reflexivity.
    cbv [Prod.MulMod barrett_red256_alloc].

    (* Extract proofs that no registers are equal to each other *)
    repeat match goal with
           | H : NoDup _ |- _ => inversion H; subst; clear H
           | H : ~ In _ _ |- _ => cbv [In] in H
           | H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H
           | H : ~ False |- _ => clear H
           end.

    step_both_sides.

    (* TODO: To prove equivalence between these two, we need to either relocate the RSHI instructions so they're in the same places or use instruction commutativity to push them down. *)

  Admitted.

  Local Ltac results_equiv :=
    match goal with
      |- ?lhs = ?rhs =>
      match lhs with
        context [spec ?li ?largs ?lcc] =>
        match rhs with
          context [spec ?ri ?rargs ?rcc] =>
          replace (spec li largs lcc) with (spec ri rargs rcc)
        end
      end
    end.
  Local Ltac simplify_cc :=
    match goal with
      |- context [CC.update ?to_write ?result ?cc_spec ?old_state] =>
      let e := eval cbv -[spec cc_spec CC.cc_l CC.cc_m CC.cc_z CC.cc_c] in
      (CC.update to_write result cc_spec old_state) in
          change (CC.update to_write result cc_spec old_state) with e
    end.

  Local Ltac step :=
    match goal with
      |- interp _ _ _ (Instr ?i ?rd1 ?args1 ?cont1) ?cc1 ?ctx1 =
         interp _ _ _ (Instr ?i ?rd2 ?args2 ?cont2) ?cc2 ?ctx2 =>
      rewrite (interp_step _ _ i rd1 args1 cont1);
      rewrite (interp_step _ _ i rd2 args2 cont2)
    end;
    cbn - [Fancy.interp Fancy.spec cc_spec];
    repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence;
    results_equiv; [ remember_single_result; repeat simplify_cc | try reflexivity ].

  Lemma prod_barrett_red256_correct :
    forall (cc_start_state : Fancy.CC.state) (* starting carry flags *)
           (start_context : register -> Z)   (* starting register values *)
           (x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 extra_reg : register), (* registers to use in computation *)
      NoDup [x; xHigh; RegMuLow; scratchp1; scratchp2; scratchp3; scratchp4; scratchp5; extra_reg; RegMod; RegZero] -> (* registers are unique *)
             0 <= start_context x < 2^machine_wordsize ->
             0 <= start_context xHigh < M ->
             start_context RegMuLow = muLow ->
             start_context RegMod = M ->
             start_context RegZero = 0 ->
             cc_start_state.(Fancy.CC.cc_m) = cc_spec CC.M (start_context xHigh) ->
             let X := start_context x + 2^machine_wordsize * start_context xHigh in
             ProdEquiv.interp256 (Prod.MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5) cc_start_state start_context = X mod M.
  Proof.
    intros. subst X.
    assert (0 <= start_context xHigh < 2^machine_wordsize) by (cbv [M] in *; cbn; omega).
    let r := (eval compute in (2 ^ machine_wordsize)) in
    replace (2^machine_wordsize) with r in * by reflexivity.

    erewrite <-barrett_red256_fancy_correct with (error:=100000%positive) by eauto.
    rewrite <-barrett_red256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (auto; cbv [M muLow] in *; cbn; auto with omega).

    cbv [interp256 Translation.wordmax].
    match goal with
      |- context [make_cc ?last_wrote ?ctx ?carry] =>
      let e := fresh in
      let He := fresh in
      remember (make_cc last_wrote ctx carry) as e eqn:He;
        cbv [make_ctx app make_cc] in He;
        cbn [Pos.eqb] in He; autorewrite with zsimplify in He;
          subst e
    end.

    repeat match goal with
             H : context [start_context] |- _ =>
             rewrite <-H end.
    
    cbv [barrett_red256_alloc barrett_red256_fancy].
    repeat step.
    reflexivity.
  Qed.
End Barrett256.
