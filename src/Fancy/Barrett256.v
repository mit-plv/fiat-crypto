Require Import Coq.Bool.Bool.
Require Import Coq.derive.Derive.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.
Require Import Crypto.Fancy.Compiler.
Require Import Crypto.Fancy.Prod.
Require Import Crypto.Fancy.Spec.
Require Import Crypto.Language. Import Language.Compilers.
Require Import Crypto.LanguageWf.
Require Import Crypto.PushButtonSynthesis.BarrettReduction.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Module Barrett256.

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

  Strategy -100 [type.app_curried].
  Local Arguments ZRange.is_bounded_by_bool / .
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
    lazy - [ADD ADDC SUB SUBC MUL128LL MUL128LU MUL128UL MUL128UU RSHI SELC SELM SELL ADDM].
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
      let last_wrote := (fun x : CC.code =>
                           match x with
                           | CC.C => RegZero
                           | _ => RegxHigh (* xHigh needs to have written M; others unused *)
                           end) in
      let cc := make_cc last_wrote ctx carry_flag in
      interp Pos.eqb wordmax cc_spec (barrett_red256_fancy RegxLow RegxHigh RegMuLow RegMod RegZero error) cc ctx = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
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
             | _ => apply Compilers.expr.WfLetIn
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

  Import Spec.Registers.

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
                                             else errorR)%positive.
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
  Ltac remember_single_result :=
    match goal with |- context [(spec ?i ?args ?cc) mod ?w] =>
                    let x := fresh "x" in
                    let y := fresh "y" in
                    let Heqx := fresh "Heqx" in
                    remember (spec i args cc) as x eqn:Heqx;
                    remember (x mod w) as y
    end.
  Local Ltac step :=
    match goal with
      |- interp _ _ _ (Instr ?i ?rd1 ?args1 ?cont1) ?cc1 ?ctx1 =
         interp _ _ _ (Instr ?i ?rd2 ?args2 ?cont2) ?cc2 ?ctx2 =>
      rewrite (interp_step _ _ i rd1 args1 cont1);
      rewrite (interp_step _ _ i rd2 args2 cont2)
    end;
    cbn - [interp spec cc_spec];
    repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence;
    results_equiv; [ remember_single_result; repeat simplify_cc | try reflexivity ].

  Local Notation interp := (interp reg_eqb wordmax cc_spec).
  Lemma barrett_red256_alloc_equivalent errorP errorR cc_start_state start_context :
    forall x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 extra_reg,
      NoDup [x; xHigh; RegMuLow; scratchp1; scratchp2; scratchp3; scratchp4; scratchp5; extra_reg; RegMod; RegZero] ->
      0 <= start_context x < 2^machine_wordsize ->
      0 <= start_context xHigh < 2^machine_wordsize ->
      0 <= start_context RegMuLow < 2^machine_wordsize ->
      0 <= start_context RegZero < 2^machine_wordsize ->
      interp
        (barrett_red256_alloc r0 r1 r30 errorP errorR) cc_start_state
                          (fun r => if reg_eqb r r0
                                    then start_context x
                                    else if reg_eqb r r1
                                         then start_context xHigh
                                         else if reg_eqb r r30
                                              then start_context RegMuLow
                                              else start_context r)
    = interp (Prod.MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5) cc_start_state start_context.
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

    repeat step_lhs.


    repeat step_rhs.
    rewrite interp_Mul256x256 with (tmp2 := extra_reg) by
        (try congruence; push_value_unused).
    repeat step_rhs.
    rewrite mulhh_comm by simplify_with_register_properties.
    repeat step_rhs.
    rewrite mulll_comm by simplify_with_register_properties.
    repeat step_rhs.

    rewrite swap_add_chain
      by
        repeat match goal with
               | |- _ <> _ => congruence
               | _ => progress simplify_with_register_properties
               | |- _ = 2 ^ 256 => reflexivity
               | |- flags_unused _ _ =>
                 cbv [flags_unused]; intros;
                   do 2 step; reflexivity
               end.
    repeat step_rhs.

    assert (0 < 2 ^ 256) by ZeroBounds.Z.zero_bounds.
    rewrite add_comm by simplify_with_register_properties.
    step_rhs.
    rewrite addc_comm by simplify_with_register_properties.
    step_rhs.
    rewrite add_comm by simplify_with_register_properties.
    step_rhs.
    rewrite addc_comm by simplify_with_register_properties.
    step_rhs.
    repeat step_rhs.
    rewrite interp_Mul256x256 with (tmp2 := extra_reg) by
        (try congruence; push_value_unused).
    repeat step_rhs.
    rewrite mulhh_comm by simplify_with_register_properties.
    repeat step_rhs.
    rewrite mulll_comm by simplify_with_register_properties.
    repeat step_rhs.

    rewrite swap_add_chain;
        repeat match goal with
               | |- _ <> _ => congruence
               | _ => progress simplify_with_register_properties
               | |- _ = 2 ^ 256 => reflexivity
               | |- flags_unused _ _ =>
                 cbv [flags_unused]; intros;
                   repeat (step; try reflexivity)
               end.

    repeat step_rhs.

    cbv [Spec.interp].
    rewrite !reg_eqb_refl.
    reflexivity.
  Qed.

  Lemma prod_barrett_red256_correct :
    forall (cc_start_state : CC.state) (* starting carry flags *)
           (start_context : register -> Z)   (* starting register values *)
           (x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 extra_reg : register), (* registers to use in computation *)
      NoDup [x; xHigh; RegMuLow; scratchp1; scratchp2; scratchp3; scratchp4; scratchp5; extra_reg; RegMod; RegZero] -> (* registers are unique *)
             0 <= start_context x < 2^machine_wordsize ->
             0 <= start_context xHigh < M ->
             start_context RegMuLow = muLow ->
             start_context RegMod = M ->
             start_context RegZero = 0 ->
             cc_start_state.(CC.cc_m) = cc_spec CC.M (start_context xHigh) ->
             let X := start_context x + 2^machine_wordsize * start_context xHigh in
             interp (Prod.MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5) cc_start_state start_context = X mod M.
  Proof.
    intros. subst X.
    assert (0 <= start_context xHigh < 2^machine_wordsize) by (cbv [M] in *; cbn; omega).
    let r := (eval compute in (2 ^ machine_wordsize)) in
    replace (2^machine_wordsize) with r in * by reflexivity.

    erewrite <-barrett_red256_fancy_correct with (error:=100000%positive) by eauto.
    rewrite <-barrett_red256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (auto; cbv [M muLow] in *; cbn; auto with omega).

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

Import Registers.

(* Notations to make code more readable *)
Local Notation "i rd x y ; cont" := (Instr i rd (x, y) cont) (at level 40, cont at level 200, format "i  rd  x  y ; '//' cont").
Local Notation "i rd x y z ; cont" := (Instr i rd (x, y, z) cont) (at level 40, cont at level 200, format "i  rd  x  y  z ; '//' cont").

(* Barrett reference code: *)
Eval cbv beta iota delta [Prod.MulMod Prod.Mul256x256] in Prod.MulMod.
(*
     = fun x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 : register =>
       let q1Bottom256 := scratchp1 in
       let muSelect := scratchp2 in
       let q2 := scratchp3 in
       let q2High := scratchp4 in
       let q2High2 := scratchp5 in
       let q3 := scratchp1 in
       let r2 := scratchp2 in
       let r2High := scratchp3 in
       let maybeM := scratchp1 in
       SELM muSelect RegMuLow RegZero;
       RSHI 255 q1Bottom256 xHigh x;
       MUL128LL q2 q1Bottom256 RegMuLow;
       MUL128UU q2High q1Bottom256 RegMuLow;
       MUL128UL scratchp5 q1Bottom256 RegMuLow;
       ADD 128 q2 q2 scratchp5;
       ADDC (-128) q2High q2High scratchp5;
       MUL128LU scratchp5 q1Bottom256 RegMuLow;
       ADD 128 q2 q2 scratchp5;
       ADDC (-128) q2High q2High scratchp5;
       RSHI 255 q2High2 RegZero xHigh;
       ADD 0 q2High q2High q1Bottom256;
       ADDC 0 q2High2 q2High2 RegZero;
       ADD 0 q2High q2High muSelect;
       ADDC 0 q2High2 q2High2 RegZero;
       RSHI 1 q3 q2High2 q2High;
       MUL128LL r2 RegMod q3;
       MUL128UU r2High RegMod q3;
       MUL128UL scratchp4 RegMod q3;
       ADD 128 r2 r2 scratchp4;
       ADDC (-128) r2High r2High scratchp4;
       MUL128LU scratchp4 RegMod q3;
       ADD 128 r2 r2 scratchp4;
       ADDC (-128) r2High r2High scratchp4;
       SUB 0 muSelect x r2;
       SUBC 0 xHigh xHigh r2High;
       SELL maybeM RegMod RegZero;
       SUB 0 q3 muSelect maybeM;
       ADDM x q3 RegZero RegMod;
       Ret x
 *)

(* Uncomment to see proof statement and remaining admitted statements. *)
(*
Check Barrett256.prod_barrett_red256_correct.
Print Assumptions Barrett256.prod_barrett_red256_correct.
(* The equivalence with generated code is admitted as barrett_red256_alloc_equivalent. *)
*)
