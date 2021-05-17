Require Import Coq.Bool.Bool.
Require Import Coq.derive.Derive.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.COperationSpecifications. Import COperationSpecifications.BarrettReduction.
Require Import Rewriter.Language.Language. Import Language.Compilers.
Require Import Crypto.Language.API. Import Language.API.Compilers.
Require Import Rewriter.Language.Wf. Import Language.Wf.Compilers.
Require Import Crypto.PushButtonSynthesis.BarrettReduction.
Require Import Crypto.Fancy.Compiler.
Require Import Crypto.Fancy.Prod.
Require Import Crypto.Fancy.Spec.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Module Barrett256.

  Definition M := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition machine_wordsize := 256.

  Derive barrett_red256
         SuchThat (barrett_red M machine_wordsize = ErrorT.Success barrett_red256)
         As barrett_red256_eq.
  Proof. lazy; reflexivity. Qed.

  Lemma Wf_barrett_red256 : API.Wf barrett_red256.
  Proof using Type. eapply Wf_barrett_red, barrett_red256_eq. Qed.

  Lemma barrett_red256_correct :
    COperationSpecifications.BarrettReduction.barrett_red_correct machine_wordsize M (API.Interp barrett_red256).
  Proof.
    apply barrett_red_correct with (machine_wordsize:=machine_wordsize) (requests:=[]).
    { lazy. reflexivity. }
    { apply barrett_red256_eq. }
  Qed.

  Definition muLow := Eval lazy in (2 ^ (2 * machine_wordsize) / M) mod (2^machine_wordsize).

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
    repeat first [ progress cbn [List.In type.and_for_each_lhs_of_arrow fst snd List.app List.map]
                 | apply expr.wf_smart_App_curried
                 | progress intros
                 | exfalso; assumption
                 | apply conj
                 | exact I
                 | solve [ eauto 50 using or_introl, or_intror, eq_refl with nocore ] ].
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
      let carry_flag := false in
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
    rewrite <-barrett_red256_correct by auto.
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
      intuition; Prod.inversion_prod; subst; apply Z.mod_small; lia. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      match goal with |- context [_ mod ?m] => change m with (2 ^ machine_wordsize) end.
      assert (M < 2 ^ machine_wordsize) by (cbv; congruence).
      assert (0 <= muLow < 2 ^ machine_wordsize) by (split; cbv; congruence).
      intuition; Prod.inversion_prod; subst; apply Z.mod_small; lia. }
    { repeat first [ eapply expr.wf_Proper_list, Wf_barrett_red256
                   | progress cbv [make_pairs consts_list arg_list]
                   | wf_subgoal ]. }
    { cbn. cbv [muLow M].
      repeat (match goal with
             | _ => eapply valid_LetInZZ
             | _ => eapply valid_LetInZ
              end; [ solve [valid_expr_subgoal] | intros ]).
      econstructor. valid_expr_subgoal. }
    { reflexivity. }
  Qed.

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

    Time repeat match goal with
                | _ => progress prove_programs_equivalent
                | _ => rewrite interp_Mul256x256 with (tmp2 := extra_reg) by
                      (match goal with
                       | |- _ <> _ => assumption || congruence
                       | _ => push_value_unused
                       end)
                | _ =>
                  rewrite swap_add_chain by
                      repeat match goal with
                             | |- _ <> _ => assumption || congruence
                             | _ => progress simplify_with_register_properties
                             | |- _ = 2 ^ 256 => reflexivity
                             | |- flags_unused _ _ =>
                               cbv [flags_unused]; intros; prove_programs_equivalent (* TODO: there is probably a faster way to do this one *)
                             end
                end.

    cbv [Spec.interp].
    simplify_with_register_properties.
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
    assert (0 <= start_context xHigh < 2^machine_wordsize) by (cbv [M] in *; cbn; lia).
    let r := (eval compute in (2 ^ machine_wordsize)) in
    replace (2^machine_wordsize) with r in * by reflexivity.

    erewrite <-barrett_red256_fancy_correct with (error:=100000%positive) by eauto.
    rewrite <-barrett_red256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (auto; cbv [M muLow] in *; cbn; auto with lia).

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

Section with_notations.
  Import Crypto.Language.IdentifiersBasicGENERATED.Compilers.
  Import Crypto.Util.ZRange.
  Local Open Scope zrange_scope.
  Local Open Scope Z_scope.
  Local Open Scope expr_scope.
  Local Notation uint256 := r[0 ~> 115792089237316195423570985008687907853269984665640564039457584007913129639935]%zrange.
  Local Set Printing Width 500.
  Redirect "Crypto.Fancy.Barrett256.barrett_red256" Print Barrett256.barrett_red256.
End with_notations.

Import Registers.

(* Notations to make code more readable *)
Local Notation "i rd x y ; cont" := (Instr i rd (x, y) cont) (at level 40, cont at level 200, format "i  rd  x  y ; '//' cont").
Local Notation "i rd x y z ; cont" := (Instr i rd (x, y, z) cont) (at level 40, cont at level 200, format "i  rd  x  y  z ; '//' cont").

(* Barrett reference code: *)
Local Set Printing Width 150.
Redirect "Crypto.Fancy.Barrett256.Prod.MulMod" Eval cbv beta iota delta [Prod.MulMod Prod.Mul256x256] in Prod.MulMod.
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

(* Remove Redirect to see proof statement and remaining admitted statements. *)
Redirect "Crypto.Fancy.Barrett256.prod_barrett_red256_correct" Check Barrett256.prod_barrett_red256_correct.
Redirect "Crypto.Fancy.Barrett256.prod_barrett_red256_correct.Assumptions" Print Assumptions Barrett256.prod_barrett_red256_correct.
