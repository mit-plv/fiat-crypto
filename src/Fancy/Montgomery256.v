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
(* Notation "x" := (expr.Var x) (only printing, at level 9) : expr_scope. *)

Import UnsaturatedSolinas.

Import Spec.Fancy.
Import LanguageWf.Compilers.

Module Montgomery256.

  Definition N := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition N':= (115792089210356248768974548684794254293921932838497980611635986753331132366849).
  Definition R := Eval lazy in (2^256).
  Definition R' := 115792089183396302114378112356516095823261736990586219612555396166510339686400.
  Definition machine_wordsize := 256.

  Derive montred256
         SuchThat (MontgomeryReduction.rmontred_correctT N R N' machine_wordsize montred256)
         As montred256_correct.
  Proof. Time solve_rmontred_nocache machine_wordsize. Time Qed.

  Lemma montred'_correct_specialized R' (R'_correct : Z.equiv_modulo N (R * R') 1) :
    forall (lo hi : Z),
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2 lo hi = ((lo + R * hi) * R') mod N.
  Proof.
    intros.
    apply MontgomeryReduction.montred'_correct with (T:=lo + R * hi) (R':=R');
      try match goal with
            | |- context[R'] => assumption
            | |- context [lo] =>
              try assumption; progress autorewrite with zsimplify cancel_pair; reflexivity
          end; lazy; try split; congruence.
  Qed.

  Strategy -100 [type.app_curried].
  Local Arguments is_bounded_by_bool / .
  Lemma montred256_correct_full  R' (R'_correct : Z.equiv_modulo N (R * R') 1) :
    forall (lo hi : Z),
      0 <= lo < R ->
      0 <= hi < R ->
      0 <= lo + R * hi < R * N ->
      expr.Interp (@ident.interp) montred256 lo hi = ((lo + R * hi) * R') mod N.
  Proof.
    intros.
    rewrite <-montred'_correct_specialized by assumption.
    destruct (proj1 montred256_correct (lo, (hi, tt)) (lo, (hi, tt))) as [H2 H3].
    { repeat split. }
    { cbn -[Z.pow].
      rewrite !andb_true_iff.
      repeat apply conj; Z.ltb_to_lt; trivial; cbv [R N machine_wordsize] in *; lia. }
    { etransitivity; [ eapply H3 | ]. (* need Strategy -100 [type.app_curried]. for this to be fast *)
      generalize MontgomeryReduction.montred'; vm_compute; reflexivity. }
  Qed.

  Definition montred256_fancy' (RegMod RegPInv RegZero lo hi error : positive) :=
    of_Expr 6%positive
            (make_consts [(RegMod, N); (RegZero, 0); (RegPInv, N')])
            montred256
            (lo, (hi, tt))
            error.
  Derive montred256_fancy
         SuchThat (forall RegMod RegPInv RegZero,
                      montred256_fancy RegMod RegPInv RegZero = montred256_fancy' RegMod RegPInv RegZero)
         As montred256_fancy_eq.
  Proof.
    intros.
    cbv [montred256_fancy'].
    lazy - [Fancy.ADD Fancy.ADDC Fancy.SUB
                      Fancy.MUL128LL Fancy.MUL128LU Fancy.MUL128UL Fancy.MUL128UU
                      Fancy.RSHI Fancy.SELC Fancy.SELM Fancy.SELL Fancy.ADDM].
    reflexivity.
  Qed.

  (* TODO: these tactics are duplicated; move them elsewhere (probably translation *)
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

  Lemma montred256_fancy_correct :
    forall lo hi error,
      0 <= lo < R ->
      0 <= hi < R ->
      0 <= lo + R * hi < R * N ->
      let RegZero := 1%positive in
      let RegMod := 2%positive in
      let RegPInv := 3%positive in
      let RegHi := 4%positive in
      let RegLo := 5%positive in
      let consts_list := [(RegMod, N); (RegZero, 0); (RegPInv, N')] in
      let arg_list := [(RegHi, hi); (RegLo, lo)] in
      let ctx := make_ctx (consts_list ++ arg_list) in
      let carry_flag := false in
      let last_wrote := (fun x : Fancy.CC.code => RegZero) in
      let cc := make_cc last_wrote ctx carry_flag in
      interp Pos.eqb wordmax Fancy.cc_spec (montred256_fancy RegMod RegPInv RegZero RegLo RegHi error) cc ctx = ((lo + R * hi) * R') mod N.
  Proof.
    intros.
    rewrite montred256_fancy_eq.
    cbv [montred256_fancy'].
    rewrite <-montred256_correct_full by (auto; reflexivity).
    eapply of_Expr_correct with (x2 := (lo, (hi, tt))).
    { cbn; intros; subst RegZero RegMod RegPInv RegHi RegLo.
      intuition; Prod.inversion_prod; subst; cbv. break_innermost_match; congruence. }
    { cbn; intros; subst RegZero RegMod RegPInv RegHi RegLo.
      intuition; Prod.inversion_prod; subst; cbv; congruence. }
    { cbn; intros; subst RegZero RegMod RegPInv RegHi RegLo. tauto. }
    { cbn; intros; subst RegZero RegMod RegPInv RegHi RegLo.
      intuition; Prod.inversion_prod; subst; cbv; congruence. }
    { cbn; intros; subst RegZero RegMod RegPInv RegHi RegLo.
      match goal with |- context [_ mod ?m] => change m with (2 ^ machine_wordsize) end.
      intuition; Prod.inversion_prod; subst; apply Z.mod_small; cbv; try split; congruence. }
    { cbn; intros; subst RegZero RegMod RegPInv RegHi RegLo.
      match goal with |- context [_ mod ?m] => change m with (2 ^ machine_wordsize) end.
      assert (R <= 2 ^ machine_wordsize) by (cbv; congruence).
      intuition; Prod.inversion_prod; subst; apply Z.mod_small; omega. }
    { cbn.
      repeat match goal with
             | _ => apply expr.WfLetIn
             | _ => progress wf_subgoal 
             | _ => econstructor
             end. }
    { cbn. cbv [N' N].
      repeat (econstructor; [ solve [valid_expr_subgoal] | intros ]).
      econstructor. valid_expr_subgoal. }
    { cbn - [montred256]. cbv [id].
      f_equal.
      (* TODO(jgross): switch out casts *)
      (* might need to use CheckCasts.interp_eqv_without_casts? *)
      replace (@ident.gen_interp cast_oor) with (@ident.interp) by admit.
      reflexivity. }
  Admitted.

  Import Fancy.Registers.

  Definition montred256_alloc' lo hi RegPInv :=
    fun errorP errorR =>
      allocate register
               positive Pos.eqb
               errorR
               (montred256_fancy 1000%positive 1001%positive 1002%positive 1003%positive 1004%positive errorP)
               [r2;r3;r4;r5;r6;r7;r8;r9;r10;r11;r12;r13;r14;r15;r16;r17;r18;r19;r20]
               (fun n => if n =? 1000 then RegMod
                         else if n =? 1001 then RegPInv
                              else if n =? 1002 then RegZero
                                   else if n =? 1003 then lo
                                        else if n =? 1004 then hi
                                                 else errorR).
  Derive montred256_alloc
         SuchThat (montred256_alloc = montred256_alloc')
         As montred256_alloc_eq.
  Proof.
    intros.
    cbv [montred256_alloc' montred256_fancy].
    cbn. subst montred256_alloc.
    reflexivity.
  Qed.

  (* TODO: also factor out these tactics *)
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
    match goal with |- context [(Fancy.spec ?i ?args ?cc) mod ?w] =>
                    let x := fresh "x" in
                    let y := fresh "y" in
                    let Heqx := fresh "Heqx" in
                    remember (Fancy.spec i args cc) as x eqn:Heqx;
                    remember (x mod w) as y
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

  Local Notation interp := (interp reg_eqb wordmax cc_spec).
  Lemma montred256_alloc_equivalent errorP errorR cc_start_state start_context :
    forall lo hi y t1 t2 scratch RegPInv extra_reg,
      NoDup [lo; hi; y; t1; t2; scratch; RegPInv; extra_reg; RegMod; RegZero] ->
      0 <= start_context lo < R ->
      0 <= start_context hi < R ->
      0 <= start_context RegPInv < R ->
      interp
        (montred256_alloc r0 r1 r30 errorP errorR) cc_start_state
                          (fun r => if reg_eqb r r0
                                    then start_context lo
                                    else if reg_eqb r r1
                                         then start_context hi
                                         else if reg_eqb r r30
                                              then start_context RegPInv
                                              else start_context r)
    = interp (Prod.MontRed256 lo hi y t1 t2 scratch RegPInv) cc_start_state start_context.
  Proof.
    intros. cbv [R] in *.
    cbv [Prod.MontRed256 montred256_alloc].

    (* Extract proofs that no registers are equal to each other *)
    repeat match goal with
           | H : NoDup _ |- _ => inversion H; subst; clear H
           | H : ~ In _ _ |- _ => cbv [In] in H
           | H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H
           | H : ~ False |- _ => clear H
           end.

    rewrite interp_Mul256 with (tmp2:=extra_reg) by (congruence || push_value_unused).

    rewrite mullh_mulhl.
    step.
    rewrite mullh_mulhl.
    step. step. step. step.


    rewrite interp_Mul256x256 with (tmp2:=extra_reg) by
        (match goal with
         | |- _ <> _ => congruence
         | _ => push_value_unused
         end).

    rewrite mulll_comm.
    step. step. step.
    rewrite mulhh_comm.
    step. step. step. step. step.
    rewrite add_comm by (cbn; solve_bounds).
    step.
    rewrite addc_comm by (cbn; solve_bounds).
    step. step. step. step.

    cbn; repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence.
    reflexivity.
  Qed.


  Lemma prod_montred256_correct :
    forall (cc_start_state : Fancy.CC.state) (* starting carry flags can be anything *)
           (start_context : register -> Z)   (* starting register values *)
           (lo hi y t1 t2 scratch RegPInv extra_reg : register), (* registers to use in computation *)
      NoDup [lo; hi; y; t1; t2; scratch; RegPInv; extra_reg; RegMod; RegZero] -> (* registers must be distinct *)
      start_context RegPInv = N' ->  (* RegPInv needs to hold the inverse of the modulus *)
      start_context RegMod = N ->    (* RegMod needs to hold the modulus *)
      start_context RegZero = 0 ->   (* RegZero needs to hold zero *)
      (0 <= start_context lo < R) -> (* low half of the input is in bounds (R=2^256) *)
      (0 <= start_context hi < R) -> (* high half of the input is in bounds (R=2^256) *)
      let x := (start_context lo) + R * (start_context hi) in (* x is the input (split into two registers) *)
      (0 <= x < R * N) -> (* input precondition *)
      (interp (Prod.MontRed256 lo hi y t1 t2 scratch RegPInv) cc_start_state start_context = (x * R') mod N).
  Proof.
    intros. subst x.
    erewrite <-montred256_fancy_correct with (error:=100000%positive) by eauto.
    rewrite <-montred256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (cbv [R N N'] in *; auto with omega).

    (* TODO: factor out this tactic *)
    match goal with
      |- context [make_cc ?last_wrote ?ctx ?carry] =>
      let e := fresh in
      let He := fresh in
      remember (make_cc last_wrote ctx carry) as e eqn:He;
        cbv [make_ctx app make_cc] in He;
        cbn [Pos.eqb] in He; autorewrite with zsimplify in He;
          subst e
    end.
    cbv [montred256_alloc montred256_fancy].
    repeat match goal with
             H : context [start_context] |- _ =>
             rewrite <-H end.
    repeat step.
    reflexivity.
  Qed.
End Montgomery256.
