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
Require Import Crypto.Fancy.Spec.
Require Crypto.Language.
Require Crypto.UnderLets.
Require Crypto.AbstractInterpretation.
Require Crypto.AbstractInterpretationProofs.
Require Crypto.Rewriter.
Require Crypto.MiscCompilerPasses.
Require Crypto.CStringification.
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
Import Spec.Fancy. Import Registers.

(* TODO : change these modules to sections *)
Module Prod.
  Definition Mul256 (out src1 src2 tmp : register) (cont : Fancy.expr) : Fancy.expr :=
    Instr MUL128LL out (src1, src2)
          (Instr MUL128UL tmp (src1, src2)
                 (Instr (ADD 128) out (out, tmp)
                        (Instr MUL128LU tmp (src1, src2)
                               (Instr (ADD 128) out (out, tmp) cont)))).
  Definition Mul256x256 (out outHigh src1 src2 tmp : register) (cont : Fancy.expr) : Fancy.expr :=
    Instr MUL128LL out (src1, src2)
          (Instr MUL128UU outHigh (src1, src2)
                 (Instr MUL128UL tmp (src1, src2)
                        (Instr (ADD 128) out (out, tmp)
                               (Instr (ADDC (-128)) outHigh (outHigh, tmp)
                                      (Instr MUL128LU tmp (src1, src2)
                                             (Instr (ADD 128) out (out, tmp)
                                                    (Instr (ADDC (-128)) outHigh (outHigh, tmp) cont))))))).

  Definition MontRed256 lo hi y t1 t2 scratch RegPInv : @Fancy.expr register :=
    Mul256 y lo RegPInv t1
           (Mul256x256 t1 t2 y RegMod scratch
                       (Instr (ADD 0) lo (lo, t1)
                              (Instr (ADDC 0) hi (hi, t2)
                                     (Instr SELC y (RegMod, RegZero)
                                            (Instr (SUB 0) lo (hi, y)
                                                   (Instr ADDM lo (lo, RegZero, RegMod)
                                                          (Ret lo))))))).

  (* Barrett reduction -- this is only the "reduce" part, excluding the initial multiplication. *)
  Definition MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 : @Fancy.expr register :=
    let q1Bottom256 := scratchp1 in
    let muSelect := scratchp2 in
    let q2 := scratchp3 in
    let q2High := scratchp4 in
    let q2High2 := scratchp5 in
    let q3 := scratchp1 in
    let r2 := scratchp2 in
    let r2High := scratchp3 in
    let maybeM := scratchp1 in
    Instr SELM muSelect (RegMuLow, RegZero)
          (Instr (RSHI 255) q1Bottom256 (xHigh, x)
                 (Mul256x256 q2 q2High q1Bottom256 RegMuLow scratchp5
                             (Instr (RSHI 255) q2High2 (RegZero, xHigh)
                                    (Instr (ADD 0) q2High (q2High, q1Bottom256)
                                           (Instr (ADDC 0) q2High2 (q2High2, RegZero)
                                                  (Instr (ADD 0) q2High (q2High, muSelect)
                                                         (Instr (ADDC 0) q2High2 (q2High2, RegZero)
                                                                (Instr (RSHI 1) q3 (q2High2, q2High)
                                                                       (Mul256x256 r2 r2High RegMod q3 scratchp4
                                                                                   (Instr (SUB 0) muSelect (x, r2)
                                                                                          (Instr (SUBC 0) xHigh (xHigh, r2High)
                                                                                                 (Instr SELL maybeM (RegMod, RegZero)
                                                                                                        (Instr (SUB 0) q3 (muSelect, maybeM)
                                                                                                               (Instr ADDM x (q3, RegZero, RegMod)
                                                                                                                      (Ret x))))))))))))))).
End Prod.

(* TODO : move to Fancy *)
Section interp_proofs.
  Context {name} (name_eqb : name -> name -> bool) (wordmax : Z).
  Let interp := interp name_eqb wordmax cc_spec.
  Lemma interp_step i rd args cont cc ctx :
    interp (Instr i rd args cont) cc ctx =
    let result := spec i (Tuple.map ctx args) cc in
    let new_cc := CC.update (writes_conditions i) result cc_spec cc in
    let new_ctx := fun n => if name_eqb n rd then result mod wordmax else ctx n in interp cont new_cc new_ctx.
  Proof. reflexivity. Qed.

  Lemma interp_state_equiv e :
    forall cc ctx cc' ctx',
      cc = cc' -> (forall r, ctx r = ctx' r) ->
      interp e cc ctx = interp e cc' ctx'.
  Proof.
    induction e; intros; subst; cbn; [solve[auto]|].
    apply IHe; rewrite Tuple.map_ext with (g:=ctx') by auto;
      [reflexivity|].
    intros; break_match; auto.
  Qed.
End interp_proofs.

Module ProdEquiv.

  Definition wordmax := 2^256.
  Definition interp256 := Fancy.interp reg_eqb (2^256) cc_spec.
  Lemma cc_overwrite_full x1 x2 l1 cc :
    CC.update [CC.C; CC.M; CC.L; CC.Z] x2 cc_spec (CC.update l1 x1 cc_spec cc) = CC.update [CC.C; CC.M; CC.L; CC.Z] x2 cc_spec cc.
  Proof.
    cbv [CC.update]. cbn [CC.cc_c CC.cc_m CC.cc_l CC.cc_z].
    break_match; try match goal with H : ~ In _ _ |- _ => cbv [In] in H; tauto end.
    reflexivity.
  Qed.

  Definition value_unused r e : Prop :=
    forall x cc ctx, interp256 e cc ctx = interp256 e cc (fun r' => if reg_eqb r' r then x else ctx r').

  Lemma value_unused_skip r i rd args cont (Hcont: value_unused r cont) :
    r <> rd ->
    (~ In r (Tuple.to_list _ args)) ->
    value_unused r (Instr i rd args cont).
  Proof.
    cbv [value_unused interp256] in *; intros.
    rewrite !interp_step; cbv zeta.
    rewrite Hcont with (x:=x).
    match goal with |- ?lhs = ?rhs =>
                    match lhs with context [Tuple.map ?f ?t] =>
                                   match rhs with context [Tuple.map ?g ?t] =>
                                                  rewrite (Tuple.map_ext_In f g) by (intros; cbv [reg_eqb]; break_match; congruence)
                                   end end end.
    apply interp_state_equiv; [ congruence | ].
    { intros; cbv [reg_eqb] in *; break_match; congruence. }
  Qed.

  Lemma value_unused_overwrite r i args cont :
    (~ In r (Tuple.to_list _ args)) ->
    value_unused r (Instr i r args cont).
  Proof.
    cbv [value_unused interp256]; intros; rewrite !interp_step; cbv zeta.
    match goal with |- ?lhs = ?rhs =>
                    match lhs with context [Tuple.map ?f ?t] =>
                                   match rhs with context [Tuple.map ?g ?t] =>
                                                  rewrite (Tuple.map_ext_In f g) by (intros; cbv [reg_eqb]; break_match; congruence)
                                   end end end.
    apply interp_state_equiv; [ congruence | ].
    { intros; cbv [reg_eqb] in *; break_match; congruence. }
  Qed.

  Lemma value_unused_ret r r' :
    r <> r' ->
    value_unused r (Ret r').
  Proof.
    cbv - [reg_dec]; intros.
    break_match; congruence.
  Qed.

  Ltac remember_results :=
    repeat match goal with |- context [(spec ?i ?args ?flags) mod ?w] =>
                    let x := fresh "x" in
                    let y := fresh "y" in
                    let Heqx := fresh "Heqx" in
                    remember (spec i args flags) as x eqn:Heqx;
                    remember (x mod w) as y
           end.

  Ltac do_interp_step :=
    rewrite interp_step; cbn - [interp spec];
    repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence;
    remember_results.

  Lemma interp_Mul256 out src1 src2 tmp tmp2 cont cc ctx:
    out <> src1 ->
    out <> src2 ->
    out <> tmp ->
    out <> tmp2 ->
    src1 <> src2 ->
    src1 <> tmp ->
    src1 <> tmp2 ->
    src2 <> tmp ->
    src2 <> tmp2 ->
    tmp <> tmp2 ->
    value_unused tmp cont ->
    value_unused tmp2 cont ->
    interp256 (Prod.Mul256 out src1 src2 tmp cont) cc ctx =
    interp256 (
        Instr MUL128LU tmp (src1, src2)
              (Instr MUL128UL tmp2 (src1, src2)
                     (Instr MUL128LL out (src1, src2)
                                 (Instr (ADD 128) out (out, tmp2)
                                        (Instr (ADD 128) out (out, tmp) cont))))) cc ctx.
  Proof.
    intros; cbv [Prod.Mul256 interp256].
    repeat (do_interp_step; cbn [spec MUL128LL MUL128UL MUL128LU ADD] in * ).

    match goal with H : value_unused tmp _ |- _ => erewrite H end.
    match goal with H : value_unused tmp2 _ |- _ => erewrite H end.
    apply interp_state_equiv.
    { rewrite !cc_overwrite_full.
      f_equal. subst. lia. }
    { intros; cbv [reg_eqb].
      repeat (break_match_step ltac:(fun _ => idtac); try congruence); reflexivity. }
  Qed.

  Lemma interp_Mul256x256 out outHigh src1 src2 tmp tmp2 cont cc ctx:
    out <> src1 ->
    out <> outHigh ->
    out <> src2 ->
    out <> tmp ->
    out <> tmp2 ->
    outHigh <> src1 ->
    outHigh <> src2 ->
    outHigh <> tmp ->
    outHigh <> tmp2 ->
    src1 <> src2 ->
    src1 <> tmp ->
    src1 <> tmp2 ->
    src2 <> tmp ->
    src2 <> tmp2 ->
    tmp <> tmp2 ->
    value_unused tmp cont ->
    value_unused tmp2 cont ->
    interp256 (Prod.Mul256x256 out outHigh src1 src2 tmp cont) cc ctx =
    interp256 (
        Instr MUL128LL out (src1, src2)
              (Instr MUL128LU tmp (src1, src2)
                     (Instr MUL128UL tmp2 (src1, src2)
                            (Instr MUL128UU outHigh (src1, src2)
                                   (Instr (ADD 128) out (out, tmp2)
                                          (Instr (ADDC (-128)) outHigh (outHigh, tmp2)
                                                 (Instr (ADD 128) out (out, tmp)
                                                        (Instr (ADDC (-128)) outHigh (outHigh, tmp) cont)))))))) cc ctx.
  Proof.
    intros; cbv [Prod.Mul256x256 interp256].
    repeat (do_interp_step; cbn [spec MUL128LL MUL128UL MUL128LU MUL128UU ADD ADDC] in * ).

    match goal with H : value_unused tmp _ |- _ => erewrite H end.
    match goal with H : value_unused tmp2 _ |- _ => erewrite H end.
    apply interp_state_equiv.
    { rewrite !cc_overwrite_full.
      f_equal.
      subst. cbn - [Z.add Z.modulo Z.testbit Z.mul Z.shiftl Fancy.lower128 Fancy.upper128].
      lia. }
    { intros; cbv [reg_eqb].
      repeat (break_match_step ltac:(fun _ => idtac); try congruence); try reflexivity; [ ].
      subst. cbn - [Z.add Z.modulo Z.testbit Z.mul Z.shiftl Fancy.lower128 Fancy.upper128].
      lia. }
  Qed.

  Local Ltac prove_comm H :=
    cbv [interp256]; rewrite !interp_step; cbn - [Fancy.interp];
    intros; rewrite H; try reflexivity.

  Lemma mulll_comm rd x y cont cc ctx :
    interp256 (Fancy.Instr Fancy.MUL128LL rd (x, y) cont) cc ctx =
    interp256 (Fancy.Instr Fancy.MUL128LL rd (y, x) cont) cc ctx.
  Proof. prove_comm Z.mul_comm. Qed.

  Lemma mulhh_comm rd x y cont cc ctx :
    interp256 (Fancy.Instr Fancy.MUL128UU rd (x, y) cont) cc ctx =
    interp256 (Fancy.Instr Fancy.MUL128UU rd (y, x) cont) cc ctx.
  Proof. prove_comm Z.mul_comm. Qed.

  Lemma mullh_mulhl rd x y cont cc ctx :
    interp256 (Fancy.Instr Fancy.MUL128LU rd (x, y) cont) cc ctx =
    interp256 (Fancy.Instr Fancy.MUL128UL rd (y, x) cont) cc ctx.
  Proof. prove_comm Z.mul_comm. Qed.

  Lemma add_comm rd x y cont cc ctx :
    0 <= ctx x < 2^256 ->
    0 <= ctx y < 2^256 ->
    interp256 (Fancy.Instr (Fancy.ADD 0) rd (x, y) cont) cc ctx =
    interp256 (Fancy.Instr (Fancy.ADD 0) rd (y, x) cont) cc ctx.
  Proof.
    prove_comm Z.add_comm.
    rewrite !(Z.mod_small (ctx _)) by (cbn in *; omega).
    reflexivity.
  Qed.

  Lemma addc_comm rd x y cont cc ctx :
    0 <= ctx x < 2^256 ->
    0 <= ctx y < 2^256 ->
    interp256 (Fancy.Instr (Fancy.ADDC 0) rd (x, y) cont) cc ctx =
    interp256 (Fancy.Instr (Fancy.ADDC 0) rd (y, x) cont) cc ctx.
  Proof.
    intros;
    prove_comm (Z.add_comm (ctx x)).
    rewrite !(Z.mod_small (ctx _)) by (cbn in *; omega).
    reflexivity.
  Qed.

  (* Tactics to help prove that something in Fancy is line-by-line equivalent to something in PreFancy *)
  Ltac push_value_unused :=
    repeat match goal with
           | |- ~ In _ _ => cbn; intuition; congruence
           | _ => apply ProdEquiv.value_unused_overwrite
           | _ => apply ProdEquiv.value_unused_skip; [ | congruence | ]
           | _ => apply ProdEquiv.value_unused_ret; congruence
           end.

  Ltac remember_single_result :=
    match goal with |- context [(Fancy.spec ?i ?args ?cc) mod ?w] =>
                    let x := fresh "x" in
                    let y := fresh "y" in
                    let Heqx := fresh "Heqx" in
                    remember (Fancy.spec i args cc) as x eqn:Heqx;
                    remember (x mod w) as y
    end.
  Ltac step_both_sides :=
    match goal with |- ProdEquiv.interp256 (Fancy.Instr ?i ?rd1 ?args1 _) _ ?ctx1 = ProdEquiv.interp256 (Fancy.Instr ?i ?rd2 ?args2 _) _ ?ctx2 =>
                    rewrite (interp_step reg_eqb wordmax i rd1 args1); rewrite (interp_step reg_eqb wordmax i rd2 args2);
                    cbn - [Fancy.interp Fancy.spec];
                    repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence;
                    remember_single_result;
                    lazymatch goal with
                    | |- context [Fancy.spec i _ _] =>
                      let Heqa1 := fresh in
                      let Heqa2 := fresh in
                      remember (Tuple.map (n:=i.(Fancy.num_source_regs)) ctx1 args1) eqn:Heqa1;
                      remember (Tuple.map (n:=i.(Fancy.num_source_regs)) ctx2 args2) eqn:Heqa2;
                      cbn in Heqa1; cbn in Heqa2;
                      repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl in Heqa1 by congruence;
                      repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl in Heqa2 by congruence;
                      let a1 := match type of Heqa1 with _ = ?a1 => a1 end in
                      let a2 := match type of Heqa2 with _ = ?a2 => a2 end in
                      (fail 1 "arguments to " i " do not match; LHS has " a1 " and RHS has " a2)
                    | _ => idtac
                    end
    end.
End ProdEquiv.

