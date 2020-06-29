Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Algebra.Ring. (* for ring_simplify_subterms *)
Require Import Crypto.Fancy.Spec. Import Spec.Registers.
Require Import Crypto.Fancy.Compiler.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Local Open Scope Z_scope.

Module Z.
(* TODO: move to Div *)
Lemma div_add_mod_cond_l' x y d :
  d <> 0 ->
  (x mod d + y) / d = (x + y) / d - x / d.
Proof.
  intros.
  rewrite (Div.Z.div_add_mod_cond_l x y d) by lia.
  ring.
Qed.
Lemma div_add_mod_cond_r' x y d :
  d <> 0 ->
  (x + y mod d) / d = (x + y) / d - y / d.
Proof.
  intros.
  rewrite (Div.Z.div_add_mod_cond_r x y d) by lia.
  ring.
Qed.
End Z.

Section Prod.
  Definition Mul256 (out src1 src2 tmp : register) (cont : expr) : expr :=
    Instr MUL128LL out (src1, src2)
          (Instr MUL128UL tmp (src1, src2)
                 (Instr (ADD 128) out (out, tmp)
                        (Instr MUL128LU tmp (src1, src2)
                               (Instr (ADD 128) out (out, tmp) cont)))).
  Definition Mul256x256 (out outHigh src1 src2 tmp : register) (cont : expr) : expr :=
    Instr MUL128LL out (src1, src2)
          (Instr MUL128UU outHigh (src1, src2)
                 (Instr MUL128UL tmp (src1, src2)
                        (Instr (ADD 128) out (out, tmp)
                               (Instr (ADDC (-128)) outHigh (outHigh, tmp)
                                      (Instr MUL128LU tmp (src1, src2)
                                             (Instr (ADD 128) out (out, tmp)
                                                    (Instr (ADDC (-128)) outHigh (outHigh, tmp) cont))))))).

  Definition MontRed256 lo hi y t1 t2 scratch RegPInv : @expr register :=
    Mul256 y lo RegPInv t1
           (Mul256x256 t1 t2 y RegMod scratch
                       (Instr (ADD 0) lo (lo, t1)
                              (Instr (ADDC 0) hi (hi, t2)
                                     (Instr SELC y (RegMod, RegZero)
                                            (Instr (SUB 0) lo (hi, y)
                                                   (Instr ADDM lo (lo, RegZero, RegMod)
                                                          (Ret lo))))))).

  (* Barrett reduction -- this is only the "reduce" part, excluding the initial multiplication. *)
  Definition MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 : @expr register :=
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

(* Solves subgoals for commutativity proofs and simplifies register
lookup expressions *)
Ltac simplify_with_register_properties :=
  repeat
    match goal with
    | _ => rewrite reg_eqb_refl
    | _ => rewrite reg_eqb_neq by (assumption || congruence) 
    | H:?y = _ mod ?m |- 0 <= ?y < _ => rewrite H; apply Z.mod_pos_bound; lia
    | _ => assumption
    end.
Ltac cleanup :=
  cbn - [interp spec cc_spec];
  simplify_with_register_properties;
  cbv [CC.update in_dec list_rec list_rect
                 CC.code_dec];
  cbn [CC.cc_c CC.cc_m CC.cc_z CC.cc_l].
Ltac step_and_remember := 
  rewrite interp_step; cleanup;
  remember_single_result.
Ltac step_lhs :=
  match goal with
  | |- Spec.interp _ _ _ (Instr _ _ _ _) _ _ = _ =>
    step_and_remember
  end.
Ltac step_rhs :=
  rewrite interp_step; cleanup;
  match goal with
  | H: ?x = spec ?i ?args _
    |- context [spec ?i ?args ?cc] =>
    replace (spec i args cc) with x by idtac
  end;
  match goal with
  | H : ?y = (?x mod ?m)%Z |- context [(?x mod ?m)%Z] =>
    rewrite <-H
  end.
Ltac prove_programs_equivalent :=
  repeat step_lhs; (* remember the results of each step on the LHS *)
  repeat match goal with
         | _ => step_rhs
         | |- ?x = ?x => reflexivity
         | _ => rewrite mulhh_comm by simplify_with_register_properties; step_rhs
         | _ => rewrite mulll_comm by simplify_with_register_properties; step_rhs
         | _ => rewrite add_comm by simplify_with_register_properties; step_rhs
         | _ => rewrite addc_comm by simplify_with_register_properties; step_rhs
         | _ => rewrite mullh_mulhl; step_rhs
         | _ => rewrite <-mullh_mulhl; step_rhs
         end.

Section ProdEquiv.
  Context (wordmax : Z).

  Let interp256 := interp reg_eqb wordmax cc_spec.
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
    interp256 (Mul256 out src1 src2 tmp cont) cc ctx =
    interp256 (
        Instr MUL128LU tmp (src1, src2)
              (Instr MUL128UL tmp2 (src1, src2)
                     (Instr MUL128LL out (src1, src2)
                                 (Instr (ADD 128) out (out, tmp2)
                                        (Instr (ADD 128) out (out, tmp) cont))))) cc ctx.
  Proof.
    intros; cbv [Mul256 interp256].
    repeat step_lhs.
    repeat step_rhs.

    match goal with H : value_unused tmp _ |- _ => erewrite H end.
    match goal with H : value_unused tmp2 _ |- _ => erewrite H end.
    apply interp_state_equiv.
    { reflexivity. }
    { intros; cbv [reg_eqb].
      break_innermost_match; try congruence; reflexivity. }
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
    interp256 (Mul256x256 out outHigh src1 src2 tmp cont) cc ctx =
    interp256 (
        Instr MUL128UU outHigh (src1, src2)
              (Instr MUL128LU tmp (src1, src2)
                     (Instr MUL128UL tmp2 (src1, src2)
                            (Instr MUL128LL out (src1, src2)
                                   (Instr (ADD 128) out (out, tmp2)
                                          (Instr (ADDC (-128)) outHigh (outHigh, tmp2)
                                                 (Instr (ADD 128) out (out, tmp)
                                                        (Instr (ADDC (-128)) outHigh (outHigh, tmp) cont)))))))) cc ctx.
  Proof.
    intros; cbv [Mul256x256 interp256].
    repeat step_lhs.
    repeat step_rhs.

    match goal with H : value_unused tmp _ |- _ => erewrite H end.
    match goal with H : value_unused tmp2 _ |- _ => erewrite H end.
    apply interp_state_equiv; [ reflexivity | ].
    intros; cbv [reg_eqb].
    break_innermost_match; try congruence; reflexivity.
  Qed.

  Lemma interp_add_chain a b c cont cc ctx:
    a <> b -> 
    a <> c -> 
    b <> c ->
    (0 <= ctx a < wordmax)%Z ->
    (0 <= ctx b < wordmax)%Z ->
    (0 <= ctx c < wordmax)%Z ->
    (wordmax = 2 ^ 256)%Z ->
    let result := (ctx a + Z.shiftl (ctx c) 128 + ctx b * wordmax)%Z in
    interp256 (
        Instr (ADD 128) a (a, c)
              (Instr (ADDC (-128)) b (b, c) cont))
              cc ctx =
    interp256 cont
              (CC.update [CC.C; CC.M; CC.L; CC.Z]
                         (result / wordmax) cc_spec cc)
              (fun r =>
                 if reg_eqb r a
                 then (result mod wordmax)%Z
                 else
                   if reg_eqb r b
                   then ((result / wordmax) mod wordmax)%Z
                   else ctx r).
  Proof.
    intros; cbv [interp256].
    repeat step_and_remember.
    cbn [spec ADD ADDC CC.cc_c] in *.
    replace x0 with (result / wordmax)%Z in *.

    { apply interp_state_equiv; [ reflexivity | ].
      intros; cbv [reg_eqb].
      break_innermost_match; try congruence; try reflexivity.
      { subst. subst result.
        autorewrite with zsimplify.
        pull_Zmod. reflexivity. } }

    (* TODO: this is a stupidly ugly arithmetic proof *)
    { subst. subst result.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.shiftl_div_pow2 by lia.
      rewrite Pos2Z.opp_neg. (* TODO : add to zsimplify? *)
      autorewrite with zsimplify.

      match goal with
        |- context [if ?x then 1 else 0] =>
        change (if x then 1 else 0) with (Z.b2z x)
      end.
      cbv [cc_spec].
      rewrite Z.testbit_spec' by lia.

      rewrite Z.mod_small with (b:=2) by
          (split; [ Z.zero_bounds | ];
            apply Z.div_lt_upper_bound; try lia;
            match goal with
              |- context [ ?x mod ?y ] =>
              pose proof (Z.mod_pos_bound x y ltac:(lia))
            end; lia).
      
      autorewrite with zsimplify.

      rewrite Z.div_add_mod_cond_r' by lia.
      rewrite Z.mod_small with (a := ctx c / 2 ^ 128)
        by (split; [ Z.zero_bounds | apply Z.div_lt_upper_bound; lia ]).
      assert (0 < 2 ^ 128) by (cbn; lia).
      change (2 ^ 256)%Z with (2 ^ 128 * 2 ^ 128)%Z.
      rewrite Z.div_mul_cancel_r by lia.
      ring. }
  Qed.

  Definition flags_unused e wordmax : Prop :=
    forall cc x ctx,
      interp reg_eqb wordmax cc_spec e cc ctx =
      interp reg_eqb wordmax cc_spec e (CC.update [CC.C; CC.M; CC.L; CC.Z] x cc_spec cc) ctx.

  Lemma swap_add_chain a b c d cont cc ctx:
    a <> b -> 
    a <> c -> 
    a <> d -> 
    b <> c ->
    b <> d ->
    c <> d ->
    0 <= ctx a < wordmax ->
    0 <= ctx b < wordmax ->
    0 <= ctx c < wordmax ->
    0 <= ctx d < wordmax ->
    wordmax = 2 ^ 256 ->
    flags_unused cont wordmax ->
    interp256 (
        Instr (ADD 128) a (a, c)
              (Instr (ADDC (-128)) b (b, c)
                     (Instr (ADD 128) a (a, d)
                            (Instr (ADDC (-128)) b (b, d) cont))))
              cc ctx =
    interp256 (
        Instr (ADD 128) a (a, d)
              (Instr (ADDC (-128)) b (b, d)
                     (Instr (ADD 128) a (a, c)
                            (Instr (ADDC (-128)) b (b, c) cont))))
              cc ctx.
  Proof.
    intros.
    assert (0 < wordmax) by lia.
    repeat (rewrite interp_add_chain by (rewrite ?reg_eqb_refl, ?reg_eqb_neq by congruence; try assumption; auto using Z.mod_pos_bound with lia)).
    rewrite ?reg_eqb_refl, ?reg_eqb_neq by congruence.
    match goal with
    | H : flags_unused ?e _
      |- interp256 ?e ?ccl _ = interp256 ?e ?ccr _ =>
      rewrite H with (cc:=ccl) (x:=0);
        rewrite H with (cc:=ccr) (x:=0)
    end.
    rewrite !cc_overwrite_full.
    apply interp_state_equiv; [ reflexivity | ].
    intros; cbv [reg_eqb].
    break_innermost_match; try congruence; try reflexivity.
    { autorewrite with zsimplify. pull_Zmod.
      f_equal; ring. }
    { autorewrite with zsimplify. pull_Zmod.
      rewrite !Z.div_add_mod_cond_l' by (subst; cbn; lia).
      ring_simplify.
      (* This is really annoying, can't a tactic do this? *)
      match goal with |- context [?a + ?b + ?c] =>
                      match goal with |- context [?a + ?c + ?b] =>
                                      replace (a + b + c) with (a + c + b) by ring
                      end end.
      f_equal. ring. }
  Qed.

End ProdEquiv.

Ltac push_value_unused :=
  repeat match goal with
         | _ => apply value_unused_skip; [ | assumption | ]
         | _ => apply value_unused_overwrite
         | _ => apply value_unused_ret; congruence
         | _ => apply not_in_cons; split;
                [ try assumption; symmetry; assumption | ]
         | _ => apply in_nil
         end.