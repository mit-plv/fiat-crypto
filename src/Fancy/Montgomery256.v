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

(* TODO : once Barrett is updated & working, fix Montgomery to match *)
(*
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
      MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2 (lo, hi) = ((lo + R * hi) * R') mod N.
  Proof.
    intros.
    apply MontgomeryReduction.montred'_correct with (T:=lo + R * hi) (R':=R');
      try match goal with
            | |- context[R'] => assumption
            | |- context [lo] =>
              try assumption; progress autorewrite with zsimplify cancel_pair; reflexivity
          end; lazy; try split; congruence.
  Qed.

  (*
  (* Note: If this is not factored out, then for some reason Qed takes forever in montred256_correct_full. *)
  Lemma montred256_correct_proj2 :
    forall xy : type.interp (type.prod type.Z type.Z),
      ZRange.type.option.is_bounded_by
        (t:=type.prod type.Z type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        xy = true ->
       expr.Interp (@ident.interp) montred256 xy = app_curried (t:=type.arrow (type.prod type.Z type.Z) type.Z) (MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2) xy.
  Proof. intros; destruct (montred256_correct xy); assumption. Qed.
  Lemma montred256_correct_proj2' :
    forall xy : type.interp (type.prod type.Z type.Z),
      ZRange.type.option.is_bounded_by
        (t:=type.prod type.Z type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        xy = true ->
       expr.Interp (@ident.interp) montred256 xy = MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2 xy.
  Proof. intros; rewrite montred256_correct_proj2 by assumption; unfold app_curried; exact eq_refl. Qed.
   *)
  Local Arguments is_bounded_by_bool / .
  Lemma montred256_correct_full  R' (R'_correct : Z.equiv_modulo N (R * R') 1) :
    forall (lo hi : Z),
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      PreFancy.Interp 256 montred256 (lo, hi) = ((lo + R * hi) * R') mod N.
  Proof.
    intros.
    rewrite <-montred'_correct_specialized by assumption.
    destruct (proj1 montred256_correct ((lo, hi), tt) ((lo, hi), tt)) as [H2 H3].
    { repeat split. }
    { cbn -[Z.pow].
      rewrite !andb_true_iff.
      repeat apply conj; Z.ltb_to_lt; trivial; cbv [R N machine_wordsize] in *; lia. }
    { etransitivity; [ eapply H3 | ]. (* need Strategy -100 [type.app_curried]. for this to be fast *)
      generalize MontgomeryReduction.montred'; vm_compute; reflexivity. }
  Qed.

  (*
  (* TODO : maybe move these ok_expr tactics somewhere else *)
  Ltac ok_expr_step' :=
    match goal with
    | _ => assumption
    | |- _ <= _ <= _ \/ @eq zrange _ _ =>
      right; lazy; try split; congruence
    | |- _ <= _ <= _ \/ @eq zrange _ _ =>
      left; lazy; try split; congruence
    | |- lower r[0~>_]%zrange = 0 => reflexivity
    | |- context [PreFancy.ok_ident] => constructor
    | |- context [PreFancy.ok_scalar] => constructor; try omega
    | |- context [PreFancy.is_halved] => eapply PreFancy.is_halved_constant; [lazy; reflexivity | ]
    | |- context [PreFancy.is_halved] => constructor
    | |- context [PreFancy.in_word_range] => lazy; reflexivity
    | |- context [PreFancy.in_flag_range] => lazy; reflexivity
    | |- context [PreFancy.get_range] =>
      cbn [PreFancy.get_range lower upper fst snd ZRange.map]
    | x : type.interp (type.prod _ _) |- _ => destruct x
    | |- (_ <=? _)%zrange = true =>
      match goal with
      | |- context [PreFancy.get_range_var] =>
        cbv [is_tighter_than_bool PreFancy.has_range fst snd upper lower R N] in *; cbn;
        apply andb_true_iff; split; apply Z.leb_le
      | _ => lazy
      end; omega || reflexivity
    | |- @eq zrange _ _ => lazy; reflexivity
    | |- _ <= _ => cbv [machine_wordsize]; omega
    | |- _ <= _ <= _ => cbv [machine_wordsize]; omega
    end; intros.

  (* TODO : maybe move these ok_expr tactics somewhere else *)
  Ltac ok_expr_step :=
    match goal with
    | |- context [PreFancy.ok_expr] => constructor; cbn [fst snd]; repeat ok_expr_step'
    end; intros; cbn [Nat.max].*)

  (*
  Lemma montred256_prefancy_correct :
    forall (lo hi : Z),
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      @PreFancy.interp machine_wordsize base.type.Z (montred256 _ @ (##lo,##hi)) = ((lo + R * hi) * R') mod N.
  Proof.
    intros.

    rewrite montred256_prefancy_eq; cbv [montred256_prefancy'].
    erewrite PreFancy.of_Expr_correct.
    { apply montred256_correct_full; try assumption; reflexivity. }
    { reflexivity. }
    { lazy; reflexivity. }
    { lazy; reflexivity. }
    { repeat constructor. }
    { cbv [In N N']; intros; intuition; subst; cbv; congruence. }
    { assert (340282366920938463463374607431768211455 * 2 ^ 128 <= 2 ^ machine_wordsize - 1) as shiftl_128_ok by (lazy; congruence).
      repeat (ok_expr_step; [ ]).
      ok_expr_step.
      lazy; congruence.
      constructor.
      constructor. }
    { lazy. omega. }
   Qed.
*)

  Definition montred256_fancy' (lo hi RegMod RegPInv RegZero error : positive) :=
    Fancy.of_Expr 3%positive
                  (fun z => if z =? N then Some RegMod else if z =? N' then Some RegPInv else if z =? 0 then Some RegZero else None)
                  [N;N']
                  montred256
                  ((lo, hi)%positive, tt)
                  error.
  Derive montred256_fancy
         SuchThat (forall RegMod RegPInv RegZero,
                      montred256_fancy RegMod RegPInv RegZero = montred256_fancy' RegMod RegPInv RegZero)
         As montred256_fancy_eq.
  Proof.
    intros.
    lazy - [Fancy.ADD Fancy.ADDC Fancy.SUB
                      Fancy.MUL128LL Fancy.MUL128LU Fancy.MUL128UL Fancy.MUL128UU
                      Fancy.RSHI Fancy.SELC Fancy.SELM Fancy.SELL Fancy.ADDM].
    reflexivity.
  Qed.

  Import Fancy.Registers.

  Definition montred256_alloc' lo hi RegPInv :=
    fun errorP errorR =>
    Fancy.allocate register
                   positive Pos.eqb
                   errorR
                   (montred256_fancy 1000%positive 1001%positive 1002%positive 1003%positive 1004%positive errorP)
                   [r2;r3;r4;r5;r6;r7;r8;r9;r10;r11;r12;r13;r14;r15;r16;r17;r18;r19;r20]
                   (fun n => if n =? 1000 then lo
                             else if n =? 1001 then hi
                                  else if n =? 1002 then RegMod
                                       else if n =? 1003 then RegPInv
                                            else if n =? 1004 then RegZero
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

  Import ProdEquiv.

  Local Ltac solve_bounds :=
    match goal with
    | H : ?a = ?b mod ?c |- 0 <= ?a < ?c => rewrite H; apply Z.mod_pos_bound; omega
    | _ => assumption
    end.

  Lemma montred256_alloc_equivalent errorP errorR cc_start_state start_context :
    forall lo hi y t1 t2 scratch RegPInv extra_reg,
      NoDup [lo; hi; y; t1; t2; scratch; RegPInv; extra_reg; RegMod; RegZero] ->
      0 <= start_context lo < R ->
      0 <= start_context hi < R ->
      0 <= start_context RegPInv < R ->
      ProdEquiv.interp256 (montred256_alloc r0 r1 r30 errorP errorR) cc_start_state
                          (fun r => if reg_eqb r r0
                                    then start_context lo
                                    else if reg_eqb r r1
                                         then start_context hi
                                         else if reg_eqb r r30
                                              then start_context RegPInv
                                              else start_context r)
    = ProdEquiv.interp256 (Prod.MontRed256 lo hi y t1 t2 scratch RegPInv) cc_start_state start_context.
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

    rewrite ProdEquiv.interp_Mul256 with (tmp2:=extra_reg) by (congruence || push_value_unused).

    rewrite mullh_mulhl. step_both_sides.
    rewrite mullh_mulhl. step_both_sides.
    (*
    step_both_sides.
    step_both_sides.

    rewrite ProdEquiv.interp_Mul256x256 with (tmp2:=extra_reg) by (congruence || push_value_unused).

    rewrite mulll_comm. step_both_sides.
    step_both_sides.
    step_both_sides.
    rewrite mulhh_comm. step_both_sides.
    step_both_sides.
    step_both_sides.
    step_both_sides.
    step_both_sides.


    rewrite add_comm by (cbn; solve_bounds). step_both_sides.
    rewrite addc_comm by (cbn; solve_bounds). step_both_sides.
    step_both_sides.
    step_both_sides.
    step_both_sides.

    cbn; repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence.
    reflexivity.*)
  Admitted.

  Import Fancy_PreFancy_Equiv.

  Definition interp_equivZZ_256 {s} :=
    @interp_equivZZ s 256 ltac:(cbv; congruence) 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(reflexivity).
  Definition interp_equivZ_256 {s} :=
    @interp_equivZ s 256 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(lia) ltac:(reflexivity).

  Local Ltac simplify_op_equiv start_ctx :=
    cbn - [Fancy.spec ident.gen_interp Fancy.cc_spec];
    repeat match goal with H : start_ctx _ = _ |- _ => rewrite H end;
    cbv - [
      Z.add_with_get_carry_full
        Z.add_get_carry_full Z.sub_get_borrow_full
        Z.le Z.ltb Z.leb Z.geb Z.eqb Z.land Z.shiftr Z.shiftl
        Z.add Z.mul Z.div Z.sub Z.modulo Z.testbit Z.pow Z.ones
        fst snd]; cbn [fst snd];
    try (replace (2 ^ (256 / 2) - 1) with (Z.ones 128) by reflexivity; rewrite !Z.land_ones by omega);
    autorewrite with to_div_mod; rewrite ?Z.mod_mod, <-?Z.testbit_spec' by omega;
    repeat match goal with
           | H : 0 <= ?x < ?m |- context [?x mod ?m] => rewrite (Z.mod_small x m) by apply H
           | |- context [?x <? 0] => rewrite (proj2 (Z.ltb_ge x 0)) by (break_match; Z.zero_bounds)
           | _ => rewrite Z.mod_small with (b:=2) by (break_match; omega)
           | |- context [ (if Z.testbit ?a ?n then 1 else 0) + ?b + ?c] =>
             replace ((if Z.testbit a n then 1 else 0) + b + c) with (b + c + (if Z.testbit a n then 1 else 0)) by ring
           end.

  Local Ltac solve_nonneg ctx :=
    match goal with x := (Fancy.spec _ _ _) |- _ => subst x end;
    simplify_op_equiv ctx; Z.zero_bounds.

  Local Ltac generalize_result :=
    let v := fresh "v" in intro v; generalize v; clear v; intro v.

  Local Ltac generalize_result_nonneg ctx :=
    let v := fresh "v" in
    let v_nonneg := fresh "v_nonneg" in
    intro v; assert (0 <= v) as v_nonneg; [solve_nonneg ctx |generalize v v_nonneg; clear v v_nonneg; intros v v_nonneg].

  Local Ltac step_abs :=
    match goal with
    | [ |- context G[expr.interp ?ident_interp (expr.Abs ?f) ?x] ]
      => let G' := context G[expr.interp ident_interp (f x)] in
         change G'; cbv beta
    end.
  Local Ltac step ctx :=
    repeat step_abs;
    match goal with
    | |- Fancy.interp _ _ _ (Fancy.Instr (Fancy.ADD _) _ _ (Fancy.Instr (Fancy.ADDC _) _ _ _)) _ _ = _ =>
      apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result_nonneg ctx]
    | [ |- _ = expr.interp _ (PreFancy.LetInAppIdentZ _ _ _ _ _ _) ]
      => apply interp_equivZ_256; [simplify_op_equiv ctx | generalize_result]
    | [ |- _ = expr.interp _ (PreFancy.LetInAppIdentZZ _ _ _ _ _ _) ]
      => apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result]
    end.

  Local Ltac break_ifs :=
    repeat (break_innermost_match_step; Z.ltb_to_lt; try (exfalso; omega); []).

  Local Opaque PreFancy.interp_cast_mod.

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
      (ProdEquiv.interp256 (Prod.MontRed256 lo hi y t1 t2 scratch RegPInv) cc_start_state start_context = (x * R') mod N).
  Proof.
    intros. subst x. cbv [N R N'] in *.
    rewrite <-montred256_correct_full by (auto; vm_compute; reflexivity).
    rewrite <-montred256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (cbv [R]; auto with omega).
    cbv [ProdEquiv.interp256].
    cbv [montred256_alloc montred256 expr.Interp].

    (*step start_context; [ break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | ].*)
    (*step start_context; [ break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | break_ifs; reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].

    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ break_innermost_match; Z.ltb_to_lt; omega | ].
    step start_context; [ reflexivity | | ].
    {
      let r := eval cbv in (2^256) in replace (2^256) with r by reflexivity.
      rewrite !Z.shiftl_0_r, !Z.mod_mod by omega.
      apply Z.testbit_neg_eq_if;
        let r := eval cbv in (2^256) in replace (2^256) with r by reflexivity;
        auto using Z.mod_pos_bound with omega. }
    step start_context; [ break_innermost_match; Z.ltb_to_lt; omega | ].
    reflexivity.
     *)
  Admitted.

  Import PrintingNotations.
  Set Printing Width 10000.

  Print montred256.
(*
montred256 = fun var : type -> Type => (λ x : var (type.type_primitive type.Z * type.type_primitive type.Z)%ctype,
    expr_let x0 := 79228162514264337593543950337 *₂₅₆ (uint128)(x₁ >> 128) in
    expr_let x1 := 340282366841710300986003757985643364352 *₂₅₆ ((uint128)(x₁) & 340282366920938463463374607431768211455) in
    expr_let x2 := 79228162514264337593543950337 *₂₅₆ ((uint128)(x₁) & 340282366920938463463374607431768211455) in
    expr_let x3 := ADD_256 ((uint256)(((uint128)(x1) & 340282366920938463463374607431768211455) << 128), x2) in
    expr_let x4 := ADD_256 ((uint256)(((uint128)(x0) & 340282366920938463463374607431768211455) << 128), x3₁) in
    expr_let x5 := 79228162514264337593543950335 *₂₅₆ ((uint128)(x4₁) & 340282366920938463463374607431768211455) in
    expr_let x6 := 79228162514264337593543950335 *₂₅₆ (uint128)(x4₁ >> 128) in
    expr_let x7 := 340282366841710300967557013911933812736 *₂₅₆ ((uint128)(x4₁) & 340282366920938463463374607431768211455) in
    expr_let x8 := 340282366841710300967557013911933812736 *₂₅₆ (uint128)(x4₁ >> 128) in
    expr_let x9 := ADD_256 ((uint256)(((uint128)(x7) & 340282366920938463463374607431768211455) << 128), x5) in
    expr_let x10 := ADDC_256 (x9₂, (uint128)(x7 >> 128), x8) in
    expr_let x11 := ADD_256 ((uint256)(((uint128)(x6) & 340282366920938463463374607431768211455) << 128), x9₁) in
    expr_let x12 := ADDC_256 (x11₂, (uint128)(x6 >> 128), x10₁) in
    expr_let x13 := ADD_256 (x11₁, x₁) in
    expr_let x14 := ADDC_256 (x13₂, x12₁, x₂) in
    expr_let x15 := SELC (x14₂, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951) in
    expr_let x16 := SUB_256 (x14₁, x15) in
    ADDM (x16₁, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951))%expr
     : Expr (type.uncurry (type.type_primitive type.Z * type.type_primitive type.Z -> type.type_primitive type.Z))
*)

  Import PreFancy.
  Import PreFancy.Notations.
  Local Notation "'RegMod'" := (expr.Ident (ident.Literal 115792089210356248762697446949407573530086143415290314195533631308867097853951)).
  Local Notation "'RegPInv'" := (expr.Ident (ident.Literal 115792089210356248768974548684794254293921932838497980611635986753331132366849)).
  Local Open Scope expr_scope.
  Local Notation mulhl := (#(fancy_mulhl 256)).
  Local Notation mulhh := (#(fancy_mulhh 256)).
  Local Notation mulll := (#(fancy_mulll 256)).
  Local Notation mullh := (#(fancy_mullh 256)).
  Local Notation selc := (#(fancy_selc)).
  Local Notation addm := (#(fancy_addm)).
  Notation add n := (#(fancy_add 256 n)).
  Notation addc n := (#(fancy_addc 256 n)).

  Print montred256.
  (*
montred256 =
fun var : type -> Type =>
λ x : var (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype),
mulhl@(x0, x₁, RegPInv);
mullh@(x1, x₁, RegPInv);
mulll@(x2, x₁, RegPInv);
(add 128)@(x3, x2, Lower{x1});
(add 128)@(x4, x3₁, Lower{x0});
mulll@(x5, RegMod, x4₁);
mullh@(x6, RegMod, x4₁);
mulhl@(x7, RegMod, x4₁);
mulhh@(x8, RegMod, x4₁);
(add 128)@(x9, x5, Lower{x7});
(addc (-128))@(x10, carry{$x9}, x8, x7);
(add 128)@(x11, x9₁, Lower{x6});
(addc (-128))@(x12, carry{$x11}, x10₁, x6);
(add 0)@(x13, x11₁, x₁);
(addc 0)@(x14, carry{$x13}, x12₁, x₂);
selc@(x15, (carry{$x14}, RegZero), RegMod);
#(fancy_sub 256 0)@(x16, x14₁, x15);
addm@(x17, (x16₁, RegZero), RegMod);
x17
     : Expr
         (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype ->
          type.base (base.type.type_base base.type.Z))%ptype
  *)

End Montgomery256.
