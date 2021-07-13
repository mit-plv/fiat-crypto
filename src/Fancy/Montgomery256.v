Require Import Coq.Bool.Bool.
Require Import Coq.derive.Derive.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Rewriter.Language.Language. Import Language.Compilers.
Require Import Crypto.Language.API. Import Language.API.Compilers.
Require Import Rewriter.Language.Wf. Import Language.Wf.Compilers.
Require Import Crypto.Arithmetic.FancyMontgomeryReduction.
Require Import Crypto.PushButtonSynthesis.FancyMontgomeryReduction.
Require Import Crypto.Fancy.Compiler.
Require Import Crypto.Fancy.Prod.
Require Import Crypto.Fancy.Spec.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Module Montgomery256.

  Definition N := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition N':= (115792089210356248768974548684794254293921932838497980611635986753331132366849).
  Definition R := Eval lazy in (2^256).
  Definition R' := 115792089183396302114378112356516095823261736990586219612555396166510339686400.
  Definition machine_wordsize := 256.

  Derive montred256
         SuchThat (montred N R N' machine_wordsize = ErrorT.Success montred256)
         As montred256_eq.
  Proof. lazy; reflexivity. Qed.

  Lemma Wf_montred256 : API.Wf montred256.
  Proof using Type. eapply Wf_montred, montred256_eq. Qed.

  Lemma montred256_correct :
    COperationSpecifications.MontgomeryReduction.montred_correct N R R' (API.Interp montred256).
  Proof.
    apply montred_correct with (n:=2%nat) (machine_wordsize:=machine_wordsize) (N':=N') (requests:=[]).
    { lazy. reflexivity. }
    { apply montred256_eq. }
  Qed.

  Lemma montred'_correct_specialized R' (R'_correct : Z.equiv_modulo N (R * R') 1) :
    forall (lo hi : Z),
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      MontgomeryReduction.montred' N R N' (Z.log2 R) lo hi = ((lo + R * hi) * R') mod N.
  Proof.
    intros.
    apply MontgomeryReduction.montred'_correct with (T:=lo + R * hi) (R':=R') (n:=2%nat);
      try match goal with
            | |- context[R'] => assumption
            | |- context [lo] =>
              try assumption; progress autorewrite with zsimplify cancel_pair; reflexivity
          end; lazy; try split; congruence.
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
    lazy - [ADD ADDC SUB MUL128LL MUL128LU MUL128UL MUL128UU RSHI SELC SELM SELL ADDM].
    reflexivity.
  Qed.

  (* TODO: these tactics are duplicated; move them elsewhere (probably translation *)
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
      let last_wrote := (fun x : CC.code => RegZero) in
      let cc := make_cc last_wrote ctx carry_flag in
      interp Pos.eqb wordmax cc_spec (montred256_fancy RegMod RegPInv RegZero RegLo RegHi error) cc ctx = ((lo + R * hi) * R') mod N.
  Proof.
    intros.
    rewrite montred256_fancy_eq.
    cbv [montred256_fancy'].
    rewrite <-montred256_correct by (auto; reflexivity).
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
      intuition; Prod.inversion_prod; subst; apply Z.mod_small; lia. }
    { repeat first [ eapply expr.wf_Proper_list, Wf_montred256
                   | progress cbv [make_pairs consts_list arg_list]
                   | wf_subgoal ]. }
    { cbn. cbv [N' N].
      repeat (econstructor; [ solve [valid_expr_subgoal] | intros ]).
      econstructor. valid_expr_subgoal. }
    { reflexivity. }
  Qed.

  Import Spec.Registers.

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
                                                 else errorR)%positive.
  Derive montred256_alloc
         SuchThat (montred256_alloc = montred256_alloc')
         As montred256_alloc_eq.
  Proof.
    intros.
    cbv [montred256_alloc' montred256_fancy].
    cbn. subst montred256_alloc.
    reflexivity.
  Qed.

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

    Time repeat match goal with
                | _ => progress prove_programs_equivalent
                | _ => rewrite interp_Mul256 with (tmp2 := extra_reg) by
                      (match goal with
                       | |- _ <> _ => assumption || congruence
                       | _ => push_value_unused
                       end)
                | _ => rewrite interp_Mul256x256 with (tmp2 := extra_reg) by
                      (match goal with
                       | |- _ <> _ => assumption || congruence
                       | _ => push_value_unused
                       end)
                end.

    cbn [Spec.interp]; simplify_with_register_properties.
    reflexivity.
  Qed.


  Lemma prod_montred256_correct :
    forall (cc_start_state : CC.state) (* starting carry flags can be anything *)
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
      by (cbv [R N N'] in *; auto with lia).

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

Section with_notations.
  Import Crypto.Language.IdentifiersBasicGENERATED.Compilers.
  Import Crypto.Util.ZRange.
  Local Open Scope zrange_scope.
  Local Open Scope Z_scope.
  Local Open Scope expr_scope.
  Local Notation uint256 := r[0 ~> 115792089237316195423570985008687907853269984665640564039457584007913129639935]%zrange.
  Local Set Printing Width 500.
  Redirect "Crypto.Fancy.Montgomery256.montred256" Print Montgomery256.montred256.
End with_notations.

Import Registers.

(* Notations to make code more readable *)
Local Notation "i rd x y ; cont" := (Instr i rd (x, y) cont) (at level 40, cont at level 200, format "i  rd  x  y ; '//' cont").
Local Notation "i rd x y z ; cont" := (Instr i rd (x, y, z) cont) (at level 40, cont at level 200, format "i  rd  x  y  z ; '//' cont").

(* Montgomery reference code : *)
Local Set Printing Width 150.
Redirect "Crypto.Fancy.Montgomery256.Prod.MontRed256" Eval cbv beta iota delta [Prod.MontRed256 Prod.Mul256 Prod.Mul256x256] in Prod.MontRed256.
(*
     = fun lo hi y t1 t2 scratch RegPInv : register =>
       MUL128LL y lo RegPInv;
       MUL128UL t1 lo RegPInv;
       ADD 128 y y t1;
       MUL128LU t1 lo RegPInv;
       ADD 128 y y t1;
       MUL128LL t1 y RegMod;
       MUL128UU t2 y RegMod;
       MUL128UL scratch y RegMod;
       ADD 128 t1 t1 scratch;
       ADDC (-128) t2 t2 scratch;
       MUL128LU scratch y RegMod;
       ADD 128 t1 t1 scratch;
       ADDC (-128) t2 t2 scratch;
       ADD 0 lo lo t1;
       ADDC 0 hi hi t2;
       SELC y RegMod RegZero;
       SUB 0 lo hi y;
       ADDM lo lo RegZero RegMod;
       Ret lo
 *)

(* Remove Redirect to see proof statement and remaining admitted statements,
or search for "prod_montred256_correct" to see comments on the proof
preconditions. *)
Redirect "Crypto.Fancy.Montgomery256.prod_montred256_correct" Check Montgomery256.prod_montred256_correct.
Redirect "Crypto.Fancy.Montgomery256.prod_montred256_correct.Assumptions" Print Assumptions Montgomery256.prod_montred256_correct.
