Require Import Crypto.Assembly.PhoasCommon.

Require Export Crypto.Assembly.QhasmUtil.
Require Export Crypto.Assembly.QhasmEvalCommon.
Require Export Crypto.Assembly.WordizeUtil.
Require Export Crypto.Assembly.Evaluables.
Require Export Crypto.Assembly.HL.
Require Export Crypto.Assembly.LL.

Require Export FunctionalExtensionality.

Require Import Bedrock.Nomega.

Require Import Coq.ZArith.ZArith_dec.
Require Import Coq.ZArith.Znat.

Module HLConversions.
  Import HL.

  Definition convertVar {A B: Type} {EA: Evaluable A} {EB: Evaluable B} {t} (a: interp_type (T := A) t): interp_type (T := B) t.
  Proof.
    induction t as [| t3 IHt1 t4 IHt2].

    - refine (@toT B EB (@fromT A EA _)); assumption.

    - destruct a as [a1 a2]; constructor;
        [exact (IHt1 a1) | exact (IHt2 a2)].
  Defined.

  Fixpoint convertExpr {A B: Type} {EA: Evaluable A} {EB: Evaluable B} {t v} (a: expr (T := A) (var := v) t): expr (T := B) (var := v) t :=
    match a with
    | Const x => Const (@toT B EB (@fromT A EA x))
    | Var t x => @Var B _ t x
    | Binop t1 t2 t3 o e1 e2 =>
      @Binop B _ t1 t2 t3 o (convertExpr e1) (convertExpr e2)
    | Let tx e tC f =>
      Let (convertExpr e) (fun x => convertExpr (f x))
    | Pair t1 e1 t2 e2 => Pair (convertExpr e1) (convertExpr e2)
    | MatchPair t1 t2 e tC f => MatchPair (convertExpr e) (fun x y =>
        convertExpr (f x y))
    end.

  Fixpoint convertExpr' {A B: Type} {EA: Evaluable A} {EB: Evaluable B} {t} (a: expr (T := A) (var := @interp_type A) t): expr (T := B) (var := @interp_type B) t :=
    match a with
    | Const x => Const (@toT B EB (@fromT A EA x))
    | Var t x => @Var B _ t (convertVar x)
    | Binop t1 t2 t3 o e1 e2 =>
      @Binop B _ t1 t2 t3 o (convertExpr' e1) (convertExpr' e2)
    | Let tx e tC f =>
      Let (convertExpr' e) (fun x => convertExpr' (f (convertVar x)))
    | Pair t1 e1 t2 e2 => Pair (convertExpr' e1) (convertExpr' e2)
    | MatchPair t1 t2 e tC f => MatchPair (convertExpr' e) (fun x y =>
        convertExpr' (f (convertVar x) (convertVar y)))
    end.

  Definition convertZToWord {t} n v a :=
    @convertExpr Z (word n) ZEvaluable (@WordEvaluable n) t v a.

  Definition convertZToWordRangeOpt {t} n v a :=
    @convertExpr Z (@WordRangeOpt n) ZEvaluable (@WordRangeOptEvaluable n) t v a.

  Definition convertZToWord' {t} n a :=
    @convertExpr' Z (word n) ZEvaluable (@WordEvaluable n) t a.

  Definition convertZToWordRangeOpt' {t} n a :=
    @convertExpr' Z (@WordRangeOpt n) ZEvaluable (@WordRangeOptEvaluable n) t a.

  Definition ZToWord {t} n (a: @Expr Z t): @Expr (word n) t :=
    fun v => convertZToWord n v (a v).

  Definition ZToRange {t} n (a: @Expr Z t): @Expr (@WordRangeOpt n) t :=
    fun v => convertZToWordRangeOpt n v (a v).

  Definition typeMap {A B t} (f: A -> B) (x: @interp_type A t): @interp_type B t.
  Proof.
    induction t; [refine (f x)|].
    destruct x as [x1 x2].
    refine (IHt1 x1, IHt2 x2).
  Defined.

  Definition RangeInterp {n t} E: @interp_type (option (Range N)) t :=
    typeMap rangeEval (@Interp (@WordRangeOpt n) (@WordRangeOptEvaluable n) t E).

  Example example_Expr : Expr TT := fun var => (
    Let (Const 7) (fun a =>
      Let (Let (Binop OPadd (Var a) (Var a)) (fun b => Pair (Var b) (Var b))) (fun p =>
        MatchPair (Var p) (fun x y =>
          Binop OPadd (Var x) (Var y)))))%Z.

  Example interp_example_range :
    RangeInterp (ZToRange 32 example_Expr) = Some (range N 28%N 28%N).
  Proof. reflexivity. Qed.
End HLConversions.

Module LLConversions.
  Import LL.

  Definition convertVar {A B: Type} {EA: Evaluable A} {EB: Evaluable B} {t} (a: interp_type (T := A) t): interp_type (T := B) t.
  Proof.
    induction t as [| t3 IHt1 t4 IHt2].

    - refine (@toT B EB (@fromT A EA _)); assumption.

    - destruct a as [a1 a2]; constructor;
        [exact (IHt1 a1) | exact (IHt2 a2)].
  Defined.

  Fixpoint convertArg {A B: Type} {EA: Evaluable A} {EB: Evaluable B} {t} (x: arg (T := A) t): arg (T := B) t :=
    match x with | Arg t' c => Arg t' (convertVar (t := t') c) end.

  Fixpoint convertExpr {A B: Type} {EA: Evaluable A} {EB: Evaluable B} {t} (a: expr (T := A) t): expr (T := B) t :=
    match a with
    | LetBinop _ _ out op a b _ eC =>
      LetBinop (T := B) op (convertArg a) (convertArg b) (fun x: (interp_type (T := B) out) => convertExpr (eC (convertVar x)))
    | Return _ a => Return (convertArg a)
    end.

  Definition convertZToWord {t} n a :=
    @convertExpr Z (word n) ZEvaluable (@WordEvaluable n) t a.

  Definition convertZToWordRangeOpt {t} n a :=
    @convertExpr Z (@WordRangeOpt n) ZEvaluable (@WordRangeOptEvaluable n) t a.

  Definition typeMap {A B t} (f: A -> B) (x: @interp_type A t): @interp_type B t.
  Proof.
    induction t; [refine (f x)|].
    destruct x as [x1 x2].
    refine (IHt1 x1, IHt2 x2).
  Defined.

  Definition zinterp {t} E := @interp Z ZEvaluable t E.

  Definition wordInterp {n t} E := @interp (word n) (@WordEvaluable n) t E.

  Definition rangeInterp {n t} E: @interp_type (@WordRangeOpt n) t :=
    @interp (@WordRangeOpt n) (@WordRangeOptEvaluable n) t E.

  Section Correctness.
    (* Aliases to make the proofs easier to read. *)

    Definition varZToRange {n t} (v: @interp_type Z t): @interp_type (@WordRangeOpt n) t :=
      @convertVar Z (@WordRangeOpt n) ZEvaluable (WordRangeOptEvaluable) t v.

    Definition varRangeToZ {n t} (v: @interp_type (@WordRangeOpt n) t): @interp_type Z t :=
      @convertVar (@WordRangeOpt n) Z (WordRangeOptEvaluable) ZEvaluable t v.

    Definition varZToWord {n t} (v: @interp_type Z t): @interp_type (@word n) t :=
      @convertVar Z (@word n) ZEvaluable (@WordEvaluable n) t v.

    Definition varWordToZ {n t} (v: @interp_type (@word n) t): @interp_type Z t :=
      @convertVar (word n) Z (@WordEvaluable n) ZEvaluable t v.

    Definition zOp {tx ty tz: type} (op: binop tx ty tz)
               (x: @interp_type Z tx) (y: @interp_type Z ty): @interp_type Z tz :=
      @interp_binop Z ZEvaluable _ _ _ op x y.

    Definition wordOp {n} {tx ty tz: type} (op: binop tx ty tz)
               (x: @interp_type _ tx) (y: @interp_type _ ty): @interp_type _ tz :=
      @interp_binop (word n) (@WordEvaluable n) _ _ _ op x y.

    Definition rangeOp {n} {tx ty tz: type} (op: binop tx ty tz)
               (x: @interp_type _ tx) (y: @interp_type _ ty): @interp_type _ tz :=
      @interp_binop (@WordRangeOpt n) (@WordRangeOptEvaluable n) _ _ _ op x y.

    Definition rangeArg {n t} (x: @arg (@WordRangeOpt n) t) := @interp_arg _ _ x.

    Definition wordArg {n t} (x: @arg (word n) t) := @interp_arg _ _ x.


    (* Bounds-checking fixpoint *)

    Fixpoint checkVar {n t} (x: @interp_type (@WordRangeOpt n) t) :=
      match t as t' return (interp_type t') -> Prop with
      | TT => fun x' =>
        match (rangeEval x') with
        | Some (range low high) => True
        | None => False
        end
      | Prod t0 t1 => fun x' =>
        match x' with
        | (x0, x1) => (checkVar (n := n) x0) /\ (checkVar (n := n) x1)
        end
      end x.

    Fixpoint check {n t} (e : @expr (@WordRangeOpt n) t): Prop :=
      match e with
      | LetBinop ta tb tc op a b _ eC =>
          (@checkVar n tc (rangeOp op (interp_arg a) (interp_arg b)))
        /\ (check (eC (rangeOp op (interp_arg a) (interp_arg b))))
      | Return _ a => checkVar (interp_arg a)
      end.

    (* Utility Lemmas *)

    Lemma interp_arg_convert : forall {A B t} {EA: Evaluable A} {EB: Evaluable B} (x: @arg A t),
        (interp_arg (@convertArg A B EA EB t x)) = @convertVar A B EA EB t (interp_arg x).
    Proof. induction x as [t i]; induction t, EA, EB; simpl; reflexivity. Qed.

    Lemma ZToRange_binop_correct : forall {n tx ty tz} (op: binop tx ty tz) (x: @arg _ tx) (y: @arg _ ty) e,
        check (t := tz) (convertZToWordRangeOpt n (LetBinop op x y e))
      -> zOp op (interp_arg x) (interp_arg y) =
          varRangeToZ (rangeOp (n := n) op (varZToRange (interp_arg x)) (varZToRange (interp_arg y))).
    Proof.
      intros until e; intro H.
      unfold convertZToWordRangeOpt, convertExpr, check, rangeOp in H.
      repeat rewrite interp_arg_convert in H; simpl in H.
      destruct H as [H H0]; clear H0.

      induction op; unfold zOp, varRangeToZ, rangeOp.

      - simpl; unfold getUpperBoundOpt.
        repeat rewrite interp_arg_convert in H; simpl in H.
        unfold id, makeRange in *.
        repeat match goal with
        | [|- context[Z_le_dec ?a ?b] ] => destruct (Z_le_dec a b)
        | [|- context[Z_lt_dec ?a ?b] ] => destruct (Z_lt_dec a b)
        end; simpl in H; intuition.

        rewrite applyBinOp_constr_spec; simpl.
        rewrite applyBinOp_constr_spec in H; simpl in H.
        destruct (overflows n _); [intuition|]; simpl.

    Admitted.

    Lemma ZToWord_binop_correct : forall {n tx ty tz} (op: binop tx ty tz) (x: @arg _ tx) (y: @arg _ ty) e,
        check (t := tz) (convertZToWordRangeOpt n (LetBinop op x y e))
      -> zOp op (interp_arg x) (interp_arg y) =
          varWordToZ (wordOp (n := n) op (varZToWord (interp_arg x)) (varZToWord (interp_arg y))).
    Proof.
      intros until e; intro H.
      unfold convertZToWordRangeOpt, convertExpr, check, rangeOp in H.
      repeat rewrite interp_arg_convert in H; simpl in H.
      destruct H as [H H0]; clear H0.

      induction op; unfold zOp, varRangeToZ, rangeOp.

      - simpl; unfold getUpperBoundOpt; simpl in H.
        rewrite applyBinOp_constr_spec in H; simpl in H.

        unfold makeRange in H.
        repeat match goal with
        | [ H : context[Z_le_dec ?a ?b] |- _ ] => destruct (Z_le_dec a b)
        | [ H : context[Z_lt_dec ?a ?b] |- _ ] => destruct (Z_lt_dec a b)
        end; simpl in H; intuition.

        unfold id in *.
        destruct (QhasmUtil.overflows n (Z.to_N (interp_arg x) + Z.to_N (interp_arg y)));
            [intuition|]; simpl.

        rewrite <- wordize_plus.

        + repeat rewrite wordToN_NToWord; try assumption;
            try abstract (apply N2Z.inj_lt; rewrite Z2N.id; assumption).

          rewrite N2Z.inj_add.
          repeat rewrite Z2N.id; try assumption.
          reflexivity.

        + repeat rewrite wordToN_NToWord; [assumption | |];
              rewrite N2Z.inj_lt;
              repeat rewrite Z2N.id;
              try assumption.
    Admitted.

    (* Main correctness guarantee *)

    Lemma RangeInterp_correct: forall {n t} (E: @expr Z t),
        check (convertZToWordRangeOpt n E)
      -> typeMap (fun x => NToWord n (Z.to_N x)) (zinterp E) = wordInterp (convertZToWord n E).
    Proof.
      intros n t E S.
      unfold rangeInterp, convertZToWordRangeOpt, zinterp,
             convertZToWord, wordInterp.

      induction E as [tx ty tz op x y z|]; simpl; try reflexivity.

      - rewrite H.

        + repeat f_equal; unfold id in *.
          destruct x as [tx' x], y as [ty' y]; simpl.

          destruct S as [S0 S1].

          pose proof (ZToWord_binop_correct (n := n) op (Arg _ x) (Arg _ y)) as C;
            unfold zOp, wordOp, varWordToZ, varZToWord in C; simpl in C.

          induction op; rewrite (C (fun _ => Return (Arg TT 0%Z)));
            repeat f_equal; split; try assumption; simpl; unfold makeRange;

            repeat match goal with
            | [|- context[Z_le_dec ?a ?b] ] => destruct (Z_le_dec a b)
            | [|- context[Z_lt_dec ?a ?b] ] => destruct (Z_lt_dec a b)
            end;

            simpl; clear H S0 S1 C e; unfold id in *;
            pose proof (Npow2_gt0 n) as H;
            rewrite N2Z.inj_lt in H; simpl in H; intuition;

            match goal with
            | [A: (0 <= 0)%Z -> False |- _] =>
              apply A; cbv; intro Q; inversion Q
            end.

        + destruct S as [S0 S1]; unfold convertZToWordRangeOpt.

          replace (interp_binop op _ _)
             with (varRangeToZ (rangeOp op
                    (rangeArg (@convertArg _ _ ZEvaluable (@WordRangeOptEvaluable n) _ x))
                    (rangeArg (@convertArg _ _ ZEvaluable (@WordRangeOptEvaluable n) _ y))));
            [unfold varRangeToZ, rangeArg; assumption | clear S1].

          destruct x as [tx' x], y as [ty' y]; simpl.

          pose proof (ZToRange_binop_correct (n := n) op (Arg _ x) (Arg _ y)) as C;
            unfold zOp, wordOp, varZToRange, varRangeToZ, convertZToWordRangeOpt in *;
            simpl in C.

          induction op; rewrite C with (e := fun _ => Return (Arg TT 0%Z));
            split; try assumption; simpl; unfold makeRange;
            repeat match goal with
            | [|- context[Z_le_dec ?a ?b] ] => destruct (Z_le_dec a b)
            | [|- context[Z_lt_dec ?a ?b] ] => destruct (Z_lt_dec a b)
            end;

            simpl; clear H S0 C e; unfold id in *;
            pose proof (Npow2_gt0 n) as H;
            rewrite N2Z.inj_lt in H; simpl in H; intuition;

            match goal with
            | [A: (0 <= 0)%Z -> False |- _] =>
              apply A; cbv; intro Q; inversion Q
            end.


      - simpl in S.
        induction a; simpl in *; try reflexivity.
    Qed.
  End Correctness.
End LLConversions.

Section ConversionTest.
  Import HL HLConversions.

  Fixpoint keepAddingOne {var} (x : @expr Z var TT) (n : nat) : @expr Z var TT :=
    match n with
    | O => x
    | S n' => Let (Binop OPadd x (Const 1%Z)) (fun y => keepAddingOne (Var y) n')
    end.

  Definition KeepAddingOne (n : nat) : Expr (T := Z) TT :=
    fun var => keepAddingOne (Const 1%Z) n.

  Definition testCase := Eval vm_compute in KeepAddingOne 4000.

  Eval vm_compute in RangeInterp (ZToRange 0 testCase).
  Eval vm_compute in RangeInterp (ZToRange 1 testCase).
  Eval vm_compute in RangeInterp (ZToRange 10 testCase).
  Eval vm_compute in RangeInterp (ZToRange 32 testCase).
  Eval vm_compute in RangeInterp (ZToRange 64 testCase).
  Eval vm_compute in RangeInterp (ZToRange 128 testCase).

  Definition nefarious : Expr (T := Z) TT :=
    fun var => Let (Binop OPadd (Const 10%Z) (Const 20%Z))
                   (fun y => Binop OPmul (Var y) (Const 0%Z)).

  Eval vm_compute in RangeInterp (ZToRange 0 nefarious).
  Eval vm_compute in RangeInterp (ZToRange 1 nefarious).
  Eval vm_compute in RangeInterp (ZToRange 4 nefarious).
  Eval vm_compute in RangeInterp (ZToRange 5 nefarious).
  Eval vm_compute in RangeInterp (ZToRange 32 nefarious).
  Eval vm_compute in RangeInterp (ZToRange 64 nefarious).
  Eval vm_compute in RangeInterp (ZToRange 128 nefarious).
End ConversionTest.
