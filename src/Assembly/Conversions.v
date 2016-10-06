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

  Fixpoint mapVar {A: Type} {t V0 V1} (f: forall t, V0 t -> V1 t) (g: forall t, V1 t -> V0 t) (a: expr (T := A) (var := V0) t): expr (T := A) (var := V1) t :=
    match a with
    | Const x => Const x
    | Var t x => Var (f _ x)
    | Binop t1 t2 t3 o e1 e2 => Binop o (mapVar f g e1) (mapVar f g e2)
    | Let tx e tC h => Let (mapVar f g e) (fun x => mapVar f g (h (g _ x)))
    | Pair t1 e1 t2 e2 => Pair (mapVar f g e1) (mapVar f g e2)
    | MatchPair t1 t2 e tC h => MatchPair (mapVar f g e) (fun x y => mapVar f g (h (g _ x) (g _ y)))
    end.

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

  Fixpoint convertArg {A B: Type} {EA: Evaluable A} {EB: Evaluable B} t {struct t}: @arg A A t -> @arg B B t :=
    match t as t' return @arg A A t' -> @arg B B t' with
    | TT => fun x =>
      match x with
      | Const c => Const (convertVar (t := TT) c)
      | Var v => Var (convertVar (t := TT) v)
      end
    | Prod t0 t1 => fun x =>
      match (match_arg_Prod x) with
      | (a, b) => Pair ((convertArg t0) a) ((convertArg t1) b)
      end
    end.

  Arguments convertArg [_ _ _ _ _ _].

  Fixpoint convertExpr {A B: Type} {EA: Evaluable A} {EB: Evaluable B} {t} (a: expr (T := A) t): expr (T := B) t :=
    match a with
    | LetBinop _ _ out op a b _ eC =>
      LetBinop (T := B) op (convertArg a) (convertArg b) (fun x: (arg out) => convertExpr (eC (convertArg x)))
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

    Definition rangeArg {n t} (x: @arg (@WordRangeOpt n) (@WordRangeOpt n) t) := @interp_arg _ _ x.

    Definition wordArg {n t} (x: @arg (word n) (word n) t) := @interp_arg _ _ x.

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

    Fixpoint check {n t} (e : @expr (@WordRangeOpt n) (@WordRangeOpt n) t): Prop :=
      match e with
      | LetBinop ta tb tc op a b _ eC =>
          (@checkVar n tc (rangeOp op (interp_arg a) (interp_arg b)))
        /\ (check (eC (uninterp_arg (rangeOp op (interp_arg a) (interp_arg b)))))
      | Return _ a => checkVar (interp_arg a)
      end.

    (* Utility Lemmas *)

    Lemma convertArg_interp: forall {A B t} {EA: Evaluable A} {EB: Evaluable B} (x: @arg A A t),
        (interp_arg (@convertArg A B EA EB t x)) = @convertVar A B EA EB t (interp_arg x).
    Proof.
      induction x as [| |t0 t1 i0 i1]; [reflexivity|reflexivity|].
      induction EA, EB; simpl; f_equal; assumption.
    Qed.

    Lemma convertArg_var: forall {A B EA EB t} (x: @interp_type A t),
        @convertArg A B EA EB t (uninterp_arg x) = uninterp_arg (@convertVar A B EA EB t x).
    Proof.
      induction t as [|t0 IHt_0 t1 IHt_1]; simpl; intros; [reflexivity|].
      induction x as [a b]; simpl; f_equal;
        induction t0 as [|t0a IHt0_0 t0b IHt0_1],
                  t1 as [|t1a IHt1_0]; simpl in *;
        try rewrite IHt_0;
        try rewrite IHt_1;
        reflexivity.
    Qed.

    Lemma ZToRange_binop_correct : forall {n tx ty tz} (op: binop tx ty tz) (x: arg tx) (y: arg ty) e,
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

    Lemma ZToWord_binop_correct : forall {n tx ty tz} (op: binop tx ty tz) (x: arg tx) (y: arg ty) e,
        check (t := tz) (convertZToWordRangeOpt n (LetBinop op x y e))
      -> zOp op (interp_arg x) (interp_arg y) =
          varWordToZ (wordOp (n := n) op (varZToWord (interp_arg x)) (varZToWord (interp_arg y))).
    Proof.
      intros until e; intro H.
      unfold convertZToWordRangeOpt, convertExpr, check, rangeOp in H.
      repeat rewrite convertArg_interp in H; simpl in H.
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

    Lemma RangeInterp_correct: forall {n t} (E: expr t),
         check (convertZToWordRangeOpt n E)
      -> typeMap (fun x => NToWord n (Z.to_N x)) (zinterp E) = wordInterp (convertZToWord n E).
    Proof.
      intros n t E S.
      unfold rangeInterp, convertZToWordRangeOpt, zinterp,
             convertZToWord, wordInterp.

      induction E as [tx ty tz op x y z|]; simpl; try reflexivity.

      - rewrite H.

        + destruct S as [S0 S1]; unfold convertZToWordRangeOpt in *.
          repeat f_equal; unfold id in *.

          pose proof (ZToWord_binop_correct (n := n) op x y) as C;
            unfold zOp, wordOp, varWordToZ, varZToWord in C;
            simpl in C.

          repeat rewrite convertArg_var, convertArg_interp; f_equal.
          rewrite convertArg_var, convertArg_interp in C.

          induction op; rewrite (C (fun _ => Return (Const 0%Z))); clear C H;
            repeat rewrite convertArg_interp; repeat f_equal; try reflexivity;
            split; simpl in *;
            unfold rangeOp, uninterp_arg, makeRange, applyBinOp, id in *;

            repeat match goal with
            | [|- context[Z_le_dec ?A ?B] ] => destruct (Z_le_dec A B)
            | [|- context[Z_lt_dec ?A ?B] ] => destruct (Z_lt_dec A B)
            end; clear S0 S1 e; simpl;

            repeat match goal with
            | [|- context[Nge_dec ?A ?B] ] => destruct (Nge_dec A B)
            | [|- context[overflows ?N ?X] ] => destruct (overflows N X)
            end; simpl; intuition;

            try match goal with
            | [A: (0 <= 0)%Z -> False |- _] =>
              apply A; cbv; intro Q; inversion Q
            end;

            admit.

        + destruct S as [S0 S1]; unfold convertZToWordRangeOpt.

          replace (interp_binop op _ _)
             with (varRangeToZ (rangeOp op
                    (rangeArg (@convertArg _ _ ZEvaluable (@WordRangeOptEvaluable n) _ x))
                    (rangeArg (@convertArg _ _ ZEvaluable (@WordRangeOptEvaluable n) _ y))));
            [unfold varRangeToZ, rangeArg; admit | clear S1].

          pose proof (ZToRange_binop_correct (n := n) op x y) as C;
            unfold zOp, wordOp, varZToRange, varRangeToZ, convertZToWordRangeOpt in *;
            simpl in C.

          induction op; rewrite C with (e := fun _ => Return (Const 0%Z)); admit.
          (* TODO(rsloan): why is this so slow?
            try split; try assumption; simpl; unfold makeRange;
            repeat match goal with
            | [|- context[Z_le_dec ?a ?b] ] => destruct (Z_le_dec a b)
            | [|- context[Z_lt_dec ?a ?b] ] => destruct (Z_lt_dec a b)
            end;

            simpl; clear H S0 C e; unfold id in *;
            pose proof (Npow2_gt0 n) as H;
            rewrite N2Z.inj_lt in H; simpl in H; intuition;

            try match goal with
            | [A: (0 <= 0)%Z -> False |- _] =>
              apply A; cbv; intro Q; inversion Q
            end. *)

      - simpl in S.
        induction a as [| |t0 t1 a0 IHa0 a1 IHa1]; simpl in *; try reflexivity.
        destruct S; rewrite IHa0, IHa1; try reflexivity; assumption.
    Admitted.
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
