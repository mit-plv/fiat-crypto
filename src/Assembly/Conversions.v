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

Require Import Coq.NArith.Nnat Coq.NArith.Ndigits.

Require Import Coq.Bool.Sumbool.

Definition typeMap {A B t} (f: A -> B) (x: @interp_type A t): @interp_type B t.
Proof.
  induction t; [refine (f x)|].
  destruct x as [x1 x2].
  refine (IHt1 x1, IHt2 x2).
Defined.

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

  Definition convertZToBounded {t} n v a :=
    @convertExpr Z (option (@BoundedWord n))
                 ZEvaluable (@BoundedEvaluable n) t v a.

  Definition ZToWord {t} n (a: @Expr Z t): @Expr (word n) t :=
    fun v => convertZToWord n v (a v).

  Definition ZToRange {t} n (a: @Expr Z t): @Expr (option (@BoundedWord n)) t :=
    fun v => convertZToBounded n v (a v).

  Definition BInterp {n t} E: @interp_type (option (@BoundedWord n)) t :=
    @Interp (option (@BoundedWord n)) (@BoundedEvaluable n) t E.

  Example example_Expr : Expr TT := fun var => (
    Let (Const 7) (fun a =>
      Let (Let (Binop OPadd (Var a) (Var a)) (fun b => Pair (Var b) (Var b))) (fun p =>
        MatchPair (Var p) (fun x y =>
          Binop OPadd (Var x) (Var y)))))%Z.

  Example interp_example_range :
    option_map high (BInterp (ZToRange 32 example_Expr)) = Some 28%N.
  Proof. cbv; reflexivity. Qed.
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

  Definition convertZToBounded {t} n a :=
    @convertExpr Z (option (@BoundedWord n)) ZEvaluable (@BoundedEvaluable n) t a.

  Definition zinterp {t} E := @interp Z ZEvaluable t E.

  Definition wordInterp {n t} E := @interp (word n) (@WordEvaluable n) t E.

  Definition boundedInterp {n t} E: @interp_type (option (@BoundedWord n)) t :=
    @interp (option (@BoundedWord n)) (@BoundedEvaluable n) t E.

  Section Correctness.
    (* Aliases to make the proofs easier to read. *)

    Definition varZToBounded {n t} (v: @interp_type Z t): @interp_type (option (@BoundedWord n)) t :=
      @convertVar Z (option (@BoundedWord n)) ZEvaluable BoundedEvaluable t v.

    Definition varBoundedToZ {n t} (v: @interp_type _ t): @interp_type Z t :=
      @convertVar (option (@BoundedWord n)) Z BoundedEvaluable ZEvaluable t v.

    Definition varZToWord {n t} (v: @interp_type Z t): @interp_type (@word n) t :=
      @convertVar Z (@word n) ZEvaluable (@WordEvaluable n) t v.

    Definition varWordToZ {n t} (v: @interp_type (@word n) t): @interp_type Z t :=
      @convertVar (word n) Z (@WordEvaluable n) ZEvaluable t v.

    Definition zOp {tx ty tz: type} (op: binop tx ty tz)
               (x: @interp_type Z tx) (y: @interp_type Z ty): @interp_type Z tz :=
      @interp_binop Z ZEvaluable _ _ _ op x y.

    Definition wOp {n} {tx ty tz: type} (op: binop tx ty tz)
               (x: @interp_type _ tx) (y: @interp_type _ ty): @interp_type _ tz :=
      @interp_binop (word n) (@WordEvaluable n) _ _ _ op x y.

    Definition bOp {n} {tx ty tz: type} (op: binop tx ty tz)
               (x: @interp_type _ tx) (y: @interp_type _ ty): @interp_type _ tz :=
      @interp_binop (option (@BoundedWord n)) BoundedEvaluable _ _ _ op x y.

    Definition boundedArg {n t} (x: @arg (option (@BoundedWord n)) (option (@BoundedWord n)) t) :=
      @interp_arg _ _ x.

    Definition wordArg {n t} (x: @arg (word n) (word n) t) := @interp_arg _ _ x.

    (* BoundedWord-based Bounds-checking fixpoint *)

    Definition getBounds {n t} T (E: Evaluable T) (e : @expr T T t): @interp_type (option (@BoundedWord n)) t :=
      interp (E := BoundedEvaluable) (@convertExpr T (option (@BoundedWord n)) E BoundedEvaluable t e).

    Fixpoint bcheck' {n t} (x: @interp_type (option (@BoundedWord n)) t) :=
      match t as t' return (interp_type t') -> bool with
      | TT => fun x' =>
        match x' with
        | Some _ => true
        | None => false
        end
      | Prod t0 t1 => fun x' =>
        match x' with
        | (x0, x1) => andb (bcheck' x0) (bcheck' x1)
        end
      end x.

    Definition bcheck {n t} T (E: Evaluable T) (e : @expr T T t): bool := bcheck' (n := n) (getBounds T E e).

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

    Ltac kill_just n :=
      match goal with
      | [|- context[just ?x] ] =>
        let Hvalue := fresh in let Hvalue' := fresh in
        let Hlow := fresh in let Hlow' := fresh in
        let Hhigh := fresh in let Hhigh' := fresh in
        let Hnone := fresh in let Hnone' := fresh in

        let B := fresh in

        pose proof (just_value_spec (n := n) x) as Hvalue;
        pose proof (just_low_spec (n := n) x) as Hlow;
        pose proof (just_high_spec (n := n) x) as Hhigh;
        pose proof (just_None_spec (n := n) x) as Hnone;

        destruct (just x);

        try pose proof (Hlow _ eq_refl) as Hlow';
        try pose proof (Hvalue _ eq_refl) as Hvalue';
        try pose proof (Hhigh _ eq_refl) as Hhigh';
        try pose proof (Hnone eq_refl) as Hnone';

        clear Hlow Hhigh Hvalue Hnone
      end.

    Ltac kill_dec :=
      repeat match goal with
      | [|- context[Nge_dec ?a ?b] ] => destruct (Nge_dec a b)
      | [H : context[Nge_dec ?a ?b] |- _ ] => destruct (Nge_dec a b)
      end.

    Lemma ZToBounded_binop_correct : forall {n tx ty tz} (op: binop tx ty tz) (x: arg tx) (y: arg ty) e,
        bcheck (n := n) (t := tz) Z ZEvaluable (LetBinop op x y e) = true
      -> zOp op (interp_arg x) (interp_arg y) =
          varBoundedToZ (bOp (n := n) op (varZToBounded (interp_arg x)) (varZToBounded (interp_arg y))).
    Proof.
    Admitted.

    Lemma ZToWord_binop_correct : forall {n tx ty tz} (op: binop tx ty tz) (x: arg tx) (y: arg ty) e,
        bcheck (n := n) (t := tz) Z ZEvaluable (LetBinop op x y e) = true
      -> zOp op (interp_arg x) (interp_arg y) =
          varWordToZ (wOp (n := n) op (varZToWord (interp_arg x)) (varZToWord (interp_arg y))).
    Proof.
    Admitted.

    Lemma just_zero: forall n, exists x, just (n := n) 0 = Some x.
    Proof.
    Admitted.

    (* Main correctness guarantee *)

    Lemma RangeInterp_bounded_spec: forall {n t} (E: expr t),
        bcheck (n := n) Z ZEvaluable E = true
      -> typeMap (fun x => NToWord n (Z.to_N x)) (zinterp E) = wordInterp (convertZToWord n E).
    Proof.
      intros n t E S.
      unfold convertZToBounded, zinterp, convertZToWord, wordInterp.

      induction E as [tx ty tz op x y z|]; simpl; try reflexivity.

      - repeat rewrite convertArg_var in *.
        repeat rewrite convertArg_interp in *.

        rewrite H; clear H; repeat f_equal.

        + pose proof (ZToWord_binop_correct (n := n) op x y) as C;
            unfold zOp, wOp, varWordToZ, varZToWord in C;
            simpl in C.

          induction op; apply (C (fun _ => Return (Const 0%Z))); clear C;
            unfold bcheck, getBounds; simpl;
            destruct (@just_zero n) as [j p]; rewrite p; reflexivity.

        + unfold bcheck, getBounds in *; simpl in *.
          replace (interp_binop op _ _)
             with (varBoundedToZ (n := n) (bOp (n := n) op
                    (boundedArg (@convertArg _ _ ZEvaluable (@BoundedEvaluable n) _ x))
                    (boundedArg (@convertArg _ _ ZEvaluable (@BoundedEvaluable n) _ y))));
            [unfold varBoundedToZ, boundedArg; rewrite <- convertArg_var; assumption |].

          pose proof (ZToBounded_binop_correct (n := n) op x y) as C;
            unfold boundedArg, zOp, wOp, varZToBounded,
                   varBoundedToZ, convertZToBounded in *;
            simpl in C.

          repeat rewrite convertArg_interp; symmetry.

          induction op; apply (C (fun _ => Return (Const 0%Z))); clear C;
            unfold bcheck, getBounds; simpl;
            destruct (@just_zero n) as [j p]; rewrite p; reflexivity.

      - simpl in S.
        induction a as [| |t0 t1 a0 IHa0 a1 IHa1]; simpl in *; try reflexivity.
        apply andb_true_iff in S; destruct S; rewrite IHa0, IHa1; try reflexivity; assumption.
    Qed.
  End Correctness.

  Section FastCorrect.
    Context {n: nat}.

    Record RangeWithValue := rwv {
      low: N;
      value: N;
      high: N;
    }.

    Definition rwv_app {rangeF wordF}
      (op: @validBinaryWordOp n rangeF wordF)
      (X Y: RangeWithValue): option (RangeWithValue) :=
      omap (rangeF (range N (low X) (high X)) (range N (low Y) (high Y))) (fun r' =>
        match r' with
        | range l h => Some (
          rwv l (wordToN (wordF (NToWord n (value X)) (NToWord n (value Y)))) h)
        end).

    Definition proj (x: RangeWithValue): Range N := range N (low x) (high x).

    Definition from_range (x: Range N): RangeWithValue :=
      match x with
      | range l h => rwv l h h
      end.

    Instance RWVEval : Evaluable (option RangeWithValue) := {
      ezero := None;

      toT := fun x => 
        if (Nge_dec (N.pred (Npow2 n)) (Z.to_N x))
        then Some (rwv (Z.to_N x) (Z.to_N x) (Z.to_N x))
        else None;

      fromT := fun x => orElse 0%Z (option_map Z.of_N (option_map value x));

      eadd := fun x y => omap x (fun X => omap y (fun Y =>
        rwv_app range_add_valid X Y));

      esub := fun x y => omap x (fun X => omap y (fun Y =>
        rwv_app range_sub_valid X Y));

      emul := fun x y => omap x (fun X => omap y (fun Y =>
        rwv_app range_mul_valid X Y));

      eshiftr := fun x y => omap x (fun X => omap y (fun Y =>
        rwv_app range_shiftr_valid X Y));

      eand := fun x y => omap x (fun X => omap y (fun Y =>
        rwv_app range_and_valid X Y));

      eltb := fun x y =>
        match (x, y) with
        | (Some (rwv xlow xv xhigh), Some (rwv ylow yv yhigh)) =>
            N.ltb xv yv

        | _ => false 
        end;

      eeqb := fun x y =>
        match (x, y) with
        | (Some (rwv xlow xv xhigh), Some (rwv ylow yv yhigh)) =>
            andb (andb (N.eqb xlow ylow) (N.eqb xhigh yhigh)) (N.eqb xv yv)

        | _ => false
        end;
    }.

    Definition getRWV {t} T (E: Evaluable T) (e : @expr T T t): @interp_type (option RangeWithValue) t :=
      interp (@convertExpr T (option RangeWithValue) E RWVEval t e).

    Definition getRanges {t} T (E: Evaluable T) (e : @expr T T t): @interp_type (option (Range N)) t :=
      typeMap (option_map proj) (getRWV T E e).

    Fixpoint check' {t} (x: @interp_type (option RangeWithValue) t) :=
      match t as t' return (interp_type t') -> bool with
      | TT => fun x' =>
        match x' with
        | Some _ => true
        | None => false
        end
      | Prod t0 t1 => fun x' =>
        match x' with
        | (x0, x1) => andb (check' x0) (check' x1)
        end
      end x.

    Definition check {t} T (E: Evaluable T) (e : @expr T T t): bool :=
      check' (getRWV T E e).

    Ltac kill_dec :=
      repeat match goal with
      | [|- context[Nge_dec ?a ?b] ] => destruct (Nge_dec a b)
      | [H : context[Nge_dec ?a ?b] |- _ ] => destruct (Nge_dec a b)
      end.

    Lemma check_spec: forall {t} (E: expr t),
         check Z ZEvaluable E = true
      -> bcheck (n := n) Z ZEvaluable E = true.
    Proof.
      intros t E H.
      induction E as [tx ty tz op x y z eC IH| t a].

      - unfold bcheck, getBounds, check, getRWV in *.
        apply IH; simpl in *; revert H; clear IH.
        repeat rewrite convertArg_interp.
        generalize (interp_arg x) as X; intro X; clear x.
        generalize (interp_arg y) as Y; intro Y; clear y.
        intro H; rewrite <- H; clear H; repeat f_equal.

        induction op; unfold ZEvaluable, BoundedEvaluable, RWVEval, just in *;
          simpl in *; kill_dec; simpl in *; try reflexivity;
          try rewrite (bapp_value_spec _ _ _ (fun x => Z.of_N (@wordToN n x)));
          unfold vapp, rapp, rwv_app, overflows in *; kill_dec; simpl in *;
          try reflexivity; try nomega.

      - induction a as [c|v|t0 t1 a0 IHa0 a1 IHa1];
          unfold bcheck, getBounds, check, getRWV in *; simpl in *; unfold just.

        + induction (Nge_dec (N.pred (Npow2 n)) (Z.to_N c));
            simpl in *; [reflexivity|inversion H].

        + induction (Nge_dec (N.pred (Npow2 n)) (Z.to_N v));
            simpl in *; [reflexivity|inversion H].

        + apply andb_true_iff; apply andb_true_iff in H;
            destruct H as [H0 H1]; split;
            [apply IHa0|apply IHa1]; assumption.
    Qed.

    Lemma RangeInterp_spec: forall {t} (E: expr t),
        check Z ZEvaluable E = true
      -> typeMap (fun x => NToWord n (Z.to_N x)) (zinterp E) = wordInterp (convertZToWord n E).
    Proof.
      intros.
      apply RangeInterp_bounded_spec.
      apply check_spec.
      assumption.
    Qed.

    Lemma getRanges_spec: forall {t} T E (e: @expr T T t),
      getRanges T E e = typeMap (t := t) (option_map (toRange (n := n))) (getBounds T E e).
    Proof.
      intros; induction e as [tx ty tz op x y z eC IH| t a];
        unfold getRanges, getRWV, option_map, toRange, getBounds in *;
        simpl in *.

      - rewrite <- IH; clear IH; simpl.
        repeat f_equal.
        repeat rewrite (convertArg_interp x); generalize (interp_arg x) as X; intro; clear x.
        repeat rewrite (convertArg_interp y); generalize (interp_arg y) as Y; intro; clear y.

        (* induction op;
          unfold RWVEval, BoundedEvaluable, bapp, rwv_app,
                 overflows, omap, option_map, just; simpl;
          kill_dec; simpl in *. *)
    Admitted.
  End FastCorrect.
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

  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 0 testCase))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 1 testCase))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 10 testCase))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 32 testCase))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 64 testCase))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 128 testCase))).

  Definition nefarious : Expr (T := Z) TT :=
    fun var => Let (Binop OPadd (Const 10%Z) (Const 20%Z))
                   (fun y => Binop OPmul (Var y) (Const 0%Z)).

  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 0 nefarious))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 1 nefarious))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 4 nefarious))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 5 nefarious))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 32 nefarious))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 64 nefarious))).
  Eval vm_compute in (typeMap (option_map toRange) (BInterp (ZToRange 128 nefarious))).
End ConversionTest.
