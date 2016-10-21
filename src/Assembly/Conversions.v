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

  Definition convertZToWord {t} n v a :=
    @convertExpr Z (word n) (@ZEvaluable n) (@WordEvaluable n) t v a.

  Definition convertZToBounded {t} n v a :=
    @convertExpr Z (option (@BoundedWord n))
                 (@ZEvaluable n) (@BoundedEvaluable n) t v a.

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
    option_map bw_high (BInterp (ZToRange 32 example_Expr)) = Some 28%N.
  Proof. cbv; reflexivity. Qed.
End HLConversions.

Module LLConversions.
  Import LL.

  Section VarConv.
    Context {A B: Type} {EA: Evaluable A} {EB: Evaluable B}.

    Definition convertVar {t} (a: interp_type (T := A) t): interp_type (T := B) t.
    Proof.
      induction t as [| t3 IHt1 t4 IHt2].

      - refine (@toT B EB (@fromT A EA _)); assumption.

      - destruct a as [a1 a2]; constructor;
          [exact (IHt1 a1) | exact (IHt2 a2)].
    Defined.
  End VarConv.

  Section ArgConv.
    Context {A B: Type} {EA: Evaluable A} {EB: Evaluable B}.

    Fixpoint convertArg {V} t {struct t}: @arg A V t -> @arg B V t :=
      match t as t' return @arg A V t' -> @arg B V t' with
      | TT => fun x =>
        match x with
        | Const c => Const (convertVar (t := TT) c)
        | Var v => Var v
        end
      | Prod t0 t1 => fun x =>
        match (match_arg_Prod x) with
        | (a, b) => Pair ((convertArg t0) a) ((convertArg t1) b)
        end
      end.
  End ArgConv.

  Section ExprConv.
    Context {A B: Type} {EA: Evaluable A} {EB: Evaluable B}.

    Fixpoint convertExpr {t V} (a: @expr A V t): @expr B V t :=
        match a with
        | LetBinop _ _ out op a b _ eC =>
          LetBinop (T := B) op (convertArg _ a) (convertArg _ b) (fun x: (arg out) =>
            convertExpr (eC (convertArg _ x)))

        | Return _ a => Return (convertArg _ a)
        end.
  End ExprConv.

  Section Defaults.
    Context {t: type} {n: nat}.

    Definition Word := word n.
    Definition Bounded := option (@BoundedWord n).
    Definition RWV := option (RangeWithValue).

    Transparent Word Bounded RWV.

    Instance RWVEvaluable' : Evaluable RWV := @RWVEvaluable n.
    Instance ZEvaluable' : Evaluable Z := @ZEvaluable n.

    Existing Instance ZEvaluable'.
    Existing Instance WordEvaluable.
    Existing Instance BoundedEvaluable.
    Existing Instance RWVEvaluable'.

    Definition ZToWord a := @convertExpr Z Word _ _ t a.
    Definition ZToBounded a := @convertExpr Z Bounded _ _ t a.
    Definition ZToRWV a := @convertExpr Z RWV _ _ t a.

    Definition varZToWord a := @convertVar Z Word _ _ t a.
    Definition varZToBounded a := @convertVar Z Bounded _ _ t a.
    Definition varZToRWV a := @convertVar Z RWV _ _ t a.

    Definition varWordToZ a := @convertVar Word Z _ _ t a.
    Definition varBoundedToZ a := @convertVar Bounded Z _ _ t a.
    Definition varRWVToZ a := @convertVar RWV Z _ _ t a.

    Definition zinterp E := @interp Z _ t E.
    Definition wordInterp E := @interp' Word _ _ t (fun x => NToWord n (Z.to_N x)) E.
    Definition boundedInterp E := @interp Bounded _ t E.
    Definition rwvInterp E := @interp RWV _ t E.

    Section Operations.
      Context {tx ty tz: type}.

      Definition opZ (op: binop tx ty tz)
                 (x: @interp_type Z tx) (y: @interp_type Z ty): @interp_type Z tz :=
        @interp_binop Z _ _ _ _ op x y.

      Definition opBounded (op: binop tx ty tz)
                 (x: @interp_type Bounded tx) (y: @interp_type Bounded ty): @interp_type Bounded tz :=
        @interp_binop Bounded _ _ _ _ op x y.

      Definition opWord (op: binop tx ty tz)
                 (x: @interp_type Word tx) (y: @interp_type Word ty): @interp_type Word tz :=
        @interp_binop Word _ _ _ _ op x y.

      Definition opRWV (op: binop tx ty tz)
                 (x: @interp_type RWV tx) (y: @interp_type RWV ty): @interp_type RWV tz :=
        @interp_binop RWV _ _ _ _ op x y.
    End Operations.
  End Defaults.

  Section Correctness.
    Context {n: nat}.

    Definition W := (word n).
    Definition B := (@Bounded n).
    Definition R := (option RangeWithValue).

    Instance RE : Evaluable R := @RWVEvaluable n.
    Instance ZE : Evaluable Z := @ZEvaluable n.
    Instance WE : Evaluable W := @WordEvaluable n.
    Instance BE : Evaluable B := @BoundedEvaluable n.

    Transparent ZE RE WE BE W B R.

    Existing Instance ZE.
    Existing Instance RE.
    Existing Instance WE.
    Existing Instance BE.

    Ltac kill_dec :=
      repeat match goal with
      | [|- context[Nge_dec ?a ?b] ] => destruct (Nge_dec a b)
      | [H : context[Nge_dec ?a ?b] |- _ ] => destruct (Nge_dec a b)
      end.

    Section BoundsChecking.
      Context {T: Type} {E: Evaluable T}.

      Definition boundVarInterp := fun x => bwFromRWV (n := n) (rwv 0%N (Z.to_N x) (Z.to_N x)).

      Definition getBounds {t} (e : @expr T Z t): @interp_type B t :=
        interp' boundVarInterp (@convertExpr T B _ _ t _ e).

      Fixpoint bcheck' {t} (x: @interp_type B t) :=
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

      Definition bcheck {t} (e : expr t): bool := bcheck' (getBounds e).
    End BoundsChecking.

    Section UtilityLemmas.
      Context {A B} {EA: Evaluable A} {EB: Evaluable B}.

      Lemma convertArg_interp' : forall {t V} f (x: @arg A V t),
          (interp_arg' (fun z => toT (fromT (f z))) (@convertArg A B EA EB _ t x))
            = @convertVar A B EA EB t (interp_arg' f x).
      Proof.
        intros.
        induction x as [| |t0 t1 i0 i1]; simpl; [reflexivity|reflexivity|].
        induction EA, EB; simpl; f_equal; assumption.
      Qed.

      Lemma convertArg_var: forall {A B EA EB t} V (x: @interp_type A t),
          @convertArg A B EA EB V t (uninterp_arg x) = uninterp_arg (var := V) (@convertVar A B EA EB t x).
      Proof.
        induction t as [|t0 IHt_0 t1 IHt_1]; simpl; intros; [reflexivity|].
        induction x as [a b]; simpl; f_equal;
            induction t0 as [|t0a IHt0_0 t0b IHt0_1],
                    t1 as [|t1a IHt1_0]; simpl in *;
            try rewrite IHt_0;
            try rewrite IHt_1;
            reflexivity.
      Qed.

      Lemma ZToBounded_binop_correct : forall {tx ty tz} (op: binop tx ty tz) (x: @arg Z Z tx) (y: @arg Z Z ty) e,
          bcheck (t := tz) (LetBinop op x y e) = true
        -> opZ (n := n) op (interp_arg x) (interp_arg y) =
          varBoundedToZ (n := n) (opBounded op
             (interp_arg' boundVarInterp (convertArg _ x))
             (interp_arg' boundVarInterp (convertArg _ y))).
      Proof.
      Admitted.

      Lemma ZToWord_binop_correct : forall {tx ty tz} (op: binop tx ty tz) (x: arg tx) (y: arg ty) e,
          bcheck (t := tz) (LetBinop op x y e) = true
        -> opZ (n := n) op (interp_arg x) (interp_arg y) =
            varWordToZ (opWord (n := n) op (varZToWord (interp_arg x)) (varZToWord (interp_arg y))).
      Proof.
      Admitted.

      Lemma roundTrip_0 : @toT Correctness.B BE (@fromT Z ZE 0%Z) <> None.
      Proof.
        intros; unfold toT, fromT, BE, ZE, BoundedEvaluable, ZEvaluable, bwFromRWV;
          kill_dec; simpl; kill_dec; simpl; try abstract (intro Z; inversion Z);
          pose proof (Npow2_gt0 n); simpl in *; nomega.
      Qed.

      Lemma double_conv_var: forall t x,
        @convertVar R Z _ _ t (@convertVar B R _ _ t x) =
          @convertVar B Z _ _ t x.
      Proof.
        intros.
      Admitted.

      Lemma double_conv_arg: forall V t a,
        @convertArg R B _ _ V t (@convertArg Z R _ _ V t a) =
          @convertArg Z B _ _ V t a.
      Proof.
        intros.
      Admitted.
    End UtilityLemmas.


    Section Spec.
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

      Lemma RangeInterp_bounded_spec: forall {t} (E: expr t),
          bcheck (@convertExpr Z R _ _ _ _ E) = true
        -> typeMap (fun x => NToWord n (Z.to_N x)) (zinterp (n := n) E) = wordInterp (ZToWord _ E).
      Proof.
        intros t E S.
        unfold zinterp, ZToWord, wordInterp.

        induction E as [tx ty tz op x y z|]; simpl; try reflexivity.

        - repeat rewrite convertArg_var in *.
          repeat rewrite convertArg_interp in *.

          rewrite H; clear H; repeat f_equal.

          + pose proof (ZToWord_binop_correct op x y) as C;
              unfold opZ, opWord, varWordToZ, varZToWord in C;
              simpl in C.

            assert (N.pred (Npow2 n) >= 0)%N. {
              apply N.le_ge.
              rewrite <- (N.pred_succ 0).
              apply N.le_pred_le_succ.
              rewrite N.succ_pred; [| apply N.neq_0_lt_0; apply Npow2_gt0].
              apply N.le_succ_l.
              apply Npow2_gt0.
            }

            admit. (*
            induction op; rewrite (C (fun _ => Return (Const 0%Z))); clear C;
              unfold bcheck, getBounds, boundedInterp, bwFromRWV in *; simpl in *;
              kill_dec; simpl in *; kill_dec; first [reflexivity|nomega]. *)

          + unfold bcheck, getBounds in *.
            replace (interp_binop op _ _)
                with (varBoundedToZ (n := n) (opBounded op
                        (interp_arg' boundVarInterp (convertArg _ x))
                        (interp_arg' boundVarInterp (convertArg _ y)))).

            * rewrite <- S; f_equal; clear S.
              simpl; repeat f_equal.
              unfold varBoundedToZ, opBounded.
              repeat rewrite convertArg_var.
              Arguments convertArg _ _ _ _ _ _ _ : clear implicits.
              rewrite double_conv_var.
              repeat rewrite double_conv_arg.
              reflexivity.

            * pose proof (ZToBounded_binop_correct op x y) as C;
                unfold opZ, opWord, varZToBounded,
                    varBoundedToZ in *;
                simpl in C.

              Local Opaque boundVarInterp toT fromT.

              induction op; rewrite (C (fun _ => Return (Const 0%Z))); clear C; try reflexivity;
                unfold bcheck, getBounds; simpl;
                pose proof roundTrip_0 as H;
                induction (toT (fromT _)); first [reflexivity|contradict H; reflexivity].

              Local Transparent boundVarInterp toT fromT.

        - simpl in S.
          induction a as [| |t0 t1 a0 IHa0 a1 IHa1]; simpl in *; try reflexivity.
          admit.

          (*
          + f_equal.
            unfold bcheck, getBounds, boundedInterp in S; simpl in S.
            kill_dec; simpl; [reflexivity|simpl in S; inversion S].

          + f_equal.
            unfold bcheck, getBounds, boundedInterp, boundVarInterp in S; simpl in S;
              kill_dec; simpl; try reflexivity; try nomega.
            inversion S.
            admit.
            admit.

          + unfold bcheck in S; simpl in S;
              apply andb_true_iff in S; destruct S as [S0 S1];
              rewrite IHa0, IHa1; [reflexivity| |];
              unfold bcheck, getBounds; simpl; assumption. *)
      Admitted.
    End Spec.

    Section RWVSpec.
      Definition rangeOf := fun x =>
        Some (rwv 0%N (Z.to_N x) (Z.to_N x)).

      Definition getRWV {t} (e : @expr R Z t): @interp_type R t :=
        interp' rangeOf e.

      Definition getRanges {t} (e : @expr R Z t): @interp_type (option (Range N)) t :=
        typeMap (option_map rwvToRange) (getRWV e).

      Fixpoint check' {t} (x: @interp_type (option RangeWithValue) t) :=
        match t as t' return (interp_type t') -> bool with
        | TT => fun x' =>
            match omap x' (bwFromRWV (n := n)) with
            | Some _ => true
            | None => false
            end
        | Prod t0 t1 => fun x' =>
            match x' with
            | (x0, x1) => andb (check' x0) (check' x1)
            end
        end x.

      Definition check {t} (e : @expr R Z t): bool := check' (getRWV e).

      Ltac kill_dec :=
        repeat match goal with
        | [|- context[Nge_dec ?a ?b] ] => destruct (Nge_dec a b)
        | [H : context[Nge_dec ?a ?b] |- _ ] => destruct (Nge_dec a b)
        end.

      Lemma check_spec' : forall {rangeF wordF} (op: @validBinaryWordOp n rangeF wordF) x y,
        @convertVar B R _ _ TT (
          omap (interp_arg' boundVarInterp (convertArg TT x)) (fun X =>
            omap (interp_arg' boundVarInterp (convertArg TT y)) (fun Y =>
              bapp op X Y))) =
          omap (interp_arg' rangeOf x) (fun X =>
            omap (interp_arg' rangeOf y) (fun Y =>
              rwv_app (n := n) op X Y)).
      Proof.
      Admitted.

      Lemma check_spec: forall {t} (E: @expr R Z t), check E = true -> bcheck E = true.
      Proof.
        intros t E H.
        induction E as [tx ty tz op x y z eC IH| t a].

        - unfold bcheck, getBounds, check, getRWV in *.

          simpl; apply IH; clear IH; rewrite <- H; clear H.
          simpl; rewrite convertArg_var; repeat f_equal.

          unfold interp_binop, RE, WE, BE, ZE,
              BoundedEvaluable, RWVEvaluable, ZEvaluable,
              eadd, emul, esub, eshiftr, eand.

          induction op; rewrite check_spec'; reflexivity.

        - unfold bcheck, getBounds, check, getRWV in *.

          induction a as [a|a|t0 t1 a0 IHa0 a1 IHa1].

          + induction a as [a|]; [| inversion H]; simpl in *.

            assert (Z : (exists a', bwFromRWV (n := n) a = Some a')
                  \/ bwFromRWV (n := n) a = None) by (
              destruct (bwFromRWV a);
              [left; eexists; reflexivity | right; reflexivity]).

            destruct Z as [aSome|aNone]; [destruct aSome as [a' aSome] |].

            * rewrite aSome; simpl; rewrite aSome; reflexivity.
            * rewrite aNone in H; inversion H.

          + unfold boundVarInterp, rangeOf in *.
            simpl in *; kill_dec; try reflexivity; try inversion H.

          + simpl in *; rewrite IHa0, IHa1; simpl; [reflexivity | | ];
              apply andb_true_iff in H; destruct H as [H1 H2];
              assumption.
      Qed.

      Lemma RangeInterp_spec: forall {t} (E: expr t),
          check (convertExpr E) = true
        -> typeMap (fun x => NToWord n (Z.to_N x)) (zinterp (n := n) E)
            = wordInterp (ZToWord _ E).
      Proof.
        intros.
        apply RangeInterp_bounded_spec.
        apply check_spec.
        assumption.
      Qed.
    End RWVSpec.
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

  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 0 testCase))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 1 testCase))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 10 testCase))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 32 testCase))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 64 testCase))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 128 testCase))).

  Definition nefarious : Expr (T := Z) TT :=
    fun var => Let (Binop OPadd (Const 10%Z) (Const 20%Z))
                   (fun y => Binop OPmul (Var y) (Const 0%Z)).

  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 0 nefarious))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 1 nefarious))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 4 nefarious))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 5 nefarious))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 32 nefarious))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 64 nefarious))).
  Eval vm_compute in (typeMap (option_map bwToRange) (BInterp (ZToRange 128 nefarious))).
End ConversionTest.
