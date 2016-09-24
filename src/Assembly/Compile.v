Require Import Coq.Logic.Eqdep.
Require Import Compare_dec Sumbool.
Require Import PeanoNat Omega.

Require Import Crypto.Assembly.PhoasCommon.
Require Import Crypto.Assembly.HL.
Require Import Crypto.Assembly.LL.
Require Import Crypto.Assembly.QhasmEvalCommon.
Require Import Crypto.Assembly.QhasmCommon.
Require Import Crypto.Assembly.Qhasm.

Module CompileHL.
  Context {ivar : type -> Type}.
  Context {ovar : Type}.

  Fixpoint compile {t} (e:@HL.expr Z (@LL.arg Z Z) t) : @LL.expr Z Z t :=
    match e with
    | HL.Const n => LL.Return (LL.Const n)
    | HL.Var _ arg => LL.Return arg
    | HL.Binop t1 t2 t3 op e1 e2 =>
       LL.under_lets (@compile _ e1) (fun arg1 =>
          LL.under_lets (@compile _ e2) (fun arg2 =>
            LL.LetBinop op arg1 arg2 (fun v =>
              LL.Return v)))
    | HL.Let _ ex _ eC =>
       LL.under_lets (@compile _ ex) (fun arg => @compile _ (eC arg))
    | HL.Pair t1 e1 t2 e2 =>
       LL.under_lets (@compile _ e1) (fun arg1 =>
          LL.under_lets (@compile _ e2) (fun arg2 =>
             LL.Return (LL.Pair arg1 arg2)))
    | HL.MatchPair _ _ ep _ eC =>
        LL.under_lets (@compile _ ep) (fun arg =>
          let (a1, a2) := LL.match_arg_Prod arg in @compile _ (eC a1 a2))
    end.

  Section Correctness.
    Lemma compile_correct {_: Evaluable Z} {t} e1 e2 G (wf:HL.wf G e1 e2) :
      List.Forall (fun v => let 'existT _ (x, a) := v in LL.interp_arg a = x) G ->
        LL.interp (compile e2) = HL.interp e1 :> interp_type t.
    Proof.
      induction wf;
        repeat match goal with
        | [HIn:In ?x ?l, HForall:Forall _ ?l |- _ ] =>
          (pose proof (proj1 (Forall_forall _ _) HForall _ HIn); clear HIn)
        | [ H : LL.match_arg_Prod _ = (_, _) |- _ ] =>
          apply LL.match_arg_Prod_correct in H
        | [ H : LL.Pair _ _ = LL.Pair _ _ |- _ ] =>
          apply LL.Pair_eq in H
        | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
        | _ => progress intros
        | _ => progress simpl in *
        | _ => progress subst
        | _ => progress specialize_by assumption
        | _ => progress break_match
        | _ => rewrite !LL.interp_under_lets
        | _ => rewrite !LL.interp_arg_uninterp_arg
        | _ => progress erewrite_hyp !*
        | _ => apply Forall_cons
        | _ => solve [intuition (congruence || eauto)]
        end.
    Qed.
  End Correctness.
End CompileHL.

Module CompileLL.
  Import LL Qhasm.
  Import QhasmUtil ListNotations.

  Section Compile.
    Context {n: nat} {w: Width n}.

    Definition WArg t': Type := @LL.arg (word n) (word n) t'.
    Definition WExpr t': Type := @LL.expr (word n) (word n) t'.

    Fixpoint LLProgram t (inputs: nat): Type :=
      match inputs with
      | (S m) => WArg TT -> @LLProgram t m
      | O => WExpr t
      end.

    Section Mappings.
      Definition indexize (x: nat) : Index n.
        intros; destruct (le_dec n 0).

        - exists 0; abstract intuition auto with zarith.
        - exists (x mod n)%nat.
            abstract (pose proof (Nat.mod_bound_pos x n);
                    omega).
      Defined.

      Definition getMapping (x: WArg TT) :=
        match x with
        | Const v => constM n (@constant n w v)
        | Var v => regM n (@reg n w (wordToNat v))
        end.

      Definition getReg (x: Mapping n): option (Reg n) :=
        match x with | regM r => Some r | _ => None end.

      Definition getConst (x: Mapping n): option (QhasmCommon.Const n) :=
        match x with | constM c => Some c | _ => None end.

      Definition makeA (output input: Mapping n): option Assignment :=
        match (output, input) with
        | (regM r, constM c) => Some (AConstInt r c)
        | (regM r0, regM r1) => Some (ARegReg r0 r1)
        | _ => None
        end.

      Definition makeOp {t1 t2 t3} (op: binop t1 t2 t3) (out in1 in2: Mapping n):
            option (Reg n * option Assignment * Operation) :=
        let mov :=
          if (EvalUtil.mapping_dec out in1)
          then None
          else makeA out in1 in

        match op with
        | OPadd =>
          omap (getReg out) (fun r0 =>
            match in2 with
            | regM r1 => Some (r0, mov, IOpReg IAdd r0 r1)
            | constM c => Some (r0, mov, IOpConst IAdd r0 c)
            | _ => None
            end)

        | OPsub =>
          omap (getReg out) (fun r0 =>
            match in2 with
            | regM r1 => Some (r0, mov, IOpReg ISub r0 r1)
            | constM c => Some (r0, mov, IOpConst ISub r0 c)
            | _ => None
            end)

        | OPmul => 
          omap (getReg out) (fun r0 =>
            match in2 with
            | regM r1 => Some (r0, mov, DOp Mult r0 r1 None)
            | _ => None
            end)

        | OPand =>
          omap (getReg out) (fun r0 =>
            match in2 with
            | regM r1 => Some (r0, mov, IOpReg IAnd r0 r1)
            | constM c => Some (r0, mov, IOpConst IAnd r0 c)
            | _ => None
            end)

        | OPshiftr => 
          omap (getReg out) (fun r0 =>
            match in2 with
            | constM (constant _ _ w) =>
                Some (r0, mov, ROp Shr r0 (indexize (wordToNat w)))
            | _ => None
            end)
        end.
    End Mappings.

    Section TypeDec.
      Fixpoint type_eqb (t0 t1: type): bool :=
        match (t0, t1) with
        | (TT, TT) => true
        | (Prod t0a t0b, Prod t1a t1b) => andb (type_eqb t0a t1a) (type_eqb t0b t1b)
        | _ => false
        end.

      Lemma type_eqb_spec: forall t0 t1, type_eqb t0 t1 = true <-> t0 = t1.
      Proof.
        intros; split.

        - revert t1; induction t0 as [|t0a IHt0a t0b IHt0b].

            + induction t1; intro H; simpl in H; inversion H; reflexivity.

            + induction t1; intro H; simpl in H; inversion H.
            apply andb_true_iff in H; destruct H as [Ha Hb].

            apply IHt0a in Ha; apply IHt0b in Hb; subst.
            reflexivity.

        - intro H; subst.
            induction t1; simpl; [reflexivity|]; apply andb_true_iff; intuition.
      Qed.

      Definition type_dec (t0 t1: type): {t0 = t1} + {t0 <> t1}.
        refine (match (type_eqb t0 t1) as b return _ = b -> _ with
            | true => fun e => left _
            | false => fun e => right _
            end eq_refl);
        [ abstract (apply type_eqb_spec in e; assumption)
        | abstract (intro H; apply type_eqb_spec in H;
                    rewrite e in H; contradict H; intro C; inversion C) ].
      Defined.
    End TypeDec.

    Fixpoint vars {t} (a: WArg t): list nat :=
      match t as t' return WArg t' -> list nat with
      | TT => fun a' =>
        match a' with
        | Var v' => [wordToNat v']
        | _ => @nil nat
        end
      | Prod t0 t1 => fun a' =>
        match a' with
        | Pair _ _ a0 a1 => (vars a0) ++ (vars a1)
        end
      end a.

    Definition getOutputSlot {t} (nextRegName: nat) (op: binop TT TT TT) (x y: WArg TT)
               (eC: WArg TT -> WExpr t) : option nat :=
      match (makeOp op (regM _ (reg w nextRegName)) (getMapping x) (getMapping y)) with
      | Some (reg _ _ r, Some a, op') => Some r
      | Some (reg _ _ r, None, op')   => Some r
      | _                             => None
      end.

    Section ExprF.
      Context (Out: Type)
              (update: binop TT TT TT -> WArg TT -> WArg TT -> Out -> option Out)
              (get: forall t', WArg t' -> option Out).

      Fixpoint zeros (t: type): WArg t :=
        match t with
        | TT => Const (@wzero n)
        | Prod t0 t1 => Pair (zeros t0) (zeros t1)
        end.
 
      Fixpoint depth {t} (p: WExpr t) {struct p}: nat :=
        match p with
        | LetBinop _ _ _ _ _ _ t' eC => S (depth (eC (zeros _)))
        | Return _ a => O
        end.

      Fixpoint exprF0 t d (nextVar: nat) (p: {e: WExpr t | depth e = d}) {struct d}: option Out.
        refine (match d as d' return {e: WExpr t | depth e = d'} -> _ with
        | (S m) => fun p' =>
          match proj1_sig p' with
          | LetBinop TT TT TT op x y t' eC =>
            omap (getOutputSlot nextVar op x y eC) (fun r =>
              omap (exprF0 t' m (S nextVar) (exist _ (eC (Var (@natToWord n r))) _)) (fun o =>
                update op x y o))
          | _ => None
          end
        | O => fun p' =>
          match proj1_sig p' with
          | Return _ a => get _ a
          | _ => None
          end
        end p).

        destruct p' as [p' D'], p'; simpl in D'.
        inversion D'; subst.
      Admitted.

      Fixpoint exprF1 t inputs (args: list nat) (p: LLProgram t inputs): option Out.
        refine (match inputs as i' return LLProgram t i' -> _ with
        | (S m) => fun p' => @exprF Out t m update get (cons inputs args)
                                (p' (@Var (word n) (word n) (@natToWord n nextVar)))
        | O => fun p' =>
        end p).
        Defined.
    Section ExprF.

    Fixpoint exprF {t Out}
        
        t) (e: @LL.expr (word n) nat t) {struct e}: option Out :=
      match e with
      | LetBinop TT TT TT op x y t' eC =>
        omap (getOutputSlot nextRegName op x y eC) (fun r =>
          omap (exprF update get (S nextRegName) (eC (Var r))) (fun out =>
            update op x y out))
      | Return _ a => get _ a
      | _ => None
      end.

    Fixpoint getProg {t} :=
      @exprF t Program
        (fun op x y out ->
            match (makeOp op (regM _ (reg w nextRegName)) (@getMapping n w x) (@getMapping n w y)) with
            | Some (reg _ _ r, Some a, op') => Some ((QAssign a) :: (QOp op') :: out)
            | Some (reg _ _ r, None, op')   => Some ((QOp op') :: out)
            | _                             => None
            end)
        (fun t' a => [])

    Fixpoint getOuts {t} :=
      @exprF t Program
        (fun op x y out -> Some out)
        (fun t' a => vars a)

      match e with
      | LetBinop TT TT TT op x y t' eC =>
        if (type_dec t t')
        then match compile'' nextRegName op x y _ with
          | Some (progHead, outputVar, nextRegName') =>
            match compile' nextRegName' (_ op eC) with
            | Some (progTail, outputs) => Some (progHead ++ progTail, outputs)
            | None => None
            end
          | None => None
          end
        else None
      | Return _ a => Some ([], vars a)
      | _ => None
      end.

    Definition compile {t inputs} (prog: @LLProgram _ t inputs): option (Program * list nat) :=
      @compile' t inputs (freeVars prog).
  End Compile.
End CompileLL.
