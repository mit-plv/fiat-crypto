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
Require Import Crypto.Util.Prod.
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

(* TODO: organize this file *)
Section of_prefancy.
  Local Notation cexpr := (@Compilers.expr.expr base.type ident.ident).
  Local Notation LetInAppIdentZ S D r eidc x f
    := (expr.LetIn
          (A:=type.base (base.type.type_base base.type.Z))
          (B:=type.base D)
          (expr.App
             (s:=type.base (base.type.type_base base.type.Z))
             (d:=type.base (base.type.type_base base.type.Z))
             (expr.Ident (ident.Z_cast r))
             (expr.App
                (s:=type.base S)
                (d:=type.base (base.type.type_base base.type.Z))
                eidc
                x))
          f).
  Local Notation LetInAppIdentZZ S D r eidc x f
    := (expr.LetIn
          (A:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
          (B:=type.base D)
          (expr.App
             (s:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
             (d:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
             (expr.Ident (ident.Z_cast2 r))
             (expr.App
                (s:=type.base S)
                (d:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
                eidc
                x))
          f).
  Context (name : Type) (name_succ : name -> name) (error : name) (consts : Z -> option name).

  Fixpoint base_var (t : base.type) : Type :=
    match t with
    | base.type.Z => name
    | base.type.prod a b => base_var a * base_var b
    | _ => unit
    end.
  Fixpoint var (t : type.type base.type) : Type :=
    match t with
    | type.base t => base_var t
    | type.arrow s d => var s -> var d
    end.
  Fixpoint base_error {t} : base_var t
    := match t with
       | base.type.Z => error
       | base.type.prod A B => (@base_error A, @base_error B)
       | _ => tt
       end.
  Fixpoint make_error {t} : var t
    := match t with
       | type.base _ => base_error
       | type.arrow s d => fun _ => @make_error d
       end.

  Fixpoint of_prefancy_scalar {t} (s : @cexpr var t) : var t
    := match s in expr.expr t return var t with
       | Compilers.expr.Var t v => v
       | expr.App s d f x => @of_prefancy_scalar _ f (@of_prefancy_scalar _ x)
       | expr.Ident t idc
         => match idc in ident.ident t return var t with
            | ident.Literal base.type.Z v => match consts v with
                                             | Some n => n
                                             | None => error
                                             end
            | ident.pair A B => fun a b => (a, b)%core
            | ident.fst A B => fun v => fst v
            | ident.snd A B => fun v => snd v
            | ident.Z_cast r => fun v => v
            | ident.Z_cast2 (r1, r2) => fun v => v
            | ident.Z_land => fun x y => x
            | _ => make_error
            end
       | expr.Abs s d f => make_error
       | expr.LetIn A B x f => make_error
       end%expr_pat%etype.

  (* Note : some argument orders are reversed for MUL128LU, MUL128UL, SELC, SELM, and SELL *)
  Local Notation tZ := base.type.Z.
  Definition of_prefancy_ident {s d : base.type} (idc : ident.ident (s -> d))
    : @cexpr var s -> option {i : instruction & tuple name i.(num_source_regs) } :=
    match idc in ident.ident t return match t return Type with
                                      | type.arrow (type.base s) (type.base d)
                                        => @cexpr var s
                                      | _ => unit
                                      end
                                      -> option {i : instruction & tuple name i.(num_source_regs) }
    with
    | ident.fancy_add log2wordmax imm
      => fun args : @cexpr var (tZ * tZ) =>
           if Z.eqb log2wordmax 256
           then Some (existT _ (ADD imm) (of_prefancy_scalar args))
           else None
    | ident.fancy_addc log2wordmax imm
      => fun args : @cexpr var (tZ * tZ * tZ)  =>
           if Z.eqb log2wordmax 256
           then Some (existT _ (ADDC imm) (of_prefancy_scalar ((#ident.snd @ (#ident.fst @ args)), (#ident.snd @ args))))
           else None
    | ident.fancy_sub log2wordmax imm
      => fun args : @cexpr var (tZ * tZ)  =>
           if Z.eqb log2wordmax 256
           then Some (existT _ (SUB imm) (of_prefancy_scalar args))
           else None
    | ident.fancy_subb log2wordmax imm
      => fun args : @cexpr var (tZ * tZ * tZ)  =>
           if Z.eqb log2wordmax 256
           then Some (existT _ (SUBC imm) (of_prefancy_scalar ((#ident.snd @ (#ident.fst @ args)), (#ident.snd @ args))))
           else None
    | ident.fancy_mulll log2wordmax
      => fun args : @cexpr var (tZ * tZ)  =>
           if Z.eqb log2wordmax 256
           then Some (existT _ MUL128LL (of_prefancy_scalar args))
           else None
    | ident.fancy_mullh log2wordmax
      => fun args : @cexpr var (tZ * tZ)  =>
           if Z.eqb log2wordmax 256
           then Some (existT _ MUL128LU (of_prefancy_scalar ((#ident.snd @ args), (#ident.fst @ args))))
           else None
    | ident.fancy_mulhl log2wordmax
      => fun args : @cexpr var (tZ * tZ)  =>
           if Z.eqb log2wordmax 256
           then Some (existT _ MUL128UL (of_prefancy_scalar ((#ident.snd @ args), (#ident.fst @ args))))
           else None
    | ident.fancy_mulhh log2wordmax
      => fun args : @cexpr var (tZ * tZ)  =>
           if Z.eqb log2wordmax 256
           then Some (existT _ MUL128UU (of_prefancy_scalar args))
           else None
    | ident.fancy_rshi log2wordmax imm
      => fun args : @cexpr var (tZ * tZ)  =>
           if Z.eqb log2wordmax 256
           then Some (existT _ (RSHI imm) (of_prefancy_scalar args))
           else None
    | ident.fancy_selc
      => fun args : @cexpr var (tZ * tZ * tZ) => Some (existT _ SELC (of_prefancy_scalar ((#ident.snd @ args), (#ident.snd @ (#ident.fst @ args)))))
    | ident.fancy_selm log2wordmax
      => fun args : @cexpr var (tZ * tZ * tZ)  =>
           if Z.eqb log2wordmax 256
           then Some (existT _ SELM (of_prefancy_scalar ((#ident.snd @ args), (#ident.snd @ (#ident.fst @ args)))))
           else None
    | ident.fancy_sell
      => fun args : @cexpr var (tZ * tZ * tZ) => Some (existT _ SELL (of_prefancy_scalar ((#ident.snd @ args), (#ident.snd @ (#ident.fst @ args)))))
    | ident.fancy_addm
      => fun args : @cexpr var (tZ * tZ * tZ) => Some (existT _ ADDM (of_prefancy_scalar args))
    | _ => fun _ => None
    end.

  Local Notation "x <- y ; f" := (match y with Some x => f | None => Ret error end).
  Definition of_prefancy_step
             (of_prefancy : forall (next_name : name) {t} (e : @cexpr var t), @expr name)
             (next_name : name) {t} (e : @cexpr var t) : @expr name
    := let default _ := (e' <- type.try_transport (@base.try_make_transport_cps) (@cexpr var) t tZ e;
                           Ret (of_prefancy_scalar e')) in
       match e with
       | LetInAppIdentZ s d r eidc x f
         => idc <- invert_expr.invert_Ident eidc;
              instr_args <- @of_prefancy_ident s tZ idc x;
              let i : instruction := projT1 instr_args in
              let args : tuple name i.(num_source_regs) := projT2 instr_args in
              Instr i next_name args (@of_prefancy (name_succ next_name) _ (f next_name))
       | LetInAppIdentZZ s d r eidc x f
         => idc <- invert_expr.invert_Ident eidc;
              instr_args <- @of_prefancy_ident s (tZ * tZ) idc x;
              let i : instruction := projT1 instr_args in
              let args : tuple name i.(num_source_regs) := projT2 instr_args in
              Instr i next_name args (@of_prefancy (name_succ next_name) _ (f (next_name, next_name))) (* the second argument is for the carry, and it will not be read from directly. *)
       | _  => default tt
       end.
  Fixpoint of_prefancy (next_name : name) {t} (e : @cexpr var t) : @expr name
    := @of_prefancy_step of_prefancy next_name t e.

  Section Proofs.
    Context (name_eqb : name -> name -> bool).
    Context (name_lt : name -> name -> Prop)
            (name_lt_trans : forall n1 n2 n3,
                name_lt n1 n2 -> name_lt n2 n3 -> name_lt n1 n3)
            (name_lt_irr : forall n, ~ name_lt n n)
            (name_lt_succ : forall n, name_lt n (name_succ n))
            (name_eqb_eq : forall n1 n2, name_eqb n1 n2 = true -> n1 = n2)
            (name_eqb_neq : forall n1 n2, name_eqb n1 n2 = false -> n1 <> n2).
    Local Notation wordmax := (2^256).
    Local Notation interp := (interp name_eqb wordmax cc_spec).
    Local Notation uint256 := r[0~>wordmax-1]%zrange.
    Local Notation uint128 := r[0~>(2 ^ (Z.log2 wordmax / 2) - 1)]%zrange.
    Definition cast_oor (r : zrange) (v : Z) := v mod (upper r + 1).
    Local Notation "'existZ' x" := (existT _ (type.base (base.type.type_base tZ)) x) (at level 200).
    Local Notation "'existZZ' x" := (existT _ (type.base (base.type.type_base tZ * base.type.type_base tZ)%etype) x) (at level 200).
    Local Notation cinterp := (expr.interp (@ident.gen_interp cast_oor)).
    Definition interp_if_Z {t} (e : cexpr t) : option Z :=
      option_map (expr.interp (@ident.gen_interp cast_oor) (t:=tZ))
                 (type.try_transport
                    (@base.try_make_transport_cps)
                    _ _ tZ e).

    Lemma interp_if_Z_Some {t} e r :
      @interp_if_Z t e = Some r ->
      exists e',
        (type.try_transport
           (@base.try_make_transport_cps) _ _ tZ e) = Some e' /\
        expr.interp (@ident.gen_interp cast_oor) (t:=tZ) e' = r.
    Proof.
      clear. cbv [interp_if_Z option_map].
      break_match; inversion 1; intros.
      subst; eexists. tauto.
    Qed.

    Inductive valid_scalar
      : @cexpr var (base.type.type_base tZ) -> Prop :=
    | valid_scalar_literal :
        forall v n,
          consts v = Some n ->
          valid_scalar (expr.Ident (@ident.Literal base.type.Z v))
    | valid_scalar_Var :
        forall v,
          valid_scalar (expr.App (expr.Ident (ident.Z_cast uint256)) (expr.Var v))
    | valid_scalar_fst :
        forall v r2,
          valid_scalar
            (expr.App (expr.Ident (ident.Z_cast uint256))
                      (expr.App (expr.Ident (@ident.fst (base.type.type_base tZ)
                                                        (base.type.type_base tZ)))
                                (expr.App (expr.Ident (ident.Z_cast2 (uint256, r2))) (expr.Var v))))
    .
    Inductive valid_carry
      :  @cexpr var (base.type.type_base tZ) -> Prop :=
    | valid_carry_0 : consts 0 <> None -> valid_carry (expr.Ident (@ident.Literal base.type.Z 0))
    | valid_carry_1 : consts 1 <> None -> valid_carry (expr.Ident (@ident.Literal base.type.Z 1))
    | valid_carry_snd :
        forall v r2,
          valid_carry
            (expr.App (expr.Ident (ident.Z_cast r[0~>1]))
                      (expr.App (expr.Ident (@ident.snd (base.type.type_base tZ)
                                                        (base.type.type_base tZ)))
                                (expr.App (expr.Ident (ident.Z_cast2 (r2, r[0~>1]))) (expr.Var v))))
    .

    Fixpoint interp_base (ctx : name -> Z) (cctx : name -> bool) {t}
      : base_var t -> base.interp t :=
      match t as t0 return base_var t0 -> base.interp t0 with
      | base.type.type_base tZ => fun n => ctx n
      | (base.type.type_base tZ * base.type.type_base tZ)%etype =>
        fun v => (ctx (fst v), Z.b2z (cctx (snd v)))
      | (a * b)%etype =>
        fun _ => DefaultValue.type.base.default
      | _ => fun _ : unit =>
               DefaultValue.type.base.default
      end.

    Definition new_write {d} : var d -> name :=
      match d with
      | type.base (base.type.type_base tZ) => fun r => r
      | type.base (base.type.type_base tZ * base.type.type_base tZ)%etype => fst
      | _ => fun _ => error
      end.
    Definition new_cc_to_name (old_cc_to_name : CC.code -> name) (i : instruction)
               {d} (new_r : var d) (x : CC.code) : name :=
      if (in_dec CC.code_dec x (writes_conditions i))
      then new_write new_r
      else old_cc_to_name x.

    Inductive valid_ident
      : forall {s d},
        (CC.code -> name) -> (* last variables that wrote to each flag *)
        (var d -> CC.code -> name) -> (* new last variables that wrote to each flag *)
        ident.ident (s->d) -> @cexpr var s -> Prop :=
    | valid_fancy_add :
        forall r imm x y,
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r (ADD imm)) (ident.fancy_add 256 imm) (x, y)%expr_pat
    | valid_fancy_addc :
        forall r imm c x y,
          (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.C) ->
          valid_carry c ->
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r (ADDC imm)) (ident.fancy_addc 256 imm) (c, x, y)%expr_pat
    | valid_fancy_sub :
        forall r imm x y,
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r (SUB imm)) (ident.fancy_sub 256 imm) (x, y)%expr_pat
    | valid_fancy_subb :
        forall r imm c x y,
          (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.C) ->
          valid_carry c ->
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r (SUBC imm)) (ident.fancy_subb 256 imm) (c, x, y)%expr_pat
    | valid_fancy_mulll :
        forall r x y,
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r MUL128LL) (ident.fancy_mulll 256) (x, y)%expr_pat
    | valid_fancy_mullh :
        forall r x y,
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r MUL128LU) (ident.fancy_mullh 256) (x, y)%expr_pat
    | valid_fancy_mulhl :
        forall r x y,
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r MUL128UL) (ident.fancy_mulhl 256) (x, y)%expr_pat
    | valid_fancy_mulhh :
        forall r x y,
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r MUL128UU) (ident.fancy_mulhh 256) (x, y)%expr_pat
    | valid_fancy_rshi :
        forall r imm x y,
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r (RSHI imm)) (ident.fancy_rshi 256 imm) (x, y)%expr_pat
    | valid_fancy_selc :
        forall r c x y,
          (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.C) ->
          valid_carry c ->
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r SELC) ident.fancy_selc (c, x, y)%expr_pat
    | valid_fancy_selm :
        forall r c x y,
          (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.M) ->
          valid_scalar c ->
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r SELM) (ident.fancy_selm 256) (c, x, y)%expr_pat
    | valid_fancy_sell :
        forall r c x y,
          (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.L) ->
          valid_scalar c ->
          valid_scalar x ->
          valid_scalar y ->
          valid_ident r (new_cc_to_name r SELL) ident.fancy_sell (c, x, y)%expr_pat
    | valid_fancy_addm :
        forall r x y m,
          valid_scalar x ->
          valid_scalar y ->
          valid_scalar m ->
          valid_ident r (new_cc_to_name r ADDM) ident.fancy_addm (x, y, m)%expr_pat
    .

    Inductive valid_expr
      : forall t,
        (CC.code -> name) -> (* the last variables that wrote to each flag *)
        @cexpr var t -> Prop :=
    | valid_LetInZ_loosen :
        forall s d idc r rf x f u ia,
          valid_ident r rf idc x ->
          0 < u < wordmax ->
          (forall x, valid_expr _ (rf x) (f x)) ->
          of_prefancy_ident idc x = Some ia ->
          (forall cc ctx,
              (forall n v, consts v = Some n -> ctx n = v) ->
              (forall n, ctx n mod wordmax = ctx n) ->
              let args := Tuple.map ctx (projT2 ia) in
              spec (projT1 ia) args cc mod wordmax = spec (projT1 ia) args cc mod (u+1)) ->
          valid_expr _ r (LetInAppIdentZ s d r[0~>u] (expr.Ident idc) x f)
    | valid_LetInZ :
        forall s d idc r rf x f,
          valid_ident r rf idc x ->
          (forall x, valid_expr _ (rf x) (f x)) ->
          valid_expr _ r (LetInAppIdentZ s d uint256 (expr.Ident idc) x f)
    | valid_LetInZZ :
        forall s d idc r rf x f,
          valid_ident r rf idc x ->
          (forall x : var (type.base (base.type.type_base tZ * base.type.type_base tZ)%etype),
              fst x = snd x ->
              valid_expr _ (rf x) (f x)) ->
          valid_expr _ r (LetInAppIdentZZ s d (uint256, r[0~>1]) (expr.Ident idc) x f)
    | valid_Ret :
        forall r x,
          valid_scalar x ->
          valid_expr _ r x
    .

    Lemma cast_oor_id v u : 0 <= v <= u -> cast_oor r[0 ~> u] v = v.
    Proof. intros; cbv [cast_oor upper]. apply Z.mod_small; omega. Qed.
    Lemma cast_oor_mod v u : 0 <= u -> cast_oor r[0 ~> u] v mod (u+1) = v mod (u+1).
    Proof. intros; cbv [cast_oor upper]. apply Z.mod_mod; omega. Qed.

    Lemma wordmax_nonneg : 0 <= wordmax.
    Proof. cbv; congruence. Qed.

    Lemma of_prefancy_scalar_correct'
          (e1 : @cexpr var (type.base (base.type.type_base tZ)))
          (e2 : cexpr (type.base (base.type.type_base tZ)))
          G (ctx : name -> Z) (cctx : name -> bool) :
      valid_scalar e1 ->
      LanguageWf.Compilers.expr.wf G e1 e2 ->
      (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
      (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
      (forall v1 v2, In (existZ (v1, v2)) G -> ctx v1 = v2) -> (* implied by above *)
      (forall n, ctx n mod wordmax = ctx n) ->
      (forall v1 v2, In (existZZ (v1, v2)) G -> ctx (fst v1) = fst v2) ->
      (forall v1 v2, In (existZZ (v1, v2)) G -> Z.b2z (cctx (snd v1)) = snd v2) ->
      ctx (of_prefancy_scalar e1) = cinterp e2.
    Proof.
      inversion 1; inversion 1;
        cbv [interp_if_Z option_map];
        cbn [of_prefancy_scalar interp_base]; intros.
      all: repeat first [
                    progress subst
                  | exfalso; assumption
                  | progress inversion_sigma
                  | progress inversion_option
                  | progress inversion_prod
                  | progress LanguageInversion.Compilers.expr.inversion_expr
                  | progress LanguageInversion.Compilers.expr.invert_subst
                  | progress LanguageWf.Compilers.expr.inversion_wf_one_constr
                  | progress LanguageInversion.Compilers.expr.invert_match
                  | progress destruct_head'_sig
                  | progress destruct_head'_and
                  | progress destruct_head'_or
                  | progress Z.ltb_to_lt
                  | progress cbv [id]
                  | progress cbn [fst snd upper lower fst snd eq_rect projT1 projT2 expr.interp ident.interp ident.gen_interp interp_base] in *
                  | progress HProp.eliminate_hprop_eq
                  | progress break_innermost_match_hyps
                  | progress break_innermost_match
                  | match goal with H : context [_ = cinterp _] |- context [cinterp _] =>
                                    rewrite <-H by eauto; try reflexivity end
                  | solve [eauto using (f_equal2 pair), cast_oor_id, wordmax_nonneg]
                  | rewrite LanguageWf.Compilers.ident.cast_out_of_bounds_simple_0_mod
                  | rewrite Z.mod_mod by lia
                  | rewrite cast_oor_mod by (cbv; congruence)
                  | lia
                  | match goal with
                      H : context[ ?x mod _ = ?x ] |- _ => rewrite H end
                  | match goal with
                    | H : context [In _ _ -> _ = _] |- _ => erewrite H by eauto end
                  | match goal with
                    | H : forall v1 v2, In _ _ -> ?ctx v1 = v2 |- ?x = ?x mod ?m =>
                      replace m with wordmax by ring; erewrite <-(H _ x)  by eauto; solve [eauto]
                    end
                  | match goal with
                    | H : forall v1 v2, In _ _ -> ?ctx (fst v1) = fst v2,
                      H' : In (existZZ (_,(?x,?y))) _ |- ?x = ?x mod ?m =>
                    replace m with wordmax by ring;
                    specialize (H _ _ H'); cbn [fst] in H; rewrite <-H; solve [eauto] end
                  ].
    Qed.

    Lemma of_prefancy_scalar_correct
          (e1 : @cexpr var (type.base (base.type.type_base tZ)))
          (e2 : cexpr (type.base (base.type.type_base tZ)))
          G (ctx : name -> Z) cc :
      valid_scalar e1 ->
      LanguageWf.Compilers.expr.wf G e1 e2 ->
      (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
      (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cc v1 = v2) ->
      (forall n, ctx n mod wordmax = ctx n) ->
      ctx (of_prefancy_scalar e1) = cinterp e2.
    Proof.
      intros; match goal with H : context [interp_base _ _ _ = _] |- _ =>
                              pose proof (H (base.type.type_base base.type.Z));
                                pose proof (H (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype); cbn [interp_base] in *
              end.
      eapply of_prefancy_scalar_correct'; eauto;
        match goal with
        | H : forall _ _, In _ _ -> (_, _) = _ |- _ =>
          let v1 := fresh "v" in
          let v2 := fresh "v" in
          intros v1 v2 ?; rewrite <-(H v1 v2) by auto
        end; reflexivity.
    Qed.

    Lemma of_prefancy_ident_Some {s d} idc r rf x:
      @valid_ident (type.base s) (type.base d) r rf idc x ->
      of_prefancy_ident idc x <> None.
    Proof.
      induction s; inversion 1; intros;
        repeat first [
                 progress subst
               | progress inversion_sigma
               | progress cbn [eq_rect projT1 projT2 of_prefancy_ident invert_expr.invert_Ident option_map] in *
               | progress Z.ltb_to_lt
               | progress break_innermost_match
               | progress LanguageInversion.Compilers.type.inversion_type
               | progress LanguageInversion.Compilers.expr.inversion_expr
               | congruence
               ].
    Qed.

    Ltac name_eqb_to_eq :=
      repeat match goal with
             | H : name_eqb _ _ = true |- _ => apply name_eqb_eq in H
             | H : name_eqb _ _ = false |- _ => apply name_eqb_neq in H
             end.
    Ltac inversion_of_prefancy_ident :=
        match goal with
        | H : of_prefancy_ident _ _ = None |- _ =>
          eapply of_prefancy_ident_Some in H;
          [ contradiction | eassumption]
        end.

    Local Ltac hammer :=
      repeat first [
                    progress subst
                  | progress inversion_sigma
                  | progress inversion_option
                  | progress inversion_of_prefancy_ident
                  | progress inversion_prod
                  | progress cbv [id]
                  | progress cbn [eq_rect projT1 projT2 expr.interp ident.interp ident.gen_interp interp_base interp invert_expr.invert_Ident interp_if_Z option_map] in *
                  | progress LanguageInversion.Compilers.type_beq_to_eq
                  | progress name_eqb_to_eq
                  | progress LanguageInversion.Compilers.rewrite_type_transport_correct
                  | progress HProp.eliminate_hprop_eq
                  | progress break_innermost_match_hyps
                  | progress break_innermost_match
                  | progress LanguageInversion.Compilers.type.inversion_type
                  | progress LanguageInversion.Compilers.expr.inversion_expr
                  | solve [auto]
                  | contradiction
             ].
    Ltac prove_Ret :=
      repeat match goal with
             | H : valid_scalar (expr.LetIn _ _) |- _ =>
               inversion H
             | _ => progress cbn [id of_prefancy of_prefancy_step of_prefancy_scalar]
             | _ => progress hammer
             | H : valid_scalar (expr.Ident _) |- _ =>
               inversion H; clear H
             | |- _ = cinterp ?f (cinterp ?x) =>
               transitivity
                 (cinterp (f @ x)%expr);
               [ | reflexivity ];
               erewrite <-of_prefancy_scalar_correct by (try reflexivity; eassumption)
             end.

    Lemma cast_mod u v :
      0 <= u ->
      ident.cast cast_oor r[0~>u] v = v mod (u + 1).
    Proof.
      intros.
      rewrite LanguageWf.Compilers.ident.cast_out_of_bounds_simple_0_mod by auto using cast_oor_id.
      cbv [cast_oor upper]. apply Z.mod_mod. omega.
    Qed.

    Lemma cc_spec_c v :
      Z.b2z (cc_spec CC.C v) = (v / wordmax) mod 2.
    Proof. cbv [cc_spec]; apply Z.testbit_spec'. omega. Qed.

    Lemma cc_m_zselect x z nz :
      x mod wordmax = x ->
      (if (if cc_spec CC.M x then 1 else 0) =? 1 then nz else z) =
      Z.zselect (x >> 255) z nz.
    Proof.
      intro Hx_small.
      transitivity (if (Z.b2z (cc_spec CC.M x) =? 1) then nz else z); [ reflexivity | ].
      cbv [cc_spec Z.zselect].
      rewrite Z.testbit_spec', Z.shiftr_div_pow2 by omega. rewrite <-Hx_small.
      rewrite Div.Z.div_between_0_if by (try replace (2 * (2 ^ 255)) with wordmax by reflexivity;
                                         auto with zarith).
      break_innermost_match; Z.ltb_to_lt; try rewrite Z.mod_small in * by omega; congruence.
    Qed.

    Lemma cc_l_zselect x z nz :
      (if (if cc_spec CC.L x then 1 else 0) =? 1 then nz else z) = Z.zselect (x &' 1) z nz.
    Proof.
      transitivity (if (Z.b2z (cc_spec CC.L x) =? 1) then nz else z); [ reflexivity | ].
      transitivity (Z.zselect (x &' Z.ones 1) z nz); [ | reflexivity ].
      cbv [cc_spec Z.zselect]. rewrite Z.testbit_spec', Z.land_ones by omega.
      autorewrite with zsimplify_fast. rewrite Zmod_even.
      break_innermost_match; Z.ltb_to_lt; congruence.
    Qed.

    Lemma b2z_range b : 0<= Z.b2z b < 2.
    Proof. cbv [Z.b2z]. break_match; lia. Qed.


    Lemma of_prefancy_scalar_carry
          (c : @cexpr var (type.base (base.type.type_base tZ)))
          (e : cexpr (type.base (base.type.type_base tZ)))
          G (ctx : name -> Z) cctx :
      valid_carry c ->
      LanguageWf.Compilers.expr.wf G c e ->
      (forall n0, consts 0 = Some n0 -> cctx n0 = false) ->
      (forall n1, consts 1 = Some n1 -> cctx n1 = true) ->
      (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
      Z.b2z (cctx (of_prefancy_scalar c)) = cinterp e.
    Proof.
      inversion 1; inversion 1; intros; hammer; cbn;
      repeat match goal with
             | H : context [ _ = false] |- Z.b2z _ = 0 => rewrite H; reflexivity
             | H : context [ _ = true] |- Z.b2z _ = 1 => rewrite H; reflexivity
             | _ => progress LanguageWf.Compilers.expr.inversion_wf_one_constr
             | _ => progress cbn [fst snd]
             | _ => progress destruct_head'_sig
             | _ => progress destruct_head'_and
             | _ => progress hammer
             | _ => progress LanguageInversion.Compilers.expr.invert_subst
             | _ => rewrite cast_mod by (cbv; congruence)
             | _ => rewrite Z.mod_mod by omega
             | _ => rewrite Z.mod_small by apply b2z_range
             | H : (forall _ _ _, In _ _ -> interp_base _ _ _ = _),
                   H' : In (existZZ (?v, _)) _ |- context [cctx (snd ?v)] =>
               specialize (H _ _ _ H'); cbn in H
             end.
    Qed.

    Ltac simplify_ident :=
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd of_prefancy_ident] in *
               | _ => progress LanguageWf.Compilers.expr.inversion_wf_one_constr
               | H : { _ | _ } |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
               | H : upper _ = _ |- _ => rewrite H
               | _ => rewrite cc_spec_c by auto
               | _ => rewrite cast_mod by (cbv; congruence)
               | H : _ |- _ =>
                 apply LanguageInversion.Compilers.expr.invert_Ident_Some in H
               | H : _ |- _ =>
                 apply LanguageInversion.Compilers.expr.invert_App_Some in H
               | H : ?P, H' : ?P |- _ => clear H'
               | _ => progress hammer
               end.

    (* TODO: zero flag is a little tricky, since the value
      depends both on the stored variable and the carry if there
      is one. For now, since Barrett doesn't use it, we're just
      pretending it doesn't exist. *)
    Definition cc_good cc cctx ctx r :=
        CC.cc_c cc = cctx (r CC.C) /\
        CC.cc_m cc = cc_spec CC.M (ctx (r CC.M)) /\
        CC.cc_l cc = cc_spec CC.L (ctx (r CC.L)) /\
        (forall n0 : name, consts 0 = Some n0 -> cctx n0 = false) /\
        (forall n1 : name, consts 1 = Some n1 -> cctx n1 = true).

    Lemma of_prefancy_identZ_loosen_correct {s} idc:
      forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f u,
        @valid_ident (type.base s) (type_base tZ) r rf idc x ->
        LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
        LanguageWf.Compilers.expr.wf G #(ident.Z_cast r[0~>u]) f ->
        0 < u < wordmax ->
        cc_good cc cctx ctx r ->
        (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
        (forall n, ctx n mod wordmax = ctx n) ->
        of_prefancy_ident idc x = Some i ->
        (spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod (u+1)) ->
        spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = (cinterp f (cinterp x2)).
    Proof.
      Time
        inversion 1; inversion 1; cbn [of_prefancy_ident]; hammer; (simplify_ident; [ ]). (* TODO : suuuuuper slow *)
      all:
        rewrite cast_mod by omega;
        match goal with
                 | H : context [spec _ _ _ mod _ = _] |- ?x mod wordmax = _ mod ?m =>
                   replace (x mod wordmax) with (x mod m) by auto
        end.
      all:  cbn - [Z.shiftl wordmax]; cbv [cc_good] in *; destruct_head'_and;
          repeat match goal with
                 | H : CC.cc_c _ = _ |- _ => rewrite H
                 | H : CC.cc_m _ = _ |- _ => rewrite H
                 | H : CC.cc_l _ = _ |- _ => rewrite H
                 | H : CC.cc_z _ = _ |- _ => rewrite H
                 | H: of_prefancy_scalar _ = ?r ?c |- _ => rewrite <-H
                 | _ => progress rewrite ?cc_m_zselect, ?cc_l_zselect by auto
                 | _ => progress rewrite ?Z.add_modulo_correct, ?Z.geb_leb by auto
                 | |- context [cinterp ?x] =>
                   erewrite of_prefancy_scalar_correct with (e2:=x) by eauto
                 | |- context [cinterp ?x] =>
                   erewrite <-of_prefancy_scalar_carry with (e:=x) by eauto
                 | |- context [if _ (of_prefancy_scalar _) then _ else _ ] =>
                   cbv [Z.zselect Z.b2z];
                     break_innermost_match; Z.ltb_to_lt; try reflexivity;
                       congruence
                 end; try reflexivity.

      { (* RSHI case *)
        cbv [Z.rshi].
        rewrite Z.land_ones, Z.shiftl_mul_pow2 by (cbv; congruence).
        change (2 ^ Z.log2 wordmax) with wordmax.
        break_innermost_match; try congruence; [ ]. autorewrite with zsimplify_fast.
        repeat (f_equal; try ring). }
    Qed.
    Lemma of_prefancy_identZ_correct {s} idc:
      forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f,
        @valid_ident (type.base s) (type_base tZ) r rf idc x ->
        LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
        LanguageWf.Compilers.expr.wf G #(ident.Z_cast uint256) f ->
        cc_good cc cctx ctx r ->
        (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
        (forall n, ctx n mod wordmax = ctx n) ->
        of_prefancy_ident idc x = Some i ->
        spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = (cinterp f (cinterp x2)).
    Proof.
      intros; eapply of_prefancy_identZ_loosen_correct; try eassumption; [ | ].
      { cbn; omega. } { intros; f_equal; ring. }
    Qed.
    Lemma of_prefancy_identZZ_correct' {s} idc:
      forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f,
        @valid_ident (type.base s) (type_base (tZ * tZ)) r rf idc x ->
        LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
        LanguageWf.Compilers.expr.wf G #(ident.Z_cast2 (uint256, r[0~>1])) f ->
        cc_good cc cctx ctx r ->
        (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
        (forall n, ctx n mod wordmax = ctx n) ->
        of_prefancy_ident idc x = Some i ->
        spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = fst (cinterp f (cinterp x2)) /\
        Z.b2z (cc_spec CC.C (spec (projT1 i) (Tuple.map ctx (projT2 i)) cc)) = snd (cinterp f (cinterp x2)).
    Proof.
      inversion 1; inversion 1; cbn [of_prefancy_ident]; intros; hammer; (simplify_ident; [ ]);
        cbn - [Z.div Z.modulo]; cbv [Z.sub_with_borrow Z.add_with_carry];
          cbv [cc_good] in *; destruct_head'_and; autorewrite with zsimplify_fast.
      all: repeat match goal with
               | H : CC.cc_c _ = _ |- _ => rewrite H
               | H: of_prefancy_scalar _ = ?r ?c |- _ => rewrite <-H
               | H : LanguageWf.Compilers.expr.wf _ ?x ?e |- context [cinterp ?e] =>
                 erewrite <-of_prefancy_scalar_correct with (e1:=x) (e2:=e) by eauto
               | H : LanguageWf.Compilers.expr.wf _ ?x ?e2 |- context [cinterp ?e2] =>
                 erewrite <-of_prefancy_scalar_carry with (c:=x) (e:=e2) by eauto
                  end.
      all: match goal with |- context [(?x << ?n) mod ?m] =>
                           pose proof (Z.mod_pos_bound (x << n) m ltac:(omega)) end.
      all:repeat match goal with
               | |- context [if _ (of_prefancy_scalar _) then _ else _ ] =>
                 cbv [Z.zselect Z.b2z]; break_innermost_match; Z.ltb_to_lt; try congruence; [ | ]
               | _ => rewrite Z.add_opp_r
               | _ => rewrite Div.Z.div_sub_small by auto with zarith
               | H : forall n, ?ctx n mod wordmax = ?ctx n |- context [?ctx ?m - _] => rewrite <-(H m)
               |  |- ((?x - ?y - ?c) / _) mod _ = - ((- ?c + ?x - ?y) / _) mod _ =>
                  replace (-c + x - y) with (x - (y + c)) by ring; replace (x - y - c) with (x - (y + c)) by ring
               | _ => split
               | _ => try apply (f_equal2 Z.modulo); try apply (f_equal2 Z.div); ring
               | _ => break_innermost_match; reflexivity
               end.
    Qed.
    Lemma of_prefancy_identZZ_correct {s} idc:
      forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f,
        @valid_ident (type.base s) (type_base (tZ * tZ)) r rf idc x ->
        LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
        LanguageWf.Compilers.expr.wf G #(ident.Z_cast2 (uint256, r[0~>1])) f ->
        cc_good cc cctx ctx r ->
        (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
        (forall n, ctx n mod wordmax = ctx n) ->
        of_prefancy_ident idc x = Some i ->
        spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = fst (cinterp f (cinterp x2)).
    Proof. apply of_prefancy_identZZ_correct'. Qed.
    Lemma of_prefancy_identZZ_correct_carry {s} idc:
      forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f,
        @valid_ident (type.base s) (type_base (tZ * tZ)) r rf idc x ->
        LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
        LanguageWf.Compilers.expr.wf G #(ident.Z_cast2 (uint256, r[0~>1])) f ->
        cc_good cc cctx ctx r ->
        (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
        (forall n, ctx n mod wordmax = ctx n) ->
        of_prefancy_ident idc x = Some i ->
        Z.b2z (cc_spec CC.C (spec (projT1 i) (Tuple.map ctx (projT2 i)) cc)) = snd (cinterp f (cinterp x2)).
    Proof. apply of_prefancy_identZZ_correct'. Qed.

    Lemma identZZ_writes {s} idc r rf x:
      @valid_ident (type.base s) (type_base (tZ * tZ)) r rf idc x ->
      forall i, of_prefancy_ident idc x = Some i ->
                  In CC.C (writes_conditions (projT1 i)).
    Proof.
      inversion 1;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [of_prefancy_ident writes_conditions ADD ADDC SUB SUBC In] in *
               | _ => progress hammer; Z.ltb_to_lt
               | _ => congruence
               end.
    Qed.

    (* Common side conditions for cases in of_prefancy_correct *)
    Local Ltac side_cond :=
      repeat match goal with
             | _ => progress intros
             | _ => progress cbn [In fst snd] in *
             | H : _ \/ _ |- _ => destruct H
             | [H : forall _ _, In _ ?l -> _, H' : In _ ?l |- _] =>
               let H'' := fresh in
               pose proof H'; apply H in H''; clear H
             | H : name_lt ?n ?n |- _ =>
               specialize (name_lt_irr n); contradiction
             | _ => progress hammer
             | _ => solve [eauto]
             end.

    Lemma interp_base_helper G next_name ctx cctx :
      (forall n v2, In (existZ (n, v2)) G -> name_lt n next_name) ->
      (forall n v2, In (existZZ (n, v2)) G -> name_lt (fst n) next_name) ->
      (forall n v2, In (existZZ (n, v2)) G -> fst n = snd n) ->
      (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
      (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G ->
                       t = base.type.type_base tZ
                       \/ t = (base.type.type_base tZ * base.type.type_base tZ)%etype) ->
      forall t v1 v2 x xc,
        In (existT (fun t : type => (var t * type.interp base.interp t)%type) (type.base t) (v1, v2)%zrange)
           ((existZ (next_name, x)%zrange) :: G) ->
        interp_base (fun n : name => if name_eqb n next_name then x else ctx n)
                    (fun n : name => if name_eqb n next_name then xc else cctx n) v1 = v2.
    Proof.
      intros.
      repeat match goal with
             | H: In _ (_ :: _) |- _ => cbn [In] in H; destruct H; [ solve [side_cond] | ]
             | H : (forall t _ _, In _ ?G -> (t = _ \/ t = _)), H' : In _ ?G |- _ =>
               destruct (H _ _ _ H'); subst t
             | H : forall _ _ _, In _ ?G -> interp_base _ _ _ = _, H' : In _ G |- _ => specialize (H _ _ _ H')
      end; side_cond.
    Qed.

    Lemma name_eqb_refl n : name_eqb n n = true.
    Proof. case_eq (name_eqb n n); intros; name_eqb_to_eq; auto. Qed.

    Lemma valid_ident_new_cc_to_name s d r rf idc x y n :
      @valid_ident (type.base s) (type.base d) r rf idc x ->
      of_prefancy_ident idc x = Some y ->
      rf n = new_cc_to_name r (projT1 y) n.
    Proof. inversion 1; intros; hammer; simplify_ident. Qed.

    Lemma new_cc_to_name_Z_cases r i n x :
      new_cc_to_name (d:=base.type.type_base tZ) r i n x
      = if in_dec CC.code_dec x (writes_conditions i)
        then n else r x.
    Proof. reflexivity. Qed.
    Lemma new_cc_to_name_ZZ_cases r i n x :
      new_cc_to_name (d:=base.type.type_base tZ * base.type.type_base tZ) r i n x
      = if in_dec CC.code_dec x (writes_conditions i)
        then fst n else r x.
    Proof. reflexivity. Qed.

    Lemma cc_good_helper cc cctx ctx r i x next_name :
      (forall c, name_lt (r c) next_name) ->
      (forall n v, consts v = Some n -> name_lt n next_name) ->
      cc_good cc cctx ctx r ->
      cc_good (CC.update (writes_conditions i) x cc_spec cc)
              (fun n : name =>
                 if name_eqb n next_name
                 then CC.cc_c (CC.update (writes_conditions i) x cc_spec cc)
                 else cctx n)
              (fun n : name => if name_eqb n next_name then x mod wordmax else ctx n)
              (new_cc_to_name (d:=base.type.type_base tZ) r i next_name).
    Proof.
      cbv [cc_good]; intros; destruct_head'_and.
      rewrite !new_cc_to_name_Z_cases.
      cbv [CC.update CC.cc_c CC.cc_m CC.cc_l CC.cc_z].
      repeat match goal with
             | _ => split; intros
             | _ => progress hammer
             | H : forall c, name_lt (r c) (r ?c2) |- _ => specialize (H c2)
             | H : (forall n v, consts v = Some n -> name_lt _ _),
                   H' : consts _ = Some _ |- _ => specialize (H _ _ H')
             | H : name_lt ?n ?n |- _ => apply name_lt_irr in H; contradiction
             | _ => cbv [cc_spec]; rewrite Z.mod_pow2_bits_low by omega
             | _ => congruence
             end.
    Qed.

    Lemma of_prefancy_correct
          {t} (e1 : @cexpr var t) (e2 : @cexpr _ t) r :
      valid_expr _ r e1 ->
      forall G,
      LanguageWf.Compilers.expr.wf G e1 e2 ->
      forall ctx cc cctx,
        cc_good cc cctx ctx r ->
        (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
        (forall n v2, In (existZZ (n, v2)) G -> fst n = snd n) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G ->
                         t = base.type.type_base tZ
                         \/ t = (base.type.type_base tZ * base.type.type_base tZ)%etype) ->
        (forall n, ctx n mod wordmax = ctx n) ->
        forall next_name result,
          (forall c : CC.code, name_lt (r c) next_name) ->
          (forall n v2, In (existZ (n, v2)) G -> name_lt n next_name) ->
          (forall n v2, In (existZZ (n, v2)) G -> name_lt (fst n) next_name) ->
          (interp_if_Z e2 = Some result) ->
          interp (@of_prefancy next_name t e1) cc ctx = result.
    Proof.
      induction 1; inversion 1; cbv [interp_if_Z];
        cbn [of_prefancy of_prefancy_step]; intros;
          match goal with H : context [interp_base _ _ _ = _] |- _ =>
                          pose proof (H (base.type.type_base base.type.Z)) end;
          try solve [prove_Ret]; [ | | ]; hammer;
            match goal with
            | H : context [interp (of_prefancy _ _) _ _ = _]
              |- interp _ ?cc' ?ctx' = _ =>
              match goal with
              | _ : context [LetInAppIdentZ _ _ _ _ _ _] |-  _=>
                erewrite H with
                    (G := (existZ (next_name, ctx' next_name)) :: G)
                    (e2 := _ (ctx' next_name))
                    (cctx := (fun n => if name_eqb n next_name then CC.cc_c cc' else cctx n))
              | _ : context [LetInAppIdentZZ _ _ _ _ _ _] |-  _=>
                erewrite H with
                    (G := (existZZ ((next_name, next_name), (ctx' next_name, Z.b2z (CC.cc_c cc')))) :: G)
                    (e2 := _ (ctx' next_name, Z.b2z (CC.cc_c cc')))
                    (cctx := (fun n => if name_eqb n next_name then CC.cc_c cc' else cctx n))
              end
            end;
            repeat match goal with
                   | _ => progress intros
                   | _ => rewrite name_eqb_refl in *
                   | _ => rewrite Z.testbit_spec' in *
                   | _ =>  erewrite valid_ident_new_cc_to_name by eassumption
                   | _ => rewrite new_cc_to_name_Z_cases
                   | _ => rewrite new_cc_to_name_ZZ_cases
                   | _ => solve [intros; eapply interp_base_helper; side_cond]
                   | _ => solve [intros; apply cc_good_helper; eauto]
                   | _ => reflexivity
                   | _ => solve [eauto using Z.mod_small, b2z_range]
                   | _ => progress autorewrite with zsimplify_fast
                   | _ => progress side_cond
                   end; [ | | ].
      { cbn - [cc_spec]; cbv [id]; cbn - [cc_spec].
        inversion wf_x; hammer.
        erewrite of_prefancy_identZ_loosen_correct by eauto.
        reflexivity. }
      { cbn - [cc_spec]; cbv [id]; cbn - [cc_spec].
        inversion wf_x; hammer.
        erewrite of_prefancy_identZ_correct by eassumption.
        reflexivity. }
      { cbn - [cc_spec]; cbv [id]; cbn - [cc_spec].
        match goal with H : _ |- _ => pose proof H; eapply identZZ_writes in H; [ | eassumption] end.
        inversion wf_x; hammer.
        erewrite of_prefancy_identZZ_correct by eassumption.
        erewrite of_prefancy_identZZ_correct_carry by eassumption.
        rewrite <-surjective_pairing. reflexivity. }
    Qed.
  End Proofs.
End of_prefancy.

Section allocate_registers.
  Context (reg name : Type) (name_eqb : name -> name -> bool) (error : reg).
  Fixpoint allocate (e : @expr name) (reg_list : list reg) (name_to_reg : name -> reg) : @expr reg :=
    match e with
    | Ret n => Ret (name_to_reg n)
    | Instr i rd args cont =>
      match reg_list with
      | r :: reg_list' => Instr i r (Tuple.map name_to_reg args) (allocate cont reg_list' (fun n => if name_eqb n rd then r else name_to_reg n))
      | nil => Ret error
      end
    end.
End allocate_registers.

Definition test_prog : @expr positive :=
  Instr (ADD (128)) 3%positive (1, 2)%positive
        (Instr (ADDC 0) 4%positive (3,1)%positive
               (Ret 4%positive)).

Definition x1 := 2^256 - 1.
Definition x2 := 2^128 - 1.
Definition wordmax := 2^256.
Definition expected :=
  let r3' := (x1 + (x2 << 128)) in
  let r3 := r3' mod wordmax in
  let c := r3' / wordmax in
  let r4' := (r3 + x1 + c) in
  r4' mod wordmax.
Definition actual :=
  interp Pos.eqb
         (2^256) cc_spec test_prog {|CC.cc_c:=false; CC.cc_m:=false; CC.cc_l:=false; CC.cc_z:=false|}
         (fun n => if n =? 1%positive
                   then x1
                   else if n =? 2%positive
                        then x2
                        else 0).
Lemma test_prog_ok : expected = actual.
Proof. reflexivity. Qed.

Definition of_Expr {t} next_name (consts : Z -> option positive)
           (e : expr.Expr t)
           (x : type.for_each_lhs_of_arrow (var positive) t)
  : positive -> @expr positive :=
  fun error =>
    @of_prefancy positive Pos.succ error consts next_name _ (invert_expr.smart_App_curried (e _) x).

Section Proofs.
  Fixpoint var_pairs {t var1 var2}
    : type.for_each_lhs_of_arrow var1 t
      -> type.for_each_lhs_of_arrow var2 t
      -> list {t : Compilers.type base.type.type & (var1 t * var2 t)%type } :=
    match t as t0 return
          (type.for_each_lhs_of_arrow var1 t0
           -> type.for_each_lhs_of_arrow var2 t0 -> _) with
    | type.base _ => fun _ _ => nil
    | (s -> d)%ptype =>
      fun x1 x2 =>
        existT _ _ (fst x1, fst x2) :: var_pairs (snd x1) (snd x2)
    end.

  Local Notation existZ := (existT _  (type.base (base.type.type_base base.type.Z))).
  Local Notation existZZ := (existT _  (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)).

  Fixpoint make_ctx (var_list : list (positive * Z)) : positive -> Z :=
    match var_list with
    | [] => fun _ => 0
    | (n, v) :: l' => fun m => if (m =? n)%positive then v else make_ctx l' m
    end.

  Definition make_pairs :
    list (positive * Z) -> list {t : Compilers.type base.type.type & (var positive t * @type.interp base.type base.interp t)%type } := map (fun x => existZ x).

  Fixpoint make_consts (consts_list : list (positive * Z)) : Z -> option positive :=
    match consts_list with
    | [] => fun _ => None
    | (n, v) :: l' => fun x => if x =? v then Some n else make_consts l' x
    end.

  Local Ltac ez :=
    repeat match goal with
           | _ => progress intros
           | _ => progress subst
           | H : _ \/ _ |- _ => destruct H
           | H : _ |- _ => rewrite Pos.eqb_eq in H
           | H : _ |- _ => rewrite Pos.eqb_neq in H
           | _ => progress break_innermost_match
           | _ => progress break_match_hyps
           | _ => progress inversion_sigma
           | _ => progress inversion_option
           | _ => progress inversion_prod
           | _ => progress HProp.eliminate_hprop_eq
           | _ => progress Z.ltb_to_lt
           | _ => reflexivity
           | _ => congruence
           | _ => solve [eauto]
           end.


  Lemma make_consts_ok consts_list n v :
    make_consts consts_list v = Some n ->
    In (existZ (n, v)%zrange) (make_pairs consts_list).
  Proof.
    cbv [make_pairs]; induction consts_list as [|[ ? ? ] ?]; cbn; ez.
  Qed.

  Lemma make_pairs_ok consts_list:
    forall v1 v2,
      In (existZ (v1, v2)%zrange) (make_pairs consts_list) ->
      In (v1, v2) consts_list.
  Proof.
    cbv [make_pairs]. induction consts_list as [| [ n v ] ? ]; cbn; [ tauto | ]. ez.
  Qed.
  Lemma make_ctx_ok consts_list:
    (forall n v1 v2, In (n, v1) consts_list ->
                     In (n, v2) consts_list -> v1 = v2) ->
    forall n v,
      In (n, v) consts_list ->
    make_ctx consts_list n = v.
  Proof.
    induction consts_list as [| [ n v ] ? ]; cbn; [ tauto | ].
    repeat match goal with
           | _ => progress cbn [eq_rect fst snd] in *
           | _ => progress ez
           end.
  Qed.

  Lemma make_ctx_cases consts_list n :
    make_ctx consts_list n = 0 \/
    In (n, make_ctx consts_list n) consts_list.
  Proof. induction consts_list; cbn; ez. Qed.

  Lemma only_integers consts_list t v1 v2 :
    In (existT (fun t : type => (var positive t * type.interp base.interp t)%type) (type.base t)
               (v1, v2)%zrange) (make_pairs consts_list) ->
    t = base.type.type_base base.type.Z.
  Proof.
    induction consts_list; cbn; [ tauto | ].
    destruct 1; congruence || tauto.
  Qed.

  Lemma no_pairs consts_list v1 v2 :
    In (existZZ (v1, v2)%zrange) (make_pairs consts_list) -> False.
  Proof. intro H; apply only_integers in H. congruence. Qed.


  Definition make_cc last_wrote ctx carry_flag : CC.state :=
    {| CC.cc_c := carry_flag;
       CC.cc_m := cc_spec CC.M (ctx (last_wrote CC.M));
       CC.cc_l := cc_spec CC.L (ctx (last_wrote CC.L));
       CC.cc_z := cc_spec CC.Z (ctx (last_wrote CC.Z)
                                + (if (last_wrote CC.C =? last_wrote CC.Z)%positive
                                   then wordmax * Z.b2z carry_flag else 0));
    |}.


  Hint Resolve Pos.lt_trans Pos.lt_irrefl Pos.lt_succ_diag_r Pos.eqb_refl.
  Hint Resolve in_or_app.
  Hint Resolve make_consts_ok make_pairs_ok make_ctx_ok no_pairs.
  (* TODO : probably not all of these preconditions are necessary -- prune them sometime *)
  Lemma of_Expr_correct next_name consts_list arg_list error
        (carry_flag : bool)
        (last_wrote : CC.code -> positive) (* variables which last wrote to each flag; put RegZero if flag empty *)
        t (e : Expr t)
        (x1 : type.for_each_lhs_of_arrow (var positive) t)
        (x2 : type.for_each_lhs_of_arrow _ t) result :
    let e1 := (invert_expr.smart_App_curried (e _) x1) in
    let e2 := (invert_expr.smart_App_curried (e _) x2) in
    let ctx := make_ctx (consts_list ++ arg_list) in
    let consts := make_consts consts_list in
    let cc := make_cc last_wrote ctx carry_flag in
    let G := make_pairs consts_list ++ make_pairs arg_list in
    (forall c, last_wrote c < next_name)%positive ->
    (forall n v, In (n, v) (consts_list ++ arg_list) -> (n < next_name)%positive) ->
    (In (last_wrote CC.C, Z.b2z carry_flag) consts_list) ->
    (forall n v1 v2, In (n, v1) (consts_list ++ arg_list) ->
                     In (n, v2) (consts_list ++ arg_list) -> v1 = v2) (* no duplicate names *) ->
    (forall v1 v2, In (v1, v2) consts_list -> v2 mod 2 ^ 256 = v2) ->
    (forall v1 v2, In (v1, v2) arg_list -> v2 mod 2 ^ 256 = v2) ->
    (LanguageWf.Compilers.expr.wf G e1 e2) ->
    valid_expr _ error consts _ last_wrote e1 ->
    interp_if_Z e2 = Some result ->
    interp Pos.eqb wordmax cc_spec (of_Expr next_name consts e x1 error) cc ctx = result.
  Proof.
    cbv [of_Expr]; intros.
    eapply of_prefancy_correct with (name_lt := Pos.lt)
                                    (cctx := fun n => if (n =? last_wrote CC.C)%positive
                                                      then carry_flag
                                                      else match make_consts consts_list 1 with
                                                           | Some n1 => (n =? n1)%positive
                                                           | _ => false
                                                           end);
      cbv [id]; eauto;
      try apply Pos.eqb_neq; intros;
        try solve [apply make_ctx_ok; auto; apply make_pairs_ok;
                   cbv [make_pairs]; rewrite map_app; auto ];
        repeat match goal with
               | H : _ |- _ => apply in_app_or in H; destruct H
               | H : In _ (make_pairs _) |- context [ _ = base.type.type_base _] => apply only_integers in H
               | H : In _ (make_pairs _) |- context [interp_base] =>
                 pose proof (only_integers _ _ _ _ H); subst; cbn [interp_base]
               | _ => solve [eauto]
               | _ => solve [exfalso; eauto]
               end.
    (* TODO : clean this up *)
    { cbv [cc_good make_cc]; repeat split; intros;
        [ rewrite Pos.eqb_refl; reflexivity | | ];
        break_innermost_match; try rewrite Pos.eqb_eq in *; subst; try reflexivity;
          repeat match goal with
                 | H : make_consts _ _ = Some _ |- _ =>
                   apply make_consts_ok, make_pairs_ok in H
                 | _ => apply Pos.eqb_neq; intro; subst
                 | _ => inversion_option; congruence
                 end;
          match goal with
          | H : In (?n, ?x) consts_list, H': In (?n, ?y) consts_list,
                                             H'' : forall n x y, In (n,x) _ -> In (n,y) _ -> x = y |- _ =>
            assert (x = y) by (eapply H''; eauto)
          end; destruct carry_flag; cbn [Z.b2z] in *; congruence. }
    { match goal with |- context [make_ctx ?l ?n] =>
                      let H := fresh in
                      destruct (make_ctx_cases l n) as [H | H];
                        [ rewrite H | apply in_app_or in H; destruct H ]
      end; eauto. }
  Qed.
End Proofs.
