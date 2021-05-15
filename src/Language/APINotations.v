Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Language.PreExtra.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.IdentifiersBasicGENERATED.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.DebugPrint.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.Head.
Import Coq.Lists.List ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.
Export Language.Pre.
Export Language.
Export IdentifiersBasicGENERATED.

Import EqNotations.
Module Compilers.
  Export Language.Pre.
  Export Language.Compilers.
  Import IdentifiersBasicLibrary.Compilers.
  Import IdentifiersBasicLibrary.Compilers.Basic.
  Import IdentifiersBasicGenerate.Compilers.Basic.Tactic.
  Import IdentifiersBasicGENERATED.Compilers.

  Definition exprInfo : Classes.ExprInfoT := Eval hnf in GoalType.exprInfo package.
  Definition exprExtraInfo : @Classes.ExprExtraInfoT exprInfo := Eval hnf in GoalType.exprExtraInfo package.

  Global Existing Instances
         baseHasNat
         baseHasNatCorrect
         try_make_base_transport_cps_correct
         buildEagerIdent
         buildInterpEagerIdentCorrect
         toRestrictedIdent
         toFromRestrictedIdent
         buildInterpIdentCorrect
         invertIdent
         buildInvertIdentCorrect
         base_default
         exprInfo
  .
  Global Existing Instance reflect_base_beq | 10.
  Global Existing Instance reflect_base_interp_beq | 10.
  Global Existing Instance try_make_base_transport_cps | 5.
  Global Existing Instance buildIdent | 5.
  Global Existing Instance eqv_Reflexive_Proper | 1.
  Global Existing Instance ident_interp_Proper | 1.

  Bind Scope etype_scope with base.

  Global Arguments ident_Literal {_} _ : assert.
  Global Arguments ident_comment {_} : assert.
  Global Arguments ident_comment_no_keep {_} : assert.
  Global Arguments ident_value_barrier : assert.
  Global Arguments ident_nil {_} : assert.
  Global Arguments ident_cons {_} : assert.
  Global Arguments ident_pair {_ _} : assert.
  Global Arguments ident_fst {_ _} : assert.
  Global Arguments ident_snd {_ _} : assert.
  Global Arguments ident_prod_rect {_ _ _} : assert.
  Global Arguments ident_bool_rect {_} : assert.
  Global Arguments ident_bool_rect_nodep {_} : assert.
  Global Arguments ident_nat_rect {_} : assert.
  Global Arguments ident_nat_rect_arrow {_ _} : assert.
  Global Arguments ident_eager_nat_rect {_} : assert.
  Global Arguments ident_eager_nat_rect_arrow {_ _} : assert.
  Global Arguments ident_list_rect {_ _} : assert.
  Global Arguments ident_list_rect_arrow {_ _ _} : assert.
  Global Arguments ident_eager_list_rect {_ _} : assert.
  Global Arguments ident_eager_list_rect_arrow {_ _ _} : assert.
  Global Arguments ident_list_case {_ _} : assert.
  Global Arguments ident_List_length {_} : assert.
  Global Arguments ident_List_firstn {_} : assert.
  Global Arguments ident_List_skipn {_} : assert.
  Global Arguments ident_List_repeat {_} : assert.
  Global Arguments ident_List_combine {_ _} : assert.
  Global Arguments ident_List_map {_ _} : assert.
  Global Arguments ident_List_app {_} : assert.
  Global Arguments ident_List_rev {_} : assert.
  Global Arguments ident_List_flat_map {_ _} : assert.
  Global Arguments ident_List_partition {_} : assert.
  Global Arguments ident_List_fold_right {_ _} : assert.
  Global Arguments ident_List_update_nth {_} : assert.
  Global Arguments ident_List_nth_default {_} : assert.
  Global Arguments ident_eager_List_nth_default {_} : assert.
  Global Arguments ident_Some {_} : assert.
  Global Arguments ident_None {_} : assert.
  Global Arguments ident_option_rect {_ _} : assert.
  Global Arguments ident_zrange_rect {_} : assert.
  Global Arguments eta_base_cps {_} _ _ : assert.
  Global Arguments ident_interp {_} _ : assert.
  Global Arguments base_interp_beq {_ _} _ _ : assert.
  Global Arguments reflect_base_interp_beq {_}.
  Global Arguments ident_is_var_like {_} _ : assert.
  Global Arguments eqv_Reflexive_Proper {_} _.
  Global Arguments ident_interp_Proper {_}.

  Ltac reify_base :=
    let package := reify_package_of_package package in
    reify_base_via_reify_package package.
  Ltac reify_base_type :=
    let package := reify_package_of_package package in
    reify_base_type_via_reify_package package.
  Ltac reify_type :=
    let package := reify_package_of_package package in
    reify_type_via_reify_package package.
  Ltac reify_ident :=
    let package := reify_package_of_package package in
    reify_ident_via_reify_package package.

  (** This file defines some convenience notations and definitions. *)
  Module base.
    Export Language.Compilers.base.

    Module type.
      Import IdentifiersBasicGENERATED.Compilers.
      Notation base := base (only parsing).
      Notation Z := Z (only parsing).
      Notation nat := nat (only parsing).
      Notation zrange := zrange (only parsing).
      Notation bool := bool (only parsing).
      Notation base_beq := Compilers.base_beq (only parsing).
      Notation string := string (only parsing).

      Export Language.Compilers.base.type.
      Notation type := (@type base) (only parsing).

      Notation baseHasNat := Compilers.baseHasNat (only parsing).
      Notation eta_base_cps_gen := Compilers.eta_base_cps_gen (only parsing).
      Notation eta_base_cps := Compilers.eta_base_cps (only parsing).
    End type.
    Notation type := (@base.type base) (only parsing).
    Notation base_interp := Compilers.base_interp (only parsing).
    Notation interp := (base.interp Compilers.base_interp) (only parsing).
    Notation reflect_base_beq := Compilers.reflect_base_beq (only parsing).
    Notation base_interp_beq := Compilers.base_interp_beq (only parsing).
    Notation baseHasNatCorrect := Compilers.baseHasNatCorrect (only parsing).
    Notation reflect_base_interp_eq := Compilers.reflect_base_interp_beq (only parsing).
    Notation try_make_base_transport_cps := Compilers.try_make_base_transport_cps (only parsing).
    Notation try_make_base_transport_cps_correct := Compilers.try_make_base_transport_cps_correct (only parsing).

    Notation reify_base t := (ltac:(let rt := reify_base t in exact rt)) (only parsing).
    Notation reify t := (ltac:(let rt := reify_base_type t in exact rt)) (only parsing).
    Notation reify_norm_base t := (ltac:(let t' := eval cbv in t in let rt := reify_base t' in exact rt)) (only parsing).
    Notation reify_norm t := (ltac:(let t' := eval cbv in t in let rt := reify_base_type t' in exact rt)) (only parsing).
    Notation reify_base_type_of e := (reify_base ((fun t (_ : t) => t) _ e)) (only parsing).
    Notation reify_type_of e := (reify ((fun t (_ : t) => t) _ e)) (only parsing).
    Notation reify_norm_base_type_of e := (reify_norm_base ((fun t (_ : t) => t) _ e)) (only parsing).
    Notation reify_norm_type_of e := (reify_norm ((fun t (_ : t) => t) _ e)) (only parsing).

    Ltac reify_base ty := Compilers.reify_base ty.
    Ltac reify ty := Compilers.reify_base_type ty.
    Ltac reify_type ty := Compilers.reify_type ty.
  End base.

  Module ident.
    Export Language.Compilers.ident.
    Notation ident := Compilers.ident (only parsing).

    Notation Literal := Compilers.ident_Literal (only parsing).
    Notation comment := Compilers.ident_comment (only parsing).
    Notation comment_no_keep := Compilers.ident_comment_no_keep (only parsing).
    Notation value_barrier := Compilers.ident_value_barrier (only parsing).
    Notation Nat_succ := Compilers.ident_Nat_succ (only parsing).
    Notation Nat_pred := Compilers.ident_Nat_pred (only parsing).
    Notation Nat_max := Compilers.ident_Nat_max (only parsing).
    Notation Nat_mul := Compilers.ident_Nat_mul (only parsing).
    Notation Nat_add := Compilers.ident_Nat_add (only parsing).
    Notation Nat_sub := Compilers.ident_Nat_sub (only parsing).
    Notation Nat_eqb := Compilers.ident_Nat_eqb (only parsing).
    Notation nil := Compilers.ident_nil (only parsing).
    Notation cons := Compilers.ident_cons (only parsing).
    Notation tt := Compilers.ident_tt (only parsing).
    Notation pair := Compilers.ident_pair (only parsing).
    Notation fst := Compilers.ident_fst (only parsing).
    Notation snd := Compilers.ident_snd (only parsing).
    Notation prod_rect := Compilers.ident_prod_rect (only parsing).
    Notation bool_rect := Compilers.ident_bool_rect (only parsing).
    Notation bool_rect_nodep := Compilers.ident_bool_rect_nodep (only parsing).
    Notation nat_rect := Compilers.ident_nat_rect (only parsing).
    Notation nat_rect_arrow := Compilers.ident_nat_rect_arrow (only parsing).
    Notation eager_nat_rect := Compilers.ident_eager_nat_rect (only parsing).
    Notation eager_nat_rect_arrow := Compilers.ident_eager_nat_rect_arrow (only parsing).
    Notation list_rect := Compilers.ident_list_rect (only parsing).
    Notation list_rect_arrow := Compilers.ident_list_rect_arrow (only parsing).
    Notation eager_list_rect := Compilers.ident_eager_list_rect (only parsing).
    Notation eager_list_rect_arrow := Compilers.ident_eager_list_rect_arrow (only parsing).
    Notation list_case := Compilers.ident_list_case (only parsing).
    Notation List_length := Compilers.ident_List_length (only parsing).
    Notation List_seq := Compilers.ident_List_seq (only parsing).
    Notation List_firstn := Compilers.ident_List_firstn (only parsing).
    Notation List_skipn := Compilers.ident_List_skipn (only parsing).
    Notation List_repeat := Compilers.ident_List_repeat (only parsing).
    Notation List_combine := Compilers.ident_List_combine (only parsing).
    Notation List_map := Compilers.ident_List_map (only parsing).
    Notation List_app := Compilers.ident_List_app (only parsing).
    Notation List_rev := Compilers.ident_List_rev (only parsing).
    Notation List_flat_map := Compilers.ident_List_flat_map (only parsing).
    Notation List_partition := Compilers.ident_List_partition (only parsing).
    Notation List_fold_right := Compilers.ident_List_fold_right (only parsing).
    Notation List_update_nth := Compilers.ident_List_update_nth (only parsing).
    Notation List_nth_default := Compilers.ident_List_nth_default (only parsing).
    Notation eager_List_nth_default := Compilers.ident_eager_List_nth_default (only parsing).
    Notation Z_add := Compilers.ident_Z_add (only parsing).
    Notation Z_mul := Compilers.ident_Z_mul (only parsing).
    Notation Z_pow := Compilers.ident_Z_pow (only parsing).
    Notation Z_sub := Compilers.ident_Z_sub (only parsing).
    Notation Z_opp := Compilers.ident_Z_opp (only parsing).
    Notation Z_div := Compilers.ident_Z_div (only parsing).
    Notation Z_modulo := Compilers.ident_Z_modulo (only parsing).
    Notation Z_log2 := Compilers.ident_Z_log2 (only parsing).
    Notation Z_log2_up := Compilers.ident_Z_log2_up (only parsing).
    Notation Z_eqb := Compilers.ident_Z_eqb (only parsing).
    Notation Z_leb := Compilers.ident_Z_leb (only parsing).
    Notation Z_ltb := Compilers.ident_Z_ltb (only parsing).
    Notation Z_geb := Compilers.ident_Z_geb (only parsing).
    Notation Z_gtb := Compilers.ident_Z_gtb (only parsing).
    Notation Z_of_nat := Compilers.ident_Z_of_nat (only parsing).
    Notation Z_to_nat := Compilers.ident_Z_to_nat (only parsing).
    Notation Z_shiftr := Compilers.ident_Z_shiftr (only parsing).
    Notation Z_shiftl := Compilers.ident_Z_shiftl (only parsing).
    Notation Z_land := Compilers.ident_Z_land (only parsing).
    Notation Z_lor := Compilers.ident_Z_lor (only parsing).
    Notation Z_min := Compilers.ident_Z_min (only parsing).
    Notation Z_max := Compilers.ident_Z_max (only parsing).
    Notation Z_bneg := Compilers.ident_Z_bneg (only parsing).
    Notation Z_lnot_modulo := Compilers.ident_Z_lnot_modulo (only parsing).
    Notation Z_lxor := Compilers.ident_Z_lxor (only parsing).
    Notation Z_truncating_shiftl := Compilers.ident_Z_truncating_shiftl (only parsing).
    Notation Z_mul_split := Compilers.ident_Z_mul_split (only parsing).
    Notation Z_mul_high := Compilers.ident_Z_mul_high (only parsing).
    Notation Z_add_get_carry := Compilers.ident_Z_add_get_carry (only parsing).
    Notation Z_add_with_carry := Compilers.ident_Z_add_with_carry (only parsing).
    Notation Z_add_with_get_carry := Compilers.ident_Z_add_with_get_carry (only parsing).
    Notation Z_sub_get_borrow := Compilers.ident_Z_sub_get_borrow (only parsing).
    Notation Z_sub_with_get_borrow := Compilers.ident_Z_sub_with_get_borrow (only parsing).
    Notation Z_ltz := Compilers.ident_Z_ltz (only parsing).
    Notation Z_zselect := Compilers.ident_Z_zselect (only parsing).
    Notation Z_add_modulo := Compilers.ident_Z_add_modulo (only parsing).
    Notation Z_rshi := Compilers.ident_Z_rshi (only parsing).
    Notation Z_cc_m := Compilers.ident_Z_cc_m (only parsing).
    Notation Z_combine_at_bitwidth := Compilers.ident_Z_combine_at_bitwidth (only parsing).
    Notation Z_cast := Compilers.ident_Z_cast (only parsing).
    Notation Z_cast2 := Compilers.ident_Z_cast2 (only parsing).
    Notation Some := Compilers.ident_Some (only parsing).
    Notation None := Compilers.ident_None (only parsing).
    Notation option_rect := Compilers.ident_option_rect (only parsing).
    Notation Build_zrange := Compilers.ident_Build_zrange (only parsing).
    Notation zrange_rect := Compilers.ident_zrange_rect (only parsing).
    Notation fancy_add := Compilers.ident_fancy_add (only parsing).
    Notation fancy_addc := Compilers.ident_fancy_addc (only parsing).
    Notation fancy_sub := Compilers.ident_fancy_sub (only parsing).
    Notation fancy_subb := Compilers.ident_fancy_subb (only parsing).
    Notation fancy_mulll := Compilers.ident_fancy_mulll (only parsing).
    Notation fancy_mullh := Compilers.ident_fancy_mullh (only parsing).
    Notation fancy_mulhl := Compilers.ident_fancy_mulhl (only parsing).
    Notation fancy_mulhh := Compilers.ident_fancy_mulhh (only parsing).
    Notation fancy_rshi := Compilers.ident_fancy_rshi (only parsing).
    Notation fancy_selc := Compilers.ident_fancy_selc (only parsing).
    Notation fancy_selm := Compilers.ident_fancy_selm (only parsing).
    Notation fancy_sell := Compilers.ident_fancy_sell (only parsing).
    Notation fancy_addm := Compilers.ident_fancy_addm (only parsing).

    Notation option_Some := Compilers.ident_Some (only parsing).
    Notation option_None := Compilers.ident_None (only parsing).

    Notation interp := Compilers.ident_interp (only parsing).

    Notation buildEagerIdent := Compilers.buildEagerIdent (only parsing).
    Notation buildInterpEagerIdentCorrect := Compilers.buildInterpEagerIdentCorrect (only parsing).
    Notation toRestrictedIdent := Compilers.toRestrictedIdent (only parsing).
    Notation toFromRestrictedIdent := Compilers.toFromRestrictedIdent (only parsing).

    Ltac reify := Compilers.reify_ident.

    Notation buildIdent := Compilers.buildIdent (only parsing).
    Notation is_var_like := Compilers.ident_is_var_like (only parsing).
    Notation buildInterpIdentCorrect := Compilers.buildInterpIdentCorrect (only parsing).
    Notation eqv_Reflexive_Proper := Compilers.eqv_Reflexive_Proper (only parsing).
    Notation interp_Proper := Compilers.ident_interp_Proper (only parsing).

    Definition is_comment t (idc : ident t) : Datatypes.bool
      := match idc with
         | comment _ => true
         | comment_no_keep _ => true
         | _ => false
         end.

    Module Export Notations.
      Export Language.Compilers.ident.Notations.
      Delimit Scope ident_scope with ident.
      Bind Scope ident_scope with ident.
      Notation interp := Compilers.ident_interp (only parsing).
      Global Arguments expr.Ident {base_type%type ident%function var%function t%etype} idc%ident.
      Notation "## x" := (Compilers.ident_Literal x) (only printing) : ident_scope.
      Notation "## x" := (Compilers.ident_Literal (t:=base.reify_base_type_of x) x) (only parsing) : ident_scope.
      Notation "## x" := (expr.Ident (Compilers.ident_Literal x)) (only printing) : expr_scope.
      Notation "## x" := (smart_Literal (base_interp:=base_interp) (t:=base.reify_type_of x) x) (only parsing) : expr_scope.
      Notation "# x" := (expr.Ident x) (only parsing) : expr_pat_scope.
      Notation "# x" := (@expr.Ident base.type _ _ _ x) : expr_scope.
      Notation "x @ y" := (expr.App x%expr_pat y%expr_pat) (only parsing) : expr_pat_scope.
      Notation "( x , y , .. , z )" := (expr.App (expr.App (#Compilers.ident_pair) .. (expr.App (expr.App (#Compilers.ident_pair) x%expr) y%expr) .. ) z%expr) : expr_scope.
      Notation "( x , y , .. , z )" := (expr.App (expr.App (#Compilers.ident_pair)%expr_pat .. (expr.App (expr.App (#Compilers.ident_pair)%expr_pat x%expr_pat) y%expr_pat) .. ) z%expr_pat) (only parsing) : expr_pat_scope.
      Notation "x :: y" := (#Compilers.ident_cons @ x @ y)%expr : expr_scope.
      Notation "[ ]" := (#Compilers.ident_nil)%expr : expr_scope.
      Notation "x :: y" := (#Compilers.ident_cons @ x @ y)%expr_pat (only parsing) : expr_pat_scope.
      Notation "[ ]" := (#Compilers.ident_nil)%expr_pat (only parsing) : expr_pat_scope.
      Notation "[ x ]" := (x :: [])%expr : expr_scope.
      Notation "[ x ; y ; .. ; z ]" := (#Compilers.ident_cons @ x @ (#Compilers.ident_cons @ y @ .. (#Compilers.ident_cons @ z @ #Compilers.ident_nil) ..))%expr : expr_scope.
      Notation "ls [[ n ]]"
        := ((#(Compilers.ident_List_nth_default) @ _ @ ls @ #(Compilers.ident_Literal n%nat))%expr)
           : expr_scope.
      Notation "xs ++ ys" := (#Compilers.ident_List_app @ xs @ ys)%expr : expr_scope.
      Notation "x - y" := (#Compilers.ident_Z_sub @ x @ y)%expr : expr_scope.
      Notation "x + y" := (#Compilers.ident_Z_add @ x @ y)%expr : expr_scope.
      Notation "x / y" := (#Compilers.ident_Z_div @ x @ y)%expr : expr_scope.
      Notation "x * y" := (#Compilers.ident_Z_mul @ x @ y)%expr : expr_scope.
      Notation "x >> y" := (#Compilers.ident_Z_shiftr @ x @ y)%expr : expr_scope.
      Notation "x << y" := (#Compilers.ident_Z_shiftl @ x @ y)%expr : expr_scope.
      Notation "x &' y" := (#Compilers.ident_Z_land @ x @ y)%expr : expr_scope.
      Notation "x || y" := (#Compilers.ident_Z_lor @ x @ y)%expr : expr_scope.
      Notation "x 'mod' y" := (#Compilers.ident_Z_modulo @ x @ y)%expr : expr_scope.
      Notation "- x" := (#Compilers.ident_Z_opp @ x)%expr : expr_scope.
      Global Arguments ident_interp _ !_.
    End Notations.
  End ident.
  Export ident.Notations.
  Notation ident := IdentifiersBasicGENERATED.Compilers.ident (only parsing).

  Ltac reify var term :=
    expr.reify constr:(base.type) ident ltac:(reify_base_type) ltac:(reify_ident) var term.
  Ltac Reify term :=
    expr.Reify constr:(base.type) ident ltac:(reify_base_type) ltac:(reify_ident) term.
  Ltac Reify_rhs _ :=
    expr.Reify_rhs constr:(base.type) ident ltac:(reify_base_type) ltac:(reify_ident) (@base.interp) (@ident_interp) ().

  Global Hint Extern 1 (@expr.Reified_of _ _ _ _ ?t ?v ?rv)
  => cbv [expr.Reified_of]; Reify_rhs (); reflexivity : typeclass_instances.

  Module Import invert_expr.
    Export Language.Compilers.invert_expr.

    Module ident.
      Notation invertIdent := Compilers.invertIdent (only parsing).
      Notation buildInvertIdentCorrect := Compilers.buildInvertIdentCorrect (only parsing).
    End ident.

    Section with_var.
      Context {var : type base.type -> Type}.
      Local Notation expr := (@expr base.type ident var).
      Local Notation try_transportP P := (@type.try_transport _ _ P _ _).
      Local Notation try_transport := (try_transportP _).
      Let type_base (x : base) : base.type := base.type.type_base x.
      Let base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base : base.type >-> type.type.
      Local Coercion type_base : Compilers.base >-> base.type.
      Local Notation tZ := (base.type.type_base Z).
      Local Notation tzrange := (base.type.type_base zrange).

      Definition invert_Z_cast {t} (e : expr t)
        : option ZRange.zrange
        := match invert_AppIdent e with
           | Some (existT (type.base tzrange) (idc, r))
             => r <- reflect_smart_Literal r;
                  if match idc with ident.Z_cast => true | _ => false end
                  then Some r
                  else None
           | _ => None
           end%option.

      Definition invert_Z_cast2 {t} (e : expr t)
        : option (ZRange.zrange * ZRange.zrange)
        := match invert_AppIdent e with
           | Some (existT (type.base (tzrange * tzrange))
                          (idc, r))
             => r <- reflect_smart_Literal r;
                  if match idc with ident.Z_cast2 => true | _ => false end
                  then Some r
                  else None
           | _ => None
           end%option.

      Definition invert_App_Z_cast (e : expr tZ)
        : option (ZRange.zrange * expr Z)
        := match invert_App e with
           | Some (existT (type.base tZ) (idc, v))
             => r <- invert_Z_cast idc;
                  Some (r, v)
           | _ => None
           end.

      Definition invert_App_Z_cast2 (e : expr (tZ * tZ))
        : option ((ZRange.zrange * ZRange.zrange) * expr (Z * Z))
        := match invert_App e with
           | Some (existT (type.base (tZ * tZ)) (idc, v))
             => r <- invert_Z_cast2 idc;
                  Some (r, v)
           | _ => None
           end.

      Definition invert_App_cast {t} (e : expr t)
        : option ((type.interp (Language.Compilers.base.interp (fun _ => ZRange.zrange)) t) * expr t)
        := match t return expr t -> option (type.interp _ t * expr t) with
           | type.base tZ => invert_App_Z_cast
           | type.base (tZ * tZ) => invert_App_Z_cast2
           | _ => fun _ => None
           end e.

      Definition invert_Literal_through_cast {t} (e : expr t)
        : option (option (type.interp (Language.Compilers.base.interp (fun _ => ZRange.zrange)) t) * type.interp base.interp t)
        := match invert_Literal e, invert_App_cast e with
           | Some v, _ => Some (None, v)
           | None, Some (r, e) => (v <- invert_Literal e; Some (Some r, v))%option
           | None, None => None
           end.
    End with_var.
  End invert_expr.

  Module DefaultValue.
    Export Language.Compilers.DefaultValue.
    Module type.
      Export Language.Compilers.DefaultValue.type.
      Module base.
        Export Language.Compilers.DefaultValue.type.base.
        Notation base_default := Compilers.base_default (only parsing).
      End base.
    End type.
  End DefaultValue.

  Module Classes.
    Export Language.Compilers.Classes.
    Notation exprInfo := Compilers.exprInfo (only parsing).
    Notation exprExtraInfo := Compilers.exprExtraInfo (only parsing).
  End Classes.

  Module Coercions.
    Coercion type_base (x : base) : base.type := base.type.type_base x.
    Coercion base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
    Global Arguments base {_} _ / .
    Global Arguments type_base _ / .
  End Coercions.
End Compilers.
