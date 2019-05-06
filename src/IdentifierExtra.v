Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.PreLanguage.
Require Import Crypto.Language.
Require Import Crypto.Identifier.
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
Export PreLanguage.
Export Language.
Export Identifier.

Import EqNotations.
Module Compilers.
  Export PreLanguage.
  Export Language.Compilers.
  Export Identifier.Compilers.

  Module base.
    Export Identifier.Compilers.base.

    Notation reify_base t := (ltac:(let rt := reify_base t in exact rt)) (only parsing).
    Notation reify t := (ltac:(let rt := reify t in exact rt)) (only parsing).
    Notation reify_norm_base t := (ltac:(let t' := eval cbv in t in let rt := reify_base t' in exact rt)) (only parsing).
    Notation reify_norm t := (ltac:(let t' := eval cbv in t in let rt := reify t' in exact rt)) (only parsing).
    Notation reify_base_type_of e := (reify_base ((fun t (_ : t) => t) _ e)) (only parsing).
    Notation reify_type_of e := (reify ((fun t (_ : t) => t) _ e)) (only parsing).
    Notation reify_norm_base_type_of e := (reify_norm_base ((fun t (_ : t) => t) _ e)) (only parsing).
    Notation reify_norm_type_of e := (reify_norm ((fun t (_ : t) => t) _ e)) (only parsing).
  End base.

  Module ident.
    Export Identifier.Compilers.ident.

    Module Export Notations.
      Export Language.Compilers.ident.Notations.
      Delimit Scope ident_scope with ident.
      Bind Scope ident_scope with ident.
      Global Arguments expr.Ident {base_type%type ident%function var%function t%etype} idc%ident.
      Notation "## x" := (Literal x) (only printing) : ident_scope.
      Notation "## x" := (Literal (t:=base.reify_base_type_of x) x) (only parsing) : ident_scope.
      Notation "## x" := (expr.Ident (Literal x)) (only printing) : expr_scope.
      Notation "## x" := (smart_Literal (base_interp:=base.base_interp) (t:=base.reify_type_of x) x) (only parsing) : expr_scope.
      Notation "# x" := (expr.Ident x) : expr_pat_scope.
      Notation "# x" := (@expr.Ident base.type _ _ _ x) : expr_scope.
      Notation "x @ y" := (expr.App x%expr_pat y%expr_pat) : expr_pat_scope.
      Notation "( x , y , .. , z )" := (expr.App (expr.App (#pair) .. (expr.App (expr.App (#pair) x%expr) y%expr) .. ) z%expr) : expr_scope.
      Notation "( x , y , .. , z )" := (expr.App (expr.App (#pair)%expr_pat .. (expr.App (expr.App (#pair)%expr_pat x%expr_pat) y%expr_pat) .. ) z%expr_pat) : expr_pat_scope.
      Notation "x :: y" := (#cons @ x @ y)%expr : expr_scope.
      Notation "[ ]" := (#nil)%expr : expr_scope.
      Notation "x :: y" := (#cons @ x @ y)%expr_pat : expr_pat_scope.
      Notation "[ ]" := (#nil)%expr_pat : expr_pat_scope.
      Notation "[ x ]" := (x :: [])%expr : expr_scope.
      Notation "[ x ; y ; .. ; z ]" := (#cons @ x @ (#cons @ y @ .. (#cons @ z @ #nil) ..))%expr : expr_scope.
      Notation "ls [[ n ]]"
        := ((#(List_nth_default) @ _ @ ls @ #(Literal n%nat))%expr)
           : expr_scope.
      Notation "xs ++ ys" := (#List_app @ xs @ ys)%expr : expr_scope.
      Notation "x - y" := (#Z_sub @ x @ y)%expr : expr_scope.
      Notation "x + y" := (#Z_add @ x @ y)%expr : expr_scope.
      Notation "x / y" := (#Z_div @ x @ y)%expr : expr_scope.
      Notation "x * y" := (#Z_mul @ x @ y)%expr : expr_scope.
      Notation "x >> y" := (#Z_shiftr @ x @ y)%expr : expr_scope.
      Notation "x << y" := (#Z_shiftl @ x @ y)%expr : expr_scope.
      Notation "x &' y" := (#Z_land @ x @ y)%expr : expr_scope.
      Notation "x || y" := (#Z_lor @ x @ y)%expr : expr_scope.
      Notation "x 'mod' y" := (#Z_modulo @ x @ y)%expr : expr_scope.
      Notation "- x" := (#Z_opp @ x)%expr : expr_scope.
      Global Arguments gen_interp _ _ !_.
      Global Arguments ident.Z_cast _%zrange_scope.
      Global Arguments ident.Z_cast2 _%zrange_scope.
    End Notations.
  End ident.
  Export ident.Notations.

  Ltac reify var term :=
    expr.reify constr:(base.type) ident ltac:(base.reify) ident.reify var term.
  Ltac Reify term :=
    expr.Reify constr:(base.type) ident ltac:(base.reify) ident.reify term.
  Ltac Reify_rhs _ :=
    expr.Reify_rhs constr:(base.type) ident ltac:(base.reify) ident.reify (@base.interp) (@ident.interp) ().

  Global Hint Extern 1 (@expr.Reified_of _ _ _ _ ?t ?v ?rv)
  => cbv [expr.Reified_of]; Reify_rhs (); reflexivity : typeclass_instances.

  Module Import invert_expr.
    Export Identifier.Compilers.invert_expr.

    Section with_var.
      Context {var : type base.type -> Type}.
      Local Notation expr := (@expr base.type ident var).
      Local Notation try_transportP P := (@type.try_transport _ _ P _ _).
      Local Notation try_transport := (try_transportP _).
      Let type_base (x : base.type.base) : base.type := base.type.type_base x.
      Let base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base : base.type >-> type.type.
      Local Coercion type_base : base.type.base >-> base.type.
      Local Notation tZ := (base.type.type_base base.type.Z).

      Definition invert_Z_cast (e : expr tZ)
        : option (zrange * expr base.type.Z)
        := match e with
           | expr.App (type.base tZ) _ (#(ident.Z_cast r)) v => Some (r, v)
           | _ => None
           end%core%expr_pat%expr.

      Definition invert_Z_cast2 (e : expr (base.type.Z * base.type.Z))
        : option ((zrange * zrange) * expr (base.type.Z * base.type.Z))
        := match e with
           | expr.App (type.base (tZ * tZ)) _ (#(ident.Z_cast2 r)) v => Some (r, v)
           | _ => None
           end%etype%core%expr_pat%expr.
    End with_var.
  End invert_expr.

  Module Import defaults.
    Notation expr := (@expr base.type ident).
    Notation Expr := (@expr.Expr base.type ident).
    Notation type := (type base.type).
    Coercion type_base (x : base.type.base) : base.type := base.type.type_base x.
    Coercion base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
    Global Arguments base {_} _ / .
    Global Arguments type_base _ / .
    Notation interp := (@expr.interp base.type ident base.interp (@ident.interp)).
    Notation Interp := (@expr.Interp base.type ident base.interp (@ident.interp)).
    Ltac reify_type ty := type.reify ltac:(base.reify) constr:(base.type) ty.
    Notation reify_type t := (ltac:(let rt := reify_type t in exact rt)) (only parsing).
    Notation reify_type_of e := (reify_type ((fun t (_ : t) => t) _ e)) (only parsing).
  End defaults.

  Module GallinaReify.
    Export Language.Compilers.GallinaReify.
    Module base.
      Export Language.Compilers.GallinaReify.base.
      (** [Reify] does Ltac type inference to get the type *)
      Notation Reify v
        := (@Reify_as base.type.base base.base_interp ident ident.buildIdent (base.reify_type_of v) (fun _ => v)) (only parsing).
    End base.

    (** [Reify] does Ltac type inference to get the type *)
    Notation Reify v
      := (@Reify_as base.type.base base.base_interp ident ident.buildIdent (reify_type_of v) (fun _ => v)) (only parsing).
  End GallinaReify.
End Compilers.
