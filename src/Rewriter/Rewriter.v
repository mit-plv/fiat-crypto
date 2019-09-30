Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.MSets.MSetPositive.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Crypto.Util.PrimitiveProd.
Require Crypto.Util.PrimitiveHList.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.UnderLets.
Require Import Crypto.Language.IdentifiersLibrary.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Tactics.DebugPrint.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Local Set Primitive Projections.
Import EqNotations.
Module Compilers.
  Export Language.Compilers.
  Export UnderLets.Compilers.
  Export IdentifiersLibrary.Compilers.
  Import invert_expr.

  Notation EvarMap := Compilers.pattern.EvarMap.
  Module pattern.
    Export IdentifiersLibrary.Compilers.pattern.

    Module base.
      Import IdentifiersLibrary.Compilers.pattern.base.
      Section with_base.
        Context {base : Type}
                (base_beq : base -> base -> bool).
        Local Notation type := (type base).

        Fixpoint partial_subst (ptype : type) (evar_map : EvarMap) : type
          := match ptype with
             | type.var p => match PositiveMap.find p evar_map with
                             | Some t => relax t
                             | None => type.var p
                             end
             | type.type_base t => type.type_base t
             | type.unit => type.unit
             | type.prod A B => type.prod (partial_subst A evar_map) (partial_subst B evar_map)
             | type.list A => type.list (partial_subst A evar_map)
             | type.option A => type.option (partial_subst A evar_map)
             end.

        Fixpoint subst (ptype : type) (evar_map : EvarMap) : option (Compilers.base.type base)
          := match ptype with
             | type.var p => PositiveMap.find p evar_map
             | type.type_base t => Some (Compilers.base.type.type_base t)
             | type.unit => Some Compilers.base.type.unit
             | type.prod A B
               => (A' <- subst A evar_map;
                     B' <- subst B evar_map;
                     Some (Compilers.base.type.prod A' B'))
             | type.list A => option_map Compilers.base.type.list (subst A evar_map)
             | type.option A => option_map Compilers.base.type.option (subst A evar_map)
             end%option.

        Fixpoint subst_default_relax P {t evm} : P t -> P (@subst_default base (relax t) evm)
          := match t return P t -> P (subst_default (relax t) evm) with
             | Compilers.base.type.type_base _
             | Compilers.base.type.unit
               => fun x => x
             | Compilers.base.type.prod A B
               => fun v
                  => @subst_default_relax
                       (fun A' => P (Compilers.base.type.prod A' _)) A evm
                       (@subst_default_relax
                          (fun B' => P (Compilers.base.type.prod _ B')) B evm
                          v)
             | Compilers.base.type.list A
               => @subst_default_relax (fun t => P (Compilers.base.type.list t)) A evm
             | Compilers.base.type.option A
               => @subst_default_relax (fun t => P (Compilers.base.type.option t)) A evm
             end.

        Fixpoint unsubst_default_relax P {t evm} : P (@subst_default base (relax t) evm) -> P t
          := match t return P (subst_default (relax t) evm) -> P t with
             | Compilers.base.type.type_base _
             | Compilers.base.type.unit
               => fun x => x
             | Compilers.base.type.prod A B
               => fun v
                  => @unsubst_default_relax
                       (fun A' => P (Compilers.base.type.prod A' _)) A evm
                       (@unsubst_default_relax
                          (fun B' => P (Compilers.base.type.prod _ B')) B evm
                          v)
             | Compilers.base.type.list A
               => @unsubst_default_relax (fun t => P (Compilers.base.type.list t)) A evm
             | Compilers.base.type.option A
               => @unsubst_default_relax (fun t => P (Compilers.base.type.option t)) A evm
             end.

        Fixpoint var_types_of (t : type) : Type
          := match t with
             | type.var _ => Compilers.base.type base
             | type.unit
             | type.type_base _
               => unit
             | type.prod A B => var_types_of A * var_types_of B
             | type.list A => var_types_of A
             | type.option A => var_types_of A
             end%type.

        Fixpoint add_var_types_cps {t : type} (v : var_types_of t) (evm : EvarMap) : ~> EvarMap
          := fun T k
             => match t return var_types_of t -> T with
                | type.var p
                  => fun t => k (PositiveMap.add p t evm)
                | type.prod A B
                  => fun '(a, b) => @add_var_types_cps A a evm _ (fun evm => @add_var_types_cps B b evm _ k)
                | type.list A => fun t => @add_var_types_cps A t evm _ k
                | type.option A => fun t => @add_var_types_cps A t evm _ k
                | type.type_base _
                | type.unit
                  => fun _ => k evm
                end v.

        Fixpoint unify_extracted
                 (ptype : type) (etype : Compilers.base.type base)
          : option (var_types_of ptype)
          := match ptype, etype return option (var_types_of ptype) with
             | type.var p, _ => Some etype
             | type.type_base t, Compilers.base.type.type_base t'
               => if base_beq t t'
                  then Some tt
                  else None
             | type.prod A B, Compilers.base.type.prod A' B'
               => a <- unify_extracted A A';
                    b <- unify_extracted B B';
                    Some (a, b)
             | type.list A, Compilers.base.type.list A'
               => unify_extracted A A'
             | type.option A, Compilers.base.type.option A'
               => unify_extracted A A'
             | type.unit, Compilers.base.type.unit => Some tt
             | type.type_base _, _
             | type.prod _ _, _
             | type.list _, _
             | type.option _, _
             | type.unit, _
               => None
             end%option.
      End with_base.
    End base.

    Module type.
      Section with_base.
        Context {base : Type}
                (base_beq : base -> base -> bool).
        Local Notation type := (type base).

        Fixpoint partial_subst (ptype : type) (evar_map : EvarMap) : type
          := match ptype with
             | type.base t => type.base (base.partial_subst t evar_map)
             | type.arrow s d => type.arrow (partial_subst s evar_map) (partial_subst d evar_map)
             end.

        Fixpoint subst (ptype : type) (evar_map : EvarMap) : option (type.type (Compilers.base.type base))
          := match ptype with
             | type.base t => option_map type.base (base.subst t evar_map)
             | type.arrow s d
               => (s' <- subst s evar_map;
                     d' <- subst d evar_map;
                     Some (type.arrow s' d'))
             end%option.

        Fixpoint subst_default_relax P {t evm} : P t -> P (type.subst_default (type.relax t) evm)
          := match t return P t -> P (type.subst_default (type.relax t) evm) with
             | type.base t => base.subst_default_relax (base:=base) (fun t => P (type.base t))
             | type.arrow A B
               => fun v
                  => @subst_default_relax
                       (fun A' => P (type.arrow A' _)) A evm
                       (@subst_default_relax
                          (fun B' => P (type.arrow _ B')) B evm
                          v)
             end.

        Fixpoint unsubst_default_relax P {t evm} : P (type.subst_default (type.relax t) evm) -> P t
          := match t return P (type.subst_default (type.relax t) evm) -> P t with
             | type.base t => base.unsubst_default_relax (base:=base) (fun t => P (type.base t))
             | type.arrow A B
               => fun v
                  => @unsubst_default_relax
                       (fun A' => P (type.arrow A' _)) A evm
                       (@unsubst_default_relax
                          (fun B' => P (type.arrow _ B')) B evm
                          v)
             end.

        Fixpoint var_types_of (t : type) : Type
          := match t with
             | type.base t => base.var_types_of t
             | type.arrow s d => var_types_of s * var_types_of d
             end%type.

        Fixpoint add_var_types_cps {t : type} (v : var_types_of t) (evm : EvarMap) : ~> EvarMap
          := fun T k
             => match t return var_types_of t -> T with
                | type.base t => fun v => @base.add_var_types_cps base t v evm _ k
                | type.arrow A B
                  => fun '(a, b) => @add_var_types_cps A a evm _ (fun evm => @add_var_types_cps B b evm _ k)
                end v.

        Fixpoint unify_extracted
                 (ptype : type) (etype : type.type (Compilers.base.type base))
          : option (var_types_of ptype)
          := match ptype, etype return option (var_types_of ptype) with
             | type.base t, type.base t'
               => base.unify_extracted base_beq t t'
             | type.arrow A B, type.arrow A' B'
               => a <- unify_extracted A A';
                    b <- unify_extracted B B';
                    Some (a, b)
             | type.base _, _
             | type.arrow _ _, _
               => None
             end%option.

        Local Notation forall_vars_body K LS EVM0
          := (fold_right
                (fun i k evm => forall t : Compilers.base.type base, k (PositiveMap.add i t evm))
                K
                LS
                EVM0).

        Definition forall_vars (p : PositiveSet.t) (k : EvarMap -> Type)
          := forall_vars_body k (List.rev (PositiveSet.elements p)) (PositiveMap.empty _).

        Definition under_forall_vars {p k1 k2}
                   (F : forall evm, k1 evm -> k2 evm)
          : forall_vars p k1 -> forall_vars p k2
          := list_rect
               (fun ls
                => forall evm0, forall_vars_body k1 ls evm0 -> forall_vars_body k2 ls evm0)
               F
               (fun x xs rec evm0 K1 t => rec _ (K1 t))
               (List.rev (PositiveSet.elements p))
               (PositiveMap.empty _).

        Definition under_forall_vars_relation1 {p k1}
                   (F : forall evm, k1 evm -> Prop)
          : forall_vars p k1 -> Prop
          := list_rect
               (fun ls
                => forall evm0, forall_vars_body k1 ls evm0 -> Prop)
               F
               (fun x xs rec evm0 K1 => forall t, rec _ (K1 t))
               (List.rev (PositiveSet.elements p))
               (PositiveMap.empty _).

        Definition under_forall_vars_relation {p k1 k2}
                   (F : forall evm, k1 evm -> k2 evm -> Prop)
          : forall_vars p k1 -> forall_vars p k2 -> Prop
          := list_rect
               (fun ls
                => forall evm0, forall_vars_body k1 ls evm0 -> forall_vars_body k2 ls evm0 -> Prop)
               F
               (fun x xs rec evm0 K1 K2 => forall t, rec _ (K1 t) (K2 t))
               (List.rev (PositiveSet.elements p))
               (PositiveMap.empty _).

        Fixpoint lam_forall_vars_gen {k : EvarMap -> Type}
                 (f : forall evm, k evm)
                 (ls : list PositiveMap.key)
          : forall evm0, forall_vars_body k ls evm0
          := match ls return forall evm0, forall_vars_body k ls evm0 with
             | nil => f
             | cons x xs => fun evm t => @lam_forall_vars_gen k f xs _
             end.

        Definition lam_forall_vars {p : PositiveSet.t} {k : EvarMap -> Type}
                   (f : forall evm, k evm)
          : forall_vars p k
          := @lam_forall_vars_gen k f _ _.

        Fixpoint app_forall_vars_gen {k : EvarMap -> Type}
                 (evm : EvarMap)
                 (ls : list PositiveMap.key)
          : forall evm0, forall_vars_body k ls evm0
                         -> option (k (fold_right (fun i k evm'
                                                   => k (match PositiveMap.find i evm with Some v => PositiveMap.add i v evm' | None => evm' end))
                                                  (fun evm => evm)
                                                  ls
                                                  evm0))
          := match ls return forall evm0, forall_vars_body k ls evm0
                                          -> option (k (fold_right (fun i k evm'
                                                                    => k (match PositiveMap.find i evm with Some v => PositiveMap.add i v evm' | None => evm' end))
                                                                   (fun evm => evm)
                                                                   ls
                                                                   evm0)) with
             | nil => fun evm0 val => Some val
             | cons x xs
               => match PositiveMap.find x evm as xt
                        return (forall evm0,
                                   (forall t, fold_right _ k xs (PositiveMap.add x t evm0))
                                   -> option (k (fold_right
                                                   _ _ xs
                                                   match xt with
                                                   | Some v => PositiveMap.add x v evm0
                                                   | None => evm0
                                                   end)))
                  with
                  | Some v => fun evm0 val => @app_forall_vars_gen k evm xs _ (val v)
                  | None => fun evm0 val => None
                  end
             end.

        Definition app_forall_vars {p : PositiveSet.t} {k : EvarMap -> Type}
                   (f : forall_vars p k)
                   (evm : EvarMap)
          : option (k (fold_right (fun i k evm'
                                   => k (match PositiveMap.find i evm with Some v => PositiveMap.add i v evm' | None => evm' end))
                                  (fun evm => evm)
                                  (List.rev (PositiveSet.elements p))
                                  (PositiveMap.empty _)))
          := @app_forall_vars_gen
               k evm
               (List.rev (PositiveSet.elements p))
               (PositiveMap.empty _)
               f.
      End with_base.
    End type.

    Inductive pattern {base} {ident : type base -> Type} : type base -> Type :=
    | Wildcard (t : type base) : pattern t
    | Ident {t} (idc : ident t) : pattern t
    | App {s d} (f : pattern (s -> d)) (x : pattern s) : pattern d.

    Module Export Notations.
      Delimit Scope pattern_scope with pattern.
      Bind Scope pattern_scope with pattern.
      Infix "@" := App : pattern_scope.
      Notation "# x" := (Ident x) : pattern_scope.
    End Notations.


    Record > anypattern {base} {ident : type base -> Type}
      := { type_of_anypattern : type base;
           pattern_of_anypattern :> @pattern base ident type_of_anypattern }.

    Module Raw.
      Inductive pattern {ident : Type} :=
      | Wildcard
      | Ident (idc : ident)
      | App (f x : pattern).
    End Raw.

    Global Arguments Wildcard {base ident}%type t%ptype.

    Fixpoint to_raw {base ident raw_ident}
             {to_raw_ident : forall t, ident t -> raw_ident}
             {t} (p : @pattern base ident t) : @Raw.pattern raw_ident
      := match p with
         | Wildcard t => Raw.Wildcard
         | Ident t idc => Raw.Ident (to_raw_ident t idc)
         | App s d f x => Raw.App (@to_raw _ _ _ to_raw_ident _ f) (@to_raw _ _ _ to_raw_ident _ x)
         end.

    Fixpoint collect_vars {base ident}
             {t} (p : @pattern base ident t) : PositiveSet.t
      := match p with
         | Wildcard t => type.collect_vars t
         | Ident t idc => type.collect_vars t
         | App s d f x => PositiveSet.union (@collect_vars _ _ _ x) (@collect_vars _ _ _ f)
         end.

    Fixpoint unify_list {base A B} (unif : A -> B -> EvarMap -> option EvarMap) (ls1 : list A) (ls2 : list B) (evm : EvarMap_at base)
      : option EvarMap
      := match ls1, ls2 with
         | nil, nil => Some evm
         | cons x xs, cons y ys
           => (evm <- unif x y evm;
                @unify_list base A B unif xs ys evm)%option
         | nil, _
         | cons _ _, _
           => None
         end.
  End pattern.
  Export pattern.Notations.

  Module RewriteRules.
    Module Compile.
      Section with_var0.
        Context {base_type} {ident var : type.type base_type -> Type}.
        Local Notation type := (type.type base_type).
        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
        Let type_base (t : base_type) : type := type.base t.
        Coercion type_base : base_type >-> type.

        Fixpoint value' (with_lets : bool) (t : type)
          := match t with
             | type.base t
               => if with_lets then UnderLets (expr t) else expr t
             | type.arrow s d
               => value' false s -> value' true d
             end.
        Definition value := value' false.
        Definition value_with_lets := value' true.

        Definition Base_value {t} : value t -> value_with_lets t
          := match t with
             | type.base t => fun v => UnderLets.Base v
             | type.arrow _ _ => fun v => v
             end.

        Fixpoint splice_under_lets_with_value {T t} (x : UnderLets T) : (T -> value_with_lets t) -> value_with_lets t
          := match t return (T -> value_with_lets t) -> value_with_lets t with
             | type.arrow s d
               => fun k v => @splice_under_lets_with_value T d x (fun x' => k x' v)
             | type.base _ => fun k => x <-- x; k x
             end%under_lets.
        Local Notation "x <--- v ; f" := (splice_under_lets_with_value x (fun v => f%under_lets)) : under_lets_scope.
        Definition splice_value_with_lets {t t'} : value_with_lets t -> (value t -> value_with_lets t') -> value_with_lets t'
          := match t return value_with_lets t -> (value t -> value_with_lets t') -> value_with_lets t' with
             | type.arrow _ _
               => fun e k => k e
             | type.base _ => fun e k => e <--- e; k e
             end%under_lets.
      End with_var0.
      Local Notation EvarMap := pattern.EvarMap.
      Section with_var.
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {base : Type}
                {try_make_transport_base_type_cps : type.try_make_transport_cpsT base}
                (base_beq : base -> base -> bool).
        Local Notation base_type := (base.type base).
        Local Notation pattern_base_type := (pattern.base.type base).
        Context {ident var : type.type base_type -> Type}
                (eta_ident_cps : forall {T : type.type base_type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                {pident : type.type pattern_base_type -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))
                {raw_pident : Type}
                (strip_types : forall t, pident t -> raw_pident)
                (raw_pident_beq : raw_pident -> raw_pident -> bool)

                (full_types : raw_pident -> Type)
                (invert_bind_args invert_bind_args_unknown : forall t (idc : ident t) (pidc : raw_pident), option (full_types pidc))
                (type_of_raw_pident : forall (pidc : raw_pident), full_types pidc -> type.type base_type)
                (raw_pident_to_typed : forall (pidc : raw_pident) (args : full_types pidc), ident (type_of_raw_pident pidc args))
                (raw_pident_is_simple : raw_pident -> bool).

        Local Notation type := (type.type base_type).
        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation pattern := (@pattern.pattern base pident).
        Local Notation rawpattern := (@pattern.Raw.pattern raw_pident).
        Local Notation anypattern := (@pattern.anypattern base pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
        Local Notation ptype := (type.type pattern_base_type).
        Local Notation value' := (@value' base_type ident var).
        Local Notation value := (@value base_type ident var).
        Local Notation value_with_lets := (@value_with_lets base_type ident var).
        Local Notation Base_value := (@Base_value base_type ident var).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base_type ident var).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base_type ident var).
        Local Notation to_raw_pattern := (@pattern.to_raw _ pident raw_pident (@strip_types)).
        Let type_base (x : base) : @base.type base := base.type.type_base x.
        Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
        Local Coercion base' : base.type >-> type.type.
        Local Coercion type_base : base >-> base.type.

        Context (reify_and_let_binds_base_cps : forall (t : base_type), expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T)
                (reflect_ident_iota : forall t (idc : ident t), option (value t)).

        Definition under_type_of_list_cps {A1 A2 ls}
                   (F : A1 -> A2)
          : type_of_list_cps A1 ls -> type_of_list_cps A2 ls
          := list_rect
               (fun ls
                => type_of_list_cps A1 ls -> type_of_list_cps A2 ls)
               F
               (fun T Ts rec f x => rec (f x))
               ls.

        Definition under_type_of_list_relation1_cps {A1 ls}
                   (F : A1 -> Prop)
          : type_of_list_cps A1 ls -> Prop
          := list_rect
               (fun ls
                => type_of_list_cps A1 ls -> Prop)
               F
               (fun T Ts rec f1 => forall x, rec (f1 x))
               ls.

        Definition under_type_of_list_relation_cps {A1 A2 ls}
                   (F : A1 -> A2 -> Prop)
          : type_of_list_cps A1 ls -> type_of_list_cps A2 ls -> Prop
          := list_rect
               (fun ls
                => type_of_list_cps A1 ls -> type_of_list_cps A2 ls -> Prop)
               F
               (fun T Ts rec f1 f2 => forall x, rec (f1 x) (f2 x))
               ls.

        Local Notation "e <---- e' ; f" := (splice_value_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
        Local Notation "e <----- e' ; f" := (splice_under_lets_with_value e' (fun e => f%under_lets)) : under_lets_scope.

        Fixpoint reify {with_lets} {t} : value' with_lets t -> expr t
          := match t, with_lets return value' with_lets t -> expr t with
             | type.base _, false => fun v => v
             | type.base _, true => fun v => UnderLets.to_expr v
             | type.arrow s d, _
               => fun f
                  => λ x , @reify _ d (f (@reflect _ s ($x)))
             end%expr%under_lets%cps
        with reflect {with_lets} {t} : expr t -> value' with_lets t
             := match t, with_lets return expr t -> value' with_lets t with
                | type.base _, false => fun v => v
                | type.base _, true => fun v => UnderLets.Base v
                | type.arrow s d, _
                  => fun f (x : value' _ _) => @reflect _ d (f @ (@reify _ s x))
                end%expr%under_lets.

        Fixpoint reify_expr {t} (e : @expr.expr base_type ident value t)
          : @expr.expr base_type ident var t
          := match e in expr.expr t return expr.expr t with
             | expr.Ident t idc => expr.Ident idc
             | expr.Var t v => reify v
             | expr.Abs s d f => expr.Abs (fun x => @reify_expr _ (f (reflect (expr.Var x))))
             | expr.App s d f x => expr.App (@reify_expr _ f) (@reify_expr _ x)
             | expr.LetIn A B x f => expr.LetIn (@reify_expr _ x) (fun xv => @reify_expr _ (f (reflect (expr.Var xv))))
             end.

        (** N.B. In order to preserve the (currently unstated)
              invariant that ensures that the rewriter does enough
              rewriting, when we reify rewrite rules, we have to
              perform β on the RHS to ensure that there are no var
              nodes holding values which show up in the heads of app
              nodes.  Note that we also perform βιδ on "eager"
              identifiers, which is what allows us to handle
              [list_rect] and [nat_rect] recursion rules. *)
        Fixpoint reflect_expr_beta_iota {t} (e : @expr.expr base_type ident value t)
          : UnderLets (value t)
          := match e in expr.expr t return UnderLets (value t) with
             | expr.Var t v => UnderLets.Base v
             | expr.Abs s d f => UnderLets.Base (fun x : value s => fx <----- @reflect_expr_beta_iota d (f x); Base_value fx)
             | expr.App s (type.base d) f x
               => f <-- @reflect_expr_beta_iota _ f;
                    x <-- @reflect_expr_beta_iota _ x;
                    f x
             | expr.App s (type.arrow _ _) f x
               => f <-- @reflect_expr_beta_iota _ f;
                    x <-- @reflect_expr_beta_iota _ x;
                    UnderLets.Base (f x)
             | expr.LetIn A B x f
               => x <-- @reflect_expr_beta_iota _ x;
                    UnderLets.UnderLet
                      (reify x)
                      (fun xv => @reflect_expr_beta_iota _ (f (reflect (expr.Var xv))))
             | expr.Ident t idc => UnderLets.Base match reflect_ident_iota t idc with
                                                  | Some ridc => ridc
                                                  | None => reflect (expr.Ident idc)
                                                  end
             end%under_lets%option.

        Definition reify_to_UnderLets {with_lets} {t} : value' with_lets t -> UnderLets (expr t)
          := match t, with_lets return value' with_lets t -> UnderLets (expr t) with
             | type.base _, false => fun v => UnderLets.Base v
             | type.base _, true => fun v => v
             | type.arrow s d, _
               => fun f => UnderLets.Base (reify f)
             end.

        Definition reify_expr_beta_iota {t} (e : @expr.expr base_type ident value t)
          : UnderLets (@expr.expr base_type ident var t)
          := e <-- @reflect_expr_beta_iota t e; reify_to_UnderLets e.

        Definition reify_and_let_binds_cps {with_lets} {t} : value' with_lets t -> forall T, (expr t -> UnderLets T) -> UnderLets T
          := match t, with_lets return value' with_lets t -> forall T, (expr t -> UnderLets T) -> UnderLets T with
             | type.base _, false => reify_and_let_binds_base_cps _
             | type.base _, true => fun v => fun T k => v' <-- v; reify_and_let_binds_base_cps _ v' T k
             | type.arrow s d, _
               => fun f T k => k (reify f)
             end%expr%under_lets%cps.

        Inductive rawexpr : Type :=
        | rIdent (known : bool) {t} (idc : ident t) {t'} (alt : expr t')
        | rApp (f x : rawexpr) {t} (alt : expr t)
        | rExpr {t} (e : expr t)
        | rValue {t} (e : value t).

        Definition type_of_rawexpr (e : rawexpr) : type
          := match e with
             | rIdent _ t idc t' alt => t'
             | rApp f x t alt => t
             | rExpr t e => t
             | rValue t e => t
             end.
        Definition expr_of_rawexpr (e : rawexpr) : expr (type_of_rawexpr e)
          := match e with
             | rIdent _ t idc t' alt => alt
             | rApp f x t alt => alt
             | rExpr t e => e
             | rValue t e => reify e
             end.
        Definition value_of_rawexpr (e : rawexpr) : value (type_of_rawexpr e)
          := Eval cbv [expr_of_rawexpr] in
              match e with
              | rValue t e => e
              | e => reflect (expr_of_rawexpr e)
              end.
        Definition rValueOrExpr {t} : value t -> rawexpr
          := match t with
             | type.base _ => @rExpr _
             | type.arrow _ _ => @rValue _
             end.
        Definition rValueOrExpr2 {t} : value t -> expr t -> rawexpr
          := match t with
             | type.base _ => fun v e => @rExpr _ e
             | type.arrow _ _ => fun v e => @rValue _ v
             end.

        Definition try_rExpr_cps {T t} (k : option rawexpr -> T) : expr t -> T
          := match t with
             | type.base _ => fun e => k (Some (rExpr e))
             | type.arrow _ _ => fun _ => k None
             end.

        (* Allows assuming that we know the ident that we're revealing; mainly used in proofs *)
        Definition reveal_rawexpr_cps_gen (assume_known : option bool)
                   (e : rawexpr) : ~> rawexpr
          := fun T k
             => match e, assume_known with
                | rExpr _ e as r, _
                | rValue (type.base _) e as r, _
                  => match e with
                     | expr.Ident t idc => k (rIdent (match assume_known with Some known => known | _ => false end) idc e)
                     | expr.App s d f x => k (rApp (rExpr f) (rExpr x) e)
                     | _ => k r
                     end
                | rIdent _ t idc t' alt, Some known => k (rIdent known idc alt)
                | e', _ => k e'
                end.

        Definition reveal_rawexpr_cps (e : rawexpr) : ~> rawexpr
          := reveal_rawexpr_cps_gen None e.

        (** First, the uncurried form *)
        Fixpoint unification_resultT' {var} {t} (p : pattern t) (evm : EvarMap) : Type
          := match p return Type with
             | pattern.Wildcard t => var (pattern.type.subst_default t evm)
             | pattern.Ident t idc => type_of_list (pident_arg_types t idc)
             | pattern.App s d f x
               => @unification_resultT' var _ f evm * @unification_resultT' var _ x evm
             end%type.

        Fixpoint with_unification_resultT' {var} {t} (p : pattern t) (evm : EvarMap) (K : Type) : Type
          := match p return Type with
             | pattern.Wildcard t => var (pattern.type.subst_default t evm) -> K
             | pattern.Ident t idc => type_of_list_cps K (pident_arg_types t idc)
             | pattern.App s d f x
               => @with_unification_resultT' var _ f evm (@with_unification_resultT' var _ x evm K)
             end%type.

        Fixpoint app_with_unification_resultT' {var t p evm K} {struct p}
          : @with_unification_resultT' var t p evm K -> @unification_resultT' var t p evm -> K
          := match p return with_unification_resultT' p evm K -> unification_resultT' p evm -> K with
             | pattern.Wildcard t => fun f x => f x
             | pattern.Ident t idc => app_type_of_list
             | pattern.App s d f x
               => fun F (xy : unification_resultT' f _ * unification_resultT' x _)
                  => @app_with_unification_resultT'
                       _ _ x _ _
                       (@app_with_unification_resultT'
                          _ _ f _ _ F (fst xy))
                       (snd xy)
             end.

        Fixpoint lam_unification_resultT' {var t p evm K} {struct p}
          : (@unification_resultT' var t p evm -> K) -> @with_unification_resultT' var t p evm K
          := match p return (unification_resultT' p evm -> K) -> with_unification_resultT' p evm K with
             | pattern.Wildcard t => fun f x => f x
             | pattern.Ident t idc => lam_type_of_list
             | pattern.App s d f x
               => fun (F : unification_resultT' f _ * unification_resultT' x _ -> _)
                  => @lam_unification_resultT'
                       _ _ f _ _
                       (fun fv
                        => @lam_unification_resultT'
                             _ _ x _ _ (fun xv => F (fv, xv)))
             end.

        (** TODO: Maybe have a fancier version of this that doesn't
             actually need to insert casts, by doing a fixpoint on the
             list of elements / the evar map *)
        Fixpoint app_transport_with_unification_resultT'_cps {var t p evm1 evm2 K} {struct p}
          : @with_unification_resultT' var t p evm1 K -> @unification_resultT' var t p evm2 -> forall T, (K -> option T) -> option T
          := fun f x T k
             => match p return with_unification_resultT' p evm1 K -> unification_resultT' p evm2 -> option T with
                | pattern.Wildcard t
                  => fun f x
                     => (tr <- type.try_make_transport_cps var _ _;
                           (tr <- tr;
                              k (f (tr x)))%option)%cps
             | pattern.Ident t idc => fun f x => k (app_type_of_list f x)
             | pattern.App s d f x
               => fun F (xy : unification_resultT' f _ * unification_resultT' x _)
                  => @app_transport_with_unification_resultT'_cps
                       _ _ f _ _ _ F (fst xy) T
                       (fun F'
                        => @app_transport_with_unification_resultT'_cps
                             _ _ x _ _ _ F' (snd xy) T
                             (fun x' => k x'))
             end%option f x.

        Fixpoint under_with_unification_resultT' {var t p evm K1 K2}
                 (F : K1 -> K2)
                 {struct p}
          : @with_unification_resultT' var t p evm K1 -> @with_unification_resultT' var t p evm K2
          := match p return with_unification_resultT' p evm K1 -> with_unification_resultT' p evm K2 with
             | pattern.Wildcard t => fun f v => F (f v)
             | pattern.Ident t idc => under_type_of_list_cps F
             | pattern.App s d f x
               => @under_with_unification_resultT'
                    _ _ f evm _ _
                    (@under_with_unification_resultT' _ _ x evm _ _ F)
             end.

        Definition with_unification_resultT {var t} (p : pattern t) (K : type -> Type) : Type
          := pattern.type.forall_vars
               (pattern.collect_vars p)
               (fun evm => @with_unification_resultT' var t p evm (K (pattern.type.subst_default t evm))).

        Definition unification_resultT {var t} (p : pattern t) : Type
          := { evm : EvarMap & @unification_resultT' var t p evm }.

        Definition app_with_unification_resultT_cps {var t p K}
          : @with_unification_resultT var t p K -> @unification_resultT var t p -> forall T, ({ evm' : _ & K (pattern.type.subst_default t evm') } -> option T) -> option T
          := fun f x T k
             => (f' <- pattern.type.app_forall_vars f (projT1 x);
                   app_transport_with_unification_resultT'_cps
                     f' (projT2 x) _
                     (fun fx
                      => k (existT _ _ fx)))%option.

        Definition lam_unification_resultT {var' t p K}
          : (forall v : @unification_resultT var' t p, K (pattern.type.subst_default t (projT1 v))) -> @with_unification_resultT var' t p K
          := fun f
             => pattern.type.lam_forall_vars
                  (fun evm
                   => lam_unification_resultT'
                        (K:=K (pattern.type.subst_default t evm))
                        (fun x' => f (existT (unification_resultT' p) evm x'))).

        Definition partial_lam_unification_resultT {var' t p K}
          : (forall evm, @with_unification_resultT' var' t p evm (K (pattern.type.subst_default t evm))) -> @with_unification_resultT var' t p K
          := pattern.type.lam_forall_vars.

        Definition under_with_unification_resultT {var t p K1 K2}
                 (F : forall evm, K1 (pattern.type.subst_default t evm) -> K2 (pattern.type.subst_default t evm))
          : @with_unification_resultT var t p K1 -> @with_unification_resultT var t p K2
          := pattern.type.under_forall_vars
               (fun evm => under_with_unification_resultT' (F evm)).

        Fixpoint preunify_types {t} (e : rawexpr) (p : pattern t) {struct p}
          : option (option (ptype * type))
          := match p, e with
             | pattern.Wildcard t, _
               => Some (Some (t, type_of_rawexpr e))
             | pattern.Ident pt pidc, rIdent known t idc _ _
               => if andb known (type.type_beq _ (pattern.base.type.type_beq _ base_beq) pt (pattern.type.relax t)) (* relies on evaluating to [false] if [known] is [false] *)
                  then Some None
                  else Some (Some (pt, t))
             | pattern.App s d pf px, rApp f x _ _
               => (resa <- @preunify_types _ f pf;
                     resb <- @preunify_types _ x px;
                     Some match resa, resb with
                          | None, None => None
                          | None, Some t
                          | Some t, None => Some t
                          | Some (a, a'), Some (b, b')
                            => Some (type.arrow a b, type.arrow a' b')
                          end)
             | pattern.Ident _ _, _
             | pattern.App _ _ _ _, _
               => None
             end%option.

        (* for unfolding help *)
        Definition option_type_type_beq := option_beq (type.type_beq _ (base.type.type_beq _ base_beq)).

        Definition unify_types {t} (e : rawexpr) (p : pattern t) : ~> option EvarMap
          := fun T k
             => match preunify_types e p with
                | Some (Some (pt, t))
                  => match pattern.type.unify_extracted base_beq pt t with
                     | Some vars
                       => pattern.type.add_var_types_cps
                            vars (PositiveMap.empty _) _
                            (fun evm
                             => (* there might be multiple type variables which map to incompatible types; we check for that here *)
                               if option_type_type_beq (pattern.type.subst pt evm) (Some t)
                               then k (Some evm)
                               else k None)
                     | None => k None
                     end
                | Some None
                  => k (Some (PositiveMap.empty _))
                | None => k None
                end.

        Definition option_bind' {A B} := @Option.bind A B. (* for help with unfolding *)

        Fixpoint unify_pattern' {t} (e : rawexpr) (p : pattern t) (evm : EvarMap) {struct p}
          : forall T, (unification_resultT' p evm -> option T) -> option T
          := match p, e return forall T, (unification_resultT' p evm -> option T) -> option T with
             | pattern.Wildcard t', _
               => fun T k
                  => (tro <- type.try_make_transport_cps value (type_of_rawexpr e) (pattern.type.subst_default t' evm);
                        (tr <- tro;
                           _ <- pattern.type.subst t' evm; (* ensure that we did not fall into the default case *)
                           (k (tr (value_of_rawexpr e))))%option)%cps
             | pattern.Ident t pidc, rIdent known _ idc _ _
               => fun T k
                  => (if known
                      then Option.bind (pident_unify _ _ pidc idc)
                      else option_bind' (pident_unify_unknown _ _ pidc idc))
                       k
             | pattern.App s d pf px, rApp f x _ _
               => fun T k
                  => @unify_pattern'
                       _ f pf evm T
                       (fun fv
                        => @unify_pattern'
                             _ x px evm T
                             (fun xv
                              => k (fv, xv)))
             | pattern.Ident _ _, _
             | pattern.App _ _ _ _, _
               => fun _ k => None
             end%option.

        Definition unify_pattern {t} (e : rawexpr) (p : pattern t)
          : forall T, (unification_resultT p -> option T) -> option T
          := fun T cont
             => unify_types
                  e p _
                  (fun evm
                   => evm <- evm;
                        unify_pattern'
                          e p evm T (fun v => cont (existT _ _ v)))%option.

        (** We follow
            http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf,
            "Compiling Pattern Matching to Good Decision Trees" by Luc
            Maranget.  A [decision_tree] describes how to match a
            vector (or list) of patterns against a vector of
            expressions. The cases of a [decision_tree] are:

            - [TryLeaf k onfailure]: Try the kth rewrite rule; if it
              fails, keep going with [onfailure]

            - [Failure]: Abort; nothing left to try

            - [Switch icases app_case default]: With the first element
              of the vector, match on its kind; if it is an identifier
              matching something in [icases], remove the first element
              of the vector run that decision tree; if it is an
              application and [app_case] is not [None], try the
              [app_case] decision_tree, replacing the first element of
              each vector with the two elements of the function and
              the argument its applied to; otherwise, don't modify the
              vectors, and use the [default] decision tree.

            - [Swap i cont]: Swap the first element of the vector with
              the ith element, and keep going with [cont] *)
        Inductive decision_tree :=
        | TryLeaf (k : nat) (onfailure : decision_tree)
        | Failure
        | Switch (icases : list (raw_pident * decision_tree))
                 (app_case : option decision_tree)
                 (default : decision_tree)
        | Swap (i : nat) (cont : decision_tree).

        Definition swap_list {A} (i j : nat) (ls : list A) : option (list A)
          := match nth_error ls i, nth_error ls j with
             | Some vi, Some vj => Some (set_nth i vj (set_nth j vi ls))
             | _, _ => None
             end.

        Fixpoint eval_decision_tree {T} (ctx : list rawexpr) (d : decision_tree) (cont : nat -> list rawexpr -> option T) {struct d} : option T
          := match d with
             | TryLeaf k onfailure
               => let res := cont k ctx in
                  match onfailure with
                  | Failure => res
                  | _ => res ;; (@eval_decision_tree T ctx onfailure cont)
                  end
             | Failure => None
             | Switch icases app_case default_case
               => match ctx with
                  | nil => None
                  | ctx0 :: ctx'
                    => let res
                           := reveal_rawexpr_cps
                                ctx0 _
                                (fun ctx0'
                                 => match ctx0' with
                                    | rIdent known t idc t' alt
                                      => fold_right
                                           (fun '(pidc, icase) rest
                                            => let res
                                                   := if known
                                                      then
                                                        (args <- invert_bind_args _ idc pidc;
                                                           @eval_decision_tree
                                                             T ctx' icase
                                                             (fun k ctx''
                                                              => cont k (rIdent
                                                                           (raw_pident_is_simple pidc)
                                                                           (raw_pident_to_typed pidc args) alt :: ctx'')))
                                                      else
                                                        @eval_decision_tree
                                                          T ctx' icase
                                                          (fun k ctx''
                                                           => option_bind'
                                                                (invert_bind_args_unknown _ idc pidc)
                                                                (fun args
                                                                 => cont k (rIdent
                                                                              (raw_pident_is_simple pidc)
                                                                              (raw_pident_to_typed pidc args) alt :: ctx'')))
                                               in
                                               match rest with
                                               | None => Some res
                                               | Some rest => Some (res ;; rest)
                                               end)
                                           None
                                           icases;;;
                                           None
                                    | rApp f x t alt
                                      => match app_case with
                                         | Some app_case
                                           => @eval_decision_tree
                                                T (f :: x :: ctx') app_case
                                                (fun k ctx''
                                                 => match ctx'' with
                                                    | f' :: x' :: ctx'''
                                                      => cont k (rApp f' x' alt :: ctx''')
                                                    | _ => None
                                                    end)
                                         | None => None
                                         end
                                    | rExpr t e
                                    | rValue t e
                                      => None
                                    end) in
                       match default_case with
                       | Failure => res
                       | _ => res ;; (@eval_decision_tree T ctx default_case cont)
                       end
                  end
             | Swap i d'
               => match swap_list 0 i ctx with
                  | Some ctx'
                    => @eval_decision_tree
                         T ctx' d'
                         (fun k ctx''
                          => match swap_list 0 i ctx'' with
                             | Some ctx''' => cont k ctx'''
                             | None => None
                             end)
                  | None => None
                  end
             end%option.

        Local Notation expr_maybe_do_again should_do_again
          := (@expr.expr base_type ident (if should_do_again then value else var)).

        Local Notation deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t
          := (match (expr_maybe_do_again should_do_again t) with
              | x0 => match (if under_lets then UnderLets x0 else x0) with
                      | x1 => if with_opt then option x1 else x1
                      end
              end).

        Definition deep_rewrite_ruleTP_gen (should_do_again : bool) (with_opt : bool) (under_lets : bool) t
          := deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t.

        Definition normalize_deep_rewrite_rule {should_do_again with_opt under_lets t}
          : deep_rewrite_ruleTP_gen should_do_again with_opt under_lets t
            -> deep_rewrite_ruleTP_gen should_do_again true true t
          := match with_opt, under_lets with
             | true , true  => fun x => x
             | false, true  => fun x => Some x
             | true , false => fun x => (x <- x; Some (UnderLets.Base x))%option
             | false, false => fun x => Some (UnderLets.Base x)
             end%cps.

        Definition with_unif_rewrite_ruleTP_gen' {var t} (p : pattern t) (should_do_again : bool) (with_opt : bool) (under_lets : bool) evm
          := @with_unification_resultT' var t p evm (deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets (pattern.type.subst_default t evm)).

        Definition with_unif_rewrite_ruleTP_gen {var t} (p : pattern t) (should_do_again : bool) (with_opt : bool) (under_lets : bool)
          := @with_unification_resultT var t p (fun t => deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t).

        Definition lam_unif_rewrite_ruleTP_gen {var t} (p : pattern t) (should_do_again : bool) (with_opt : bool) (under_lets : bool)
          : _ -> @with_unif_rewrite_ruleTP_gen var t p should_do_again with_opt under_lets
          := lam_unification_resultT.

        Definition partial_lam_unif_rewrite_ruleTP_gen {var t} (p : pattern t) (should_do_again : bool) (with_opt : bool) (under_lets : bool)
          : (forall evm, @with_unif_rewrite_ruleTP_gen' var t p should_do_again with_opt under_lets evm) -> @with_unif_rewrite_ruleTP_gen var t p should_do_again with_opt under_lets
          := partial_lam_unification_resultT.

        Record rewrite_rule_data {t} {p : pattern t} :=
          { rew_should_do_again : bool;
            rew_with_opt : bool;
            rew_under_lets : bool;
            rew_replacement : @with_unif_rewrite_ruleTP_gen value t p rew_should_do_again rew_with_opt rew_under_lets }.

        Definition rewrite_ruleTP
          := (fun p : anypattern => @rewrite_rule_data _ (pattern.pattern_of_anypattern p)).
        Definition rewrite_ruleT := sigT rewrite_ruleTP.
        Definition rewrite_rulesT
          := (list rewrite_ruleT).

        Local Notation base_type_of t
          := (match t with type.base t' => t' | type.arrow _ __ => base.type.unit end).

        Definition maybe_do_againT (should_do_again : bool) (t : base_type)
          := ((@expr.expr base_type ident (if should_do_again then value else var) t) -> UnderLets (expr t)).
        Definition maybe_do_again
                   (do_again : forall t : base_type, @expr.expr base_type ident value t -> UnderLets (expr t))
                   (should_do_again : bool) (t : base_type)
          := if should_do_again return maybe_do_againT should_do_again t
             then do_again t
             else UnderLets.Base.

        Section eval_rewrite_rules.
          Context (do_again : forall t : base_type, @expr.expr base_type ident value t -> UnderLets (expr t)).

          Local Notation maybe_do_again := (maybe_do_again do_again).

          Definition rewrite_with_rule {t} e' (pf : rewrite_ruleT)
            : option (UnderLets (expr t))
            := let 'existT p f := pf in
               let should_do_again := rew_should_do_again f in
               unify_pattern
                 e' (pattern.pattern_of_anypattern p) _
                 (fun x
                  => app_with_unification_resultT_cps
                       (rew_replacement f) x _
                       (fun f'
                        => (tr <- type.try_make_transport_cps _ _ _;
                              (tr <- tr;
                                 (tr' <- type.try_make_transport_cps _ _ _;
                                    (tr' <- tr';
                                       option_bind'
                                         (normalize_deep_rewrite_rule (projT2 f'))
                                         (fun fv
                                          => Some (fv <-- fv;
                                                     fv <-- maybe_do_again should_do_again (base_type_of (type_of_rawexpr e')) (tr fv);
                                                     UnderLets.Base (tr' fv))%under_lets))%option)%cps)%option)%cps)%cps).

          Definition eval_rewrite_rules
                     (d : decision_tree)
                     (rews : rewrite_rulesT)
                     (e : rawexpr)
            : UnderLets (expr (type_of_rawexpr e))
            := let defaulte := expr_of_rawexpr e in
               (eval_decision_tree
                  (e::nil) d
                  (fun k ctx
                   => match ctx return option (UnderLets (expr (type_of_rawexpr e))) with
                      | e'::nil
                        => (pf <- nth_error rews k; rewrite_with_rule e' pf)%option
                      | _ => None
                      end);;;
                  (UnderLets.Base defaulte))%option.
        End eval_rewrite_rules.

        Local Notation enumerate ls
          := (List.combine (List.seq 0 (List.length ls)) ls).

        Fixpoint first_satisfying_helper {A B} (f : A -> option B) (ls : list A) : option B
          := match ls with
             | nil => None
             | cons x xs
               => match f x with
                 | Some v => Some v
                 | None => first_satisfying_helper f xs
                 end
             end.

        Definition get_index_of_first_non_wildcard (p : list rawpattern) : option nat
          := first_satisfying_helper
               (fun '(n, x) => match x with
                            | pattern.Raw.Wildcard => None
                            | _ => Some n
                            end)
               (enumerate p).

        Definition starts_with_wildcard : nat * list rawpattern -> bool
          := fun '(_, p) => match p with
                            | pattern.Raw.Wildcard::_ => true
                            | _ => false
                            end.

        Definition not_starts_with_wildcard : nat * list rawpattern -> bool
          := fun p => negb (starts_with_wildcard p).

        Definition filter_pattern_wildcard (p : list (nat * list rawpattern)) : list (nat * list rawpattern)
          := filter starts_with_wildcard p.

        Definition split_at_first_pattern_wildcard (p : list (nat * list rawpattern)) : list (nat * list rawpattern) * list (nat * list rawpattern)
          := (take_while not_starts_with_wildcard p, drop_while not_starts_with_wildcard p).

        Fixpoint get_unique_pattern_ident' (p : list (nat * list rawpattern)) (so_far : list raw_pident) : list raw_pident
          := match p with
             | nil => List.rev so_far
             | (_, pattern.Raw.Ident pidc :: _) :: ps
               => let so_far' := if existsb (raw_pident_beq pidc) so_far
                                 then so_far
                                 else pidc :: so_far in
                  get_unique_pattern_ident' ps so_far'
             | _ :: ps => get_unique_pattern_ident' ps so_far
             end.

        Definition get_unique_pattern_ident p : list raw_pident := get_unique_pattern_ident' p nil.

        Definition contains_pattern_pident (pidc : raw_pident) (p : list (nat * list rawpattern)) : bool
          := existsb (fun '(n, p) => match p with
                                  | pattern.Raw.Ident pidc'::_ => raw_pident_beq pidc pidc'
                                  | _ => false
                                  end)
                     p.

        Definition contains_pattern_app (p : list (nat * list rawpattern)) : bool
          := existsb (fun '(n, p) => match p with
                                  | pattern.Raw.App _ _::_ => true
                                  | _ => false
                                  end)
                     p.

        Definition filter_pattern_app (p : nat * list rawpattern) : option (nat * list rawpattern)
          := match p with
             | (n, pattern.Raw.App f x :: ps)
               => Some (n, f :: x :: ps)
             | _
               => None
             end.

        Definition filter_pattern_pident (pidc : raw_pident) (p : nat * list rawpattern) : option (nat * list rawpattern)
          := match p with
             | (n, pattern.Raw.Ident pidc'::ps)
               => if raw_pident_beq pidc pidc'
                 then Some (n, ps)
                 else None
             | _
               => None
             end.

        Definition compile_rewrites_step
                   (compile_rewrites : list (nat * list rawpattern) -> option decision_tree)
                   (pattern_matrix : list (nat * list rawpattern))
          : option decision_tree
          := match pattern_matrix with
             | nil => Some Failure
             | (n1, p1) :: ps
               => match get_index_of_first_non_wildcard p1 with
                 | None (* p1 is all wildcards *)
                   => (onfailure <- compile_rewrites ps;
                        Some (TryLeaf n1 onfailure))
                 | Some Datatypes.O
                   => let '(pattern_matrix, default_pattern_matrix) := split_at_first_pattern_wildcard pattern_matrix in
                      default_case <- compile_rewrites default_pattern_matrix;
                        app_case <- (if contains_pattern_app pattern_matrix
                                     then option_map Some (compile_rewrites (Option.List.map filter_pattern_app pattern_matrix))
                                     else Some None);
                        let pidcs := get_unique_pattern_ident pattern_matrix in
                        let icases := Option.List.map
                                        (fun pidc => option_map (pair pidc) (compile_rewrites (Option.List.map (filter_pattern_pident pidc) pattern_matrix)))
                                        pidcs in
                        Some (Switch icases app_case default_case)
                 | Some i
                   => let pattern_matrix'
                         := List.map
                              (fun '(n, ps)
                               => (n,
                                  match swap_list 0 i ps with
                                  | Some ps' => ps'
                                  | None => nil (* should be impossible *)
                                  end))
                              pattern_matrix in
                     d <- compile_rewrites pattern_matrix';
                       Some (Swap i d)
                 end
             end%option.

        (* only returns [None] if the fuel runs out *)
        Fixpoint compile_rewrites' (fuel : nat) (pattern_matrix : list (nat * list rawpattern))
          : option decision_tree
          := match fuel with
             | Datatypes.O => None
             | Datatypes.S fuel' => compile_rewrites_step (@compile_rewrites' fuel') pattern_matrix
             end.

        Definition compile_rewrites (fuel : nat) (ps : rewrite_rulesT)
          := compile_rewrites' fuel (enumerate (List.map (fun p => to_raw_pattern (pattern.pattern_of_anypattern (projT1 p)) :: nil) ps)).

        Section with_do_again.
          Context (dtree : decision_tree)
                  (rewrite_rules : rewrite_rulesT)
                  (default_fuel : nat)
                  (do_again : forall t : base_type, @expr.expr base_type ident value t -> UnderLets (expr t)).

          Let dorewrite1 (e : rawexpr) : UnderLets (expr (type_of_rawexpr e))
            := eval_rewrite_rules do_again dtree rewrite_rules e.

          Fixpoint assemble_identifier_rewriters' (t : type) : forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t
            := match t return forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t with
               | type.base _
                 => fun e k => k (fun t => UnderLets (expr t)) (dorewrite1 e)
               | type.arrow s d
                 => fun f k (x : value' _ _)
                    => let x' := reify x in
                       @assemble_identifier_rewriters' d (rApp f (rValueOrExpr2 x x') (k _ (expr_of_rawexpr f) @ x'))%expr (fun _ => id)
               end%under_lets.

          Definition assemble_identifier_rewriters {t} (idc : ident t) : value_with_lets t
            := eta_ident_cps _ _ idc (fun t' idc' => assemble_identifier_rewriters' t' (rIdent true idc' (#idc')) (fun _ => id)).
        End with_do_again.
      End with_var.
      Global Arguments rew_should_do_again {_ _ _ _ _ _ _} _.
      Global Arguments rew_with_opt        {_ _ _ _ _ _ _} _.
      Global Arguments rew_under_lets      {_ _ _ _ _ _ _} _.
      Global Arguments rew_replacement     {_ _ _ _ _ _ _} _.

      Ltac compute_with_fuel f fuel :=
        lazymatch (eval compute in (f fuel)) with
        | Some ?res => res
        | None => compute_with_fuel f (10 + fuel * 10)%nat
        | ?res => fail 0 "Invalid result of computing" f "with fuel" fuel ":" res
        end.

      Ltac compile_rewrites base ident var pident pident_arg_types raw_pident strip_types raw_pident_beq ps
        := compute_with_fuel (fun fuel : nat => @compile_rewrites base ident var pident pident_arg_types raw_pident strip_types raw_pident_beq fuel ps) 100%nat (* initial value of depth of patterns; doesn't matter too much *).
      Ltac CompileRewrites base ident pident pident_arg_types raw_pident strip_types raw_pident_beq ps :=
        let var := fresh "var" in
        let base_type := constr:(Compilers.base.type base) in
        let res
            := lazymatch constr:(
                           fun var : Compilers.type.type base_type -> Type
                           => ltac:(let res := compile_rewrites base ident var pident pident_arg_types raw_pident strip_types raw_pident_beq (ps var) in
                                    exact res))
               with
               | fun _ => ?res => res
               end in
        let dtree := fresh "dtree" in
        cache_term res dtree.

      Section full.
        Context {base : Type}.
        Local Notation base_type := (base.type base).
        Local Notation type := (type.type base_type).
        Context {ident : type -> Type}
                {base_interp : base -> Type}
                (ident_is_var_like : forall t, ident t -> bool).
        Local Notation expr := (@expr base_type ident).
        Let type_base (x : base) : @base.type base := base.type.type_base x.
        Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
        Local Coercion base' : base.type >-> type.type.
        Local Coercion type_base : base >-> base.type.
        Context {baseTypeHasNat : base.type.BaseTypeHasNatT base}
                {buildIdent : ident.BuildIdentT base_interp ident}
                {buildEagerIdent : ident.BuildEagerIdentT ident}
                {toRestrictedIdent : ident.ToRestrictedIdentT ident}
                {toFromRestrictedIdent : ident.ToFromRestrictedIdentT ident}
                {invertIdent : InvertIdentT base_interp ident}
                {baseHasNatCorrect : base.BaseHasNatCorrectT base_interp}
                {try_make_transport_base_cps : type.try_make_transport_cpsT base}.

        Section with_var.
          Context {var : type -> Type}.
          Local Notation value := (@Compile.value base_type ident var).
          Local Notation value_with_lets := (@Compile.value_with_lets base_type ident var).
          Local Notation UnderLets := (UnderLets.UnderLets base_type ident var).
          Local Notation reflect := (@Compile.reflect base ident var).

          Local Notation reify_and_let_binds_cps := (@Compile.reify_and_let_binds_cps base ident var (fun t => UnderLets.reify_and_let_binds_base_cps ident_is_var_like)).
          Local Notation base_type_nat := (match base.type.nat return base with x => x end).

          Local Notation base_to_nat := (base.to_nat (BaseHasNatCorrectT:=baseHasNatCorrect)).
          Local Notation base_of_nat := (base.of_nat (BaseHasNatCorrectT:=baseHasNatCorrect)).

          (** This definition takes in an identifier. If the identifier
            is not meant to be evaluated eagerly, [None] is
            returned. Otherwise, a value-thunk is returned. This
            value-thunk takes in all of the arguments to which the
            identifer will eventually be applied.  If there is enough
            structure for eager evaluation, then the identifier is
            "evaluated" in Gallina (e.g., [eager_list_rect] turns into
            [list_rect] over a concrete list of cons cells holding
            PHOAS expressions), and the result of this evaluation is
            returned. *)
          (* N.B. the [with_lets] argument to [reflect] doesn't matter
          here because [value' true (_ → _) ≡ value' false (_ → _)] *)
          Definition reflect_ident_iota {t} (idc : ident t) : option (value t)
            := (ident.eager_ident_rect
                  (fun t idc => value t)
                  (fun (*| ident.eager_nat_rect*) P
                   => (fun (N_case : value base.type.unit -> _) (S_case : value base_type_nat -> value P -> _) (n : expr base_type_nat) (* type annotations present for nicer fixpoint refolding *)
                       => match invert_Literal n with
                          | Some n => nat_rect
                                        (fun _ => UnderLets (expr P))
                                        (N_case (#(ident.ident_tt)))
                                        (fun n' rec
                                         => rec <-- rec;
                                              S_case (#(ident.ident_Literal (t:=base_type_nat) (base_of_nat n'))) rec)
                                        (base_to_nat n)
                          | None => reflect (with_lets:=false) (expr.Ident (ident.ident_nat_rect (P:=P))) N_case S_case n
                          end))
                  (fun (*| ident.eager_nat_rect_arrow*) P Q
                   => (fun (N_case : value P -> _) (S_case : value base_type_nat -> (value P -> _) -> _ -> _) (n : expr base_type_nat) (v : expr P) (* type annotations present for nicer fixpoint refolding *)
                       => match invert_Literal n with
                          | Some n => nat_rect
                                        (fun _ => expr P -> UnderLets (expr Q))
                                        N_case
                                        (fun n' rec v'
                                         => S_case (#(ident.ident_Literal (t:=base_type_nat) (base_of_nat n'))) rec v')
                                        (base_to_nat n)
                                        v
                          | None => reflect (with_lets:=false) (expr.Ident (ident.ident_nat_rect_arrow (P:=P) (Q:=Q))) N_case S_case n v
                          end))
                  (fun (*| ident.eager_list_rect*) A P
                   => (fun (N_case : value base.type.unit -> _) (C_case : value A -> _ -> value P -> _) (ls : expr (base.type.list A)) (* type annotations present for nicer fixpoint refolding *)
                       => match reflect_list ls with
                          | Some ls => list_rect
                                         (fun _ => UnderLets (expr P))
                                         (N_case (#(ident.ident_tt)))
                                         (fun x xs rec
                                          => rec <-- rec;
                                               C_case x (reify_list xs) rec)
                                         ls
                          | None => reflect (with_lets:=false) (expr.Ident (ident.ident_list_rect (A:=A) (P:=P))) N_case C_case ls
                          end))
                  (fun (*| ident.eager_list_rect_arrow*) A P Q
                   => (fun (N_case : value P -> _) (C_case : value A -> _ -> (value P -> _) -> value P -> _) (ls : expr (base.type.list A)) (v : value P) (* type annotations present for nicer fixpoint refolding *)
                       => match reflect_list ls with
                          | Some ls => list_rect
                                         (fun _ => expr P -> UnderLets (expr Q))
                                         N_case
                                         (fun x xs rec v
                                          => C_case x (reify_list xs) rec v)
                                         ls
                                         v
                          | None => reflect (with_lets:=false) (expr.Ident (ident.ident_list_rect_arrow (A:=A) (P:=P) (Q:=Q))) N_case C_case ls v
                          end))
                  (fun (*| ident.eager_List_nth_default*) A
                   => (fun default (ls : expr (base.type.list A)) (n : expr base_type_nat)
                       => match reflect_list ls, invert_Literal n with
                          | Some ls, Some n => UnderLets.Base (nth_default default ls (base_to_nat n))
                          | _, _ => reflect (with_lets:=false) (expr.Ident (ident.ident_List_nth_default (T:=A))) default ls n
                          end))
                  idc)%expr%under_lets.

          Section with_rewrite_head.
            Context (rewrite_head : forall t (idc : ident t), value_with_lets t).

            Local Notation "e <---- e' ; f" := (Compile.splice_value_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
            Local Notation "e <----- e' ; f" := (Compile.splice_under_lets_with_value e' (fun e => f%under_lets)) : under_lets_scope.

            Fixpoint rewrite_bottomup {t} (e : @expr value t) : value_with_lets t
              := match e in expr.expr t return value_with_lets t with
                 | expr.Ident t idc
                   => rewrite_head _ idc
                 | expr.App s d f x => let f : value s -> value_with_lets d := @rewrite_bottomup _ f in x <---- @rewrite_bottomup _ x; f x
                 | expr.LetIn A B x f => x <---- @rewrite_bottomup A x;
                                           xv <----- reify_and_let_binds_cps x _ UnderLets.Base;
                                           @rewrite_bottomup B (f (reflect xv))
                 | expr.Var t v => Compile.Base_value v
                 | expr.Abs s d f => fun x : value s => @rewrite_bottomup d (f x)
                 end%under_lets.
          End with_rewrite_head.

          Notation nbe := (@rewrite_bottomup (fun t idc => reflect (expr.Ident idc))).

          Fixpoint repeat_rewrite
                   (rewrite_head : forall (do_again : forall t : base_type, @expr value (type.base t) -> UnderLets (@expr var (type.base t)))
                                          t (idc : ident t), value_with_lets t)
                   (fuel : nat) {t} e : value_with_lets t
            := @rewrite_bottomup
                 (rewrite_head
                    (fun t' e'
                     => match fuel with
                        | Datatypes.O => nbe e'
                        | Datatypes.S fuel' => @repeat_rewrite rewrite_head fuel' (type.base t') e'
                        end%under_lets))
                 t e.

          Definition rewrite rewrite_head fuel {t} e : expr t
            := reify (@repeat_rewrite rewrite_head fuel t e).
        End with_var.

        Definition Rewrite rewrite_head fuel {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
          := fun var => @rewrite var (rewrite_head var) fuel t (e _).
      End full.
    End Compile.

    Module Reify.
      (* Here we only include the definitions that will have proofs about them; the rest of them are in [Rewriter.Reify.v] *)
      Import Compile.
      Local Notation EvarMap := pattern.EvarMap.

      Inductive dynlist := dynnil | dyncons {T} (x : T) (xs : dynlist).

      Section with_var.
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {base : Type}.
        Local Notation base_type := (base.type base).
        Local Notation pattern_base_type := (pattern.base.type base).
        Local Notation type := (type.type base_type).
        Local Notation ptype := (type.type pattern_base_type).
        Context {ident var : type -> Type}
                {pident : ptype -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_type_of_list_arg_types_beq : forall t idc, type_of_list (pident_arg_types t idc) -> type_of_list (pident_arg_types t idc) -> bool)
                (pident_of_typed_ident : forall t, ident t -> pident (pattern.type.relax t))
                (pident_arg_types_of_typed_ident : forall t (idc : ident t), type_of_list (pident_arg_types _ (pident_of_typed_ident t idc)))
                (reflect_ident_iota : forall t (idc : ident t), option (@value base_type ident var t)).

        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation pattern := (@pattern.pattern pident).
        Local Notation value := (@Compile.value base_type ident var).
        Local Notation UnderLets := (UnderLets.UnderLets base_type ident var).
        Local Notation reify_expr_beta_iota := (@reify_expr_beta_iota base ident var reflect_ident_iota).

        Local Notation expr_maybe_do_again should_do_again
          := (@expr.expr base_type ident (if should_do_again then value else var)).

        Definition expr_value_to_rewrite_rule_replacement (should_do_again : bool) {t} (e : @expr.expr base_type ident value t)
          : UnderLets (expr_maybe_do_again should_do_again t)
          := (e <-- UnderLets.flat_map (@reify_expr_beta_iota) (fun t v => reflect (expr.Var v)) (UnderLets.of_expr e);
                if should_do_again return UnderLets (expr_maybe_do_again should_do_again t)
                then UnderLets.Base e
                else reify_expr_beta_iota e)%under_lets.
      End with_var.
    End Reify.

    Module Make.
      Import pattern.ident.GoalType.

      Ltac rewriter_assembly_debug_level := constr:(1%nat).

      Ltac check_debug_level_then_Set _ :=
        let lvl := rewriter_assembly_debug_level in
        lazymatch type of lvl with
        | nat => constr:(Set)
        | ?T => constr_run_tac ltac:(fun _ => idtac "Error: rewriter_assembly_debug_level should have type nat but instead has type" T)
        end.
      Ltac debug0 tac :=
        constr_run_tac tac.
      Ltac debug1 tac :=
        let lvl := rewriter_assembly_debug_level in
        lazymatch lvl with
        | S _ => constr_run_tac tac
        | _ => check_debug_level_then_Set ()
        end.
      Ltac debug2 tac :=
        let lvl := rewriter_assembly_debug_level in
        lazymatch lvl with
        | S (S _) => constr_run_tac tac
        | _ => check_debug_level_then_Set ()
        end.

      Ltac time_if_debug1 :=
        let lvl := rewriter_assembly_debug_level in
        lazymatch lvl with
        | O => ltac:(fun tac => tac ())
        | S _ => ltac:(fun tac => time tac ())
        | ?v => ltac:(fun tac => fail 0 "Invalid non-nat rewriter_assembly_debug_level" v)
        end.
      Ltac time_tac_in_constr_if_debug1 tac :=
        constr:(ltac:(time_if_debug1 ltac:(fun _ => idtac; let v := tac () in exact v))).

      Module Export GoalType.
        Local Set Primitive Projections.
        Import Compilers.Classes.
        Record rewriter_dataT
               {exprInfo : ExprInfoT}
               {exprExtraInfo : ExprExtraInfoT}
               {pkg : @package base ident} :=
          Build_rewriter_dataT'
            {
              ident_is_var_like : forall t : type (base.type base), ident t -> bool;

              rewrite_rules_specs : list (bool * Prop);
              dummy_count : nat;
              dtree : @Compile.decision_tree raw_ident;

              rewrite_rules : forall var, @Compile.rewrite_rulesT base ident var pattern_ident arg_types ;
              all_rewrite_rules (* adjusted version *) : _;
              all_rewrite_rules_eq : all_rewrite_rules = rewrite_rules;

              default_fuel : nat;

              rewrite_head0
              := (fun var
                  => @Compile.assemble_identifier_rewriters base _ base_beq ident var eta_ident_cps pattern_ident arg_types (@unify _ _ pkg) (@unify_unknown _ _ pkg) raw_ident full_types (@invert_bind_args _ _ pkg) (@invert_bind_args_unknown _ _ pkg) type_of raw_to_typed is_simple dtree (all_rewrite_rules var));
              rewrite_head (* adjusted version *) : forall var (do_again : forall t, @expr.expr (base.type base) ident (@Compile.value _ ident var) (type.base t) -> @UnderLets.UnderLets _ ident var (@expr.expr (base.type base) ident var (type.base t)))
                                     t (idc : ident t), @Compile.value_with_lets (base.type base) ident var t;
              rewrite_head_eq : rewrite_head = rewrite_head0
            }.
      End GoalType.
      Import Compilers.Classes.
      Definition Rewrite
               {exprInfo : ExprInfoT}
               {exprExtraInfo : ExprExtraInfoT}
               {pkg : @package base ident}
               (data : rewriter_dataT)
               {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
        := Compile.Rewrite (ident_is_var_like data) (rewrite_head data) (default_fuel data) e.
    End Make.
    Export Make.GoalType.

    Module Export GoalType.
      Import Compilers.Classes.
      Import pattern.ident.GoalType.
      Record RewriterT
             {exprInfo : ExprInfoT}
             {exprExtraInfo : ExprExtraInfoT}
             {pkg : package} :=
        {
          Rewriter_data : rewriter_dataT;
          Rewrite : forall {t} (e : expr.Expr (ident:=ident) t), expr.Expr (ident:=ident) t;
          Rewrite_eq : @Rewrite = @Make.Rewrite _ _ pkg Rewriter_data
        }.
    End GoalType.
  End RewriteRules.
End Compilers.
