Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.MSets.MSetPositive.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Crypto.Util.PrimitiveProd.
Require Crypto.Util.PrimitiveHList.
Require Import Crypto.Language.
Require Import Crypto.UnderLets.
Require Import Crypto.GENERATEDIdentifiersWithoutTypes.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Local Set Primitive Projections.
Import EqNotations.
Module Compilers.
  Export Language.Compilers.
  Export UnderLets.Compilers.
  Export GENERATEDIdentifiersWithoutTypes.Compilers.
  Import invert_expr.

  Notation EvarMap := (PositiveMap.t Compilers.base.type).
  Module pattern.
    Export GENERATEDIdentifiersWithoutTypes.Compilers.pattern.

    Module base.
      Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.base.

      Fixpoint partial_subst (ptype : type) (evar_map : EvarMap) : type
        := match ptype with
           | type.var p => match PositiveMap.find p evar_map with
                           | Some t => relax t
                           | None => type.var p
                           end
           | type.type_base t => type.type_base t
           | type.prod A B => type.prod (partial_subst A evar_map) (partial_subst B evar_map)
           | type.list A => type.list (partial_subst A evar_map)
           end.

      Fixpoint subst (ptype : type) (evar_map : EvarMap) : option Compilers.base.type
        := match ptype with
           | type.var p => PositiveMap.find p evar_map
           | type.type_base t => Some (Compilers.base.type.type_base t)
           | type.prod A B
             => (A' <- subst A evar_map;
                   B' <- subst B evar_map;
                   Some (Compilers.base.type.prod A' B'))
           | type.list A => option_map Compilers.base.type.list (subst A evar_map)
           end%option.

      Fixpoint subst_default_relax P {t evm} : P t -> P (subst_default (relax t) evm)
        := match t return P t -> P (subst_default (relax t) evm) with
           | Compilers.base.type.type_base t => fun x => x
           | Compilers.base.type.prod A B
             => fun v
                => @subst_default_relax
                     (fun A' => P (Compilers.base.type.prod A' _)) A evm
                     (@subst_default_relax
                        (fun B' => P (Compilers.base.type.prod _ B')) B evm
                        v)
           | Compilers.base.type.list A
             => @subst_default_relax (fun t => P (Compilers.base.type.list t)) A evm
           end.

      Fixpoint var_types_of (t : type) : Set
        := match t with
           | type.var _ => Compilers.base.type
           | type.type_base _ => unit
           | type.prod A B => var_types_of A * var_types_of B
           | type.list A => var_types_of A
           end%type.

      Fixpoint add_var_types_cps {t : type} (v : var_types_of t) (evm : EvarMap) : ~> EvarMap
        := fun T k
           => match t return var_types_of t -> T with
              | type.var p
                => fun t => k (PositiveMap.add p t evm)
              | type.prod A B
                => fun '(a, b) => @add_var_types_cps A a evm _ (fun evm => @add_var_types_cps B b evm _ k)
              | type.list A => fun t => @add_var_types_cps A t evm _ k
              | type.type_base _ => fun _ => k evm
              end v.

      Fixpoint unify_extracted
               (ptype : type) (etype : Compilers.base.type)
        : option (var_types_of ptype)
        := match ptype, etype return option (var_types_of ptype) with
           | type.var p, _ => Some etype
           | type.type_base t, Compilers.base.type.type_base t'
             => if base.type.base_beq t t'
                then Some tt
                else None
           | type.prod A B, Compilers.base.type.prod A' B'
             => a <- unify_extracted A A';
                  b <- unify_extracted B B';
                  Some (a, b)
           | type.list A, Compilers.base.type.list A'
             => unify_extracted A A'
           | type.type_base _, _
           | type.prod _ _, _
           | type.list _, _
             => None
           end%option.
    End base.

    Module type.
      Fixpoint partial_subst (ptype : type) (evar_map : EvarMap) : type
        := match ptype with
           | type.base t => type.base (base.partial_subst t evar_map)
           | type.arrow s d => type.arrow (partial_subst s evar_map) (partial_subst d evar_map)
           end.

      Fixpoint subst (ptype : type) (evar_map : EvarMap) : option (type.type Compilers.base.type)
        := match ptype with
           | type.base t => option_map type.base (base.subst t evar_map)
           | type.arrow s d
             => (s' <- subst s evar_map;
                   d' <- subst d evar_map;
                   Some (type.arrow s' d'))
           end%option.

      Fixpoint subst_default_relax P {t evm} : P t -> P (type.subst_default (type.relax t) evm)
        := match t return P t -> P (type.subst_default (type.relax t) evm) with
           | type.base t => base.subst_default_relax (fun t => P (type.base t))
           | type.arrow A B
             => fun v
                => @subst_default_relax
                     (fun A' => P (type.arrow A' _)) A evm
                     (@subst_default_relax
                        (fun B' => P (type.arrow _ B')) B evm
                        v)
           end.

      Fixpoint var_types_of (t : type) : Set
        := match t with
           | type.base t => base.var_types_of t
           | type.arrow s d => var_types_of s * var_types_of d
           end%type.

      Fixpoint add_var_types_cps {t : type} (v : var_types_of t) (evm : EvarMap) : ~> EvarMap
        := fun T k
           => match t return var_types_of t -> T with
              | type.base t => fun v => @base.add_var_types_cps t v evm _ k
              | type.arrow A B
                => fun '(a, b) => @add_var_types_cps A a evm _ (fun evm => @add_var_types_cps B b evm _ k)
              end v.

      Fixpoint unify_extracted
               (ptype : type) (etype : type.type Compilers.base.type)
        : option (var_types_of ptype)
        := match ptype, etype return option (var_types_of ptype) with
           | type.base t, type.base t'
             => base.unify_extracted t t'
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
              (fun i k evm => forall t : Compilers.base.type, k (PositiveMap.add i t evm))
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
    End type.

    Inductive pattern {ident : type -> Type} : type -> Type :=
    | Wildcard (t : type) : pattern t
    | Ident {t} (idc : ident t) : pattern t
    | App {s d} (f : pattern (s -> d)) (x : pattern s) : pattern d.

    Record > anypattern {ident : type -> Type}
      := { type_of_anypattern : type;
           pattern_of_anypattern :> @pattern ident type_of_anypattern }.

    Module Raw.
      Inductive pattern {ident : Type} :=
      | Wildcard
      | Ident (idc : ident)
      | App (f x : pattern).
    End Raw.

    Global Arguments Wildcard {ident%type} t%ptype.

    Fixpoint to_raw {ident raw_ident}
             {to_raw_ident : forall t, ident t -> raw_ident}
             {t} (p : @pattern ident t) : @Raw.pattern raw_ident
      := match p with
         | Wildcard t => Raw.Wildcard
         | Ident t idc => Raw.Ident (to_raw_ident t idc)
         | App s d f x => Raw.App (@to_raw _ _ to_raw_ident _ f) (@to_raw _ _ to_raw_ident _ x)
         end.

    Fixpoint collect_vars {ident}
             {t} (p : @pattern ident t) : PositiveSet.t
      := match p with
         | Wildcard t => type.collect_vars t
         | Ident t idc => type.collect_vars t
         | App s d f x => PositiveSet.union (@collect_vars _ _ x) (@collect_vars _ _ f)
         end.

    Notation ident := ident.ident.

    Fixpoint unify_list {A B} (unif : A -> B -> EvarMap -> option EvarMap) (ls1 : list A) (ls2 : list B) (evm : EvarMap)
      : option EvarMap
      := match ls1, ls2 with
         | nil, nil => Some evm
         | cons x xs, cons y ys
           => (evm <- unif x y evm;
                @unify_list A B unif xs ys evm)%option
         | nil, _
         | cons _ _, _
           => None
         end.

    Module Export Notations.
      Export base.Notations.
      Delimit Scope pattern_scope with pattern.
      Bind Scope pattern_scope with pattern.
      Local Open Scope pattern_scope.
      Notation "# idc" := (Ident idc) : pattern_scope.
      Notation "#?" := (Ident (@ident.Literal _)) : pattern_scope.
      Notation "#?{ t }" := (Ident (@ident.Literal t)) (format "#?{ t }") : pattern_scope.
      Notation "#?()" := (#?{base.type.unit}) : pattern_scope.
      Notation "#?N" := (#?{base.type.nat}) : pattern_scope.
      Notation "#?ℕ" := (#?{base.type.nat}) : pattern_scope.
      Notation "#?Z" := (#?{base.type.Z}) : pattern_scope.
      Notation "#?ℤ" := (#?{base.type.Z}) : pattern_scope.
      Notation "#?B" := (#?{base.type.bool}) : pattern_scope.
      Notation "#?𝔹" := (#?{base.type.bool}) : pattern_scope.
      Notation "??" := (Wildcard _) : pattern_scope.
      Notation "??{ t }" := (Wildcard t) (format "??{ t }") : pattern_scope.
      Notation "' n" := (??{' n})%pattern : pattern_scope.
      Notation "'1" := (' 1) : pattern_scope.
      Notation "'2" := (' 2) : pattern_scope.
      Notation "'3" := (' 3) : pattern_scope.
      Notation "'4" := (' 4) : pattern_scope.
      Notation "'5" := (' 5) : pattern_scope.
      Infix "@" := App : pattern_scope.
      Notation "( x , y , .. , z )" := (#ident.pair @ .. (#ident.pair @ x @ y) .. @ z) : pattern_scope.
      Notation "x :: xs" := (#ident.cons @ x @ xs) : pattern_scope.
      Notation "xs ++ ys" := (#ident.List_app @ xs @ ys) : pattern_scope.
      Notation "[ ]" := (#ident.nil) : pattern_scope.
      Notation "[ x ]" := (x :: []) : pattern_scope.
      Notation "[ x ; y ; .. ; z ]" :=  (x :: (y :: .. (z :: []) ..)) : pattern_scope.
      Notation "x - y" := (#ident.Z_sub @ x @ y) : pattern_scope.
      Notation "x + y" := (#ident.Z_add @ x @ y) : pattern_scope.
      Notation "x / y" := (#ident.Z_div @ x @ y) : pattern_scope.
      Notation "x * y" := (#ident.Z_mul @ x @ y) : pattern_scope.
      Notation "x >> y" := (#ident.Z_shiftr @ x @ y) : pattern_scope.
      Notation "x << y" := (#ident.Z_shiftl @ x @ y) : pattern_scope.
      Notation "x &' y" := (#ident.Z_land @ x @ y) : pattern_scope.
      Notation "x 'mod' y" := (#ident.Z_modulo @ x @ y)%pattern : pattern_scope.
      Notation "- x" := (#ident.Z_opp @ x) : pattern_scope.

      Notation "#?ℤ'" := (#ident.Z_cast @ #?ℤ) : pattern_scope.
      Notation "??'" := (#ident.Z_cast @ Wildcard _) : pattern_scope.
      Notation "x -' y" := (#ident.Z_cast @ (#ident.Z_sub @ x @ y)) : pattern_scope.
      Notation "x +' y" := (#ident.Z_cast @ (#ident.Z_add @ x @ y)) : pattern_scope.
      Notation "x /' y" := (#ident.Z_cast @ (#ident.Z_div @ x @ y)) : pattern_scope.
      Notation "x *' y" := (#ident.Z_cast @ (#ident.Z_mul @ x @ y)) : pattern_scope.
      Notation "x >>' y" := (#ident.Z_cast @ (#ident.Z_shiftr @ x @ y)) : pattern_scope.
      Notation "x <<' y" := (#ident.Z_cast @ (#ident.Z_shiftl @ x @ y)) : pattern_scope.
      Notation "x &'' y" := (#ident.Z_cast @ (#ident.Z_land @ x @ y)) : pattern_scope.
      Notation "x 'mod'' y" := (#ident.Z_cast @ (#ident.Z_modulo @ x @ y))%pattern : pattern_scope.
      Notation "-' x" := (#ident.Z_cast @ (#ident.Z_opp @ x)) : pattern_scope.
    End Notations.
  End pattern.
  Export pattern.Notations.
  Notation pattern := (@pattern.pattern pattern.ident).

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
        Context {ident var : type.type base.type -> Type}
                (eta_ident_cps : forall {T : type.type base.type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                {pident : type.type pattern.base.type -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))
                {raw_pident : Type}
                (strip_types : forall t, pident t -> raw_pident)
                (raw_pident_beq : raw_pident -> raw_pident -> bool)

                (full_types : raw_pident -> Type)
                (invert_bind_args invert_bind_args_unknown : forall t (idc : ident t) (pidc : raw_pident), option (full_types pidc))
                (type_of_raw_pident : forall (pidc : raw_pident), full_types pidc -> type.type base.type)
                (raw_pident_to_typed : forall (pidc : raw_pident) (args : full_types pidc), ident (type_of_raw_pident pidc args))
                (raw_pident_is_simple : raw_pident -> bool).

        Local Notation type := (type.type base.type).
        Local Notation expr := (@expr.expr base.type ident var).
        Local Notation pattern := (@pattern.pattern pident).
        Local Notation rawpattern := (@pattern.Raw.pattern raw_pident).
        Local Notation anypattern := (@pattern.anypattern pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
        Local Notation ptype := (type.type pattern.base.type).
        Local Notation value' := (@value' base.type ident var).
        Local Notation value := (@value base.type ident var).
        Local Notation value_with_lets := (@value_with_lets base.type ident var).
        Local Notation Base_value := (@Base_value base.type ident var).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base.type ident var).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base.type ident var).
        Local Notation to_raw_pattern := (@pattern.to_raw pident raw_pident (@strip_types)).
        Let type_base (t : base.type) : type := type.base t.
        Coercion type_base : base.type >-> type.

        Context (reify_and_let_binds_base_cps : forall (t : base.type), expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T).

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

        Definition app_type_of_list {K} {ls : list Type} (f : type_of_list_cps K ls) (args : type_of_list ls) : K
          := list_rect
               (fun ls
                => type_of_list_cps K ls -> type_of_list ls -> K)
               (fun v _ => v)
               (fun T Ts rec f x
                => rec (f (fst x)) (snd x))
               ls
               f args.

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

        Fixpoint reify_expr {t} (e : @expr.expr base.type ident value t)
          : @expr.expr base.type ident var t
          := match e in expr.expr t return expr.expr t with
             | expr.Ident t idc => expr.Ident idc
             | expr.Var t v => reify v
             | expr.Abs s d f => expr.Abs (fun x => @reify_expr _ (f (reflect (expr.Var x))))
             | expr.App s d f x => expr.App (@reify_expr _ f) (@reify_expr _ x)
             | expr.LetIn A B x f => expr.LetIn (@reify_expr _ x) (fun xv => @reify_expr _ (f (reflect (expr.Var xv))))
             end.

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

        (** TODO: Maybe have a fancier version of this that doesn't
             actually need to insert casts, by doing a fixpoint on the
             list of elements / the evar map *)
        Fixpoint app_transport_with_unification_resultT'_cps {var t p evm1 evm2 K} {struct p}
          : @with_unification_resultT' var t p evm1 K -> @unification_resultT' var t p evm2 -> forall T, (K -> option T) -> option T
          := fun f x T k
             => match p return with_unification_resultT' p evm1 K -> unification_resultT' p evm2 -> option T with
                | pattern.Wildcard t
                  => fun f x
                     => (tr <- type.try_make_transport_cps base.try_make_transport_cps var _ _;
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
               (@pattern.collect_vars _ t p)
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
               => if andb known (type.type_beq _ pattern.base.type.type_beq pt (pattern.type.relax t)) (* relies on evaluating to [false] if [known] is [false] *)
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
        Definition option_type_type_beq := option_beq (type.type_beq _ base.type.type_beq).

        Definition unify_types {t} (e : rawexpr) (p : pattern t) : ~> option EvarMap
          := fun T k
             => match preunify_types e p with
                | Some (Some (pt, t))
                  => match pattern.type.unify_extracted pt t with
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
                  => (tro <- type.try_make_transport_cps (@base.try_make_transport_cps) value (type_of_rawexpr e) (pattern.type.subst_default t' evm);
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

        Local Notation deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t
          := (match (@expr.expr base.type ident (if should_do_again then value else var) t) with
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

        Definition with_unif_rewrite_ruleTP_gen {var t} (p : pattern t) (should_do_again : bool) (with_opt : bool) (under_lets : bool)
          := @with_unification_resultT var t p (fun t => deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t).

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

        Definition maybe_do_againT (should_do_again : bool) (t : base.type)
          := ((@expr.expr base.type ident (if should_do_again then value else var) t) -> UnderLets (expr t)).
        Definition maybe_do_again
                   (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
                   (should_do_again : bool) (t : base.type)
          := if should_do_again return maybe_do_againT should_do_again t
             then do_again t
             else UnderLets.Base.

        Section eval_rewrite_rules.
          Context (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t)).

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
                        => (tr <- type.try_make_transport_cps (@base.try_make_transport_cps) _ _ _;
                              (tr <- tr;
                                 (tr' <- type.try_make_transport_cps (@base.try_make_transport_cps) _ _ _;
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
                  (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t)).

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
            := eta_ident_cps _ _ idc (fun t' idc' => assemble_identifier_rewriters' t' (rIdent true idc' #idc') (fun _ => id)).
        End with_do_again.
      End with_var.
      Global Arguments rew_should_do_again {_ _ _ _ _ _} _.
      Global Arguments rew_with_opt        {_ _ _ _ _ _} _.
      Global Arguments rew_under_lets      {_ _ _ _ _ _} _.
      Global Arguments rew_replacement     {_ _ _ _ _ _} _.

      Section full.
        Context {var : type.type base.type -> Type}.
        Local Notation expr := (@expr base.type ident).
        Local Notation value := (@Compile.value base.type ident var).
        Local Notation value_with_lets := (@Compile.value_with_lets base.type ident var).
        Local Notation UnderLets := (UnderLets.UnderLets base.type ident var).
        Local Notation reify_and_let_binds_cps := (@Compile.reify_and_let_binds_cps ident var (@UnderLets.reify_and_let_binds_base_cps var)).
        Local Notation reflect := (@Compile.reflect ident var).
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
                 (rewrite_head : forall (do_again : forall t : base.type, @expr value (type.base t) -> UnderLets (@expr var (type.base t)))
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
      End full.

      Definition Rewrite rewrite_head fuel {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
        := fun var => @rewrite var (rewrite_head var) fuel t (e _).
    End Compile.

    Module Make.
      Section make_rewrite_rules.
        Import Compile.
        Context {var : type.type base.type -> Type}.
        Local Notation type := (type.type base.type).
        Local Notation expr := (@expr.expr base.type ident var).
        Local Notation value := (@value base.type ident var).
        Local Notation pattern := (@pattern.pattern pattern.ident).
        Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
        Local Notation ptype := (type.type pattern.base.type).
        Let type_base (t : base.type) : type := type.base t.
        Let ptype_base (t : pattern.base.type) : ptype := type.base t.
        Let ptype_base' (t : base.type.base) : ptype := @type.base pattern.base.type t.
        Coercion ptype_base' : base.type.base >-> ptype.
        Coercion type_base : base.type >-> type.
        Coercion ptype_base : pattern.base.type >-> ptype.
        Local Notation collect_vars := (@pattern.collect_vars pattern.ident).
        Local Notation with_unification_resultT' := (@with_unification_resultT' pattern.ident (@pattern.ident.arg_types) value).
        Local Notation with_unification_resultT := (@with_unification_resultT pattern.ident (@pattern.ident.arg_types) value).
        Local Notation under_with_unification_resultT' := (@under_with_unification_resultT' pattern.ident (@pattern.ident.arg_types) value).
        Local Notation under_with_unification_resultT := (@under_with_unification_resultT pattern.ident (@pattern.ident.arg_types) value).
        Local Notation rewrite_ruleTP := (@rewrite_ruleTP ident var pattern.ident (@pattern.ident.arg_types)).
        Local Notation rewrite_ruleT := (@rewrite_ruleT ident var pattern.ident (@pattern.ident.arg_types)).
        Local Notation rewrite_rule_data := (@rewrite_rule_data ident var pattern.ident (@pattern.ident.arg_types)).

        Definition make_base_Literal_pattern (t : base.type.base) : pattern t
          := Eval cbv [pattern.ident.of_typed_ident] in
              pattern.Ident (pattern.ident.of_typed_ident (@ident.Literal t DefaultValue.type.base.default)).

        Fixpoint make_Literal_pattern (t : pattern.base.type) : option (pattern t)
          := match t return option (pattern t) with
             | pattern.base.type.var _ => None
             | pattern.base.type.type_base t => Some (make_base_Literal_pattern t)
             | pattern.base.type.prod A B
               => (a <- make_Literal_pattern A;
                    b <- make_Literal_pattern B;
                    Some ((#pattern.ident.pair @ a @ b)%pattern))
             | pattern.base.type.list A => None
             end%option%cps.

        Fixpoint make_interp_rewrite_pattern {t}
          : pattern t -> option (pattern (type.final_codomain t))
          := match t return pattern t -> option (pattern (type.final_codomain t)) with
             | type.base t
               => fun p => Some p
             | type.arrow (type.base s) d
               => fun p => (x <- make_Literal_pattern s; @make_interp_rewrite_pattern d (pattern.App p x))%option
             | type.arrow _ _ => fun _ => None
             end.

        Lemma collect_vars_literal_empty {t}
          : match make_Literal_pattern t with
            | Some p => collect_vars p = PositiveSet.empty /\ pattern.base.collect_vars t = PositiveSet.empty
            | None => True
            end.
        Proof using Type.
          induction t; cbn; cbv [Option.bind ptype_base] in *; break_innermost_match; cbn; auto.
          destruct_head'_and.
          repeat match goal with H : _ |- _ => rewrite H end; cbn; auto.
        Qed.

        Fixpoint make_Literal_pattern_interp_helper {t evm T}
                 {struct t}
          : match make_Literal_pattern t with
            | Some x
              => (base.interp (pattern.base.subst_default t evm) -> T)
                 -> with_unification_resultT' x evm T
            | None => True
            end.
        Proof.
          refine match t return match make_Literal_pattern t with
                                | Some x
                                  => (base.interp (pattern.base.subst_default t evm) -> T)
                                     -> with_unification_resultT' x evm T
                                | None => True
                                end
                 with
                 | pattern.base.type.var _
                 | pattern.base.type.list _
                   => I
                 | pattern.base.type.type_base t
                   => fun f x => f x
                 | pattern.base.type.prod A B
                   => let recA := @make_Literal_pattern_interp_helper
                                    A evm
                                    (match make_Literal_pattern A, make_Literal_pattern B return Type with
                                     | Some a, Some b => _
                                     | _, _ => unit
                                     end) in
                      let recB := @make_Literal_pattern_interp_helper
                                    B evm
                                    (match make_Literal_pattern A, make_Literal_pattern B return Type with
                                     | Some a, Some b => _
                                     | _, _ => unit
                                     end) in
                      _
                 end;
            clearbody recA recB;
            cbn in *.
          destruct (make_Literal_pattern A) as [a|], (make_Literal_pattern B) as [b|]; try exact I; cbn.
          refine (fun f
                  => recA (fun a' => recB (fun b' => f (a', b')))).
        Defined.

        (** We can only do this because we're dealing with literal patterns that have no variables *)
        Definition strip_collect_vars
                 {s : pattern.base.type} {d : ptype}
                 {p : pattern (type.base s -> d)%ptype}
                 (p_res : pattern.type.forall_vars
                            (collect_vars p)
                            (fun evm =>
                               with_unification_resultT'
                                 p evm
                                 (type.interp base.interp (pattern.type.subst_default (type.base s -> d)%ptype evm))))
          : forall (rec : forall x : pattern (type.base s),
                       pattern.type.forall_vars (PositiveSet.union (collect_vars x) (collect_vars p))
                                                (fun evm =>
                                                   with_unification_resultT'
                                                     p evm
                                                     (with_unification_resultT'
                                                        x evm
                                                        (type.interp base.interp (pattern.type.subst_default d evm))))
                       -> match make_interp_rewrite_pattern (p @ x) with
                          | Some p' => @rewrite_rule_data _ p'
                          | None => True
                          end),
            match (x <- make_Literal_pattern s;
                     make_interp_rewrite_pattern (p @ x))%option with
            | Some p' => @rewrite_rule_data _ p'
            | None => True
            end.
        Proof.
          intro rec_call.
          pose proof (@collect_vars_literal_empty s) as H.
          pose proof (@make_Literal_pattern_interp_helper s) as F.
          destruct (make_Literal_pattern s) as [x|]; [ | exact I ]; cbn [Option.bind].
          cbv [ptype_base] in *.
          refine (rec_call x _); clear rec_call.
          destruct (pattern.collect_vars x); [ | exfalso; clear -H; abstract (destruct H as [H _]; cbv in H; discriminate) ].
          refine (pattern.type.under_forall_vars (fun evm => under_with_unification_resultT' (F _ _)) p_res).
        Defined.

        Fixpoint make_interp_rewrite'_helper {t}
          : forall (p : pattern t)
                   (base_rewrite : with_unification_resultT p (type.interp base.interp))
                   (p' := make_interp_rewrite_pattern p),
            match p' return Type with
            | Some p' => rewrite_ruleTP {| pattern.pattern_of_anypattern := p' |}
            | None => True
            end
          := match t return (forall (p : pattern t)
                                    (base_rewrite : with_unification_resultT p (type.interp base.interp))
                                    (p' := make_interp_rewrite_pattern p),
                                match p' return Type with
                                | Some p' => rewrite_ruleTP {| pattern.pattern_of_anypattern := p' |}
                                | None => True
                                end)
             with
             | type.base t
               => fun p base_rewrite
                  => {| rew_should_do_again := false;
                        rew_with_opt := false;
                        rew_under_lets := false;
                        rew_replacement
                        := under_with_unification_resultT
                             (fun evm v => ident.smart_Literal v)
                             base_rewrite |}
             | type.arrow (type.base s) d
               => fun p base_rewrite
                  => let rec_call
                         := fun x => @make_interp_rewrite'_helper d (p @ x)%pattern in
                     strip_collect_vars base_rewrite rec_call
             | type.arrow _ _
               => fun _ _ => I
             end.

        Definition make_interp_rewrite' {t} (idc : ident t)
                   (pidc := pattern.Ident (pattern.ident.of_typed_ident idc))
                   (val : with_unification_resultT pidc (type.interp base.interp))
          : option rewrite_ruleT
          := match make_interp_rewrite_pattern pidc as p
                   return match p return Type with
                          | Some p' => rewrite_ruleTP {| pattern.pattern_of_anypattern := p' |}
                          | None => True
                          end
                          -> option rewrite_ruleT
             with
             | Some p'
               => fun r
                  => Some (existT _ {| pattern.pattern_of_anypattern := p' |} r)
             | None => fun _ => None
             end (make_interp_rewrite'_helper pidc val).

        Definition make_default_with_unification_resultT {t vs ls} (v : type.interp base.interp t)
          : pattern.type.forall_vars
              vs
              (fun evm =>
                 fold_right (fun a K : Type => a -> K)
                            (type.interp base.interp (pattern.type.subst_default (pattern.type.relax t) evm))
                            ls)
          := pattern.type.lam_forall_vars
               (fun evm
                => list_rect
                     (fun ls => fold_right (fun a K => a -> K) _ ls)
                     (@pattern.type.subst_default_relax _ t _ v)
                     (fun x xs rec _ => rec)
                     _).

        Definition make_interp_rewrite'' {t} (idc : ident t) : option rewrite_ruleT
          := @make_interp_rewrite'
               t idc (make_default_with_unification_resultT (ident.interp idc)).

        Local Ltac collect_id body so_far :=
          let next := match body with
                      | context[@id ?t ?v]
                        => lazymatch so_far with
                           | context[cons (existT _ _ v) _] => constr:(I : I)
                           | _ => constr:(@Some _ v)
                           end
                      | _ => constr:(@None unit)
                      end in
          lazymatch next with
          | @Some (ident ?t) ?v => collect_id body (cons (existT ident t v) so_far)
          | None => (eval cbv [List.rev List.app] in (List.rev so_far))
          end.

        Definition simple_idents : list (sigT ident)
          := ltac:(let v := constr:(fun t idc => @pattern.ident.eta_ident_cps _ t idc (fun _ => id)) in
                   let v := (eval cbv [pattern.ident.eta_ident_cps] in v) in
                   let ls := collect_id v (@nil (sigT ident)) in
                   exact ls).

        Let interp_rewrite_rules'
          := Eval cbv -[ident.interp ident.gen_interp ident.smart_Literal] in
              Option.List.map
               (fun '(existT _ idc) => make_interp_rewrite'' idc)
               (simple_idents).

        Definition interp_rewrite_rules
          := Eval cbv [interp_rewrite_rules' ident.interp ident.gen_interp ident.smart_Literal] in
              interp_rewrite_rules'.
      End make_rewrite_rules.
    End Make.

    Section with_var.
      Import Compile.
      Context {var : type.type base.type -> Type}.
      Local Notation type := (type.type base.type).
      Local Notation expr := (@expr.expr base.type ident var).
      Local Notation value := (@value base.type ident var).
      Local Notation pattern := (@pattern.pattern pattern.ident).
      Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
      Local Notation ptype := (type.type pattern.base.type).
      Let type_base (t : base.type) : type := type.base t.
      Let ptype_base (t : pattern.base.type) : ptype := type.base t.
      Let ptype_base' (t : base.type.base) : ptype := @type.base pattern.base.type t.
      Coercion ptype_base' : base.type.base >-> ptype.
      Coercion type_base : base.type >-> type.
      Coercion ptype_base : pattern.base.type >-> ptype.
      Local Notation Build_rewrite_rule_data := (@Build_rewrite_rule_data ident var pattern.ident (@pattern.ident.arg_types)).
      Local Notation Build_anypattern := (@pattern.Build_anypattern pattern.ident).
      Local Notation rewrite_ruleTP := (@rewrite_ruleTP ident var pattern.ident (@pattern.ident.arg_types)).
      Local Notation rewrite_ruleT := (@rewrite_ruleT ident var pattern.ident (@pattern.ident.arg_types)).
      Local Notation rewrite_rulesT := (@rewrite_rulesT ident var pattern.ident (@pattern.ident.arg_types)).
      Definition pident_unify_unknown := @pattern.ident.unify.
      Definition invert_bind_args_unknown := @pattern.Raw.ident.invert_bind_args.
      Local Notation assemble_identifier_rewriters := (@assemble_identifier_rewriters ident var (@pattern.ident.eta_ident_cps) (@pattern.ident) (@pattern.ident.arg_types) (@pattern.ident.unify) pident_unify_unknown pattern.Raw.ident (@pattern.Raw.ident.full_types) (@pattern.Raw.ident.invert_bind_args) invert_bind_args_unknown (@pattern.Raw.ident.type_of) (@pattern.Raw.ident.to_typed) pattern.Raw.ident.is_simple).

      Delimit Scope rewrite_scope with rewrite.
      Delimit Scope rewrite_opt_scope with rewrite_opt.
      Delimit Scope rewrite_lets_scope with rewrite_lets.
      Local Open Scope rewrite_opt_scope.
      Local Open Scope rewrite_lets_scope.
      Local Open Scope rewrite_scope.

      Notation make_rewrite_gen should_do_again with_opt under_lets p f
        := (existT
              rewrite_ruleTP
              (@Build_anypattern _ p%pattern)
              (@Build_rewrite_rule_data _ p%pattern should_do_again with_opt under_lets f)).
      (* %cps%option%under_lets *)
      Notation make_rewrite p f
        := (make_rewrite_gen false false false p f%rewrite%expr%list%Z%bool).
      Notation make_rewritel p f
        := (make_rewrite_gen false false true p f%rewrite_lets%rewrite%expr%list%Z%bool%under_lets).
      Notation make_rewriteo p f
        := (make_rewrite_gen false true false p f%rewrite_opt%rewrite%expr%list%Z%bool).
      Notation make_rewriteol p f
        := (make_rewrite_gen false true true p f%rewrite_lets%rewrite_opt%rewrite%expr%list%Z%bool%under_lets).
      Notation make_rewrite_step p f
        := (make_rewrite_gen true false false p f%rewrite%expr%list%Z%bool).
      Notation make_rewritel_step p f
        := (make_rewrite_gen true false true p f%rewrite_lets%rewrite%expr%list%Z%bool%under_lets).
      Notation make_rewriteo_step p f
        := (make_rewrite_gen true true false p f%rewrite_opt%rewrite%expr%list%Z%bool).
      Notation make_rewriteol_step p f
        := (make_rewrite_gen true true true p f%rewrite_lets%rewrite_opt%rewrite%expr%list%Z%bool%under_lets).
      Let UnderLetsExpr {btype bident ivar} t := @UnderLets.UnderLets base.type ident var (@expr.expr btype bident ivar t).
      Let OptExpr {btype bident ivar} t := option (@expr.expr btype bident ivar t).
      Let OptUnderLetsExpr {btype bident ivar} t := option (@UnderLets.UnderLets base.type ident var (@expr.expr btype bident ivar t)).
      Let BaseExpr {btype ident ivar t} : @expr.expr btype ident ivar t -> @UnderLetsExpr btype ident ivar t := UnderLets.Base.
      Let SomeExpr {btype ident ivar t} : @expr.expr btype ident ivar t -> @OptExpr btype ident ivar t := Some.
      Let SomeUnderLetsExpr {btype ident ivar t} : @UnderLetsExpr btype ident ivar t -> @OptUnderLetsExpr btype ident ivar t := Some.
      Coercion BaseExpr : expr >-> UnderLetsExpr.
      Coercion SomeExpr : expr >-> OptExpr.
      Coercion SomeUnderLetsExpr : UnderLetsExpr >-> OptUnderLetsExpr.

      Local Notation "x <- y ; f" := (Compile.option_bind' y%rewrite_lets%rewrite_opt%rewrite (fun x => f%rewrite_lets%rewrite_opt%rewrite : OptUnderLetsExpr _)) : rewrite_lets_scope.
      Local Notation "x <- y ; f" := (Compile.option_bind' y%rewrite_opt%rewrite (fun x => f%rewrite_opt%rewrite : OptExpr _)) : rewrite_opt_scope.
      Local Notation "x <-- y ; f" := (UnderLets.splice y%rewrite_lets%rewrite (fun x => (f%rewrite_lets%rewrite : UnderLetsExpr _))) : rewrite_lets_scope.
      Local Notation "x <--- y ; f" := (UnderLets.splice_list y%rewrite_lets%rewrite (fun x => (f%rewrite_lets%rewrite : UnderLetsExpr _))) : rewrite_lets_scope.
      Local Notation "x <---- y ; f" := (Compile.option_bind' y%rewrite_lets%rewrite_opt%rewrite (fun x => (f%rewrite_lets%rewrite : UnderLetsExpr _) : OptUnderLetsExpr _)) : rewrite_lets_scope.
      Local Notation "'llet' x := y 'in' f" := (UnderLets.UnderLet y%rewrite_lets%rewrite (fun x => (f%rewrite_lets%rewrite : UnderLetsExpr _))) : rewrite_lets_scope.

      Definition rlist_rect {A P}
                 {ivar}
                 (Pnil : @UnderLetsExpr base.type ident ivar (type.base P))
                 (Pcons : expr (type.base A) -> list (expr (type.base A)) -> @expr.expr base.type ident ivar (type.base P) -> @UnderLetsExpr base.type ident ivar (type.base P))
                 (e : expr (type.base (base.type.list A)))
        : @OptUnderLetsExpr base.type ident ivar P
        := (ls <- reflect_list e;
              list_rect
                (fun _ => UnderLetsExpr (type.base P))
                Pnil
                (fun x xs rec => rec' <-- rec; Pcons x xs rec')
                ls).

      Definition rwhen {ivar t} (v : @OptExpr base.type ident ivar t) (cond : bool)
        : @OptExpr base.type ident ivar t
        := if cond then v else None.
      Definition rwhenl {ivar t} (v : @OptUnderLetsExpr base.type ident ivar t) (cond : bool)
        : @OptUnderLetsExpr base.type ident ivar t
        := if cond then v else None.

      Local Notation "e 'when' cond" := (rwhen e%rewrite_opt%rewrite cond) (only parsing, at level 100) : rewrite_opt_scope.
      Local Notation "e 'owhen' cond" := (rwhenl e%rewrite_lets%rewrite_opt%rewrite cond) (only parsing, at level 100) : rewrite_lets_scope.
      Local Notation "e 'when' cond" := (rwhenl (e%rewrite_lets%rewrite : UnderLetsExpr _)  cond) (only parsing, at level 100) : rewrite_lets_scope.

      Local Notation ℤ := base.type.Z.
      Local Notation ℕ := base.type.nat.
      Local Notation bool := base.type.bool.
      Local Notation list := pattern.base.type.list.

      (*
      Local Arguments Make.interp_rewrite_rules / .
      *)
      (**
         The follow are rules for rewriting expressions. On the left is a pattern to match:
           ??: any expression whose type contains no arrows.
           ??{x}: any expression whose type is x.
           ??{list '1}: for example, a list with elements of a type variable '1.
           x @ y: x applied to y.
           #?x: a value, know at compile time, with type x. (Where x is one of {ℕ or N (nat), 𝔹 or B (bool), ℤ or Z (integers)}.)
           #x: the identifer x.

         A matched expression is replaced with the right-hand-side, which is a function that returns a syntax tree, or None to indicate that the match didn't really match. The syntax tree is under two monads: option, and custom UnderLets monad.

         The function takes first any types that appeared as type variables (e.g., '1, '2, etc), and then the elements that where matched on the LHS as arguments. The arguments are given in the same order as on the LHS.

         In the RHS, the follow notation applies:
           ##x: the literal value x
           #x: the identifier x
           x @ y: x applied to y
           $x: PHOAS variable named x
           λ: PHOAS abstraction / functions

         On the RHS, since we're returning a value under three monads, there's some fun notion for dealing with different levels of the monad stack in a single expression:
           <-: bind, under the Option monad.
           <--: bind, under the UnderLets monad
           <---: bind, under the UnderLets+List monad.
           <----: bind+ret, under the Option monad.

         There are eight choices for kinds of rewrite rules:
         - [make_rewrite] for rules returning [expr]
         - [make_rewriteo] for rules returning [option expr]
         - [make_rewritel] for rules returning [UnderLets expr]
         - [make_rewriteol] for rules returning [option (UnderLets expr)]
         - [make_rewrite*_step] as [make_rewrite*] above, but indicating that rewriting should happen again in the result of rewriting with this rule.

         If stuck, email Jason.
       *)
      Local Arguments pattern.anypattern : clear implicits.
      Local Arguments Make.interp_rewrite_rules / .
      Let myapp {A} := Eval cbv [List.app] in @List.app A.
      Definition nbe_rewrite_rules : rewrite_rulesT
        := Eval cbv [Make.interp_rewrite_rules myapp] in
            myapp
              Make.interp_rewrite_rules
              [make_rewrite (#(@pattern.ident.fst '1 '2) @ (??, ??)) (fun _ _ x y => x)
               ; make_rewrite (#(@pattern.ident.snd '1 '2) @ (??, ??)) (fun _ x _ y => y)
               ; make_rewrite (#(@pattern.ident.List_repeat '1) @ ?? @ #?ℕ) (fun _ x n => reify_list (repeat x n))
               ; make_rewritel (#(@pattern.ident.bool_rect '1) @ ?? @ ?? @ #?𝔹) (fun _ t f b => if b then t ##tt else f ##tt)
               ; make_rewritel (#(@pattern.ident.prod_rect '1 '2 '3) @ ?? @ (??, ??)) (fun _ _ _ f x y => f x y)
               ; make_rewriteol (??{list '1} ++ ??{list '1}) (fun _ xs ys => rlist_rect ys (fun x _ xs_ys => x :: xs_ys) xs)
               ; make_rewriteol
                   (#(@pattern.ident.List_firstn '1) @ #?ℕ @ ??)
                   (fun _ n xs => xs <- reflect_list xs; reify_list (List.firstn n xs))
               ; make_rewriteol
                   (#(@pattern.ident.List_skipn '1) @ #?ℕ @ ??)
                   (fun _ n xs => xs <- reflect_list xs; reify_list (List.skipn n xs))
               ; make_rewriteol
                   (#(@pattern.ident.List_rev '1) @ ??)
                   (fun _ xs => xs <- reflect_list xs; reify_list (List.rev xs))
               ; make_rewriteol_step
                   (#(@pattern.ident.List_flat_map '1 '2) @ ?? @ ??)
                   (fun _ _ f xs
                    => rlist_rect
                         []
                         (fun x _ flat_map_tl => fx <-- f x; ($fx ++ flat_map_tl))
                         xs)
               ; make_rewriteol_step
                    (#(@pattern.ident.List_partition '1) @ ?? @ ??)
                    (fun _ f xs
                     => rlist_rect
                          ([], [])
                          (fun x tl partition_tl
                           => fx <-- f x;
                                (#ident.prod_rect
                                  @ (λ g d, #ident.bool_rect
                                             @ (λ _, ($x :: $g, $d))
                                             @ (λ _, ($g, $x :: $d))
                                             @ $fx)
                                  @ partition_tl))
                          xs)
               ; make_rewriteol
                    (#(@pattern.ident.List_fold_right '1 '2) @ ?? @ ?? @ ??)
                    (fun _ _ f init xs => rlist_rect init (fun x _ y => f x y) xs)
               ; make_rewriteol
                   (#(@pattern.ident.list_rect '1 '2) @ ?? @ ?? @ ??)
                   (fun _ _ Pnil Pcons xs
                    => rlist_rect (Pnil ##tt) (fun x' xs' rec => Pcons x' (reify_list xs') rec) xs)
               ; make_rewritel
                   (#(@pattern.ident.list_case '1 '2) @ ?? @ ?? @ [])
                   (fun _ _ Pnil Pcons => Pnil ##tt)
               ; make_rewritel
                   (#(@pattern.ident.list_case '1 '2) @ ?? @ ?? @ (?? :: ??))
                   (fun _ _ Pnil Pcons x xs => Pcons x xs)
               ; make_rewriteol
                   (#(@pattern.ident.List_map '1 '2) @ ?? @ ??)
                   (fun _ _ f xs => rlist_rect [] (fun x _ fxs => fx <-- f x; fx :: fxs) xs)
               ; make_rewriteo
                   (#(@pattern.ident.List_nth_default '1) @ ?? @ ?? @ #?ℕ)
                   (fun _ default ls n => ls <- reflect_list ls; nth_default default ls n)
               ; make_rewritel
                   (#(@pattern.ident.nat_rect '1) @ ?? @ ?? @ #?ℕ)
                   (fun _ O_case S_case n
                    => nat_rect _ (O_case ##tt) (fun n' rec => rec <-- rec; S_case ##n' rec) n)
               ; make_rewritel
                   (#(@pattern.ident.nat_rect_arrow '1 '2) @ ?? @ ?? @ #?ℕ @ ??)
                   (fun _ _ O_case S_case n v
                    => nat_rect _ O_case (fun n' rec v => S_case ##n' rec v) n v)
               ; make_rewriteo
                   (#(@pattern.ident.List_length '1) @ ??)
                   (fun _ xs => xs <- reflect_list xs; ##(List.length xs))
               ; make_rewriteo
                   (#(@pattern.ident.List_combine '1 '2) @ ?? @ ??)
                   (fun _ _ xs ys
                    => xs <- reflect_list xs;
                         ys <- reflect_list ys;
                         reify_list (List.map (fun '((x, y)%core) => (x, y)) (List.combine xs ys)))
               ; make_rewriteol
                   (#(@pattern.ident.List_update_nth '1) @ #?ℕ @ ?? @ ??)
                   (fun _ n f ls
                    => ls <---- reflect_list ls;
                         retv <--- (update_nth
                                      n
                                      (fun x => x <-- x; f x)
                                      (List.map UnderLets.Base ls));
                         reify_list retv)
              ].

      Definition arith_rewrite_rules (max_const_val : Z) : rewrite_rulesT
        := [make_rewrite (#(@pattern.ident.fst '1 '2) @ (??, ??)) (fun _ _ x y => x)
            ; make_rewrite (#(@pattern.ident.snd '1 '2) @ (??, ??)) (fun _ x _ y => y)
            ; make_rewriteo (#?ℤ   + ??) (fun z v => v  when  z =? 0)
            ; make_rewriteo (?? + #?ℤ  ) (fun v z => v  when  z =? 0)
            ; make_rewriteo (#?ℤ   + (-??)) (fun z v => ##z - v  when  z >? 0)
            ; make_rewriteo ((-??) + #?ℤ  ) (fun v z => ##z - v  when  z >? 0)
            ; make_rewriteo (#?ℤ   + (-??)) (fun z v => -(##((-z)%Z) + v)  when  z <? 0)
            ; make_rewriteo ((-??) + #?ℤ  ) (fun v z => -(v + ##((-z)%Z))  when  z <? 0)
            ; make_rewrite ((-??) + (-??)) (fun x y => -(x + y))
            ; make_rewrite ((-??) +   ?? ) (fun x y => y - x)
            ; make_rewrite (  ??  + (-??)) (fun x y => x - y)

            ; make_rewriteo (#?ℤ   - (-??)) (fun z v =>  v  when  z =? 0)
            ; make_rewriteo (#?ℤ   -   ?? ) (fun z v => -v  when  z =? 0)
            ; make_rewriteo (?? - #?ℤ     ) (fun v z =>  v  when  z =? 0)
            ; make_rewriteo (#?ℤ   - (-??)) (fun z v => ##z + v  when  z >? 0)
            ; make_rewriteo (#?ℤ   - (-??)) (fun z v => v - ##((-z)%Z)     when  z <? 0)
            ; make_rewriteo (#?ℤ   -   ?? ) (fun z v => -(##((-z)%Z) + v)  when  z <? 0)
            ; make_rewriteo ((-??) - #?ℤ  ) (fun v z => -(v + ##(z))       when  z >? 0)
            ; make_rewriteo ((-??) - #?ℤ  ) (fun v z => ##((-z)%Z) - v     when  z <? 0)
            ; make_rewriteo (  ??  - #?ℤ  ) (fun v z => v + ##((-z)%Z)     when  z <? 0)
            ; make_rewrite ((-??) - (-??)) (fun x y => y - x)
            ; make_rewrite ((-??) -   ?? ) (fun x y => -(x + y))
            ; make_rewrite (  ??  - (-??)) (fun x y => x + y)

            ; make_rewrite (#?ℤ   *  #?ℤ ) (fun x y => ##((x*y)%Z))
            ; make_rewriteo (#?ℤ   * ??) (fun z v => ##0  when  z =? 0)
            ; make_rewriteo (?? * #?ℤ  ) (fun v z => ##0  when  z =? 0)
            ; make_rewriteo (#?ℤ   * ??) (fun z v => v  when  z =? 1)
            ; make_rewriteo (?? * #?ℤ  ) (fun v z => v  when  z =? 1)
            ; make_rewriteo (#?ℤ      * (-??)) (fun z v =>  v  when  z =? (-1))
            ; make_rewriteo ((-??) * #?ℤ     ) (fun v z =>  v  when  z =? (-1))
            ; make_rewriteo (#?ℤ      *   ?? ) (fun z v => -v  when  z =? (-1))
            ; make_rewriteo (??    * #?ℤ     ) (fun v z => -v  when  z =? (-1))
            ; make_rewriteo (#?ℤ      * ??   ) (fun z v => -(##((-z)%Z) * v)  when  z <? 0)
            ; make_rewriteo (??    * #?ℤ     ) (fun v z => -(v * ##((-z)%Z))  when  z <? 0)
            ; make_rewrite ((-??) * (-??)) (fun x y => x * y)
            ; make_rewrite ((-??) *   ?? ) (fun x y => -(x * y))
            ; make_rewrite (  ??  * (-??)) (fun x y => -(x * y))

            ; make_rewriteo (?? &' #?ℤ) (fun x mask => ##(0)%Z  when  mask =? 0)
            ; make_rewriteo (#?ℤ &' ??) (fun mask x => ##(0)%Z  when  mask =? 0)

            ; make_rewriteo (?? * #?ℤ)   (fun x y => x << ##(Z.log2 y)  when  (y =? (2^Z.log2 y)) && (negb (y =? 2)))
            ; make_rewriteo (#?ℤ * ??)   (fun y x => x << ##(Z.log2 y)  when  (y =? (2^Z.log2 y)) && (negb (y =? 2)))
            ; make_rewriteo (?? / #?ℤ)   (fun x y => x                  when  (y =? 1))
            ; make_rewriteo (?? mod #?ℤ) (fun x y => ##(0)%Z            when  (y =? 1))
            ; make_rewriteo (?? / #?ℤ)   (fun x y => x >> ##(Z.log2 y)  when  (y =? (2^Z.log2 y)))
            ; make_rewriteo (?? mod #?ℤ) (fun x y => x &' ##(y-1)%Z     when  (y =? (2^Z.log2 y)))
            ; make_rewrite (-(-??)) (fun v => v)

            (* We reassociate some multiplication of small constants  *)
            ; make_rewriteo (#?ℤ * (#?ℤ * (?? * ??))) (fun c1 c2 x y => (x * (y * (##c1 * ##c2))) when  (Z.abs c1 <=? Z.abs max_const_val) && (Z.abs c2 <=? Z.abs max_const_val))
            ; make_rewriteo (#?ℤ * (?? * (?? * #?ℤ))) (fun c1 x y c2 => (x * (y * (##c1 * ##c2))) when  (Z.abs c1 <=? Z.abs max_const_val) && (Z.abs c2 <=? Z.abs max_const_val))
            ; make_rewriteo (#?ℤ * (?? * ??)) (fun c x y => (x * (y * ##c)) when  (Z.abs c <=? Z.abs max_const_val))
            ; make_rewriteo (#?ℤ * ??) (fun c x => (x * ##c) when  (Z.abs c <=? Z.abs max_const_val))

            ; make_rewrite_step (* _step, so that if one of the arguments is concrete, we automatically get the rewrite rule for [Z_cast] applying to it *)
                (#pattern.ident.Z_cast2 @ (??, ??)) (fun r x y => (#(ident.Z_cast (fst r)) @ $x, #(ident.Z_cast (snd r)) @ $y))

            ; make_rewriteol (-??) (fun e => (llet v := e in -$v)  when  negb (SubstVarLike.is_var_fst_snd_pair_opp_cast e)) (* inline negation when the rewriter wouldn't already inline it *)
           ].

      Let cst {var} (r : zrange) (e : @expr.expr _ _ var _) := (#(ident.Z_cast r) @ e)%expr.
      Let cst' {var} (r : zrange) (e : @expr.expr _ _ var _) := (#(ident.Z_cast (-r)) @ e)%expr.
      Let cst2 {var} (r : zrange * zrange) (e : @expr.expr _ _ var _) := (#(ident.Z_cast2 r) @ e)%expr.

      Let llet2_opp2 (rvc : zrange * zrange) e
        := (let rvc' := (fst rvc, -snd rvc)%zrange in
            let cst' e := #(ident.Z_cast2 rvc') @ e in
            let cst1 e := #(ident.Z_cast (fst rvc)) @ e in
            let cst2 e := #(ident.Z_cast (snd rvc)) @ e in
            let cst2' e := #(ident.Z_cast (-snd rvc)) @ e in
            (llet vc := cst' e in
                 (cst1 (#ident.fst @ (cst' ($vc))), cst2 (-(cst2' (#ident.snd @ (cst' ($vc))))))))%expr.

      Let llet2 (rvc : zrange * zrange) e
        := ((llet vc := cst2 rvc e in
                 (cst (fst rvc) (#ident.fst @ (cst2 rvc ($vc))),
                  cst (snd rvc) (#ident.snd @ (cst2 rvc ($vc))))))%expr.

      Definition arith_with_casts_rewrite_rules : rewrite_rulesT
        := [make_rewrite (#(@pattern.ident.fst '1 '2) @ (??, ??)) (fun _ _ x y => x)
            ; make_rewrite (#(@pattern.ident.snd '1 '2) @ (??, ??)) (fun _ _ x y => y)

            ; make_rewriteo (??') (fun r v => cst r (##(lower r))  when  lower r =? upper r)

            ; make_rewriteo
                (#?ℤ' + ??  )
                (fun rz z v => v  when  (z =? 0) && (is_bounded_by_bool z (ZRange.normalize rz)))
            ; make_rewriteo
                (??   + #?ℤ')
                (fun v rz z => v  when  (z =? 0) && (is_bounded_by_bool z (ZRange.normalize rz)))

            ; make_rewriteo
                (#?ℤ'  - (-'??'))
                (fun rz z rnv rv v => cst rv v  when  (z =? 0) && (ZRange.normalize rv <=? -ZRange.normalize rnv)%zrange && (is_bounded_by_bool z rz))
            ; make_rewriteo (#?ℤ'  -   ?? ) (fun rz z v => -v  when  (z =? 0) && is_bounded_by_bool z (ZRange.normalize rz))

            ; make_rewriteo (#?ℤ' << ??) (fun rx x y => ##0  when  (x =? 0) && is_bounded_by_bool x (ZRange.normalize rx))

            ; make_rewriteo (-(-'??')) (fun rnv rv v => cst rv v  when (ZRange.normalize rv <=? -ZRange.normalize rnv)%zrange)

            ; make_rewriteo (#pattern.ident.Z_mul_split @ ?? @ #?ℤ' @ ??) (fun s rxx xx y => (cst r[0~>0] ##0, cst r[0~>0] ##0)%Z  when  (xx =? 0) && is_bounded_by_bool xx (ZRange.normalize rxx))
            ; make_rewriteo (#pattern.ident.Z_mul_split @ ?? @ ?? @ #?ℤ') (fun s y rxx xx => (cst r[0~>0] ##0, cst r[0~>0] ##0)%Z  when  (xx =? 0) && is_bounded_by_bool xx (ZRange.normalize rxx))
            ; make_rewriteo
                (#pattern.ident.Z_mul_split @ #?ℤ' @ #?ℤ' @ ??')
                (fun rs s rxx xx ry y => (cst ry y, cst r[0~>0] ##0)%Z  when  (xx =? 1) && (ZRange.normalize ry <=? r[0~>s-1])%zrange && is_bounded_by_bool s (ZRange.normalize rs) && is_bounded_by_bool xx (ZRange.normalize rxx))
            ; make_rewriteo
                (#pattern.ident.Z_mul_split @ #?ℤ' @ ??' @ #?ℤ')
                (fun rs s ry y rxx xx => (cst ry y, cst r[0~>0] ##0)%Z  when  (xx =? 1) && (ZRange.normalize ry <=? r[0~>s-1])%zrange && is_bounded_by_bool s (ZRange.normalize rs) && is_bounded_by_bool xx (ZRange.normalize rxx))
                (*
            ; make_rewriteo
                (#pattern.ident.Z_mul_split @ #?ℤ @ #?ℤ @ ??')
                (fun s xx ry y => (cst' ry (-cst ry y), ##0%Z)  when  (xx =? (-1)) && (ZRange.normalize ry <=? r[0~>s-1])%zrange)
            ; make_rewriteo
                (#pattern.ident.Z_mul_split @ #?ℤ @ ??' @ #?ℤ)
                (fun s ry y xx => (cst' ry (-cst ry y), ##0%Z)  when  (xx =? (-1)) && (ZRange.normalize ry <=? r[0~>s-1])%zrange)
                 *)


            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_get_carry @ ?? @ (-'??') @ ??))
                (fun rvc s rny ry y x
                 => (llet2_opp2 rvc (#ident.Z_sub_get_borrow @ s @ x @ cst ry y))
                      when (ZRange.normalize ry <=? -ZRange.normalize rny)%zrange)
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_get_carry @ ?? @ ?? @ (-'??')))
                (fun rvc s x rny ry y
                 => (llet2_opp2 rvc (#ident.Z_sub_get_borrow @ s @ x @ cst ry y))
                      when (ZRange.normalize ry <=? -ZRange.normalize rny)%zrange)
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_get_carry @ ?? @ #?ℤ' @ ??))
                (fun rvc s ryy yy x
                 => (llet2_opp2 rvc (#ident.Z_sub_get_borrow @ s @ x @ cst (ZRange.opp ryy) ##(-yy)%Z))
                      when  (yy <? 0) && is_bounded_by_bool yy (ZRange.normalize ryy))
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_get_carry @ ?? @ ?? @ #?ℤ'))
                (fun rvc s x ryy yy => (llet2_opp2 rvc (#ident.Z_sub_get_borrow @ s @ x @ cst (ZRange.opp ryy) ##(-yy)%Z))
                                     when  (yy <? 0) && is_bounded_by_bool yy (ZRange.normalize ryy))


            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ (-'??') @ (-'??') @ ??))
                (fun rvc s rnc rc c rny ry y x
                 => (llet2_opp2 rvc (#ident.Z_sub_with_get_borrow @ s @ (cst rc c) @ x @ (cst ry y)))
                      when ((ZRange.normalize ry <=? -ZRange.normalize rny) && (ZRange.normalize rc <=? -ZRange.normalize rnc))%zrange)
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ (-'??') @ ?? @ (-'??')))
                (fun rvc s rnc rc c x rny ry y
                 => (llet2_opp2 rvc (#ident.Z_sub_with_get_borrow @ s @ (cst rc c) @ x @ (cst ry y)))
                      when ((ZRange.normalize ry <=? -ZRange.normalize rny) && (ZRange.normalize rc <=? -ZRange.normalize rnc))%zrange)
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ #?ℤ' @ (-'??') @ ??))
                (fun rvc s rcc cc rny ry y x
                 => (llet2_opp2 rvc (#ident.Z_sub_get_borrow @ s @ x @ cst ry y))
                      when  (cc =? 0) && (ZRange.normalize ry <=? -ZRange.normalize rny)%zrange && is_bounded_by_bool cc (ZRange.normalize rcc))
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ #?ℤ' @ (-'??') @ ??))
                (fun rvc s rcc cc rny ry y x
                 => (llet2_opp2 rvc (#ident.Z_sub_with_get_borrow @ s @ cst (ZRange.opp rcc) ##(-cc)%Z @ x @ cst ry y))
                      when  (cc <? 0) && (ZRange.normalize ry <=? -ZRange.normalize rny)%zrange && is_bounded_by_bool cc (ZRange.normalize rcc))
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ #?ℤ' @ ?? @ (-'??')))
                (fun rvc s rcc cc x rny ry y
                 => (llet2_opp2 rvc (#ident.Z_sub_get_borrow @ s @ x @ cst ry y))
                      when  (cc =? 0) && (ZRange.normalize ry <=? -ZRange.normalize rny)%zrange && is_bounded_by_bool cc (ZRange.normalize rcc))
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ #?ℤ' @ ?? @ (-'??')))
                (fun rvc s rcc cc x rny ry y
                 => (llet2_opp2 rvc (#ident.Z_sub_with_get_borrow @ s @ cst (ZRange.opp rcc) ##(-cc)%Z @ x @ cst ry y)
                      when  (cc <? 0) && (ZRange.normalize ry <=? -ZRange.normalize rny)%zrange && is_bounded_by_bool cc (ZRange.normalize rcc)))
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ (-'??') @ #?ℤ' @ ??))
                (fun rvc s rnc rc c ryy yy x
                 => (llet2_opp2 rvc (#ident.Z_sub_with_get_borrow @ s @ cst rc c @ x @ cst (ZRange.opp ryy) ##(-yy)%Z))
                      when  (yy <=? 0) && (ZRange.normalize rc <=? -ZRange.normalize rnc)%zrange && is_bounded_by_bool yy (ZRange.normalize ryy))
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ (-'??') @ ?? @ #?ℤ'))
                (fun rvc s rnc rc c x ryy yy
                 => (llet2_opp2 rvc (#ident.Z_sub_with_get_borrow @ s @ cst rc c @ x @ cst (ZRange.opp ryy) ##(-yy)%Z))
                      when  (yy <=? 0) && (ZRange.normalize rc <=? -ZRange.normalize rnc)%zrange && is_bounded_by_bool yy (ZRange.normalize ryy))
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ #?ℤ' @ #?ℤ' @ ??))
                (fun rvc s rcc cc ryy yy x
                 => (llet2_opp2 rvc (#ident.Z_sub_with_get_borrow @ s @ cst (ZRange.opp rcc) ##(-cc)%Z @ x @ cst (ZRange.opp ryy) ##(-yy)%Z))
                      when  (yy <=? 0) && (cc <=? 0) && ((yy + cc) <? 0) && is_bounded_by_bool yy (ZRange.normalize ryy) && is_bounded_by_bool cc (ZRange.normalize rcc)) (* at least one must be strictly negative *)
            ; make_rewriteol
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ #?ℤ' @ ?? @ #?ℤ'))
                (fun rvc s rcc cc x ryy yy
                 => (llet2_opp2 rvc (#ident.Z_sub_with_get_borrow @ s @ cst (ZRange.opp rcc) ##(-cc)%Z @ x @ cst (ZRange.opp ryy) ##(-yy)%Z))
                      when  (yy <=? 0) && (cc <=? 0) && ((yy + cc) <? 0) && is_bounded_by_bool yy (ZRange.normalize ryy) && is_bounded_by_bool cc (ZRange.normalize rcc)) (* at least one must be strictly negative *)


            ; make_rewriteo
                (#pattern.ident.Z_add_get_carry @ #?ℤ' @ #?ℤ' @ #?ℤ')
                (fun rs s rxx xx ryy yy => ##(Z.add_get_carry_full s xx yy)  when  is_bounded_by_bool s (ZRange.normalize rs) && is_bounded_by_bool xx (ZRange.normalize rxx) && is_bounded_by_bool yy (ZRange.normalize ryy))
            ; make_rewriteo
                (#pattern.ident.Z_add_get_carry @ #?ℤ' @ #?ℤ' @ ??')
                (fun rs s rxx xx ry y => (cst ry y, cst r[0~>0] ##0)  when  (xx =? 0) && (ZRange.normalize ry <=? r[0~>s-1])%zrange && is_bounded_by_bool xx (ZRange.normalize rxx) && is_bounded_by_bool s (ZRange.normalize rs))
            ; make_rewriteo
                (#pattern.ident.Z_add_get_carry @ #?ℤ' @ ??' @ #?ℤ')
                (fun rs s ry y rxx xx => (cst ry y, cst r[0~>0] ##0)  when  (xx =? 0) && (ZRange.normalize ry <=? r[0~>s-1])%zrange && is_bounded_by_bool xx (ZRange.normalize rxx) && is_bounded_by_bool s (ZRange.normalize rs))

            ; make_rewriteo (#pattern.ident.Z_add_with_carry @ #?ℤ' @ ?? @ ??) (fun rcc cc x y => x + y  when  (cc =? 0) && is_bounded_by_bool cc (ZRange.normalize rcc))
            (*; make_rewrite_step (#pattern.ident.Z_add_with_carry @ ?? @ ?? @ ??) (fun x y z => $x + $y + $z)*)

            ; make_rewriteo
                (#pattern.ident.Z_add_with_get_carry @ #?ℤ' @ #?ℤ' @ #?ℤ' @ #?ℤ')
                (fun rs s rcc cc rxx xx ryy yy => ##(Z.add_with_get_carry_full s cc xx yy)  when  is_bounded_by_bool s (ZRange.normalize rs) && is_bounded_by_bool cc (ZRange.normalize rcc) && is_bounded_by_bool xx (ZRange.normalize rxx) && is_bounded_by_bool yy (ZRange.normalize ryy))
            ; make_rewriteo
                (#pattern.ident.Z_add_with_get_carry @ #?ℤ' @ #?ℤ' @ #?ℤ' @ ??')
                (fun rs s rcc cc rxx xx ry y => (cst ry y, cst r[0~>0] ##0)   when   (cc =? 0) && (xx =? 0) && (ZRange.normalize ry <=? r[0~>s-1])%zrange && is_bounded_by_bool s (ZRange.normalize rs) && is_bounded_by_bool cc (ZRange.normalize rcc) && is_bounded_by_bool xx (ZRange.normalize rxx))
            ; make_rewriteo
                (#pattern.ident.Z_add_with_get_carry @ #?ℤ' @ #?ℤ' @ ??' @ #?ℤ')
                (fun rs s rcc cc ry y rxx xx => (cst ry y, cst r[0~>0] ##0)   when   (cc =? 0) && (xx =? 0) && (ZRange.normalize ry <=? r[0~>s-1])%zrange && is_bounded_by_bool s (ZRange.normalize rs) && is_bounded_by_bool cc (ZRange.normalize rcc) && is_bounded_by_bool xx (ZRange.normalize rxx))
            (*; make_rewriteo
                (#pattern.ident.Z_add_with_get_carry @ ?? @ ?? @ #?ℤ @ #?ℤ) (fun s c xx yy => (c, ##0) when   (xx =? 0) && (yy =? 0))*)
            ; make_rewriteol (* carry = 0: ADC x y -> ADD x y *)
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ #?ℤ' @ ?? @ ??))
                (fun rvc s rcc cc x y
                 => (llet2 rvc (#ident.Z_add_get_carry @ s @ x @ y))
                      when  (cc =? 0) && is_bounded_by_bool cc (ZRange.normalize rcc))
            ; make_rewriteol (* ADC 0 0 -> (ADX 0 0, 0) *) (* except we don't do ADX, because C stringification doesn't handle it *)
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ #?ℤ' @ ??' @ #?ℤ' @ #?ℤ'))
                (fun rvc rs s rc c rxx xx ryy yy
                 => (llet vc := cst2 rvc (#ident.Z_add_with_get_carry @ cst rs ##s @ cst rc c @ cst rxx ##xx @ cst ryy ##yy) in
                         (cst (fst rvc) (#ident.fst @ cst2 rvc ($vc)), cst r[0~>0] ##0))
                      when  (xx =? 0) && (yy =? 0) && (ZRange.normalize rc <=? r[0~>s-1])%zrange && is_bounded_by_bool 0 (snd rvc) && is_bounded_by_bool s (ZRange.normalize rs) && is_bounded_by_bool xx (ZRange.normalize rxx) && is_bounded_by_bool yy (ZRange.normalize ryy))


            (* let-bind any adc/sbb/mulx *)
            ; make_rewritel
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_with_get_carry @ ?? @ ?? @ ?? @ ??))
                (fun rvc s c x y => llet2 rvc (#ident.Z_add_with_get_carry @ s @ c @ x @ y))
            ; make_rewritel
                (#pattern.ident.Z_cast @ (#pattern.ident.Z_add_with_carry @ ?? @ ?? @ ??))
                (fun rv c x y => (llet vc := cst rv (#ident.Z_add_with_carry @ c @ x @ y) in
                                      (cst rv ($vc))))
            ; make_rewritel
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_add_get_carry @ ?? @ ?? @ ??))
                (fun rvc s x y => llet2 rvc (#ident.Z_add_get_carry @ s @ x @ y))
            ; make_rewritel
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_sub_with_get_borrow @ ?? @ ?? @ ?? @ ??))
                (fun rvc s c x y => llet2 rvc (#ident.Z_sub_with_get_borrow @ s @ c @ x @ y))
            ; make_rewritel
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_sub_get_borrow @ ?? @ ?? @ ??))
                (fun rvc s x y => llet2 rvc (#ident.Z_sub_get_borrow @ s @ x @ y))
            ; make_rewritel
                (#pattern.ident.Z_cast2 @ (#pattern.ident.Z_mul_split @ ?? @ ?? @ ??))
                (fun rvc s x y => llet2 rvc (#ident.Z_mul_split @ s @ x @ y))

            ; make_rewrite_step (#pattern.ident.Z_cast2 @ (??, ??)) (fun r v1 v2 => (#(ident.Z_cast (fst r)) @ $v1, #(ident.Z_cast (snd r)) @ $v2))

            ; make_rewriteo
                (#pattern.ident.Z_cast @ (#pattern.ident.Z_cast @ ??))
                (fun r1 r2 x => #(ident.Z_cast r2) @ x  when  ZRange.is_tighter_than_bool (ZRange.normalize r2) (ZRange.normalize r1))
           ].

      Definition strip_literal_casts_rewrite_rules : rewrite_rulesT
        := [make_rewriteo (#?ℤ') (fun rx x => ##x  when  is_bounded_by_bool x (ZRange.normalize rx))].


      Definition nbe_dtree'
        := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 nbe_rewrite_rules.
      Definition arith_dtree'
        := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 (arith_rewrite_rules 0%Z (* dummy val *)).
      Definition arith_with_casts_dtree'
        := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 arith_with_casts_rewrite_rules.
      Definition strip_literal_casts_dtree'
        := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 strip_literal_casts_rewrite_rules.
      Definition nbe_dtree : decision_tree
        := Eval compute in invert_Some nbe_dtree'.
      Definition arith_dtree : decision_tree
        := Eval compute in invert_Some arith_dtree'.
      Definition arith_with_casts_dtree : decision_tree
        := Eval compute in invert_Some arith_with_casts_dtree'.
      Definition strip_literal_casts_dtree : decision_tree
        := Eval compute in invert_Some strip_literal_casts_dtree'.

      Definition nbe_default_fuel := Eval compute in List.length nbe_rewrite_rules.
      Definition arith_default_fuel := Eval compute in List.length (arith_rewrite_rules 0%Z (* dummy val *)).
      Definition arith_with_casts_default_fuel := Eval compute in List.length arith_with_casts_rewrite_rules.
      Definition strip_literal_casts_default_fuel := Eval compute in List.length strip_literal_casts_rewrite_rules.

      Import PrimitiveHList.
      (* N.B. The [combine_hlist] call MUST eta-expand
         [pr2_rewrite_rules].  That is, it MUST NOT block reduction of
         the resulting list of cons cells on the pair-structure of
         [pr2_rewrite_rules].  This is required so that we can use
         [cbv -] to unfold the entire discrimination tree evaluation,
         including choosing which rewrite rule to apply and binding
         its arguments, without unfolding any of the identifiers used
         to define the replacement value.  (The symptom of messing
         this up is that the [cbv -] will run out of memory when
         trying to reduce things.)  We accomplish this by making
         [hlist] based on a primitive [prod] type with judgmental η,
         so that matching on its structure never blocks reduction. *)
      Definition nbe_split_rewrite_rules := Eval cbv [split_list projT1 projT2 nbe_rewrite_rules] in split_list nbe_rewrite_rules.
      Definition nbe_pr1_rewrite_rules := Eval hnf in projT1 nbe_split_rewrite_rules.
      Definition nbe_pr2_rewrite_rules := Eval hnf in projT2 nbe_split_rewrite_rules.
      Definition nbe_all_rewrite_rules := combine_hlist (P:=rewrite_ruleTP) nbe_pr1_rewrite_rules nbe_pr2_rewrite_rules.

      Definition arith_split_rewrite_rules max_const_val := Eval cbv [split_list projT1 projT2 arith_rewrite_rules] in split_list (arith_rewrite_rules max_const_val).
      Definition arith_pr1_rewrite_rules max_const_val := Eval hnf in projT1 (arith_split_rewrite_rules max_const_val).
      Definition arith_pr2_rewrite_rules max_const_val := Eval hnf in projT2 (arith_split_rewrite_rules max_const_val).
      Definition arith_all_rewrite_rules max_const_val := combine_hlist (P:=rewrite_ruleTP) (arith_pr1_rewrite_rules max_const_val) (arith_pr2_rewrite_rules max_const_val).
      Definition arith_with_casts_split_rewrite_rules := Eval cbv [split_list projT1 projT2 arith_with_casts_rewrite_rules] in split_list arith_with_casts_rewrite_rules.
      Definition arith_with_casts_pr1_rewrite_rules := Eval hnf in projT1 arith_with_casts_split_rewrite_rules.
      Definition arith_with_casts_pr2_rewrite_rules := Eval hnf in projT2 arith_with_casts_split_rewrite_rules.
      Definition arith_with_casts_all_rewrite_rules := combine_hlist (P:=rewrite_ruleTP) (arith_with_casts_pr1_rewrite_rules) arith_with_casts_pr2_rewrite_rules.
      Definition strip_literal_casts_split_rewrite_rules := Eval cbv [split_list projT1 projT2 strip_literal_casts_rewrite_rules] in split_list strip_literal_casts_rewrite_rules.
      Definition strip_literal_casts_pr1_rewrite_rules := Eval hnf in projT1 strip_literal_casts_split_rewrite_rules.
      Definition strip_literal_casts_pr2_rewrite_rules := Eval hnf in projT2 strip_literal_casts_split_rewrite_rules.
      Definition strip_literal_casts_all_rewrite_rules := combine_hlist (P:=rewrite_ruleTP) (strip_literal_casts_pr1_rewrite_rules) strip_literal_casts_pr2_rewrite_rules.
      Definition nbe_rewrite_head0 do_again {t} (idc : ident t) : value_with_lets t
        := @assemble_identifier_rewriters nbe_dtree nbe_all_rewrite_rules do_again t idc.
      Definition arith_rewrite_head0 max_const_val do_again {t} (idc : ident t) : value_with_lets t
        := @assemble_identifier_rewriters arith_dtree (arith_all_rewrite_rules max_const_val) do_again t idc.
      Definition arith_with_casts_rewrite_head0 do_again {t} (idc : ident t) : value_with_lets t
        := @assemble_identifier_rewriters arith_with_casts_dtree arith_with_casts_all_rewrite_rules do_again t idc.
      Definition strip_literal_casts_rewrite_head0 do_again {t} (idc : ident t) : value_with_lets t
        := @assemble_identifier_rewriters strip_literal_casts_dtree strip_literal_casts_all_rewrite_rules do_again t idc.

      Section fancy.
        Context (invert_low invert_high : Z (*log2wordmax*) -> Z -> option Z)
                (value_range flag_range : zrange).
        Definition fancy_rewrite_rules : rewrite_rulesT
          := [].

        Local Notation pcst v := (#pattern.ident.Z_cast @ v)%pattern.
        Local Notation pcst2 v := (#pattern.ident.Z_cast2 @ v)%pattern.

        Local Coercion ZRange.constant : Z >-> zrange. (* for ease of use with sanity-checking bounds *)
        Let bounds1_good (f : zrange -> zrange) (output x_bs : zrange)
          := is_tighter_than_bool (f (ZRange.normalize x_bs)) (ZRange.normalize output).
        Let bounds2_good (f : zrange -> zrange -> zrange) (output x_bs y_bs : zrange)
          := is_tighter_than_bool (f (ZRange.normalize x_bs) (ZRange.normalize y_bs)) (ZRange.normalize output).
        Let range_in_bitwidth r s
          := is_tighter_than_bool (ZRange.normalize r) r[0~>s-1]%zrange.
        Local Notation shiftl_good := (bounds2_good ZRange.shiftl).
        Local Notation shiftr_good := (bounds2_good ZRange.shiftr).
        Local Notation land_good := (bounds2_good ZRange.land).
        Local Notation mul_good := (bounds2_good ZRange.mul).
        Local Notation cc_m_good output s := (bounds1_good (ZRange.cc_m s) output).
        Local Notation lit_good x rx := (is_bounded_by_bool x (ZRange.normalize rx)).

        Definition fancy_with_casts_rewrite_rules : rewrite_rulesT
          := [
              (*
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y << 128) --> (add 128) @@ (x, y)
(Z.add_get_carry_concrete 2^256) @@ (?x << 128, ?y) --> (add 128) @@ (y, x)
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y >> 128) --> (add (- 128)) @@ (x, y)
(Z.add_get_carry_concrete 2^256) @@ (?x >> 128, ?y) --> (add (- 128)) @@ (y, x)
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y)        --> (add 0) @@ (y, x)
*)
              make_rewriteo
                (pcst2 (#pattern.ident.Z_add_get_carry @ #?ℤ' @ ??' @ (pcst (#pattern.ident.Z_shiftl @ (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ')) @ #?ℤ'))))
                (fun '((r1, r2)%core) rs s rx x rshiftl rland ry y rmask mask roffset offset => cst2 (r1, r2)%core (#(ident.fancy_add (Z.log2 s) offset) @ (cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftl_good rshiftl rland offset && land_good rland ry mask && range_in_bitwidth rshiftl s && (mask =? Z.ones (Z.log2 s - offset)) && (0 <=? offset) && (offset <=? Z.log2 s) && lit_good s rs && lit_good mask rmask && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_add_get_carry @ #?ℤ' @ (pcst (#pattern.ident.Z_shiftl @ (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ')) @ #?ℤ')) @ ??'))
                  (fun '((r1, r2)%core) rs s rshiftl rland ry y rmask mask roffset offset rx x => cst2 (r1, r2)%core (#(ident.fancy_add (Z.log2 s) offset) @ (cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftl_good rshiftl rland offset && land_good rland ry mask && range_in_bitwidth rshiftl s && (mask =? Z.ones (Z.log2 s - offset)) && (0 <=? offset) && (offset <=? Z.log2 s) && lit_good s rs && lit_good mask rmask && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_add_get_carry @ #?ℤ' @ ??' @ (pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ'))))
                  (fun '((r1, r2)%core) rs s rx x rshiftr ry y roffset offset => cst2 (r1, r2)%core (#(ident.fancy_add (Z.log2 s) (-offset)) @ (cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftr_good rshiftr ry offset && range_in_bitwidth rshiftr s && lit_good s rs && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_add_get_carry @ #?ℤ' @ pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ') @ ??'))
                  (fun '((r1, r2)%core) rs s rshiftr ry y roffset offset rx x => cst2 (r1, r2)%core (#(ident.fancy_add (Z.log2 s) (-offset)) @ (cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftr_good rshiftr ry offset && range_in_bitwidth rshiftr s && lit_good s rs && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_add_get_carry @ #?ℤ' @ ??' @ ??'))
                  (fun '((r1, r2)%core) rs s rx x ry y => cst2 (r1, r2)%core (#(ident.fancy_add (Z.log2 s) 0) @ (cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && range_in_bitwidth ry s && lit_good s rs)
(*
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y << 128) --> (addc 128) @@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x << 128, ?y) --> (addc 128) @@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y >> 128) --> (addc (- 128)) @@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x >> 128, ?y) --> (addc (- 128)) @@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y)        --> (addc 0) @@ (c, y, x)
 *)
              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_add_with_get_carry @ #?ℤ' @ ??' @ ??' @ pcst (#pattern.ident.Z_shiftl @ (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ')) @ #?ℤ')))
                  (fun '((r1, r2)%core) rs s rc c rx x rshiftl rland ry y rmask mask roffset offset => cst2 (r1, r2)%core (#(ident.fancy_addc (Z.log2 s) offset) @ (cst rc c, cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftl_good rshiftl rland offset && land_good rland ry mask && range_in_bitwidth rshiftl s && (mask =? Z.ones (Z.log2 s - offset)) && (0 <=? offset) && (offset <=? Z.log2 s) && lit_good s rs && lit_good mask rmask && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_add_with_get_carry @ #?ℤ' @ ??' @ pcst (#pattern.ident.Z_shiftl @ (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ')) @ #?ℤ') @ ??'))
                  (fun '((r1, r2)%core) rs s rc c rshiftl rland ry y rmask mask roffset offset rx x => cst2 (r1, r2)%core (#(ident.fancy_addc (Z.log2 s) offset) @ (cst rc c, cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftl_good rshiftl rland offset && range_in_bitwidth rshiftl s && land_good rland ry mask && (mask =? Z.ones (Z.log2 s - offset)) && (0 <=? offset) && (offset <=? Z.log2 s) && lit_good s rs && lit_good mask rmask && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_add_with_get_carry @ #?ℤ' @ ??' @ ??' @ pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ')))
                  (fun '((r1, r2)%core) rs s rc c rx x rshiftr ry y roffset offset => cst2 (r1, r2)%core (#(ident.fancy_addc (Z.log2 s) (-offset)) @ (cst rc c, cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftr_good rshiftr ry offset && range_in_bitwidth rshiftr s && lit_good s rs && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_add_with_get_carry @ #?ℤ' @ ??' @ pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ') @ ??'))
                  (fun '((r1, r2)%core) rs s rc c rshiftr ry y roffset offset rx x => cst2 (r1, r2)%core (#(ident.fancy_addc (Z.log2 s) (-offset)) @ (cst rc c, cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftr_good rshiftr ry offset && range_in_bitwidth rshiftr s && lit_good s rs && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_add_with_get_carry @ #?ℤ' @ ??' @ ??' @ ??'))
                  (fun '((r1, r2)%core) rs s rc c rx x ry y => cst2 (r1, r2)%core (#(ident.fancy_addc (Z.log2 s) 0) @ (cst rc c, cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && range_in_bitwidth ry s && lit_good s rs)

(*
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y << 128) --> (sub 128) @@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y >> 128) --> (sub (- 128)) @@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y)        --> (sub 0) @@ (y, x)
 *)
              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_sub_get_borrow @ #?ℤ' @ ??' @ pcst (#pattern.ident.Z_shiftl @ (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ')) @ #?ℤ')))
                  (fun '((r1, r2)%core) rs s rx x rshiftl rland ry y rmask mask roffset offset => cst2 (r1, r2)%core (#(ident.fancy_sub (Z.log2 s) offset) @ (cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftl_good rshiftl rland offset && range_in_bitwidth rshiftl s && land_good rland ry mask && (mask =? Z.ones (Z.log2 s - offset)) && (0 <=? offset) && (offset <=? Z.log2 s) && lit_good s rs && lit_good mask rmask && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_sub_get_borrow @ #?ℤ' @ ??' @ pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ')))
                  (fun '((r1, r2)%core) rs s rx x rshiftr ry y roffset offset => cst2 (r1, r2)%core (#(ident.fancy_sub (Z.log2 s) (-offset)) @ (cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftr_good rshiftr ry offset && range_in_bitwidth rshiftr s && lit_good s rs && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_sub_get_borrow @ #?ℤ' @ ??' @ ??'))
                  (fun '((r1, r2)%core) rs s rx x ry y => cst2 (r1, r2)%core (#(ident.fancy_sub (Z.log2 s) 0) @ (cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && range_in_bitwidth ry s && lit_good s rs)
(*
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y << 128) --> (subb 128) @@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y >> 128) --> (subb (- 128)) @@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y)        --> (subb 0) @@ (c, y, x)
 *)
              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_sub_with_get_borrow @ #?ℤ' @ ??' @ ??' @ pcst (#pattern.ident.Z_shiftl @ (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ')) @ #?ℤ')))
                  (fun '((r1, r2)%core) rs s rb b rx x rshiftl rland ry y rmask mask roffset offset => cst2 (r1, r2)%core (#(ident.fancy_subb (Z.log2 s) offset) @ (cst rb b, cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftl_good rshiftl rland offset && range_in_bitwidth rshiftl s && land_good rland ry mask && (mask =? Z.ones (Z.log2 s - offset)) && (0 <=? offset) && (offset <=? Z.log2 s) && lit_good s rs && lit_good mask rmask && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_sub_with_get_borrow @ #?ℤ' @ ??' @ ??' @ pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ')))
                  (fun '((r1, r2)%core) rs s rb b rx x rshiftr ry y roffset offset => cst2 (r1, r2)%core (#(ident.fancy_subb (Z.log2 s) (-offset)) @ (cst rb b, cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && shiftr_good rshiftr ry offset && range_in_bitwidth rshiftr s && lit_good s rs && lit_good offset roffset)

              ; make_rewriteo
                  (pcst2 (#pattern.ident.Z_sub_with_get_borrow @ #?ℤ' @ ??' @ ??' @ ??'))
                  (fun '((r1, r2)%core) rs s rb b rx x ry y => cst2 (r1, r2)%core (#(ident.fancy_subb (Z.log2 s) 0) @ (cst rb b, cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && range_in_bitwidth ry s && lit_good s rs)

              (*(Z.rshi_concrete 2^256 ?n) @@ (?c, ?x, ?y) --> (rshi n) @@ (x, y)*)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_rshi @ #?ℤ' @ ??' @ ??' @ #?ℤ'))
                  (fun r rs s rx x ry y rn n => cst r (#(ident.fancy_rshi (Z.log2 s) n) @ (cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && lit_good s rs && lit_good n rn)
(*
Z.zselect @@ (Z.cc_m_concrete 2^256 ?c, ?x, ?y) --> selm @@ (c, x, y)
Z.zselect @@ (?c &' 1, ?x, ?y)                  --> sell @@ (c, x, y)
Z.zselect @@ (?c, ?x, ?y)                       --> selc @@ (c, x, y)
 *)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_zselect @ pcst (#pattern.ident.Z_cc_m @ #?ℤ' @ ??') @ ??' @ ??'))
                  (fun r rccm rs s rc c rx x ry y => cst r (#(ident.fancy_selm (Z.log2 s)) @ (cst rc c, cst rx x, cst ry y))  when  (s =? 2^Z.log2 s) && cc_m_good rccm s rc && lit_good s rs)

              ; make_rewriteo
                  (pcst (#pattern.ident.Z_zselect @ pcst (#pattern.ident.Z_land @ #?ℤ' @ ??') @ ??' @ ??'))
                  (fun r rland rmask mask rc c rx x ry y => cst r (#ident.fancy_sell @ (cst rc c, cst rx x, cst ry y))  when  (mask =? 1) && land_good rland mask rc && lit_good mask rmask)

              ; make_rewriteo
                  (pcst (#pattern.ident.Z_zselect @ pcst (#pattern.ident.Z_land @ ??' @ #?ℤ') @ ??' @ ??'))
                  (fun r rland rc c rmask mask rx x ry y => cst r (#ident.fancy_sell @ (cst rc c, cst rx x, cst ry y))  when  (mask =? 1) && land_good rland rc mask && lit_good mask rmask)

              ; make_rewrite
                  (pcst (#pattern.ident.Z_zselect @ ?? @ ?? @ ??))
                  (fun r c x y => cst r (#ident.fancy_selc @ (c, x, y)))

(*Z.add_modulo @@ (?x, ?y, ?m) --> addm @@ (x, y, m)*)
              ; make_rewrite
                  (#pattern.ident.Z_add_modulo @ ?? @ ?? @ ??)
                  (fun x y m => #ident.fancy_addm @ (x, y, m))
(*
Z.mul @@ (?x &' (2^128-1), ?y &' (2^128-1)) --> mulll @@ (x, y)
Z.mul @@ (?x &' (2^128-1), ?y >> 128)       --> mullh @@ (x, y)
Z.mul @@ (?x >> 128, ?y &' (2^128-1))       --> mulhl @@ (x, y)
Z.mul @@ (?x >> 128, ?y >> 128)             --> mulhh @@ (x, y)
 *)
              (* literal on left *)
              ; make_rewriteo
                  (#?ℤ' *' pcst (#pattern.ident.Z_land @ ??' @ #?ℤ'))
                  (fun r rx x rland ry y rmask mask => let s := (2*Z.log2_up mask)%Z in x <- invert_low s x; cst r (#(ident.fancy_mulll s) @ (##x, cst ry y))  when  (mask =? 2^(s/2)-1) && land_good rland ry mask && lit_good x rx && lit_good mask rmask)
              ; make_rewriteo
                  (#?ℤ' *' pcst (#pattern.ident.Z_land @ #?ℤ' @ ??'))
                  (fun r rx x rland rmask mask ry y => let s := (2*Z.log2_up mask)%Z in x <- invert_low s x; cst r (#(ident.fancy_mulll s) @ (##x, cst ry y))  when  (mask =? 2^(s/2)-1) && land_good rland mask ry && lit_good x rx && lit_good mask rmask)
              ; make_rewriteo
                  (#?ℤ' *' pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ'))
                  (fun r rx x rshiftr ry y roffset offset => let s := (2*offset)%Z in x <- invert_low s x; cst r (#(ident.fancy_mullh s) @ (##x, cst ry y))  when  shiftr_good rshiftr ry offset && lit_good x rx && lit_good offset roffset)
              ; make_rewriteo
                  (#?ℤ' *' pcst (#pattern.ident.Z_land @ #?ℤ' @ ??'))
                  (fun r rx x rland rmask mask ry y => let s := (2*Z.log2_up mask)%Z in x <- invert_high s x; cst r (#(ident.fancy_mulhl s) @ (##x, cst ry y))  when  (mask =? 2^(s/2)-1) && land_good rland mask ry && lit_good x rx && lit_good mask rmask)
              ; make_rewriteo
                  (#?ℤ' *' pcst (#pattern.ident.Z_land @ ??' @ #?ℤ'))
                  (fun r rx x rland ry y rmask mask => let s := (2*Z.log2_up mask)%Z in x <- invert_high s x; cst r (#(ident.fancy_mulhl s) @ (##x, cst ry y))  when  (mask =? 2^(s/2)-1) && land_good rland ry mask && lit_good x rx && lit_good mask rmask)
              ; make_rewriteo
                  (#?ℤ' *' pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ'))
                  (fun r rx x rshiftr ry y roffset offset => let s := (2*offset)%Z in x <- invert_high s x; cst r (#(ident.fancy_mulhh s) @ (##x, cst ry y))  when  shiftr_good rshiftr ry offset && lit_good x rx && lit_good offset roffset)
              (* literal on right *)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ #?ℤ' @ ??') *' #?ℤ')
                  (fun r rland rmask mask rx x ry y => let s := (2*Z.log2_up mask)%Z in y <- invert_low s y; cst r (#(ident.fancy_mulll s) @ (cst rx x, ##y))  when  (mask =? 2^(s/2)-1) && land_good rland mask rx && lit_good y ry && lit_good mask rmask)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ') *' #?ℤ')
                  (fun r rland rx x rmask mask ry y => let s := (2*Z.log2_up mask)%Z in y <- invert_low s y; cst r (#(ident.fancy_mulll s) @ (cst rx x, ##y))  when  (mask =? 2^(s/2)-1) && land_good rland rx mask && lit_good y ry && lit_good mask rmask)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ #?ℤ' @ ??') *' #?ℤ')
                  (fun r rland rmask mask rx x ry y => let s := (2*Z.log2_up mask)%Z in y <- invert_high s y; cst r (#(ident.fancy_mullh s) @ (cst rx x, ##y))  when  (mask =? 2^(s/2)-1) && land_good rland mask rx && lit_good y ry && lit_good mask rmask)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ') *' #?ℤ')
                  (fun r rland rx x rmask mask ry y => let s := (2*Z.log2_up mask)%Z in y <- invert_high s y; cst r (#(ident.fancy_mullh s) @ (cst rx x, ##y))  when  (mask =? 2^(s/2)-1) && land_good rland rx mask && lit_good y ry && lit_good mask rmask)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ') *' #?ℤ')
                  (fun r rshiftr rx x roffset offset ry y => let s := (2*offset)%Z in y <- invert_low s y; cst r (#(ident.fancy_mulhl s) @ (cst rx x, ##y))  when  shiftr_good rshiftr rx offset && lit_good y ry && lit_good offset roffset)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ') *' #?ℤ')
                  (fun r rshiftr rx x roffset offset ry y => let s := (2*offset)%Z in y <- invert_high s y; cst r (#(ident.fancy_mulhh s) @ (cst rx x, ##y))  when  shiftr_good rshiftr rx offset && lit_good y ry && lit_good offset roffset)
              (* no literal *)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ #?ℤ' @ ??') *' pcst (#pattern.ident.Z_land @ #?ℤ' @ ??'))
                  (fun r rland1 rmask1 mask1 rx x rland2 rmask2 mask2 ry y => let s := (2*Z.log2_up mask1)%Z in cst r (#(ident.fancy_mulll s) @ (cst rx x, cst ry y))  when  (mask1 =? 2^(s/2)-1) && (mask2 =? 2^(s/2)-1) && land_good rland1 mask1 rx && land_good rland2 mask2 ry && lit_good mask1 rmask1 && lit_good mask2 rmask2)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ') *' pcst (#pattern.ident.Z_land @ #?ℤ' @ ??'))
                  (fun r rland1 rx x rmask1 mask1 rland2 rmask2 mask2 ry y => let s := (2*Z.log2_up mask1)%Z in cst r (#(ident.fancy_mulll s) @ (cst rx x, cst ry y))  when  (mask1 =? 2^(s/2)-1) && (mask2 =? 2^(s/2)-1) && land_good rland1 rx mask1 && land_good rland2 mask2 ry && lit_good mask1 rmask1 && lit_good mask2 rmask2)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ #?ℤ' @ ??') *' pcst (#pattern.ident.Z_land @ ??' @ #?ℤ'))
                  (fun r rland1 rmask1 mask1 rx x rland2 ry y rmask2 mask2 => let s := (2*Z.log2_up mask1)%Z in cst r (#(ident.fancy_mulll s) @ (cst rx x, cst ry y))  when  (mask1 =? 2^(s/2)-1) && (mask2 =? 2^(s/2)-1) && land_good rland1 mask1 rx && land_good rland2 ry mask2 && lit_good mask1 rmask1 && lit_good mask2 rmask2)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ') *' pcst (#pattern.ident.Z_land @ ??' @ #?ℤ'))
                  (fun r rland1 rx x rmask1 mask1 rland2 ry y rmask2 mask2 => let s := (2*Z.log2_up mask1)%Z in cst r (#(ident.fancy_mulll s) @ (cst rx x, cst ry y))  when  (mask1 =? 2^(s/2)-1) && (mask2 =? 2^(s/2)-1) && land_good rland1 rx mask1 && land_good rland2 ry mask2 && lit_good mask1 rmask1 && lit_good mask2 rmask2)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ #?ℤ' @ ??') *' pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ'))
                  (fun r rland1 rmask mask rx x rshiftr2 ry y roffset offset => let s := (2*offset)%Z in cst r (#(ident.fancy_mullh s) @ (cst rx x, cst ry y))  when  (mask =? 2^(s/2)-1) && land_good rland1 mask rx && shiftr_good rshiftr2 ry offset && lit_good mask rmask && lit_good offset roffset)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_land @ ??' @ #?ℤ') *' pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ'))
                  (fun r rland1 rx x rmask mask rshiftr2 ry y roffset offset => let s := (2*offset)%Z in cst r (#(ident.fancy_mullh s) @ (cst rx x, cst ry y))  when  (mask =? 2^(s/2)-1) && land_good rland1 rx mask && shiftr_good rshiftr2 ry offset && lit_good mask rmask && lit_good offset roffset)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ') *' pcst (#pattern.ident.Z_land @ #?ℤ' @ ??'))
                  (fun r rshiftr1 rx x roffset offset rland2 rmask mask ry y => let s := (2*offset)%Z in cst r (#(ident.fancy_mulhl s) @ (cst rx x, cst ry y))  when  (mask =? 2^(s/2)-1) && shiftr_good rshiftr1 rx offset && land_good rland2 mask ry && lit_good mask rmask && lit_good offset roffset)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ') *' pcst (#pattern.ident.Z_land @ ??' @ #?ℤ'))
                  (fun r rshiftr1 rx x roffset offset rland2 ry y rmask mask => let s := (2*offset)%Z in cst r (#(ident.fancy_mulhl s) @ (cst rx x, cst ry y))  when  (mask =? 2^(s/2)-1) && shiftr_good rshiftr1 rx offset && land_good rland2 ry mask && lit_good mask rmask && lit_good offset roffset)
              ; make_rewriteo
                  (pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ') *' pcst (#pattern.ident.Z_shiftr @ ??' @ #?ℤ'))
                  (fun r rshiftr1 rx x roffset1 offset1 rshiftr2 ry y roffset2 offset2 => let s := (2*offset1)%Z in cst r (#(ident.fancy_mulhh s) @ (cst rx x, cst ry y))  when  (offset1 =? offset2) && shiftr_good rshiftr1 rx offset1 && shiftr_good rshiftr2 ry offset2 && lit_good offset1 roffset1 && lit_good offset2 roffset2)



                  (** Dummy rule to make sure we use the two value ranges; this can be removed *)
              ; make_rewriteo
                  (??')
                  (fun rx x => cst rx x  when  is_tighter_than_bool rx value_range || is_tighter_than_bool rx flag_range)

            ].

        Definition fancy_dtree'
          := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 fancy_rewrite_rules.
        Definition fancy_dtree : decision_tree
          := Eval compute in invert_Some fancy_dtree'.
        Definition fancy_with_casts_dtree'
          := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 fancy_with_casts_rewrite_rules.
        Definition fancy_with_casts_dtree : decision_tree
          := Eval compute in invert_Some fancy_with_casts_dtree'.
        Definition fancy_default_fuel := Eval compute in List.length fancy_rewrite_rules.
        Definition fancy_with_casts_default_fuel := Eval compute in List.length fancy_with_casts_rewrite_rules.
        Import PrimitiveHList.
        Definition fancy_split_rewrite_rules := Eval cbv [split_list projT1 projT2 fancy_rewrite_rules] in split_list fancy_rewrite_rules.
        Definition fancy_pr1_rewrite_rules := Eval hnf in projT1 fancy_split_rewrite_rules.
        Definition fancy_pr2_rewrite_rules := Eval hnf in projT2 fancy_split_rewrite_rules.
        Definition fancy_all_rewrite_rules := combine_hlist (P:=rewrite_ruleTP) fancy_pr1_rewrite_rules fancy_pr2_rewrite_rules.
        Definition fancy_with_casts_split_rewrite_rules := Eval cbv [split_list projT1 projT2 fancy_with_casts_rewrite_rules] in split_list fancy_with_casts_rewrite_rules.
        Definition fancy_with_casts_pr1_rewrite_rules := Eval hnf in projT1 fancy_with_casts_split_rewrite_rules.
        Definition fancy_with_casts_pr2_rewrite_rules := Eval hnf in projT2 fancy_with_casts_split_rewrite_rules.
        Definition fancy_with_casts_all_rewrite_rules := combine_hlist (P:=rewrite_ruleTP) fancy_with_casts_pr1_rewrite_rules fancy_with_casts_pr2_rewrite_rules.
        Definition fancy_rewrite_head0 do_again {t} (idc : ident t) : value_with_lets t
          := @assemble_identifier_rewriters fancy_dtree fancy_all_rewrite_rules do_again t idc.
        Definition fancy_with_casts_rewrite_head0 do_again {t} (idc : ident t) : value_with_lets t
          := @assemble_identifier_rewriters fancy_with_casts_dtree fancy_with_casts_all_rewrite_rules do_again t idc.
      End fancy.
    End with_var.
    Module RewriterPrintingNotations.
      Arguments base.try_make_base_transport_cps _ !_ !_.
      Arguments base.try_make_transport_cps _ !_ !_.
      Arguments type.try_make_transport_cps _ _ _ !_ !_.
      Arguments Option.sequence {A} !v1 v2.
      Arguments Option.sequence_return {A} !v1 v2.
      Arguments Option.bind {A B} !_ _.
      Arguments pattern.Raw.ident.invert_bind_args {t} !_ !_.
      Arguments base.try_make_transport_cps {P} t1 t2 {_} _.
      Arguments type.try_make_transport_cps {base_type _ P} t1 t2 {_} _.
      Export pattern.Raw.ident.
      Export GENERATEDIdentifiersWithoutTypes.Compilers.pattern.Raw.
      Export GENERATEDIdentifiersWithoutTypes.Compilers.pattern.
      Export UnderLets.
      Export Compilers.ident.
      Export Language.Compilers.
      Export Language.Compilers.defaults.
      Export PrimitiveSigma.Primitive.
      Notation "'llet' x := v 'in' f" := (Let_In v (fun x => f)).
      Notation "x <- 'type.try_make_transport_cps' t1 t2 ; f" := (type.try_make_transport_cps t1 t2 (fun y => match y with Some x => f | None => None end)) (at level 70, t1 at next level, t2 at next level, right associativity, format "'[v' x  <-  'type.try_make_transport_cps'  t1  t2 ; '/' f ']'").
      Notation "x <- 'base.try_make_transport_cps' t1 t2 ; f" := (base.try_make_transport_cps t1 t2 (fun y => match y with Some x => f | None => None end)) (at level 70, t1 at next level, t2 at next level, right associativity, format "'[v' x  <-  'base.try_make_transport_cps'  t1  t2 ; '/' f ']'").
    End RewriterPrintingNotations.

    Ltac make_rewrite_head1 rewrite_head0 pr2_rewrite_rules :=
      let rewrite_head1
          := (eval cbv -[pr2_rewrite_rules
                           base.interp base.try_make_transport_cps
                           type.try_make_transport_cps
                           pattern.type.unify_extracted
                           Compile.option_type_type_beq
                           Let_In Option.sequence Option.sequence_return
                           UnderLets.splice UnderLets.to_expr
                           Compile.option_bind' pident_unify_unknown invert_bind_args_unknown Compile.normalize_deep_rewrite_rule
                           Compile.reflect UnderLets.reify_and_let_binds_base_cps Compile.reify Compile.reify_and_let_binds_cps
                           Compile.value'
                           SubstVarLike.is_var_fst_snd_pair_opp_cast
                        ] in rewrite_head0) in
      let rewrite_head1
          := (eval cbn [type.try_make_transport_cps base.try_make_transport_cps base.try_make_base_transport_cps]
               in rewrite_head1) in
      rewrite_head1.
    Ltac timed_make_rewrite_head1 rewrite_head0 pr2_rewrite_rules :=
      constr:(ltac:(time (idtac; let v := make_rewrite_head1 rewrite_head0 pr2_rewrite_rules in exact v))).
    Ltac make_rewrite_head2 rewrite_head1 pr2_rewrite_rules :=
      (eval cbv [id
                   pr2_rewrite_rules
                   projT1 projT2
                   cpsbind cpscall cps_option_bind cpsreturn
                   PrimitiveProd.Primitive.fst PrimitiveProd.Primitive.snd
                   pattern.type.subst_default pattern.base.subst_default
                   PositiveMap.add PositiveMap.find PositiveMap.empty
                   PositiveSet.rev PositiveSet.rev_append
                   pattern.ident.arg_types
                   Compile.eval_decision_tree
                   Compile.eval_rewrite_rules
                   Compile.expr_of_rawexpr
                   Compile.normalize_deep_rewrite_rule
                   Compile.option_bind' pident_unify_unknown invert_bind_args_unknown Compile.normalize_deep_rewrite_rule
                   (*Compile.reflect*)
                   (*Compile.reify*)
                   Compile.reveal_rawexpr_cps
                   Compile.reveal_rawexpr_cps_gen
                   Compile.rew_should_do_again
                   Compile.rew_with_opt
                   Compile.rew_under_lets
                   Compile.rew_replacement
                   Compile.rValueOrExpr
                   Compile.swap_list
                   Compile.type_of_rawexpr
                   Compile.option_type_type_beq
                   Compile.value
                   (*Compile.value'*)
                   Compile.value_of_rawexpr
                   Compile.value_with_lets
                   ident.smart_Literal
                   type.try_transport_cps
                   rlist_rect rwhen rwhenl
                ] in rewrite_head1).
    Ltac timed_make_rewrite_head2 rewrite_head1 pr2_rewrite_rules :=
      constr:(ltac:(time (idtac; let v := make_rewrite_head2 rewrite_head1 pr2_rewrite_rules in exact v))).
    Ltac make_rewrite_head3 rewrite_head2 :=
      (eval cbn [id
                   cpsbind cpscall cps_option_bind cpsreturn
                   Compile.reify Compile.reify_and_let_binds_cps Compile.reflect Compile.value'
                   Option.sequence Option.sequence_return Option.bind
                   UnderLets.reify_and_let_binds_base_cps
                   UnderLets.splice UnderLets.splice_list UnderLets.to_expr
                   base.interp base.base_interp
                   base.type.base_beq option_beq
                   type.try_make_transport_cps base.try_make_transport_cps base.try_make_base_transport_cps
                   Datatypes.fst Datatypes.snd
                ] in rewrite_head2).
    Ltac timed_make_rewrite_head3 rewrite_head2 :=
      constr:(ltac:(time (idtac; let v := make_rewrite_head3 rewrite_head2 in exact v))).
    Ltac make_rewrite_head rewrite_head0 pr2_rewrite_rules :=
      let rewrite_head1 := make_rewrite_head1 rewrite_head0 pr2_rewrite_rules in
      let rewrite_head2 := make_rewrite_head2 rewrite_head1 pr2_rewrite_rules in
      let rewrite_head3 := make_rewrite_head3 rewrite_head2 in
      rewrite_head3.
    Ltac timed_make_rewrite_head rewrite_head0 pr2_rewrite_rules :=
      let rewrite_head1 := timed_make_rewrite_head1 rewrite_head0 pr2_rewrite_rules in
      let rewrite_head2 := timed_make_rewrite_head2 rewrite_head1 pr2_rewrite_rules in
      let rewrite_head3 := timed_make_rewrite_head3 rewrite_head2 in
      rewrite_head3.
    Notation make_rewrite_head rewrite_head0 pr2_rewrite_rules
      := (ltac:(let v := timed_make_rewrite_head rewrite_head0 pr2_rewrite_rules in
                exact v)) (only parsing).

    (* For reduction *)
    Local Arguments base.try_make_base_transport_cps _ !_ !_.
    Local Arguments base.try_make_transport_cps _ !_ !_.
    Local Arguments type.try_make_transport_cps _ _ _ !_ !_.
    Local Arguments Option.sequence {A} !v1 v2.
    Local Arguments Option.sequence_return {A} !v1 v2.
    Local Arguments Option.bind {A B} !_ _.
    Local Arguments pattern.Raw.ident.invert_bind_args {t} !_ !_.
    Local Arguments base.try_make_transport_cps {P} t1 t2 {_} _.
    Local Arguments type.try_make_transport_cps {base_type _ P} t1 t2 {_} _.
    Local Arguments base.type.base_beq !_ !_.
    Local Arguments id / .
    (* For printing *)
    Local Arguments option {_}.
    Local Arguments UnderLets.UnderLets {_ _ _}.
    Local Arguments expr.expr {_ _ _}.
    Local Notation ℤ := base.type.Z.
    Local Notation ℕ := base.type.nat.
    Local Notation bool := base.type.bool.
    Local Notation unit := base.type.unit.
    Local Notation list := base.type.list.
    Local Notation "x" := (type.base x) (only printing, at level 9).

    Section red_fancy.
      Context (invert_low invert_high : Z (*log2wordmax*) -> Z -> @option Z)
              {var : type.type base.type -> Type}
              (do_again : forall t : base.type, @expr base.type ident (@Compile.value base.type ident var) (type.base t)
                                                -> @UnderLets.UnderLets base.type ident var (@expr base.type ident var (type.base t)))
              {t} (idc : ident t).

      Time Definition fancy_rewrite_head
        := make_rewrite_head (@fancy_rewrite_head0 var do_again t idc) (@fancy_pr2_rewrite_rules).
      (* Tactic call ran for 0.19 secs (0.187u,0.s) (success)
         Tactic call ran for 10.297 secs (10.3u,0.s) (success)
         Tactic call ran for 1.746 secs (1.747u,0.s) (success)
         Finished transaction in 12.402 secs (12.4u,0.s) (successful) *)

      Local Set Printing Depth 1000000.
      Local Set Printing Width 200.
      Import RewriterPrintingNotations.
      Redirect "fancy_rewrite_head" Print fancy_rewrite_head.
    End red_fancy.
    Section red_fancy_with_casts.
      Context (invert_low invert_high : Z (*log2wordmax*) -> Z -> @option Z)
              (value_range flag_range : zrange)
              {var : type.type base.type -> Type}
              (do_again : forall t : base.type, @expr base.type ident (@Compile.value base.type ident var) (type.base t)
                                                -> @UnderLets.UnderLets base.type ident var (@expr base.type ident var (type.base t)))
              {t} (idc : ident t).
      Time Definition fancy_with_casts_rewrite_head
        := make_rewrite_head (@fancy_with_casts_rewrite_head0 var invert_low invert_high value_range flag_range do_again t idc) (@fancy_with_casts_pr2_rewrite_rules).
      (* Tactic call ran for 4.142 secs (4.143u,0.s) (success)
         Tactic call ran for 80.563 secs (80.56u,0.s) (success)
         Tactic call ran for 0.154 secs (0.156u,0.s) (success)
         Finished transaction in 85.431 secs (85.427u,0.s) (successful) *)

      Local Set Printing Depth 1000000.
      Local Set Printing Width 200.
      Import RewriterPrintingNotations.
      Redirect "fancy_with_casts_rewrite_head" Print fancy_with_casts_rewrite_head.
    End red_fancy_with_casts.
    Section red_nbe.
      Context {var : type.type base.type -> Type}
              (do_again : forall t : base.type, @expr base.type ident (@Compile.value base.type ident var) (type.base t)
                                                -> @UnderLets.UnderLets base.type ident var (@expr base.type ident var (type.base t)))
              {t} (idc : ident t).
      Time Definition nbe_rewrite_head
        := make_rewrite_head (@nbe_rewrite_head0 var do_again t idc) (@nbe_pr2_rewrite_rules).
      (* Tactic call ran for 0.232 secs (0.235u,0.s) (success)
         Tactic call ran for 29.061 secs (29.04u,0.004s) (success)
         Tactic call ran for 1.605 secs (1.604u,0.s) (success)
         Finished transaction in 31.203 secs (31.183u,0.004s) (successful) *)

      Local Set Printing Depth 1000000.
      Local Set Printing Width 200.
      Import RewriterPrintingNotations.
      Redirect "nbe_rewrite_head" Print nbe_rewrite_head.
    End red_nbe.

    Section red_arith.
      Context (max_const_val : Z)
              {var : type.type base.type -> Type}
              (do_again : forall t : base.type, @expr base.type ident (@Compile.value base.type ident var) (type.base t)
                                                -> @UnderLets.UnderLets base.type ident var (@expr base.type ident var (type.base t)))
              {t} (idc : ident t).

      Time Definition arith_rewrite_head
        := make_rewrite_head (@arith_rewrite_head0 var max_const_val do_again t idc) (@arith_pr2_rewrite_rules).
      (* Tactic call ran for 0.283 secs (0.284u,0.s) (success)
         Tactic call ran for 79.61 secs (79.612u,0.008s) (success)
         Tactic call ran for 3.574 secs (3.576u,0.s) (success)
         Finished transaction in 83.677 secs (83.68u,0.008s) (successful) *)

      Local Set Printing Depth 1000000.
      Local Set Printing Width 200.
      Import RewriterPrintingNotations.
      Redirect "arith_rewrite_head" Print arith_rewrite_head.
    End red_arith.

    Section red_arith_with_casts.
      Context {var : type.type base.type -> Type}
              (do_again : forall t : base.type, @expr base.type ident (@Compile.value base.type ident var) (type.base t)
                                                -> @UnderLets.UnderLets base.type ident var (@expr base.type ident var (type.base t)))
              {t} (idc : ident t).

      Time Definition arith_with_casts_rewrite_head
        := make_rewrite_head (@arith_with_casts_rewrite_head0 var do_again t idc) (@arith_with_casts_pr2_rewrite_rules).

      Local Set Printing Depth 1000000.
      Local Set Printing Width 200.
      Import RewriterPrintingNotations.
      Redirect "arith_with_casts_rewrite_head" Print arith_with_casts_rewrite_head.
    End red_arith_with_casts.

    Section red_strip_literal_casts.
      Context {var : type.type base.type -> Type}
              (do_again : forall t : base.type, @expr base.type ident (@Compile.value base.type ident var) (type.base t)
                                                -> @UnderLets.UnderLets base.type ident var (@expr base.type ident var (type.base t)))
              {t} (idc : ident t).

      Time Definition strip_literal_casts_rewrite_head
        := make_rewrite_head (@strip_literal_casts_rewrite_head0 var do_again t idc) (@strip_literal_casts_pr2_rewrite_rules).

      Local Set Printing Depth 1000000.
      Local Set Printing Width 200.
      Import RewriterPrintingNotations.
      Redirect "strip_literal_casts_rewrite_head" Print strip_literal_casts_rewrite_head.
    End red_strip_literal_casts.

    Definition RewriteNBE {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
      := @Compile.Rewrite (@nbe_rewrite_head) nbe_default_fuel t e.
    Definition RewriteArith (max_const_val : Z) {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
      := @Compile.Rewrite (@arith_rewrite_head max_const_val) arith_default_fuel t e.
    Definition RewriteArithWithCasts {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
      := @Compile.Rewrite (@arith_with_casts_rewrite_head) arith_with_casts_default_fuel t e.
    Definition RewriteStripLiteralCasts {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
      := @Compile.Rewrite (fun var do_again => @strip_literal_casts_rewrite_head var) strip_literal_casts_default_fuel t e.
    Definition RewriteToFancy
               (invert_low invert_high : Z (*log2wordmax*) -> Z -> @option Z)
               {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
      := @Compile.Rewrite (fun var _ => @fancy_rewrite_head var) fancy_default_fuel t e.
    Definition RewriteToFancyWithCasts
               (invert_low invert_high : Z (*log2wordmax*) -> Z -> @option Z)
               (value_range flag_range : zrange)
               {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
      := @Compile.Rewrite (fun var _ => @fancy_with_casts_rewrite_head invert_low invert_high value_range flag_range var) fancy_with_casts_default_fuel t e.
  End RewriteRules.

  Import defaults.

  Definition PartialEvaluate {t} (e : Expr t) : Expr t := RewriteRules.RewriteNBE e.
End Compilers.
