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
Require Import Crypto.Language.
Require Import Crypto.UnderLets.
Require Import Crypto.GENERATEDIdentifiersWithoutTypes.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.Head.
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
           | type.option A => type.option (partial_subst A evar_map)
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
           | type.option A => option_map Compilers.base.type.option (subst A evar_map)
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
           | Compilers.base.type.option A
             => @subst_default_relax (fun t => P (Compilers.base.type.option t)) A evm
           end.

      Fixpoint unsubst_default_relax P {t evm} : P (subst_default (relax t) evm) -> P t
        := match t return P (subst_default (relax t) evm) -> P t with
           | Compilers.base.type.type_base t => fun x => x
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

      Fixpoint var_types_of (t : type) : Set
        := match t with
           | type.var _ => Compilers.base.type
           | type.type_base _ => unit
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
           | type.option A, Compilers.base.type.option A'
             => unify_extracted A A'
           | type.type_base _, _
           | type.prod _ _, _
           | type.list _, _
           | type.option _, _
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

      Fixpoint unsubst_default_relax P {t evm} : P (type.subst_default (type.relax t) evm) -> P t
        := match t return P (type.subst_default (type.relax t) evm) -> P t with
           | type.base t => base.unsubst_default_relax (fun t => P (type.base t))
           | type.arrow A B
             => fun v
                => @unsubst_default_relax
                     (fun A' => P (type.arrow A' _)) A evm
                     (@unsubst_default_relax
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

        Context (reify_and_let_binds_base_cps : forall (t : base.type), expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T)
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

        Definition app_type_of_list {K} {ls : list Type} (f : type_of_list_cps K ls) (args : type_of_list ls) : K
          := list_rect
               (fun ls
                => type_of_list_cps K ls -> type_of_list ls -> K)
               (fun v _ => v)
               (fun T Ts rec f x
                => rec (f (fst x)) (snd x))
               ls
               f args.

        Definition lam_type_of_list {ls K} : (type_of_list ls -> K) -> type_of_list_cps K ls
          := list_rect
               (fun ls => (type_of_list ls -> K) -> type_of_list_cps K ls)
               (fun f => f tt)
               (fun T Ts rec k t => rec (fun ts => k (t, ts)))
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

        Fixpoint reify_expr {t} (e : @expr.expr base.type ident value t)
          : @expr.expr base.type ident var t
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
        Fixpoint reflect_expr_beta_iota {t} (e : @expr.expr base.type ident value t)
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

        Definition reify_expr_beta_iota {t} (e : @expr.expr base.type ident value t)
          : UnderLets (@expr.expr base.type ident var t)
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

        Local Notation expr_maybe_do_again should_do_again
          := (@expr.expr base.type ident (if should_do_again then value else var)).

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
        Let type_base := @type.base base.type.
        Local Coercion type_base : base.type >-> type.type.

        (** This definition takes in an identifier. If the identifier
            is not meant to be evaluated eagerly, [None] is
            returned. Otherwise, a value-thunk is returned. This
            value-thunk takes in all of the arguments to which the
            identifer will eventually be applied.  If there is enough
            structure for eager evaluation, then the identifier is
            "evaluated" in Gallina (e.g., [eager_list_rect] turns into
            [list_rect] over a concrete list of cons cells holding
            PHOAS expressions), and the result of this evaluation is
            returned."  *)
        (* N.B. the [with_lets] argument to [reflect] doesn't matter
          here because [value' true (_ → _) ≡ value' false (_ → _)] *)
        Definition reflect_ident_iota {t} (idc : ident t) : option (value t)
          := Eval cbv [GallinaReify.Reify_as GallinaReify.reify GallinaReify.base.reify ident.smart_Literal] in
              match idc in ident.ident t return option (value t) with
              | ident.eager_nat_rect P
                => Some
                     (fun (N_case : value base.type.unit -> _) (S_case : value base.type.nat -> value P -> _) (n : expr base.type.nat) (* type annotations present for nicer fixpoint refolding *)
                      => match invert_Literal n with
                         | Some n => nat_rect
                                       (fun _ => UnderLets (expr P))
                                       (N_case (GallinaReify.Reify tt _))
                                       (fun n' rec
                                        => rec <-- rec;
                                             S_case (GallinaReify.Reify n' _) rec)
                                       n
                         | None => reflect (with_lets:=false) (expr.Ident (@ident.nat_rect P)) N_case S_case n
                         end)
              | ident.eager_nat_rect_arrow P Q
                => Some
                     (fun (N_case : value P -> _) (S_case : value base.type.nat -> (value P -> _) -> _ -> _) (n : expr base.type.nat) (v : expr P) (* type annotations present for nicer fixpoint refolding *)
                      => match invert_Literal n with
                         | Some n => nat_rect
                                       (fun _ => expr P -> UnderLets (expr Q))
                                       N_case
                                       (fun n' rec v'
                                        => S_case (GallinaReify.Reify n' _) rec v')
                                       n
                                       v
                         | None => reflect (with_lets:=false) (expr.Ident (@ident.nat_rect_arrow P Q)) N_case S_case n v
                         end)
              | ident.eager_list_rect A P
                => Some
                     (fun (N_case : value base.type.unit -> _) (C_case : value A -> _ -> value P -> _) (ls : expr (base.type.list A)) (* type annotations present for nicer fixpoint refolding *)
                      => match reflect_list ls with
                         | Some ls => list_rect
                                        (fun _ => UnderLets (expr P))
                                        (N_case (GallinaReify.Reify tt _))
                                        (fun x xs rec
                                         => rec <-- rec;
                                              C_case x (reify_list xs) rec)
                                        ls
                         | None => reflect (with_lets:=false) (expr.Ident (@ident.list_rect A P)) N_case C_case ls
                         end)
              | ident.eager_list_rect_arrow A P Q
                => Some
                     (fun (N_case : value P -> _) (C_case : value A -> _ -> (value P -> _) -> value P -> _) (ls : expr (base.type.list A)) (v : value P) (* type annotations present for nicer fixpoint refolding *)
                      => match reflect_list ls with
                         | Some ls => list_rect
                                        (fun _ => expr P -> UnderLets (expr Q))
                                        N_case
                                        (fun x xs rec v
                                         => C_case x (reify_list xs) rec v)
                                        ls
                                        v
                         | None => reflect (with_lets:=false) (expr.Ident (@ident.list_rect_arrow A P Q)) N_case C_case ls v
                         end)
              | ident.eager_List_nth_default A
                => Some
                     (fun default (ls : expr (base.type.list A)) (n : expr base.type.nat)
                      => match reflect_list ls, invert_Literal n with
                         | Some ls, Some n => UnderLets.Base (nth_default default ls n)
                         | _, _ => reflect (with_lets:=false) (expr.Ident (@ident.List_nth_default A)) default ls n
                         end)
              | ident.Literal _ _
              | ident.Nat_succ
              | ident.Nat_pred
              | ident.Nat_max
              | ident.Nat_mul
              | ident.Nat_add
              | ident.Nat_sub
              | ident.Nat_eqb
              | ident.nil _
              | ident.cons _
              | ident.pair _ _
              | ident.fst _ _
              | ident.snd _ _
              | ident.prod_rect _ _ _
              | ident.bool_rect _
              | ident.nat_rect _
              | ident.nat_rect_arrow _ _
              | ident.list_rect _ _
              | ident.list_rect_arrow _ _ _
              | ident.list_case _ _
              | ident.List_length _
              | ident.List_seq
              | ident.List_firstn _
              | ident.List_skipn _
              | ident.List_repeat _
              | ident.List_combine _ _
              | ident.List_map _ _
              | ident.List_app _
              | ident.List_rev _
              | ident.List_flat_map _ _
              | ident.List_partition _
              | ident.List_fold_right _ _
              | ident.List_update_nth _
              | ident.List_nth_default _
              | ident.Z_add
              | ident.Z_mul
              | ident.Z_pow
              | ident.Z_sub
              | ident.Z_opp
              | ident.Z_div
              | ident.Z_modulo
              | ident.Z_log2
              | ident.Z_log2_up
              | ident.Z_eqb
              | ident.Z_leb
              | ident.Z_ltb
              | ident.Z_geb
              | ident.Z_gtb
              | ident.Z_of_nat
              | ident.Z_to_nat
              | ident.Z_shiftr
              | ident.Z_shiftl
              | ident.Z_land
              | ident.Z_lor
              | ident.Z_min
              | ident.Z_max
              | ident.Z_bneg
              | ident.Z_lnot_modulo
              | ident.Z_mul_split
              | ident.Z_add_get_carry
              | ident.Z_add_with_carry
              | ident.Z_add_with_get_carry
              | ident.Z_sub_get_borrow
              | ident.Z_sub_with_get_borrow
              | ident.Z_zselect
              | ident.Z_add_modulo
              | ident.Z_rshi
              | ident.Z_cc_m
              | ident.Z_cast _
              | ident.Z_cast2 _
              | ident.option_Some _
              | ident.option_None _
              | ident.option_rect _ _
              | ident.Build_zrange
              | ident.zrange_rect _
              | ident.fancy_add _ _
              | ident.fancy_addc _ _
              | ident.fancy_sub _ _
              | ident.fancy_subb _ _
              | ident.fancy_mulll _
              | ident.fancy_mullh _
              | ident.fancy_mulhl _
              | ident.fancy_mulhh _
              | ident.fancy_rshi _ _
              | ident.fancy_selc
              | ident.fancy_selm _
              | ident.fancy_sell
              | ident.fancy_addm
                => None
              end%expr%under_lets.

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

    Module Reify.
      Import Compile.
      Local Notation EvarMap := pattern.EvarMap.

      Inductive dynlist := dynnil | dyncons {T} (x : T) (xs : dynlist).

      Section with_var.
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {ident var : type.type base.type -> Type}
                {pident : type.type pattern.base.type -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_type_of_list_arg_types_beq : forall t idc, type_of_list (pident_arg_types t idc) -> type_of_list (pident_arg_types t idc) -> bool)
                (pident_of_typed_ident : forall t, ident t -> pident (pattern.type.relax t))
                (pident_arg_types_of_typed_ident : forall t (idc : ident t), type_of_list (pident_arg_types _ (pident_of_typed_ident t idc)))
                (reflect_ident_iota : forall t (idc : ident t), option (@value base.type ident var t)).

        Local Notation type := (type.type base.type).
        Local Notation expr := (@expr.expr base.type ident var).
        Local Notation pattern := (@pattern.pattern pident).
        Local Notation ptype := (type.type pattern.base.type).
        Local Notation value := (@Compile.value base.type ident var).
        Local Notation value_with_lets := (@Compile.value_with_lets base.type ident var).
        Local Notation UnderLets := (UnderLets.UnderLets base.type ident var).
        Local Notation reify_expr_beta_iota := (@reify_expr_beta_iota ident var reflect_ident_iota).
        Local Notation unification_resultT' := (@unification_resultT' pident pident_arg_types).
        Local Notation with_unif_rewrite_ruleTP_gen' := (@with_unif_rewrite_ruleTP_gen' ident var pident pident_arg_types value).
        Local Notation lam_unification_resultT' := (@lam_unification_resultT' pident pident_arg_types).

        Local Notation expr_maybe_do_again should_do_again
          := (@expr.expr base.type ident (if should_do_again then value else var)).

        Fixpoint pattern_of_expr (var' := fun _ => positive) evm (invalid : forall t, @expr.expr base.type ident var' t -> { p : pattern (pattern.type.relax t) & @unification_resultT' var' _ p evm })
                 {t} (e : @expr.expr base.type ident var' t)
          : { p : pattern (pattern.type.relax t) & @unification_resultT' var' _ p evm }
          := match e in expr.expr t return { p : pattern (pattern.type.relax t) & @unification_resultT' var' _ p evm } with
             | expr.Ident t idc
               => existT _ (pattern.Ident (pident_of_typed_ident _ idc))
                         (pident_arg_types_of_typed_ident _ idc)
             | expr.Var t v
               => existT _ (pattern.Wildcard _) v
             | expr.App s d f x
               => let 'existT fp fv := @pattern_of_expr evm invalid _ f in
                  let 'existT xp xv := @pattern_of_expr evm invalid _ x in
                  existT _ (pattern.App fp xp)
                         (fv, xv)
             | expr.Abs _ _ _ as e
             | expr.LetIn _ _ _ _ as e
               => invalid _ e
             end.

        Definition expr_value_to_rewrite_rule_replacement (should_do_again : bool) {t} (e : @expr.expr base.type ident value t)
          : UnderLets (expr_maybe_do_again should_do_again t)
          := (e <-- UnderLets.flat_map (@reify_expr_beta_iota) (fun t v => reflect (expr.Var v)) (UnderLets.of_expr e);
                if should_do_again return UnderLets (expr_maybe_do_again should_do_again t)
                then UnderLets.Base e
                else reify_expr_beta_iota e)%under_lets.

        Fixpoint pair'_unification_resultT' {evm t p}
          : @unification_resultT' (fun _ => positive) t p evm -> @unification_resultT' value t p evm -> PositiveMap.t { t : _ & value t } * list bool -> PositiveMap.t { t : _ & value t } * list bool
          := match p return @unification_resultT' (fun _ => positive) _ p evm -> @unification_resultT' value _ p evm -> PositiveMap.t { t : _ & value t } * list bool -> PositiveMap.t { t : _ & value t } * list bool with
             | pattern.Wildcard t => fun p v '(m, l) => (PositiveMap.add p (existT value _ v) m, l)
             | pattern.Ident t idc => fun v1 v2 '(m, l) => (m, pident_type_of_list_arg_types_beq t idc v2 v1 :: l)
             | pattern.App _ _ F X
               => fun x y '(m, l)
                  => let '(m, l) := @pair'_unification_resultT' _ _ F (fst x) (fst y) (m, l) in
                     let '(m, l) := @pair'_unification_resultT' _ _ X (snd x) (snd y) (m, l) in
                     (m, l)
             end.

        Fixpoint expr_pos_to_expr_value
                 (invalid : forall t, positive * type * PositiveMap.t { t : _ & value t } -> @expr.expr base.type ident value t)
                 {t} (e : @expr.expr base.type ident (fun _ => positive) t) (m : PositiveMap.t { t : _ & value t }) (cur_i : positive)
          : @expr.expr base.type ident value t
          := match e in expr.expr t return expr.expr t with
             | expr.Ident t idc => expr.Ident idc
             | expr.App s d f x
               => expr.App (@expr_pos_to_expr_value invalid _ f m cur_i)
                           (@expr_pos_to_expr_value invalid _ x m cur_i)
             | expr.Var t v
               => match option_map
                          (fun tv => type.try_transport base.try_make_transport_cps value _ t (projT2 tv))
                          (PositiveMap.find v m) with
                  | Some (Some res) => expr.Var res
                  | Some None | None => invalid _ (v, t, m)
                  end
             | expr.Abs s d f
               => expr.Abs (fun v => @expr_pos_to_expr_value invalid _ (f cur_i) (PositiveMap.add cur_i (existT value _ v) m) (Pos.succ cur_i))
             | expr.LetIn A B x f
               => expr.LetIn (@expr_pos_to_expr_value invalid _ x m cur_i)
                             (fun v => @expr_pos_to_expr_value invalid _ (f cur_i) (PositiveMap.add cur_i (existT value _ v) m) (Pos.succ cur_i))
             end.

        Definition expr_to_pattern_and_replacement
                   (should_do_again : bool) evm
                   (invalid : forall A B, A -> B)
                   {t} (lhs rhs : @expr.expr base.type ident (fun _ => positive) t)
                   (side_conditions : list bool)
          : { p : pattern (pattern.type.relax t) & @with_unif_rewrite_ruleTP_gen' _ p should_do_again true true evm }
          := let (p, unif_data_lhs) := @pattern_of_expr evm (fun _ => invalid _ _) t lhs in
             existT
               _
               p
               (pattern.type.subst_default_relax
                  (fun t'
                   => with_unification_resultT'
                        pident_arg_types p evm
                        (option (UnderLets (expr_maybe_do_again should_do_again t'))))
                  (lam_unification_resultT'
                     (fun unif_data_new
                      => let '(value_map, side_conditions) := pair'_unification_resultT' unif_data_lhs unif_data_new (PositiveMap.empty _, side_conditions) in
                         let start_i := Pos.succ (PositiveMap.fold (fun k _ max => Pos.max k max) value_map 1%positive) in
                         let replacement := expr_pos_to_expr_value (fun _ => invalid _ _) rhs value_map start_i in
                         let replacement := expr_value_to_rewrite_rule_replacement should_do_again replacement in
                         if fold_left andb (List.rev side_conditions) true
                         then Some replacement
                         else None))).


        Definition expr_to_pattern_and_replacement_unfolded should_do_again evm invalid {t} lhs rhs side_conditions
          := Eval cbv beta iota delta [expr_to_pattern_and_replacement pattern_of_expr lam_unification_resultT' Pos.succ pair'_unification_resultT' PositiveMap.empty PositiveMap.fold Pos.max expr_pos_to_expr_value (* expr_value_to_rewrite_rule_replacement*) fold_left List.rev List.app value PositiveMap.add PositiveMap.xfoldi Pos.compare Pos.compare_cont FMapPositive.append projT1 projT2 PositiveMap.find Base_value (*UnderLets.map reify_expr_beta_iota reflect_expr_beta_iota*) lam_type_of_list fold_right list_rect pattern.type.relax pattern.type.subst_default pattern.type.subst_default_relax pattern.type.unsubst_default_relax option_map unification_resultT' with_unification_resultT' with_unif_rewrite_ruleTP_gen']
            in @expr_to_pattern_and_replacement should_do_again evm invalid t lhs rhs side_conditions.

        Definition partial_lam_unif_rewrite_ruleTP_gen_unfolded should_do_again {t} p
          := Eval cbv beta iota delta [partial_lam_unif_rewrite_ruleTP_gen pattern.collect_vars pattern.type.lam_forall_vars partial_lam_unification_resultT pattern.type.collect_vars pattern.base.collect_vars PositiveSet.union PositiveSet.add PositiveSet.empty pattern.type.lam_forall_vars_gen List.rev PositiveSet.elements PositiveSet.xelements PositiveSet.rev PositiveSet.rev_append List.app orb fold_right PositiveMap.add PositiveMap.empty]
            in @partial_lam_unif_rewrite_ruleTP_gen ident var pident pident_arg_types value t p should_do_again true true.
      End with_var.

      Ltac strip_functional_dependency term :=
        lazymatch term with
        | fun _ => ?P => P
        | _ => constr_fail_with ltac:(fun _ => idtac "Cannot eliminate functional dependencies of" term;
                                               fail 1 "Cannot eliminate functional dependencies of" term)
        end.

      Ltac reify_under_forall_types' ty_ctx cur_i lem cont :=
        lazymatch lem with
        | forall T : Type, ?P
          => let P' := fresh in
             let ty_ctx' := fresh "ty_ctx" in
             let t := fresh "t" in
             strip_functional_dependency
               (fun t : Compilers.base.type
                => match PositiveMap.add cur_i t ty_ctx return _ with
                   | ty_ctx'
                     => match Compilers.base.interp (pattern.base.lookup_default cur_i ty_ctx') return _ with
                        | T
                          => match P return _ with
                             | P'
                               => ltac:(let P := (eval cbv delta [P' T ty_ctx'] in P') in
                                        let ty_ctx := (eval cbv delta [ty_ctx'] in ty_ctx') in
                                        clear P' T ty_ctx';
                                        let cur_i := (eval vm_compute in (Pos.succ cur_i)) in
                                        let res := reify_under_forall_types' ty_ctx cur_i P cont in
                                        exact res)
                             end
                        end
                   end)
        | ?lem => cont ty_ctx cur_i lem
        end.

      Ltac prop_to_bool H := eval cbv [decb] in (decb H).


      Ltac push_side_conditions H side_conditions :=
        constr:(H :: side_conditions).

      Ltac equation_to_parts' lem side_conditions :=
        lazymatch lem with
        | ?H -> ?P
          => let H := prop_to_bool H in
             let side_conditions := push_side_conditions H side_conditions in
             equation_to_parts' P side_conditions
        | forall x : ?T, ?P
          => let P' := fresh in
             constr:(
               fun x : T
               => match P return _ with
                  | P'
                    => ltac:(let P := (eval cbv delta [P'] in P') in
                             clear P';
                             let res := equation_to_parts' P side_conditions in
                             exact res)
                  end)
        | @eq ?T ?A ?B
          => constr:((@eq T A B, side_conditions))
        | ?T => constr_fail_with ltac:(fun _ => fail 1 "Invalid type of equation:" T)
        end.
      Ltac equation_to_parts lem :=
        equation_to_parts' lem (@nil bool).

      Ltac reify_under_forall_types lem cont :=
        reify_under_forall_types' (@PositiveMap.empty Compilers.base.type) (1%positive) lem cont.

      Ltac preadjust_pattern_type_variables pat :=
        let pat := (eval cbv [pattern.type.relax pattern.type.subst_default pattern.type.subst_default_relax pattern.type.unsubst_default_relax] in pat) in
        let pat := (eval cbn [pattern.base.relax pattern.base.subst_default pattern.base.subst_default_relax pattern.base.unsubst_default_relax] in pat) in
        pat.

      Ltac adjust_pattern_type_variables' pat :=
        lazymatch pat with
        | context[pattern.base.relax (pattern.base.lookup_default ?p ?evm')]
          => let t := constr:(pattern.base.relax (pattern.base.lookup_default p evm')) in
             let T := fresh in
             let pat :=
                 lazymatch (eval pattern t in pat) with
                 | ?pat _
                   => let P := match type of pat with forall x, @?P x => P end in
                      lazymatch pat with
                      | fun T => ?pat
                        => constr:(match pattern.base.type.var p as T return P T with
                                   | T => pat
                                   end)
                      end
                 end in
             adjust_pattern_type_variables' pat
        | ?pat => pat
        end.

      Ltac adjust_pattern_type_variables pat :=
        let pat := preadjust_pattern_type_variables pat in
        adjust_pattern_type_variables' pat.

      Ltac strip_invalid_or_fail term :=
        lazymatch term with
        | fun _ => ?f => f
        | fun invalid : ?T => ?f
          => let f' := fresh in
             constr:(fun invalid : T
                     => match f return _ with
                        | f'
                          => ltac:(lazymatch (eval cbv [f'] in f') with
                                   | context[invalid _ _ ?x]
                                     => fail 0 "Invalid:" x
                                   | context[invalid _ ?x]
                                     => fail 0 "Invalid:" x
                                   end)
                        end)
        end.

      Definition pattern_base_subst_default_relax' t evm P
        := @pattern.base.subst_default_relax P t evm.
      Definition pattern_base_unsubst_default_relax' t evm P
        := @pattern.base.unsubst_default_relax P t evm.

      Ltac change_pattern_base_subst_default_relax term :=
        lazymatch (eval pattern (@pattern.base.subst_default_relax), (@pattern.base.unsubst_default_relax) in term) with
        | ?f _ _
          => let P := fresh "P" in
             let t := fresh "t" in
             let evm := fresh "evm" in
             (eval cbv beta in (f (fun P t evm => @pattern_base_subst_default_relax' t evm P) (fun P t evm => @pattern_base_unsubst_default_relax' t evm P)))
        end.

      Ltac adjust_lookup_default rewr :=
        lazymatch (eval pattern pattern.base.lookup_default in rewr) with
        | ?rewr _
          => let p := fresh "p" in
             let evm := fresh "evm" in
             (eval cbv beta in (rewr (fun p evm => pattern.base.subst_default (pattern.base.type.var p) evm)))
        end.

      Ltac replace_evar_map evm rewr :=
        let evm' := match rewr with
                    | context[pattern.base.lookup_default _ ?evm']
                      => let __ := match goal with _ => tryif constr_eq evm evm' then fail else idtac end in
                         evm'
                    | context[pattern.base.subst_default _ ?evm']
                      => let __ := match goal with _ => tryif constr_eq evm evm' then fail else idtac end in
                         evm'
                    | _ => tt
                    end in
        lazymatch evm' with
        | tt => rewr
        | _
          => let rewr := lazymatch (eval pattern evm' in rewr) with
                         | ?rewr _ => (eval cbv beta in (rewr evm))
                         end in
             replace_evar_map evm rewr
        end.

      Ltac adjust_type_variables rewr :=
        lazymatch rewr with
        | context[pattern.base.subst_default (pattern.base.relax ?t) ?evm'']
          => let t' := constr:(pattern.base.subst_default (pattern.base.relax t) evm'') in
             let rewr :=
                 lazymatch (eval pattern
                                 t',
                            (pattern_base_subst_default_relax' t evm''),
                            (pattern_base_unsubst_default_relax' t evm'')
                             in rewr)
                 with
                 | ?rewr _ _ _
                   => (eval cbv beta in (rewr t (fun P x => x) (fun P x => x)))
                 end in
             adjust_type_variables rewr
        | _ => rewr
        end.

      Ltac replace_type_try_transport term :=
        lazymatch term with
        | context[@type.try_transport ?base_type ?try_make_transport_base_type_cps ?P ?t ?t]
          => let v := constr:(@type.try_transport base_type try_make_transport_base_type_cps P t t) in
             let term := lazymatch (eval pattern v in term) with
                         | ?term _ => (eval cbv beta in (term (@Some _)))
                         end in
             replace_type_try_transport term
        | _ => term
        end.

      Ltac under_binders term cont ctx :=
        lazymatch term with
        | (fun x : ?T => ?f)
          => let ctx' := fresh in
             let f' := fresh in
             constr:(fun x : T
                     => match f, dyncons x ctx return _ with
                        | f', ctx'
                          => ltac:(let ctx := (eval cbv delta [ctx'] in ctx') in
                                   let f := (eval cbv delta [f'] in f') in
                                   clear f' ctx';
                                   let res := under_binders f cont ctx in
                                   exact res)
                        end)
        | ?term => cont ctx term
        end.
      Ltac substitute_with term x y :=
        lazymatch (eval pattern y in term) with
        | (fun z => ?term) _ => constr:(match x return _ with z => term end)
        end.
      Ltac substitute_beq_with full_ctx term beq x :=
        let is_good y :=
            lazymatch full_ctx with
            | context[dyncons y _] => fail
            | _ => is_var y
            end in
        let y := match term with
                 | context term' [beq x ?y]
                   => let __ := is_good y in
                      constr:(Some (beq x y))
                 | context term' [@base.interp_beq ?t x ?y]
                   => let __ := is_good y in
                      constr:(Some (@base.interp_beq t x y))
                 | context term' [@base.base_interp_beq ?t x ?y]
                   => let __ := is_good y in
                      constr:(Some (@base.base_interp_beq t x y))
                 | _ => constr:(@None unit)
                 end in
        lazymatch y with
        | Some (?beq x ?y)
          => lazymatch term with
             | context term'[beq x y]
               => let term := context term'[true] in
                  substitute_with term x y
             end
        | None => term
        end.
      Ltac remove_andb_true term :=
        let term := lazymatch (eval pattern andb, (andb true) in term) with
                    | ?f _ _ => (eval cbn [andb] in (f (fun x y => andb y x) (fun b => b)))
                    end in
        let term := lazymatch (eval pattern andb, (andb true) in term) with
                    | ?f _ _ => (eval cbn [andb] in (f (fun x y => andb y x) (fun b => b)))
                    end in
        term.
      Ltac adjust_if_negb term :=
        lazymatch term with
        | context term'[if negb ?x then ?a else ?b]
          => let term := context term'[if x then b else a] in
             adjust_if_negb term
        | _ => term
        end.
      Ltac substitute_bool_eqb term :=
        lazymatch term with
        | context term'[Bool.eqb ?x true]
          => let term := context term'[x] in
             substitute_bool_eqb term
        | context term'[Bool.eqb ?x false]
          => let term := context term'[negb x] in
             substitute_bool_eqb term
        | context term'[Bool.eqb true ?x]
          => let term := context term'[x] in
             substitute_bool_eqb term
        | context term'[Bool.eqb false ?x]
          => let term := context term'[negb x] in
             substitute_bool_eqb term
        | _ => term
        end.

      Ltac substitute_beq full_ctx ctx term :=
        lazymatch ctx with
        | dynnil
          => let term := (eval cbv [base.interp_beq base.base_interp_beq] in term) in
             let term := substitute_bool_eqb term in
             let term := remove_andb_true term in
             let term := adjust_if_negb term in
             term
        | dyncons ?v ?ctx
          => let term := substitute_beq_with full_ctx term zrange_beq v in
             let term := substitute_beq_with full_ctx term Z.eqb v in
             let term := match constr:(Set) with
                         | _ => let T := type of v in
                                let beq := (eval cbv beta delta [Reflect.decb_rel] in (Reflect.decb_rel (@eq T))) in
                                substitute_beq_with full_ctx term beq v
                         | _ => term
                         end in
             substitute_beq full_ctx ctx term
        end.

      Ltac deep_substitute_beq term :=
        lazymatch term with
        | context term'[@Build_rewrite_rule_data ?ident ?var ?pident ?pident_arg_types ?t ?p ?sda ?wo ?ul ?subterm]
          => let subterm := under_binders subterm ltac:(fun ctx term => substitute_beq ctx ctx term) dynnil in
             let term := context term'[@Build_rewrite_rule_data ident var pident pident_arg_types t p sda wo ul subterm] in
             term
        end.

      Ltac clean_beq term :=
        let term := (eval cbn [Prod.prod_beq] in term) in
        let term := (eval cbv [ident.literal] in term) in
        let term := deep_substitute_beq term in
        let term := (eval cbv [base.interp_beq base.base_interp_beq] in term) in
        let term := remove_andb_true term in
        term.


      Ltac reify_to_pattern_and_replacement_in_context ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota type_ctx var should_do_again cur_i term value_ctx :=
        let t := fresh "t" in
        let p := fresh "p" in
        let reify_rec_gen type_ctx := reify_to_pattern_and_replacement_in_context ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota type_ctx var should_do_again in
        let var_pos := constr:(fun _ : type base.type => positive) in
        let value := constr:(@value base.type ident var) in
        let cexpr_to_pattern_and_replacement_unfolded := constr:(@expr_to_pattern_and_replacement_unfolded ident var pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident (reflect_ident_iota var) should_do_again type_ctx) in
        let cpartial_lam_unif_rewrite_ruleTP_gen := constr:(@partial_lam_unif_rewrite_ruleTP_gen_unfolded ident var pident pident_arg_types should_do_again) in
        let cwith_unif_rewrite_ruleTP_gen := constr:(fun t p => @with_unif_rewrite_ruleTP_gen ident var pident pident_arg_types value t p should_do_again true true) in
        lazymatch term with
        | (fun x : ?T => ?f)
          => let rT := Compilers.type.reify ltac:(Compilers.base.reify) base.type T in
             let not_x1 := fresh in
             let not_x2 := fresh in
             let next_i := (eval vm_compute in (Pos.succ cur_i)) in
             let type_ctx' := fresh in (* COQBUG(https://github.com/coq/coq/issues/7210#issuecomment-470009463) *)
             let rf0 :=
                 constr:(
                   match type_ctx return _ with
                   | type_ctx'
                     => fun (x : T)
                        => match f, @expr.var_context.cons base.type var_pos T rT x cur_i value_ctx return _ with (* c.f. COQBUG(https://github.com/coq/coq/issues/6252#issuecomment-347041995) for [return _] *)
                           | not_x1, not_x2
                             => ltac:(
                                  let f := (eval cbv delta [not_x1] in not_x1) in
                                  let value_ctx := (eval cbv delta [not_x2] in not_x2) in
                                  let type_ctx := (eval cbv delta [type_ctx'] in type_ctx') in
                                  clear not_x1 not_x2 type_ctx';
                                  let rf := reify_rec_gen type_ctx next_i f value_ctx in
                                  exact rf)
                           end
                   end) in
             lazymatch rf0 with
             | (fun _ => ?f) => f
             | _
               => constr_fail_with ltac:(fun _ => fail 1 "Failure to eliminate functional dependencies of" rf0)
             end
        | (@eq ?T ?A ?B, ?side_conditions)
          => let rA := expr.reify_in_context base.type ident ltac:(base.reify) reify_ident var_pos A value_ctx tt in
             let rB := expr.reify_in_context base.type ident ltac:(base.reify) reify_ident var_pos B value_ctx tt in
             let invalid := fresh "invalid" in
             let res := constr:(fun invalid => cexpr_to_pattern_and_replacement_unfolded invalid _ rA rB side_conditions) in
             let res := (eval cbv [expr_to_pattern_and_replacement_unfolded pident_arg_types pident_of_typed_ident pident_type_of_list_arg_types_beq pident_arg_types_of_typed_ident (*reflect_ident_iota*)] in res) in
             let res := (eval cbn [fst snd andb pattern.base.relax pattern.base.subst_default pattern.base.subst_default_relax] in res) in
             let res := change_pattern_base_subst_default_relax res in
             let p := (eval cbv [projT1] in (fun invalid => projT1 (res invalid))) in
             let p := strip_invalid_or_fail p in
             let p := adjust_pattern_type_variables p in
             let res := (eval cbv [projT2] in (fun invalid => projT2 (res invalid))) in
             let evm' := fresh "evm" in
             let res' := fresh in
             let res :=
                 constr:(
                   fun invalid (evm' : EvarMap)
                   => match res invalid return _ with
                      | res'
                        => ltac:(let res := (eval cbv beta delta [res'] in res') in
                                 clear res';
                                 let res := adjust_lookup_default res in
                                 let res := adjust_type_variables res in
                                 let res := replace_evar_map evm' res in
                                 let res := replace_type_try_transport res in
                                 exact res)
                      end) in
             let res := (eval cbv [UnderLets.map UnderLets.flat_map reify_expr_beta_iota reflect_expr_beta_iota reify_to_UnderLets] in res) in
             let res := (eval cbn [reify reflect UnderLets.of_expr UnderLets.to_expr UnderLets.splice value' Base_value invert_Literal ident.invert_Literal splice_under_lets_with_value] in res) in
             let res := strip_invalid_or_fail res in
             (* cbv here not strictly needed *)
             let res := (eval cbv [partial_lam_unif_rewrite_ruleTP_gen_unfolded] in
                            (existT
                               (cwith_unif_rewrite_ruleTP_gen _)
                               p
                               (cpartial_lam_unif_rewrite_ruleTP_gen _ p res))) in
             (* not strictly needed *)
             let res := (eval cbn [pattern.base.subst_default pattern.base.lookup_default PositiveMap.find type.interp base.interp base.base_interp] in res) in
             let res := (eval cbv [projT1 projT2] in
                            (existT
                               (@rewrite_ruleTP ident var pident pident_arg_types)
                               {| pattern.pattern_of_anypattern := projT1 res |}
                               {| rew_replacement := projT2 res |})) in
             let res := clean_beq res in
             res
        end.

      Ltac reify ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var should_do_again lem :=
        reify_under_forall_types
          lem
          ltac:(
          fun ty_ctx cur_i lem
          => let lem := equation_to_parts lem in
             let res := reify_to_pattern_and_replacement_in_context ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota ty_ctx var should_do_again constr:(1%positive) lem (@expr.var_context.nil base.type (fun _ => positive)) in
             res).

      Ltac Reify ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota should_do_again lem :=
        let var := fresh "var" in
        constr:(fun var : Compilers.type.type Compilers.base.type -> Type
                => ltac:(let res := reify ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var should_do_again lem in
                         exact res)).

      (* lems is either a list of [Prop]s, or a list of [bool (* should_do_again *) * Prop] *)
      Ltac reify_list ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var lems :=
        let reify' := reify ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var in
        let reify_list_rec := reify_list ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var in
        lazymatch lems with
        | (?b, ?lem) :: ?lems
          => let rlem := reify' b lem in
             let rlems := reify_list_rec lems in
             constr:(rlem :: rlems)
        | nil => constr:(@nil (@rewrite_ruleT ident var pident pident_arg_types))
        | _
          => let List_map := (eval cbv delta [List.map] in (@List.map)) in
             let lems := (eval cbv beta iota in
                             (List_map _ _ (fun p : Prop => (false, p)) lems)) in
             reify_list_rec lems
        end.

      Ltac Reify_list ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota lems :=
        let var := fresh "var" in
        constr:(fun var : Compilers.type.type Compilers.base.type -> Type
                => ltac:(let res := reify_list ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var lems in
                         exact res)).
    End Reify.

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
             | pattern.base.type.option A => None
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
                 | pattern.base.type.option _
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
                           | context[cons (existT _ _ v) _] => constr_fail
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

      Ltac reify lems :=
        Reify.reify_list ident ident.reify pattern.ident (@pattern.ident.arg_types) (@pattern.ident.type_of_list_arg_types_beq) (@pattern.ident.of_typed_ident) (@pattern.ident.arg_types_of_typed_ident) (@reflect_ident_iota) var lems.
       (* Play games with [match] to get [lems] interpreted as a constr rather than an ident when it's not closed, to get better error messages *)
      Local Notation reify lems
        := (match lems return _ with
            | _LEMS => ltac:(let LEMS := (eval cbv delta [_LEMS] in _LEMS) in let res := reify LEMS in exact res)
            end) (only parsing).

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
      Local Notation "' x" := (ident.literal x).

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
      Let myflatten {A} := Eval cbv in List.fold_right myapp (@nil A).
      Local Notation do_again P := (true, P) (only parsing).
      Local Notation cstZ := (ident.cast ident.cast_outside_of_range).
      Local Notation cstZZ := (ident.cast2 ident.cast_outside_of_range).
      (* N.B. [ident.eagerly] does not play well with [do_again] *)
      Definition nbe_rewrite_rules : rewrite_rulesT
        := Eval cbv [Make.interp_rewrite_rules myapp myflatten] in
            myapp
              Make.interp_rewrite_rules
              (myflatten
                 [reify
                    [(forall A B x y, @fst A B (x, y) = x)
                     ; (forall A B x y, @snd A B (x, y) = y)
                     ; (forall P t f, @ident.Thunked.bool_rect P t f true = t tt)
                     ; (forall P t f, @ident.Thunked.bool_rect P t f false = f tt)
                     ; (forall A B C f x y, @prod_rect A B (fun _ => C) f (x, y) = f x y)

                     ; (forall A x n,
                           @List.repeat A x ('n)
                           = ident.eagerly (@nat_rect) _ nil (fun k repeat_k => x :: repeat_k) ('n))
                     ; (forall A xs ys,
                           xs ++ ys
                           = ident.eagerly (@list_rect) A _ ys (fun x xs app_xs_ys => x :: app_xs_ys) xs)
                     ; (forall A B f a ls,
                           @fold_right A B f a ls
                           = (ident.eagerly (@list_rect) _ _)
                               a
                               (fun x xs fold_right_xs => f x fold_right_xs)
                               ls)
                     ; (forall A P N C ls,
                           @ident.Thunked.list_rect A P N C ls
                           = ident.eagerly (@ident.Thunked.list_rect) A P N C ls)
                     ; (forall A P Q N C ls v,
                           @list_rect A (fun _ => P -> Q) N C ls v
                           = ident.eagerly (@list_rect) A (fun _ => P -> Q) N C ls v)
                     ; (forall A P N C, @ident.Thunked.list_case A P N C nil = N tt)
                     ; (forall A P N C x xs, @ident.Thunked.list_case A P N C (x :: xs) = C x xs)
                     ; (forall A B f ls,
                           @List.map A B f ls
                           = (ident.eagerly (@list_rect) _ _)
                               nil
                               (fun x xs map_f_xs => f x :: map_f_xs)
                               ls)
                     ; (forall P O_case S_case n,
                           @ident.Thunked.nat_rect P O_case S_case ('n)
                           = (ident.eagerly (@ident.Thunked.nat_rect) _)
                               O_case
                               S_case
                               ('n))
                     ; (forall P Q O_case S_case n v,
                           @nat_rect (fun _ => P -> Q) O_case S_case ('n) v
                           = (ident.eagerly (@nat_rect) _)
                               O_case
                               S_case
                               ('n)
                               v)
                     ; (forall A default ls n,
                           @List.nth_default A default ls ('n)
                           = ident.eagerly (@List.nth_default) _ default ls ('n))
                    ]
                  ; reify
                      [do_again
                         (forall A B xs ys,
                             @List.combine A B xs ys
                             = (list_rect _)
                                 (fun _ => nil)
                                 (fun x xs combine_xs ys
                                  => match ys with
                                     | nil => nil
                                     | y :: ys => (x, y) :: combine_xs ys
                                     end)
                                 xs
                                 ys)
                       ; do_again
                           (forall A n ls,
                             @List.firstn A ('n) ls
                             = (nat_rect _)
                                 (fun _ => nil)
                                 (fun n' firstn_n' ls
                                  => match ls with
                                     | nil => nil
                                     | cons x xs => x :: firstn_n' xs
                                     end)
                                 ('n)
                                 ls)
                       ; do_again
                           (forall A n ls,
                               @List.skipn A ('n) ls
                               = (nat_rect _)
                                   (fun ls => ls)
                                   (fun n' skipn_n' ls
                                    => match ls with
                                       | nil => nil
                                       | cons x xs => skipn_n' xs
                                       end)
                                   ('n)
                                   ls)
                       ; do_again
                           (forall A xs,
                               @List.length A xs
                               = (list_rect _)
                                   0%nat
                                   (fun _ xs length_xs => S length_xs)
                                   xs)
                       ; do_again
                           (forall A xs,
                               @List.rev A xs
                               = (list_rect _)
                                   nil
                                   (fun x xs rev_xs => rev_xs ++ [x])
                                   xs)
                       ; do_again
                           (forall A B f xs,
                               @List.flat_map A B f xs
                               = (list_rect _)
                                   nil
                                   (fun x _ flat_map_tl => f x ++ flat_map_tl)
                                   xs)
                       ; do_again
                           (forall A f xs,
                               @List.partition A f xs
                               = (list_rect _)
                                   ([], [])
                                   (fun x tl partition_tl
                                    => let '(g, d) := partition_tl in
                                       if f x then (x :: g, d) else (g, x :: d))
                                   xs)
                       ; do_again
                           (forall A n f xs,
                               @update_nth A ('n) f xs
                               = (nat_rect _)
                                   (fun xs => match xs with
                                              | nil => nil
                                              | x' :: xs' => f x' :: xs'
                                              end)
                                   (fun n' update_nth_n' xs
                                    => match xs with
                                       | nil => nil
                                       | x' :: xs' => x' :: update_nth_n' xs'
                                       end)
                                   ('n)
                                   xs)
                      ]
              ]).

      Definition arith_rewrite_rules (max_const_val : Z) : rewrite_rulesT
        := Eval cbv [Make.interp_rewrite_rules myapp myflatten] in
            myflatten
              [reify
                 [(forall A B x y, @fst A B (x, y) = x)
                  ; (forall A B x y, @snd A B (x, y) = y)
                  ; (forall v, 0 + v = v)
                  ; (forall v, v + 0 = v)
                  ; (forall x y, (-x) + (-y) = -(x + y))
                  ; (forall x y, (-x) +   y  = y - x)
                  ; (forall x y,   x  + (-y) = x - y)

                  ; (forall v, 0 - (-v) = v)
                  ; (forall v, 0 -   v  = -v)
                  ; (forall v, v -   0  = v)
                  ; (forall x y, (-x) - (-y) = y - x)
                  ; (forall x y, (-x) -   y  = -(x + y))
                  ; (forall x y,   x  - (-y) = x + y)

                  ; (forall v, 0 * v = 0)
                  ; (forall v, v * 0 = 0)
                  ; (forall v, 1 * v = v)
                  ; (forall v, v * 1 = v)
                  ; (forall v, (-1) * (-v) = v)
                  ; (forall v, (-v) * (-1) = v)
                  ; (forall v, (-1) *   v  = -v)
                  ; (forall v,   v  * (-1) = -v)
                  ; (forall x y, (-x) * (-y) = x * y)
                  ; (forall x y, (-x) *   y  = -(x * y))
                  ; (forall x y,   x  * (-y) = -(x * y))

                  ; (forall x, x &' 0 = 0)

                  ; (forall x, x / 1 = x)
                  ; (forall x, x mod 1 = 0)

                  ; (forall v, -(-v) = v)

                  ; (forall z v, z > 0 ->  'z  + (-v) = 'z - v)
                  ; (forall z v, z > 0 -> (-v) +  'z  = 'z - v)
                  ; (forall z v, z < 0 ->  'z  + (-v) = -('(-z) + v))
                  ; (forall z v, z < 0 -> (-v) +  'z  = -(v + '(-z)))

                  ; (forall z v, z > 0 ->  'z  - (-v) = 'z + v)
                  ; (forall z v, z < 0 ->  'z  - (-v) = v - '(-z))
                  ; (forall z v, z < 0 ->  'z  -   v  = -('(-z) + v))
                  ; (forall z v, z > 0 -> (-v) -  'z  = -(v + 'z))
                  ; (forall z v, z < 0 -> (-v) -  'z  = '(-z) - v)
                  ; (forall z v, z < 0 ->   v  -  'z  = v + '(-z))

                  ; (forall x y, 'x * 'y = '(x*y))
                  ; (forall z v, z < 0 -> 'z *  v = -('(-z) * v))
                  ; (forall z v, z < 0 ->  v * 'z = -(v * '(-z)))

                  ; (forall x y, y = 2^Z.log2 y -> y <> 2 ->  x * 'y = x << '(Z.log2 y))
                  ; (forall x y, y = 2^Z.log2 y -> y <> 2 -> 'y *  x = x << '(Z.log2 y))

                  ; (forall x y, y = 2^Z.log2 y -> x / 'y = x >> '(Z.log2 y))
                  ; (forall x y, y = 2^Z.log2 y -> x mod 'y = x &' '(y-1))

                  (* We reassociate some multiplication of small constants  *)
                  ; (forall c1 c2 x y,
                        Z.abs c1 <= Z.abs max_const_val
                        -> Z.abs c2 <= Z.abs max_const_val
                        -> 'c1 * ('c2 * (x * y)) = (x * (y * ('c1 * 'c2))))
                  ; (forall c1 c2 x y,
                        Z.abs c1 <= Z.abs max_const_val
                        -> Z.abs c2 <= Z.abs max_const_val
                        -> 'c1 * (x * (y * 'c2)) = (x * (y * ('c1 * 'c2))))
                  ; (forall c x y,
                        Z.abs c <= Z.abs max_const_val
                        -> 'c * (x * y) = x * (y * 'c))
                  ; (forall c x,
                        Z.abs c <= Z.abs max_const_val
                        -> 'c * x = x * 'c)

                  (* transform +- to + *)
                  ; (forall s y x,
                        Z.add_get_carry_full s x (- y)
                        = dlet vb := Z.sub_get_borrow_full s x y in (fst vb, - snd vb))
                  ; (forall s y x,
                        Z.add_get_carry_full s (- y) x
                        = dlet vb := Z.sub_get_borrow_full s x y in (fst vb, - snd vb))
                  ; (forall s y x,
                        Z.add_with_get_carry_full s 0 x (- y)
                        = dlet vb := Z.sub_get_borrow_full s x y in (fst vb, - snd vb))
                  ; (forall s y x,
                        Z.add_with_get_carry_full s 0 (- y) x
                        = dlet vb := Z.sub_get_borrow_full s x y in (fst vb, - snd vb))
                  ; (forall s c y x,
                        Z.add_with_get_carry_full s (- c) (- y) x
                        = dlet vb := Z.sub_with_get_borrow_full s c x y in (fst vb, - snd vb))
                  ; (forall s c y x,
                        Z.add_with_get_carry_full s (- c) x (- y)
                        = dlet vb := Z.sub_with_get_borrow_full s c x y in (fst vb, - snd vb))
                 ]
               ; reify
                   [ (* [do_again], so that if one of the arguments is concrete, we automatically get the rewrite rule for [Z_cast] applying to it *)
                     do_again (forall r x y, cstZZ r (x, y) = (cstZ (fst r) x, cstZ (snd r) y))
                   ]

               ; [
                 make_rewriteol (-??) (fun e => (llet v := e in -$v)  when  negb (SubstVarLike.is_var_fst_snd_pair_opp_cast e)) (* inline negation when the rewriter wouldn't already inline it *)
              ] ].

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

      Local Notation "'plet' x := y 'in' z"
        := (match y return _ with x => z end).

      Local Notation dlet2_opp2 rvc e
        := (plet rvc' := (fst rvc, -snd rvc)%zrange in
            plet cst' := cstZZ rvc' in
            plet cst1 := cstZ (fst rvc%zrange%zrange) in
            plet cst2 := cstZ (snd rvc%zrange%zrange) in
            plet cst2' := cstZ (-snd rvc%zrange%zrange) in
            (dlet vc := cst' e in
                 (cst1 (fst (cst' vc)), cst2 (-(cst2' (snd (cst' vc))))))).

      Local Notation dlet2 rvc e
        := (dlet vc := cstZZ rvc e in
                (cstZ (fst rvc) (fst (cstZZ rvc vc)),
                 cstZ (snd rvc) (snd (cstZZ rvc vc)))).


      Local Notation "x '\in' y" := (is_bounded_by_bool x (ZRange.normalize y) = true) : zrange_scope.
      Local Notation "x ∈ y" := (is_bounded_by_bool x (ZRange.normalize y) = true) : zrange_scope.
      Local Notation "x <= y" := (is_tighter_than_bool (ZRange.normalize x) y = true) : zrange_scope.
      Local Notation litZZ x := (ident.literal (fst x), ident.literal (snd x)) (only parsing).
      Local Notation n r := (ZRange.normalize r) (only parsing).

      Definition arith_with_casts_rewrite_rules : rewrite_rulesT
        := Eval cbv [Make.interp_rewrite_rules myapp myflatten] in
            myflatten
              [reify
                 [(forall A B x y, @fst A B (x, y) = x)
                  ; (forall A B x y, @snd A B (x, y) = y)
                  ; (forall r v, lower r = upper r -> cstZ r v = cstZ r ('(lower r)))
                  ; (forall r0 v, 0 ∈ r0 -> cstZ r0 0 + v = v)
                  ; (forall r0 v, 0 ∈ r0 -> v + cstZ r0 0 = v)
                  ; (forall r0 v, 0 ∈ r0 -> cstZ r0 0 - v = -v)
                  ; (forall r0 v, 0 ∈ r0 -> cstZ r0 0 << v = 0)
                  ; (forall r0 rnv rv v,
                        (rv <= -n rnv)%zrange -> 0 ∈ r0
                        -> cstZ r0 0 - cstZ rnv (-(cstZ rv v)) = cstZ rv v)
                  ; (forall rnv rv v,
                        (rv <= -n rnv)%zrange
                        -> -(cstZ rnv (-(cstZ rv v))) = cstZ rv v)

                  ; (forall s r0 y, 0 ∈ r0 -> Z.mul_split s (cstZ r0 0) y = (cstZ r[0~>0] 0, cstZ r[0~>0] 0))
                  ; (forall s r0 y, 0 ∈ r0 -> Z.mul_split s y (cstZ r0 0) = (cstZ r[0~>0] 0, cstZ r[0~>0] 0))
                  ; (forall rs s r1 ry y,
                        1 ∈ r1 -> s ∈ rs -> (ry <= r[0~>s-1])%zrange
                        -> Z.mul_split (cstZ rs ('s)) (cstZ r1 1) (cstZ ry y)
                           = (cstZ ry y, cstZ r[0~>0] 0))
                  ; (forall rs s r1 ry y,
                        1 ∈ r1 -> s ∈ rs -> (ry <= r[0~>s-1])%zrange
                        -> Z.mul_split (cstZ rs ('s)) (cstZ ry y) (cstZ r1 1)
                           = (cstZ ry y, cstZ r[0~>0] 0))

                  ; (forall rvc s rny ry y x,
                        (ry <= -n rny)%zrange
                        -> cstZZ rvc (Z.add_get_carry_full s (cstZ rny (-cstZ ry y)) x)
                           = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ ry y)))
                  ; (forall rvc s rny ry y x,
                        (ry <= -n rny)%zrange
                        -> cstZZ rvc (Z.add_get_carry_full s x (cstZ rny (-cstZ ry y)))
                           = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ ry y)))
                  ; (forall rvc s ryy yy x,
                        yy ∈ ryy -> yy < 0
                        -> cstZZ rvc (Z.add_get_carry_full s (cstZ ryy ('yy)) x)
                           = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ (-ryy) ('(-yy)))))
                  ; (forall rvc s ryy yy x,
                        yy ∈ ryy -> yy < 0
                        -> cstZZ rvc (Z.add_get_carry_full s x (cstZ ryy ('yy)))
                           = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ (-ryy) ('(-yy)))))
                  ; (forall rvc s rnc rc c rny ry y x,
                        (ry <= -n rny)%zrange -> (rc <= -n rnc)%zrange
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc c)) (cstZ rny (-cstZ ry y)) x)
                           = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ rc c) x (cstZ ry y)))
                  ; (forall rvc s rnc rc c rny ry y x,
                        (ry <= -n rny)%zrange -> (rc <= -n rnc)%zrange
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc c)) x (cstZ rny (-cstZ ry y)))
                           = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ rc c) x (cstZ ry y)))
                  ; (forall rvc s r0 rny ry y x,
                        0 ∈ r0 -> (ry <= -n rny)%zrange
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ r0 0) (cstZ rny (-cstZ ry y)) x)
                           = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ ry y)))
                  ; (forall rvc s rcc cc rny ry y x,
                        cc < 0 -> cc ∈ rcc -> (ry <= -n rny)%zrange
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) (cstZ rny (-cstZ ry y)) x)
                           = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ ry y)))
                  ; (forall rvc s r0 rny ry y x,
                        0 ∈ r0 -> (ry <= -n rny)%zrange
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ r0 0) x (cstZ rny (-cstZ ry y)))
                           = dlet2_opp2 rvc (Z.sub_get_borrow_full s x (cstZ ry y)))
                  ; (forall rvc s rcc cc rny ry y x,
                        cc < 0 -> cc ∈ rcc -> (ry <= -n rny)%zrange
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) x (cstZ rny (-cstZ ry y)))
                           = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ ry y)))
                  ; (forall rvc s rnc rc c ryy yy x,
                        yy <= 0 -> yy ∈ ryy -> (rc <= -n rnc)%zrange
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc c)) (cstZ ryy ('yy)) x)
                           = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ rc c) x (cstZ (-ryy) ('(-yy)))))
                  ; (forall rvc s rnc rc c ryy yy x,
                        yy <= 0 -> yy ∈ ryy -> (rc <= -n rnc)%zrange
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rnc (-cstZ rc c)) x (cstZ ryy ('yy)))
                           = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ rc c) x (cstZ (-ryy) ('(-yy)))))
                  ; (forall rvc s rcc cc ryy yy x,
                        yy <= 0 -> cc <= 0 -> yy + cc < 0 (* at least one must be strictly negative *) -> yy ∈ ryy -> cc ∈ rcc
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) (cstZ ryy ('yy)) x)
                           = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ (-ryy) ('(-yy)))))
                  ; (forall rvc s rcc cc ryy yy x,
                        yy <= 0 -> cc <= 0 -> yy + cc < 0 (* at least one must be strictly negative *) -> yy ∈ ryy -> cc ∈ rcc
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ rcc ('cc)) x (cstZ ryy ('yy)))
                           = dlet2_opp2 rvc (Z.sub_with_get_borrow_full s (cstZ (-rcc) ('(-cc))) x (cstZ (-ryy) ('(-yy)))))


                  ; (forall rs s rxx xx ryy yy,
                        s ∈ rs -> xx ∈ rxx -> yy ∈ ryy
                        -> Z.add_get_carry_full (cstZ rs ('s)) (cstZ rxx ('xx)) (cstZ ryy ('yy))
                           = litZZ (Z.add_get_carry_full s xx yy))
                  ; (forall rs s r0 ry y,
                        s ∈ rs -> 0 ∈ r0 -> (ry <= r[0~>s-1])%zrange
                        -> Z.add_get_carry_full (cstZ rs ('s)) (cstZ r0 0) (cstZ ry y)
                           = (cstZ ry y, cstZ r[0~>0] 0))
                  ; (forall rs s r0 ry y,
                        s ∈ rs -> 0 ∈ r0 -> (ry <= r[0~>s-1])%zrange
                        -> Z.add_get_carry_full (cstZ rs ('s)) (cstZ ry y) (cstZ r0 0)
                           = (cstZ ry y, cstZ r[0~>0] 0))

                  ; (forall r0 x y, 0 ∈ r0 -> Z.add_with_carry (cstZ r0 0) x y = x + y)

                  ; (forall rs s rcc cc rxx xx ryy yy,
                        s ∈ rs -> cc ∈ rcc -> xx ∈ rxx -> yy ∈ ryy
                        -> Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rcc ('cc)) (cstZ rxx ('xx)) (cstZ ryy ('yy))
                           = litZZ (Z.add_with_get_carry_full s cc xx yy))
                  ; (forall rs s r0c r0x ry y,
                        s ∈ rs -> 0 ∈ r0c -> 0 ∈ r0x -> (ry <= r[0~>s-1])%zrange
                        -> Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ r0c 0) (cstZ r0x 0) (cstZ ry y)
                           = (cstZ ry y, cstZ r[0~>0] 0))
                  ; (forall rs s r0c r0x ry y,
                        s ∈ rs -> 0 ∈ r0c -> 0 ∈ r0x -> (ry <= r[0~>s-1])%zrange
                        -> Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ r0c 0) (cstZ ry y) (cstZ r0x 0)
                           = (cstZ ry y, cstZ r[0~>0] 0))

                  ; (forall rvc s r0 x y, (* carry = 0: ADC x y -> ADD x y *)
                        0 ∈ r0
                        -> cstZZ rvc (Z.add_with_get_carry_full s (cstZ r0 0) x y)
                           = dlet2 rvc (Z.add_get_carry_full s x y))
                  ; (forall rvc rs s rc c r0x r0y, (* ADC 0 0 -> (ADX 0 0, 0) *) (* except we don't do ADX, because C stringification doesn't handle it *)
                        0 ∈ r0x -> 0 ∈ r0y -> (rc <= r[0~>s-1])%zrange -> 0 ∈ snd rvc -> s ∈ rs
                        -> cstZZ rvc (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ r0x 0) (cstZ r0y 0))
                           = (dlet vc := (cstZZ rvc (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ r0x 0) (cstZ r0y 0))) in
                                  (cstZ (fst rvc) (fst (cstZZ rvc vc)),
                                   cstZ r[0~>0] 0)))

                  (* let-bind any adc/sbb/mulx *)
                  ; (forall rvc s c x y,
                        cstZZ rvc (Z.add_with_get_carry_full s c x y)
                        = dlet2 rvc (Z.add_with_get_carry_full s c x y))
                  ; (forall rv c x y,
                        cstZ rv (Z.add_with_carry c x y)
                        = (dlet vc := cstZ rv (Z.add_with_carry c x y) in
                               cstZ rv vc))
                  ; (forall rvc s x y,
                        cstZZ rvc (Z.add_get_carry_full s x y)
                        = dlet2 rvc (Z.add_get_carry_full s x y))
                  ; (forall rvc s c x y,
                        cstZZ rvc (Z.sub_with_get_borrow_full s c x y)
                        = dlet2 rvc (Z.sub_with_get_borrow_full s c x y))
                  ; (forall rvc s x y,
                        cstZZ rvc (Z.sub_get_borrow_full s x y)
                        = dlet2 rvc (Z.sub_get_borrow_full s x y))
                  ; (forall rvc s x y,
                        cstZZ rvc (Z.mul_split s x y)
                        = dlet2 rvc (Z.mul_split s x y))
                 ]%Z%zrange
               ; reify
                   [ (* [do_again], so that if one of the arguments is concrete, we automatically get the rewrite rule for [Z_cast] applying to it *)
                     do_again (forall r x y, cstZZ r (x, y) = (cstZ (fst r) x, cstZ (snd r) y))
                   ]
               ; reify
                   [(forall r1 r2 x, (r2 <= n r1)%zrange -> cstZ r1 (cstZ r2 x) = cstZ r2 x)
                   ]%Z%zrange
              ].

      Definition strip_literal_casts_rewrite_rules : rewrite_rulesT
        := reify
             [(forall rx x, x ∈ rx -> cstZ rx ('x) = 'x)]%Z%zrange.


      Definition nbe_dtree'
        := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 nbe_rewrite_rules.
      Definition arith_dtree'
        := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 (arith_rewrite_rules 0%Z (* dummy val *)).
      Definition arith_with_casts_dtree'
        := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 arith_with_casts_rewrite_rules.
      Definition strip_literal_casts_dtree'
        := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 strip_literal_casts_rewrite_rules.
      Definition nbe_dtree : decision_tree
        := Eval compute in Option.invert_Some nbe_dtree'.
      Definition arith_dtree : decision_tree
        := Eval compute in Option.invert_Some arith_dtree'.
      Definition arith_with_casts_dtree : decision_tree
        := Eval compute in Option.invert_Some arith_with_casts_dtree'.
      Definition strip_literal_casts_dtree : decision_tree
        := Eval compute in Option.invert_Some strip_literal_casts_dtree'.

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
        Local Notation bounds1_good f
          := (fun (output x_bs : zrange)
              => is_tighter_than_bool (f (ZRange.normalize x_bs)) (ZRange.normalize output) = true).
        Local Notation bounds2_good f
          := (fun (output x_bs y_bs : zrange)
              => is_tighter_than_bool (f (ZRange.normalize x_bs) (ZRange.normalize y_bs)) (ZRange.normalize output) = true).
        Local Notation range_in_bitwidth r s
          := (is_tighter_than_bool (ZRange.normalize r) r[0~>s-1]%zrange = true).
        Local Notation shiftl_good := (bounds2_good ZRange.shiftl).
        Local Notation shiftr_good := (bounds2_good ZRange.shiftr).
        Local Notation land_good := (bounds2_good ZRange.land).
        Local Notation mul_good := (bounds2_good ZRange.mul).
        Local Notation cc_m_good output s := (bounds1_good (ZRange.cc_m s) output).
        Local Notation lit_good x rx := (is_bounded_by_bool x (ZRange.normalize rx)).

        Definition fancy_with_casts_rewrite_rules : rewrite_rulesT
          := Eval cbv [Make.interp_rewrite_rules myapp myflatten] in
              myflatten
                [reify
                   [(*
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y << 128) --> (add 128) @@ (x, y)
(Z.add_get_carry_concrete 2^256) @@ (?x << 128, ?y) --> (add 128) @@ (y, x)
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y >> 128) --> (add (- 128)) @@ (x, y)
(Z.add_get_carry_concrete 2^256) @@ (?x >> 128, ?y) --> (add (- 128)) @@ (y, x)
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y)        --> (add 0) @@ (y, x)
                     *)
                     (forall r rs s rx x rshiftl rland ry y rmask mask roffset offset,
                         s = 2^Z.log2 s -> s ∈ rs -> offset ∈ roffset -> mask ∈ rmask -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                         -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftl ((cstZ rland (cstZ ry y &' cstZ rmask ('mask))) << cstZ roffset ('offset))))
                            = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) (offset)) (cstZ rx x, cstZ ry y)))
                     ; (forall r rs s rx x rshiftl rland ry y rmask mask roffset offset,
                           (s = 2^Z.log2 s) -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s) -> s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s
                           -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftl (cstZ rland (cstZ ry y &' cstZ rmask ('mask)) << cstZ roffset ('offset))))
                              = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) offset) (cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rshiftl rland ry y rmask mask roffset offset rx x,
                           s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                           -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))) (cstZ rx x))
                              = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) offset) (cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rx x rshiftr ry y roffset offset,
                           s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                           -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                              = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) (-offset)) (cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rshiftr ry y roffset offset rx x,
                           s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                           -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))) (cstZ rx x))
                              = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) (-offset)) (cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rx x ry y,
                           s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                           -> cstZZ r (Z.add_get_carry_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
                              = cstZZ r (ident.interp (ident.fancy_add (Z.log2 s) 0) (cstZ rx x, cstZ ry y)))

                     (*
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y << 128) --> (addc 128) @@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x << 128, ?y) --> (addc 128) @@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y >> 128) --> (addc (- 128)) @@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x >> 128, ?y) --> (addc (- 128)) @@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y)        --> (addc 0) @@ (c, y, x)
                      *)
                     ; (forall r rs s rc c rx x rshiftl rland ry y rmask mask roffset offset,
                           s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> land_good rland ry mask -> range_in_bitwidth rshiftl s -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                           -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))))
                              = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) offset) (cstZ rc c, cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rc c rshiftl rland ry y rmask mask roffset offset rx x,
                           s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> range_in_bitwidth rshiftl s -> land_good rland ry mask -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                           -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))) (cstZ rx x))
                              = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) offset) (cstZ rc c, cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rc c rx x rshiftr ry y roffset offset,
                           s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                           -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                              = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) (-offset)) (cstZ rc c, cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rc c rshiftr ry y roffset offset rx x,
                           s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                           -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))) (cstZ rx x))
                              = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) (-offset)) (cstZ rc c, cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rc c rx x ry y,
                           s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                           -> cstZZ r (Z.add_with_get_carry_full (cstZ rs ('s)) (cstZ rc c) (cstZ rx x) (cstZ ry y))
                              = cstZZ r (ident.interp (ident.fancy_addc (Z.log2 s) 0) (cstZ rc c, cstZ rx x, cstZ ry y)))

                     (*
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y << 128) --> (sub 128) @@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y >> 128) --> (sub (- 128)) @@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y)        --> (sub 0) @@ (y, x)
                      *)

                     ; (forall r rs s rx x rshiftl rland ry y rmask mask roffset offset,
                           s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> range_in_bitwidth rshiftl s -> land_good rland ry mask -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                           -> cstZZ r (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))))
                              = cstZZ r (ident.interp (ident.fancy_sub (Z.log2 s) offset) (cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rx x rshiftr ry y roffset offset,
                           s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                           -> cstZZ r (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                              = cstZZ r (ident.interp (ident.fancy_sub (Z.log2 s) (-offset)) (cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rx x ry y,
                           s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                           -> cstZZ r (Z.sub_get_borrow_full (cstZ rs ('s)) (cstZ rx x) (cstZ ry y))
                              = cstZZ r (ident.interp (ident.fancy_sub (Z.log2 s) 0) (cstZ rx x, cstZ ry y)))

                     (*
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y << 128) --> (subb 128) @@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y >> 128) --> (subb (- 128)) @@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y)        --> (subb 0) @@ (c, y, x)
                      *)

                     ; (forall r rs s rb b rx x rshiftl rland ry y rmask mask roffset offset,
                           s ∈ rs -> mask ∈ rmask -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftl_good rshiftl rland offset -> range_in_bitwidth rshiftl s -> land_good rland ry mask -> (mask = Z.ones (Z.log2 s - offset)) -> (0 <= offset <= Z.log2 s)
                           -> cstZZ r (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rb b) (cstZ rx x) (cstZ rshiftl (Z.shiftl (cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask)))) (cstZ roffset ('offset)))))
                              = cstZZ r (ident.interp (ident.fancy_subb (Z.log2 s) offset) (cstZ rb b, cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rb b rx x rshiftr ry y roffset offset,
                           s ∈ rs -> offset ∈ roffset -> (s = 2^Z.log2 s) -> shiftr_good rshiftr ry offset -> range_in_bitwidth rshiftr s
                           -> cstZZ r (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rb b) (cstZ rx x) (cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset)))))
                              = cstZZ r (ident.interp (ident.fancy_subb (Z.log2 s) (-offset)) (cstZ rb b, cstZ rx x, cstZ ry y)))

                     ; (forall r rs s rb b rx x ry y,
                           s ∈ rs -> (s = 2^Z.log2 s) -> range_in_bitwidth ry s
                           -> cstZZ r (Z.sub_with_get_borrow_full (cstZ rs ('s)) (cstZ rb b) (cstZ rx x) (cstZ ry y))
                              = cstZZ r (ident.interp (ident.fancy_subb (Z.log2 s) 0) (cstZ rb b, cstZ rx x, cstZ ry y)))

                     (*(Z.rshi_concrete 2^256 ?n) @@ (?c, ?x, ?y) --> (rshi n) @@ (x, y)*)

                     ; (forall r rs s rx x ry y rn n,
                           s ∈ rs -> n ∈ rn -> (s = 2^Z.log2 s)
                           -> cstZ r (Z.rshi (cstZ rs ('s)) (cstZ rx x) (cstZ ry y) (cstZ rn ('n)))
                              = cstZ r (ident.interp (ident.fancy_rshi (Z.log2 s) n) (cstZ rx x, cstZ ry y)))

                     (*
Z.zselect @@ (Z.cc_m_concrete 2^256 ?c, ?x, ?y) --> selm @@ (c, x, y)
Z.zselect @@ (?c &' 1, ?x, ?y)                  --> sell @@ (c, x, y)
Z.zselect @@ (?c, ?x, ?y)                       --> selc @@ (c, x, y)
                      *)
                     ; (forall r rccm rs s rc c rx x ry y,
                           s ∈ rs -> (s = 2^Z.log2 s) -> cc_m_good rccm s rc
                           -> cstZ r (Z.zselect (cstZ rccm (Z.cc_m (cstZ rs ('s)) (cstZ rc c))) (cstZ rx x) (cstZ ry y))
                              = cstZ r (ident.interp (ident.fancy_selm (Z.log2 s)) (cstZ rc c, cstZ rx x, cstZ ry y)))

                     ; (forall r rland r1 rc c rx x ry y,
                           1 ∈ r1 -> land_good rland 1 rc
                           -> cstZ r (Z.zselect (cstZ rland (cstZ r1 1 &' cstZ rc c)) (cstZ rx x) (cstZ ry y))
                              = cstZ r (ident.interp ident.fancy_sell (cstZ rc c, cstZ rx x, cstZ ry y)))

                     ; (forall r rland rc c r1 rx x ry y,
                           1 ∈ r1 -> land_good rland rc 1
                           -> cstZ r (Z.zselect (cstZ rland (cstZ rc c &' cstZ r1 1)) (cstZ rx x) (cstZ ry y))
                              = cstZ r (ident.interp ident.fancy_sell (cstZ rc c, cstZ rx x, cstZ ry y)))

                     ; (forall r c x y,
                           cstZ r (Z.zselect c x y)
                           = cstZ r (ident.interp ident.fancy_selc (c, x, y)))

                     (*Z.add_modulo @@ (?x, ?y, ?m) --> addm @@ (x, y, m)*)
                     ; (forall x y m,
                           Z.add_modulo x y m
                           = ident.interp ident.fancy_addm (x, y, m))

                     (*
Z.mul @@ (?x &' (2^128-1), ?y &' (2^128-1)) --> mulll @@ (x, y)
Z.mul @@ (?x &' (2^128-1), ?y >> 128)       --> mullh @@ (x, y)
Z.mul @@ (?x >> 128, ?y &' (2^128-1))       --> mulhl @@ (x, y)
Z.mul @@ (?x >> 128, ?y >> 128)             --> mulhh @@ (x, y)
                      *)
                     (* literal on left *)
                     ; (forall r rx x rland ry y rmask mask,
                           plet s := (2*Z.log2_up mask)%Z in
                            plet xo := invert_low s x in
                            plet xv := match xo with Some x => x | None => 0 end in
                            xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland ry mask
                            -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask))))
                               = cstZ r (ident.interp (ident.fancy_mulll s) ('xv, cstZ ry y)))

                     ; (forall r rx x rland rmask mask ry y,
                           plet s := (2*Z.log2_up mask)%Z in
                            plet xo := invert_low s x in
                            plet xv := match xo with Some x => x | None => 0 end in
                            xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask ry
                            -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ ry y)))
                               = cstZ r (ident.interp (ident.fancy_mulll s) ('xv, cstZ ry y)))

                     ; (forall r rx x rshiftr ry y roffset offset,
                           plet s := (2*offset)%Z in
                            plet xo := invert_low s x in
                            plet xv := match xo with Some x => x | None => 0 end in
                            xo <> None -> x ∈ rx -> offset ∈ roffset -> shiftr_good rshiftr ry offset
                            -> cstZ r (cstZ rx ('x) * cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                               = cstZ r (ident.interp (ident.fancy_mullh s) ('xv, cstZ ry y)))

                     ; (forall r rx x rland rmask mask ry y,
                           plet s := (2*Z.log2_up mask)%Z in
                            plet xo := invert_high s x in
                            plet xv := match xo with Some x => x | None => 0 end in
                            xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask ry
                            -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ ry y)))
                               = cstZ r (ident.interp (ident.fancy_mulhl s) ('xv, cstZ ry y)))

                     ; (forall r rx x rland ry y rmask mask,
                           plet s := (2*Z.log2_up mask)%Z in
                            plet xo := invert_high s x in
                            plet xv := match xo with Some x => x | None => 0 end in
                            xo <> None -> x ∈ rx -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland ry mask
                            -> cstZ r (cstZ rx ('x) * cstZ rland (Z.land (cstZ ry y) (cstZ rmask ('mask))))
                               = cstZ r (ident.interp (ident.fancy_mulhl s) ('xv, cstZ ry y)))

                     ; (forall r rx x rshiftr ry y roffset offset,
                           plet s := (2*offset)%Z in
                            plet xo := invert_high s x in
                            plet xv := match xo with Some x => x | None => 0 end in
                            xo <> None -> x ∈ rx -> offset ∈ roffset -> shiftr_good rshiftr ry offset
                            -> cstZ r (cstZ rx ('x) * cstZ rshiftr (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                               = cstZ r (ident.interp (ident.fancy_mulhh s) ('xv, cstZ ry y)))

                     (* literal on right *)
                     ; (forall r rland rmask mask rx x ry y,
                           plet s := (2*Z.log2_up mask)%Z in
                            plet yo := invert_low s y in
                            plet yv := match yo with Some y => y | None => 0 end in
                            yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask rx
                            -> cstZ r (cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ rx x)) * cstZ ry ('y))
                               = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, 'yv)))

                     ; (forall r rland rx x rmask mask ry y,
                           plet s := (2*Z.log2_up mask)%Z in
                            plet yo := invert_low s y in
                            plet yv := match yo with Some y => y | None => 0 end in
                            yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland rx mask
                            -> cstZ r (cstZ rland (Z.land (cstZ rx x) (cstZ rmask ('mask))) * cstZ ry ('y))
                               = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, 'yv)))

                     ; (forall r rland rmask mask rx x ry y,
                           plet s := (2*Z.log2_up mask)%Z in
                            plet yo := invert_high s y in
                            plet yv := match yo with Some y => y | None => 0 end in
                            yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland mask rx
                            -> cstZ r (cstZ rland (Z.land (cstZ rmask ('mask)) (cstZ rx x)) * cstZ ry ('y))
                               = cstZ r (ident.interp (ident.fancy_mullh s) (cstZ rx x, 'yv)))

                     ; (forall r rland rx x rmask mask ry y,
                           plet s := (2*Z.log2_up mask)%Z in
                            plet yo := invert_high s y in
                            plet yv := match yo with Some y => y | None => 0 end in
                            yo <> None -> y ∈ ry -> mask ∈ rmask -> (mask = 2^(s/2)-1) -> land_good rland rx mask
                            -> cstZ r (cstZ rland (Z.land (cstZ rx x) (cstZ rmask ('mask))) * cstZ ry ('y))
                               = cstZ r (ident.interp (ident.fancy_mullh s) (cstZ rx x, 'yv)))

                     ; (forall r rshiftr rx x roffset offset ry y,
                           plet s := (2*offset)%Z in
                            plet yo := invert_low s y in
                            plet yv := match yo with Some y => y | None => 0 end in
                            yo <> None -> y ∈ ry -> offset ∈ roffset -> shiftr_good rshiftr rx offset
                            -> cstZ r (cstZ rshiftr (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ ry ('y))
                               = cstZ r (ident.interp (ident.fancy_mulhl s) (cstZ rx x, 'yv)))

                     ; (forall r rshiftr rx x roffset offset ry y,
                           plet s := (2*offset)%Z in
                            plet yo := invert_high s y in
                            plet yv := match yo with Some y => y | None => 0 end in
                            yo <> None -> y ∈ ry -> offset ∈ roffset -> shiftr_good rshiftr rx offset
                            -> cstZ r (cstZ rshiftr (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ ry ('y))
                               = cstZ r (ident.interp (ident.fancy_mulhh s) (cstZ rx x, 'yv)))

                     (* no literal *)
                     ; (forall r rland1 rmask1 mask1 rx x rland2 rmask2 mask2 ry y,
                           plet s := (2*Z.log2_up mask1)%Z in
                            mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 mask1 rx -> land_good rland2 mask2 ry
                            -> cstZ r (cstZ rland1 (Z.land (cstZ rmask1 ('mask1)) (cstZ rx x)) * cstZ rland2 (Z.land (cstZ rmask2 ('mask2)) (cstZ ry y)))
                               = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, cstZ ry y)))

                     ; (forall r rland1 rx x rmask1 mask1 rland2 rmask2 mask2 ry y,
                           plet s := (2*Z.log2_up mask1)%Z in
                            mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 rx mask1 -> land_good rland2 mask2 ry
                            -> cstZ r (cstZ rland1 (Z.land (cstZ rx x) (cstZ rmask1 ('mask1))) * cstZ rland2 (Z.land (cstZ rmask2 ('mask2)) (cstZ ry y)))
                               = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, cstZ ry y)))

                     ; (forall r rland1 rmask1 mask1 rx x rland2 ry y rmask2 mask2,
                           plet s := (2*Z.log2_up mask1)%Z in
                            mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 mask1 rx -> land_good rland2 ry mask2
                            -> cstZ r (cstZ rland1 (Z.land (cstZ rmask1 ('mask1)) (cstZ rx x)) * cstZ rland2 (Z.land (cstZ ry y) (cstZ rmask2 ('mask2))))
                               = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, cstZ ry y)))

                     ; (forall r rland1 rx x rmask1 mask1 rland2 ry y rmask2 mask2,
                           plet s := (2*Z.log2_up mask1)%Z in
                            mask1 ∈ rmask1 -> mask2 ∈ rmask2 -> (mask1 = 2^(s/2)-1) -> (mask2 = 2^(s/2)-1) -> land_good rland1 rx mask1 -> land_good rland2 ry mask2
                            -> cstZ r (cstZ rland1 (Z.land (cstZ rx x) (cstZ rmask1 ('mask1))) * cstZ rland2 (Z.land (cstZ ry y) (cstZ rmask2 ('mask2))))
                               = cstZ r (ident.interp (ident.fancy_mulll s) (cstZ rx x, cstZ ry y)))

                     ; (forall r rland1 rmask mask rx x rshiftr2 ry y roffset offset,
                           plet s := (2*offset)%Z in
                            mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> land_good rland1 mask rx -> shiftr_good rshiftr2 ry offset
                            -> cstZ r (cstZ rland1 (Z.land (cstZ rmask ('mask)) (cstZ rx x)) * cstZ rshiftr2 (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                               = cstZ r (ident.interp (ident.fancy_mullh s) (cstZ rx x, cstZ ry y)))

                     ; (forall r rland1 rx x rmask mask rshiftr2 ry y roffset offset,
                           plet s := (2*offset)%Z in
                            mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> land_good rland1 rx mask -> shiftr_good rshiftr2 ry offset
                            -> cstZ r (cstZ rland1 (Z.land (cstZ rx x) (cstZ rmask ('mask))) * cstZ rshiftr2 (Z.shiftr (cstZ ry y) (cstZ roffset ('offset))))
                               = cstZ r (ident.interp (ident.fancy_mullh s) (cstZ rx x, cstZ ry y)))

                     ; (forall r rshiftr1 rx x roffset offset rland2 rmask mask ry y,
                           plet s := (2*offset)%Z in
                            mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> shiftr_good rshiftr1 rx offset -> land_good rland2 mask ry
                            -> cstZ r (cstZ rshiftr1 (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ rland2 (Z.land (cstZ rmask ('mask)) (cstZ ry y)))
                               = cstZ r (ident.interp (ident.fancy_mulhl s) (cstZ rx x, cstZ ry y)))

                     ; (forall r rshiftr1 rx x roffset offset rland2 ry y rmask mask,
                           plet s := (2*offset)%Z in
                            mask ∈ rmask -> offset ∈ roffset -> (mask = 2^(s/2)-1) -> shiftr_good rshiftr1 rx offset -> land_good rland2 ry mask
                            -> cstZ r (cstZ rshiftr1 (Z.shiftr (cstZ rx x) (cstZ roffset ('offset))) * cstZ rland2 (Z.land (cstZ ry y) (cstZ rmask ('mask))))
                               = cstZ r (ident.interp (ident.fancy_mulhl s) (cstZ rx x, cstZ ry y)))

                     ; (forall r rshiftr1 rx x roffset1 offset1 rshiftr2 ry y roffset2 offset2,
                           plet s := (2*offset1)%Z in
                            offset1 ∈ roffset1 -> offset2 ∈ roffset2 -> (offset1 = offset2) -> shiftr_good rshiftr1 rx offset1 -> shiftr_good rshiftr2 ry offset2
                            -> cstZ r (cstZ rshiftr1 (Z.shiftr (cstZ rx x) (cstZ roffset1 ('offset1))) * cstZ rshiftr2 (Z.shiftr (cstZ ry y) (cstZ roffset2 ('offset2))))
                               = cstZ r (ident.interp (ident.fancy_mulhh s) (cstZ rx x, cstZ ry y)))

                     (** Dummy rule to make sure we use the two value ranges; this can be removed *)
                     ; (forall rx x,
                           ((is_tighter_than_bool rx value_range = true)
                            \/ (is_tighter_than_bool rx flag_range = true))
                           -> cstZ rx x = cstZ rx x)
                   ]%Z%zrange
                ].

        Definition fancy_dtree'
          := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 fancy_rewrite_rules.
        Definition fancy_dtree : decision_tree
          := Eval compute in Option.invert_Some fancy_dtree'.
        Definition fancy_with_casts_dtree'
          := Eval compute in @compile_rewrites ident var pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq 100 fancy_with_casts_rewrite_rules.
        Definition fancy_with_casts_dtree : decision_tree
          := Eval compute in Option.invert_Some fancy_with_casts_dtree'.
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
      Notation "x <- 'type.try_make_transport_cps' t1 t2 ; f" := (type.try_make_transport_cps t1 t2 (fun y => match y with Datatypes.Some x => f | Datatypes.None => Datatypes.None end)) (at level 70, t1 at next level, t2 at next level, right associativity, format "'[v' x  <-  'type.try_make_transport_cps'  t1  t2 ; '/' f ']'").
      Notation "x <- 'base.try_make_transport_cps' t1 t2 ; f" := (base.try_make_transport_cps t1 t2 (fun y => match y with Datatypes.Some x => f | Datatypes.None => Datatypes.None end)) (at level 70, t1 at next level, t2 at next level, right associativity, format "'[v' x  <-  'base.try_make_transport_cps'  t1  t2 ; '/' f ']'").
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
                   pattern.type.subst_default pattern.base.subst_default pattern.base.lookup_default
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
