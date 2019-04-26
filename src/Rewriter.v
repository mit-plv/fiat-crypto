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
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Tactics.DebugPrint.
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
            := eta_ident_cps _ _ idc (fun t' idc' => assemble_identifier_rewriters' t' (rIdent true idc' (#idc')) (fun _ => id)).
        End with_do_again.
      End with_var.
      Global Arguments rew_should_do_again {_ _ _ _ _ _} _.
      Global Arguments rew_with_opt        {_ _ _ _ _ _} _.
      Global Arguments rew_under_lets      {_ _ _ _ _ _} _.
      Global Arguments rew_replacement     {_ _ _ _ _ _} _.

      Ltac compute_with_fuel f fuel :=
        lazymatch (eval compute in (f fuel)) with
        | Some ?res => res
        | None => compute_with_fuel f (10 + fuel * 10)%nat
        | ?res => fail 0 "Invalid result of computing" f "with fuel" fuel ":" res
        end.

      Ltac compile_rewrites ident var pident pident_arg_types raw_pident strip_types raw_pident_beq ps
        := compute_with_fuel (fun fuel : nat => @compile_rewrites ident var pident pident_arg_types raw_pident strip_types raw_pident_beq fuel ps) 100%nat (* initial value of depth of patterns; doesn't matter too much *).
      Ltac CompileRewrites ident pident pident_arg_types raw_pident strip_types raw_pident_beq ps :=
        let var := fresh "var" in
        let res
            := lazymatch constr:(
                           fun var : Compilers.type.type Compilers.base.type -> Type
                           => ltac:(let res := compile_rewrites ident var pident pident_arg_types raw_pident strip_types raw_pident_beq (ps var) in
                                    exact res))
               with
               | fun _ => ?res => res
               end in
        let dtree := fresh "dtree" in
        cache_term res dtree.

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
            returned. *)
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
              | ident.Z_combine_at_bitwidth
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

        Fixpoint pair'_unification_resultT' {A evm t p}
          : @unification_resultT' (fun _ => positive) t p evm -> @unification_resultT' value t p evm -> PositiveMap.t { t : _ & value t } * (A -> list bool) -> PositiveMap.t { t : _ & value t } * (A -> list bool)
          := match p return @unification_resultT' (fun _ => positive) _ p evm -> @unification_resultT' value _ p evm -> PositiveMap.t { t : _ & value t } * (A -> list bool) -> PositiveMap.t { t : _ & value t } * (A -> list bool) with
             | pattern.Wildcard t => fun p v '(m, l) => (PositiveMap.add p (existT value _ v) m, l)
             | pattern.Ident t idc => fun v1 v2 '(m, l) => (m, fun a => pident_type_of_list_arg_types_beq t idc v2 v1 :: l a)
             | pattern.App _ _ F X
               => fun x y '(m, l)
                  => let '(m, l) := @pair'_unification_resultT' _ _ _ F (fst x) (fst y) (m, l) in
                     let '(m, l) := @pair'_unification_resultT' _ _ _ X (snd x) (snd y) (m, l) in
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

        Inductive lookup_gets_inlined_error_messages :=
        | NO_SUCH_EXPRESSION_TO_CHECK (p : positive) (m : PositiveMap.t { t : _ & value t })
        | TYPE_IS_NOT_BASE (p : positive) (m : PositiveMap.t { t : _ & value t }) (t : type).

        Definition lookup_expr_gets_inlined
                   (invalid : forall A B, A -> B)
                   (gets_inlined : forall t, value (type.base t) -> bool)
                   (m : PositiveMap.t { t : _ & value t })
                   (p : positive)
          : bool
          := Eval cbv -[value] in
              match PositiveMap.find p m with
              | Some (existT t e)
                => match t return value t -> _ with
                   | type.base t => gets_inlined t
                   | _ => invalid _ _ (TYPE_IS_NOT_BASE p m t)
                   end e
              | None => invalid _ _ (NO_SUCH_EXPRESSION_TO_CHECK p m)
              end.

        Definition expr_to_pattern_and_replacement
                   (gets_inlined : forall t, value (type.base t) -> bool)
                   (should_do_again : bool) evm
                   (invalid : forall A B, A -> B)
                   {t} (lhs rhs : @expr.expr base.type ident (fun _ => positive) t)
                   (side_conditions : (positive -> bool) -> list bool)
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
                         let side_conditions := side_conditions (lookup_expr_gets_inlined invalid gets_inlined value_map) in
                         let start_i := Pos.succ (PositiveMap.fold (fun k _ max => Pos.max k max) value_map 1%positive) in
                         let replacement := expr_pos_to_expr_value (fun _ => invalid _ _) rhs value_map start_i in
                         let replacement := expr_value_to_rewrite_rule_replacement should_do_again replacement in
                         if fold_left andb (List.rev side_conditions) true
                         then Some replacement
                         else None))).


        Definition expr_to_pattern_and_replacement_unfolded gets_inlined should_do_again evm invalid {t} lhs rhs side_conditions
          := Eval cbv beta iota delta [expr_to_pattern_and_replacement lookup_expr_gets_inlined pattern_of_expr lam_unification_resultT' Pos.succ pair'_unification_resultT' PositiveMap.empty PositiveMap.fold Pos.max expr_pos_to_expr_value (* expr_value_to_rewrite_rule_replacement*) fold_left List.rev List.app value PositiveMap.add PositiveMap.xfoldi Pos.compare Pos.compare_cont FMapPositive.append projT1 projT2 PositiveMap.find Base_value (*UnderLets.map reify_expr_beta_iota reflect_expr_beta_iota*) lam_type_of_list fold_right list_rect pattern.type.relax pattern.type.subst_default pattern.type.subst_default_relax pattern.type.unsubst_default_relax option_map unification_resultT' with_unification_resultT' with_unif_rewrite_ruleTP_gen']
            in @expr_to_pattern_and_replacement gets_inlined should_do_again evm invalid t lhs rhs side_conditions.

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
          => let __ := lazymatch type of H with
                       | Prop => constr:(I)
                       | ?T => constr_fail_with ltac:(fun _ => fail 1 "Invalid non-Prop non-dependent hypothesis of type" H ":" T "when reifying a lemma of type" lem)
                       end in
             let H := prop_to_bool H in
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

      Ltac under_binders payload term cont ctx :=
        lazymatch term with
        | (fun x : ?T => ?f)
          => let ctx' := fresh in
             let f' := fresh in
             let payload' := fresh in (* COQBUG(https://github.com/coq/coq/issues/7210#issuecomment-470009463) *)
             constr:(match payload return _ with
                     | payload'
                       => fun x : T
                          => match f, dyncons x ctx return _ with
                             | f', ctx'
                               => ltac:(let ctx := (eval cbv delta [ctx'] in ctx') in
                                        let f := (eval cbv delta [f'] in f') in
                                        let payload := (eval cbv delta [payload'] in payload') in
                                        clear f' ctx' payload';
                                        let res := under_binders payload f cont ctx in
                                        exact res)
                             end
                     end)
        | ?term => cont payload ctx term
        end.
      Ltac substitute_with term x y :=
        lazymatch (eval pattern y in term) with
        | (fun z => ?term) _ => constr:(match x return _ with z => term end)
        end.
      Ltac substitute_beq_with only_eliminate_in_ctx full_ctx term beq x :=
        let is_good y :=
            lazymatch full_ctx with
            | context[dyncons y _] => fail
            | _ => is_var y;
                   lazymatch only_eliminate_in_ctx with
                   | context[y] => idtac
                   end
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

      Ltac substitute_beq only_eliminate_in_ctx full_ctx ctx term :=
        lazymatch ctx with
        | dynnil
          => let term := (eval cbv [base.interp_beq base.base_interp_beq] in term) in
             let term := substitute_bool_eqb term in
             let term := remove_andb_true term in
             let term := adjust_if_negb term in
             term
        | dyncons ?v ?ctx
          => let term := substitute_beq_with only_eliminate_in_ctx full_ctx term zrange_beq v in
             let term := substitute_beq_with only_eliminate_in_ctx full_ctx term Z.eqb v in
             let term := match constr:(Set) with
                         | _ => let T := type of v in
                                let beq := (eval cbv beta delta [Reflect.decb_rel] in (Reflect.decb_rel (@eq T))) in
                                substitute_beq_with only_eliminate_in_ctx full_ctx term beq v
                         | _ => term
                         end in
             substitute_beq only_eliminate_in_ctx full_ctx ctx term
        end.

      Ltac deep_substitute_beq only_eliminate_in_ctx term :=
        lazymatch term with
        | context term'[@Build_rewrite_rule_data ?ident ?var ?pident ?pident_arg_types ?t ?p ?sda ?wo ?ul ?subterm]
          => let subterm := under_binders only_eliminate_in_ctx subterm ltac:(fun only_eliminate_in_ctx ctx term => substitute_beq only_eliminate_in_ctx ctx ctx term) dynnil in
             let term := context term'[@Build_rewrite_rule_data ident var pident pident_arg_types t p sda wo ul subterm] in
             term
        end.

      Ltac clean_beq only_eliminate_in_ctx term :=
        let term := (eval cbn [Prod.prod_beq] in term) in
        let term := (eval cbv [ident.literal] in term) in
        let term := deep_substitute_beq only_eliminate_in_ctx term in
        let term := (eval cbv [base.interp_beq base.base_interp_beq] in term) in
        let term := remove_andb_true term in
        term.

      Ltac adjust_side_conditions_for_gets_inlined' value_ctx side_conditions lookup_gets_inlined :=
        lazymatch side_conditions with
        | context sc[ident.gets_inlined _ ?x]
          => lazymatch value_ctx with
             | context[expr.var_context.cons x ?p _]
               => let rep := constr:(lookup_gets_inlined p) in
                  let side_conditions := context sc[rep] in
                  adjust_side_conditions_for_gets_inlined' value_ctx side_conditions lookup_gets_inlined
             | _ => constr_fail_with ltac:(fun _ => fail 1 "Could not find an expression corresponding to" x "in context" value_ctx)
             end
        | _ => side_conditions
        end.

      Ltac adjust_side_conditions_for_gets_inlined value_ctx side_conditions :=
        let lookup_gets_inlined := fresh in
        constr:(fun lookup_gets_inlined : positive -> bool
                => ltac:(let v := adjust_side_conditions_for_gets_inlined' value_ctx side_conditions lookup_gets_inlined in
                         exact v)).

      Ltac reify_to_pattern_and_replacement_in_context ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota type_ctx var gets_inlined should_do_again cur_i term value_ctx :=
        let t := fresh "t" in
        let p := fresh "p" in
        let reify_rec_gen type_ctx := reify_to_pattern_and_replacement_in_context ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota type_ctx var gets_inlined should_do_again in
        let var_pos := constr:(fun _ : type base.type => positive) in
        let value := constr:(@value base.type ident var) in
        let cexpr_to_pattern_and_replacement_unfolded := constr:(@expr_to_pattern_and_replacement_unfolded ident var pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident (reflect_ident_iota var) gets_inlined should_do_again type_ctx) in
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
             let side_conditions := adjust_side_conditions_for_gets_inlined value_ctx side_conditions in
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
             let res := clean_beq value_ctx res in
             res
        end.

      Ltac reify ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var gets_inlined should_do_again lem :=
        reify_under_forall_types
          lem
          ltac:(
          fun ty_ctx cur_i lem
          => let lem := equation_to_parts lem in
             let res := reify_to_pattern_and_replacement_in_context ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota ty_ctx var gets_inlined should_do_again constr:(1%positive) lem (@expr.var_context.nil base.type (fun _ => positive)) in
             res).

      Ltac Reify ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota gets_inlined should_do_again lem :=
        let var := fresh "var" in
        constr:(fun var : Compilers.type.type Compilers.base.type -> Type
                => ltac:(let res := reify ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var (gets_inlined var) should_do_again lem in
                         exact res)).

      (* lems is either a list of [Prop]s, or a list of [bool (* should_do_again *) * Prop] *)
      Ltac reify_list ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var gets_inlined lems :=
        let reify' := reify ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var gets_inlined in
        let reify_list_rec := reify_list ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var gets_inlined in
        lazymatch (eval hnf in lems) with
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

      Ltac Reify_list ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota gets_inlined lems :=
        let var := fresh "var" in
        constr:(fun var : Compilers.type.type Compilers.base.type -> Type
                => ltac:(let res := reify_list ident reify_ident pident pident_arg_types pident_type_of_list_arg_types_beq pident_of_typed_ident pident_arg_types_of_typed_ident reflect_ident_iota var (gets_inlined var) lems in
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

        Let pident_pair
          := ltac:(let v := (eval cbv in
                                (fun A B => pattern.ident.of_typed_ident (@ident.pair A B))) in
                   let h := lazymatch v with fun A B => ?f _ _ => f end in
                   exact h).

        Fixpoint make_Literal_pattern (t : pattern.base.type) : option (pattern t)
          := match t return option (pattern t) with
             | pattern.base.type.var _ => None
             | pattern.base.type.type_base t => Some (make_base_Literal_pattern t)
             | pattern.base.type.prod A B
               => (a <- make_Literal_pattern A;
                    b <- make_Literal_pattern B;
                    Some ((#(pident_pair _ _) @ a @ b)%pattern))
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

      Module Import AdjustRewriteRulesForReduction.
        Import PrimitiveHList.
        (* N.B. The [combine_hlist] call MUST eta-expand
           [pr2_rewrite_rules].  That is, it MUST NOT block reduction
           of the resulting list of cons cells on the pair-structure
           of [pr2_rewrite_rules].  This is required so that we can
           use [cbv -] to unfold the entire decision tree
           evaluation, including choosing which rewrite rule to apply
           and binding its arguments, without unfolding any of the
           identifiers used to define the replacement value.  (The
           symptom of messing this up is that the [cbv -] will run out
           of memory when trying to reduce things.)  We accomplish
           this by making [hlist] based on a primitive [prod] type
           with judgmental η, so that matching on its structure never
           blocks reduction. *)
        Ltac make_split_rewrite_rules rewrite_rules :=
          let split_rewrite_rules := fresh "split_rewrite_rules" in
          let v := constr:(fun var => split_list (rewrite_rules var)) in
          let h := head rewrite_rules in
          let do_reduce_rules := lazymatch h with
                                 | @cons => false
                                 | @nil => false
                                 | _ => true
                                 end in
          let v := lazymatch do_reduce_rules with
                   | true => (eval cbv [split_list projT1 projT2 h] in v)
                   | false => (eval cbv [split_list projT1 projT2] in v)
                   end in
          cache_term v split_rewrite_rules.
        Ltac make_pr1_rewrite_rules split_rewrite_rules :=
          let var := fresh "var" in
          constr:(fun var => ltac:(let v := (eval hnf in (projT1 (split_rewrite_rules var))) in
                                   exact v)).
        Ltac make_pr2_rewrite_rules split_rewrite_rules :=
          let pr2_rewrite_rules := fresh "pr2_rewrite_rules" in
          let var := fresh "var" in
          let v :=
              constr:(fun var
                      => ltac:(let v := (eval hnf in (projT2 (split_rewrite_rules var))) in
                               exact v)) in
          cache_term v pr2_rewrite_rules.

        Ltac make_all_rewrite_rules pr1_rewrite_rules pr2_rewrite_rules :=
          let all_rewrite_rules := fresh "all_rewrite_rules" in
          let var := fresh "var" in
          cache_term
            (fun var
             => combine_hlist (P:=@Compile.rewrite_ruleTP ident var pattern.ident (@pattern.ident.arg_types)) (pr1_rewrite_rules var) (pr2_rewrite_rules var))
            all_rewrite_rules.
      End AdjustRewriteRulesForReduction.

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

      Definition pident_unify_unknown := @pattern.ident.unify.
      Definition invert_bind_args_unknown := @pattern.Raw.ident.invert_bind_args.

      Module Export GoalType.
        Record rewriter_dataT :=
          Build_rewriter_dataT'
            {
              rewrite_rules_specs : list (bool * Prop);
              dummy_count : nat;
              dtree : @Compile.decision_tree pattern.Raw.ident;

              rewrite_rules : forall var, @Compile.rewrite_rulesT ident var pattern.ident (@pattern.ident.arg_types) ;
              all_rewrite_rules (* adjusted version *) : _;
              all_rewrite_rules_eq : all_rewrite_rules = rewrite_rules;

              default_fuel : nat;

              rewrite_head0
              := (fun var
                  => @Compile.assemble_identifier_rewriters ident var (@pattern.ident.eta_ident_cps) (@pattern.ident) (@pattern.ident.arg_types) (@pattern.ident.unify) pident_unify_unknown pattern.Raw.ident (@pattern.Raw.ident.full_types) (@pattern.Raw.ident.invert_bind_args) invert_bind_args_unknown (@pattern.Raw.ident.type_of) (@pattern.Raw.ident.to_typed) pattern.Raw.ident.is_simple dtree (all_rewrite_rules var));
              rewrite_head (* adjusted version *) : forall var (do_again : forall t, @defaults.expr (@Compile.value _ ident var) (type.base t) -> @UnderLets.UnderLets _ ident var (@defaults.expr var (type.base t)))
                                     t (idc : ident t), @Compile.value_with_lets base.type ident var t;
              rewrite_head_eq : rewrite_head = rewrite_head0
            }.
      End GoalType.
      Definition Rewrite (data : rewriter_dataT) {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
        := @Compile.Rewrite (rewrite_head data) (default_fuel data) t e.

      Ltac Reify include_interp specs :=
        let lems := Reify.Reify_list ident ident.reify pattern.ident (@pattern.ident.arg_types_unfolded) (@pattern.ident.type_of_list_arg_types_beq_unfolded) (@pattern.ident.of_typed_ident_unfolded) (@pattern.ident.arg_types_of_typed_ident_unfolded) (@Compile.reflect_ident_iota) (fun var t => @SubstVarLike.is_var_fst_snd_pair_opp_cast var (type.base t)) specs in
        lazymatch include_interp with
        | true
          => let myapp := (eval cbv [List.app] in (@List.app)) in
             let res := (eval cbv [interp_rewrite_rules] in
                            (fun var => myapp _ (@interp_rewrite_rules var) (lems var))) in
             let len := lazymatch (eval compute in (fun var => List.length (@interp_rewrite_rules var))) with (fun _ => ?n) => n end in
             let adjusted_specs := (eval cbv [List.app List.repeat] in
                                       (List.app
                                          (List.repeat (false, forall A (x : A), x = x) len))) in
             constr:((len, adjusted_specs specs, res))
        | false => constr:((O, specs, lems))
        | _ => constr_fail_with ltac:(fun _ => fail 1 "Invalid value for include_interp (must be either true or false):" include_interp)
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

      Ltac make_rewrite_head1 rewrite_head0 pr2_rewrite_rules :=
        time_tac_in_constr_if_debug1
          ltac:(fun _
                => let rewrite_head1
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
                   rewrite_head1).
      Ltac make_rewrite_head2 rewrite_head1 pr2_rewrite_rules :=
        time_tac_in_constr_if_debug1
          ltac:(fun _
                => (eval cbv [id
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
                                (*rlist_rect rwhen rwhenl*)
                             ] in rewrite_head1)).
      Ltac make_rewrite_head3 rewrite_head2 :=
        time_tac_in_constr_if_debug1
          ltac:(fun _
                => (eval cbn [id
                                cpsbind cpscall cps_option_bind cpsreturn
                                Compile.reify Compile.reify_and_let_binds_cps Compile.reflect Compile.value'
                                Option.sequence Option.sequence_return Option.bind
                                UnderLets.reify_and_let_binds_base_cps
                                UnderLets.splice UnderLets.splice_list UnderLets.to_expr
                                base.interp base.base_interp
                                base.type.base_beq option_beq
                                type.try_make_transport_cps base.try_make_transport_cps base.try_make_base_transport_cps
                                Datatypes.fst Datatypes.snd
                             ] in rewrite_head2)).
      Ltac make_rewrite_head' rewrite_head0 pr2_rewrite_rules :=
        let rewrite_head1 := make_rewrite_head1 rewrite_head0 pr2_rewrite_rules in
        let rewrite_head2 := make_rewrite_head2 rewrite_head1 pr2_rewrite_rules in
        let rewrite_head3 := make_rewrite_head3 rewrite_head2 in
        rewrite_head3.

      Ltac make_rewrite_head rewrite_head0 pr2_rewrite_rules :=
        let rewrite_head := fresh "rewrite_head" in
        let var := fresh "var" in
        let do_again := fresh "do_again" in
        let t := fresh "t" in
        let idc := fresh "idc" in
        let v :=
            constr:(
              fun var (do_again : forall t, @defaults.expr (@Compile.value _ ident var) (type.base t) -> @UnderLets.UnderLets _ ident var (@defaults.expr var (type.base t)))
                  t (idc : ident t)
              => ltac:(
                   let rewrite_head0 := constr:(rewrite_head0 var do_again t idc) in
                   let pr2_rewrite_rules := head pr2_rewrite_rules in
                   let v := make_rewrite_head' rewrite_head0 pr2_rewrite_rules in
                   exact v)) in
        cache_term v rewrite_head.

      Ltac Build_rewriter_dataT include_interp specs :=
        let __ := debug1 ltac:(fun _ => idtac "Reifying...") in
        let specs_lems := Reify include_interp specs in
        let dummy_count := lazymatch specs_lems with (?n, ?specs, ?lems) => n end in
        let specs := lazymatch specs_lems with (?n, ?specs, ?lems) => specs end in
        let rewrite_rules := lazymatch specs_lems with (?n, ?specs, ?lems) => lems end in
        let rewrite_rules_names := fresh "rewrite_rules" in
        let rewrite_rules := cache_term rewrite_rules rewrite_rules_names in
        let __ := debug1 ltac:(fun _ => idtac "Compiling decision tree...") in
        let dtree := Compile.CompileRewrites ident pattern.ident (@pattern.ident.arg_types) pattern.Raw.ident (@pattern.ident.strip_types) pattern.Raw.ident.ident_beq rewrite_rules in
        let default_fuel := (eval compute in (List.length specs)) in
        let __ := debug1 ltac:(fun _ => idtac "Splitting rewrite rules...") in
        let split_rewrite_rules := make_split_rewrite_rules rewrite_rules in
        let pr1_rewrite_rules := make_pr1_rewrite_rules split_rewrite_rules in
        let pr2_rewrite_rules := make_pr2_rewrite_rules split_rewrite_rules in
        let all_rewrite_rules := make_all_rewrite_rules pr1_rewrite_rules pr2_rewrite_rules in
        let __ := debug1 ltac:(fun _ => idtac "Assembling rewrite_head...") in
        let rewrite_head0 := fresh "rewrite_head0" in
        let var := fresh "var" in
        let rewrite_head0
            := cache_term
                 (fun var
                  => @Compile.assemble_identifier_rewriters ident var (@pattern.ident.eta_ident_cps) (@pattern.ident) (@pattern.ident.arg_types) (@pattern.ident.unify) pident_unify_unknown pattern.Raw.ident (@pattern.Raw.ident.full_types) (@pattern.Raw.ident.invert_bind_args) invert_bind_args_unknown (@pattern.Raw.ident.type_of) (@pattern.Raw.ident.to_typed) pattern.Raw.ident.is_simple dtree (all_rewrite_rules var))
                 rewrite_head0 in
        let __ := debug1 ltac:(fun _ => idtac "Reducing rewrite_head...") in
        let rewrite_head := make_rewrite_head rewrite_head0 pr2_rewrite_rules in
        constr:(@Build_rewriter_dataT'
                  specs dummy_count dtree
                  rewrite_rules all_rewrite_rules eq_refl
                  default_fuel
                  (*rewrite_head0*) rewrite_head eq_refl).

      Module Export Tactic.
        Module Export Settings.
          Global Arguments base.try_make_base_transport_cps _ !_ !_.
          Global Arguments base.try_make_transport_cps _ !_ !_.
          Global Arguments type.try_make_transport_cps _ _ _ !_ !_.
          Global Arguments Option.sequence A !v1 v2.
          Global Arguments Option.sequence_return A !v1 v2.
          Global Arguments Option.bind A B !_ _.
          Global Arguments pattern.Raw.ident.invert_bind_args t !_ !_.
          Global Arguments base.type.base_beq !_ !_.
          Global Arguments id / .
        End Settings.

        Tactic Notation "make_rewriter_data" constr(include_interp) constr(specs) :=
          let res := Build_rewriter_dataT include_interp specs in refine res.
      End Tactic.
    End Make.
    Export Make.GoalType.
    Import Make.Tactic.

    Module Export GoalType.
      Record RewriterT :=
        {
          Rewriter_data : rewriter_dataT;
          Rewrite : forall {t} (e : expr.Expr (ident:=ident) t), expr.Expr (ident:=ident) t;
          Rewrite_eq : @Rewrite = @Make.Rewrite Rewriter_data
        }.
    End GoalType.

    Ltac Build_RewriterT include_interp specs :=
      let rewriter_data := fresh "rewriter_data" in
      let data := Make.Build_rewriter_dataT include_interp specs in
      let Rewrite_name := fresh "Rewriter" in
      let Rewrite := (eval cbv [Make.Rewrite rewrite_head default_fuel] in (@Make.Rewrite data)) in
      let Rewrite := cache_term Rewrite Rewrite_name in
      constr:(@Build_RewriterT data Rewrite eq_refl).

    Module Export Tactic.
      Module Export Settings.
        Export Make.Tactic.Settings.
      End Settings.

      Tactic Notation "make_Rewriter" constr(include_interp) constr(specs) :=
        let res := Build_RewriterT include_interp specs in refine res.
    End Tactic.
  End RewriteRules.
End Compilers.
