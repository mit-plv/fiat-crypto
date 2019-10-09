Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Lists.List.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.PrimitiveSigma.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Notations.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.IdentifiersBasicLibrary.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Tactics.DebugPrint.
Import ListNotations. Local Open Scope list_scope.
Import PrimitiveSigma.Primitive.

Import EqNotations.
Module Compilers.
  Set Boolean Equality Schemes.
  Set Decidable Equality Schemes.
  Local Set Primitive Projections.
  Import IdentifiersBasicLibrary.Compilers.
  Export Language.Compilers.

  Local Notation type_of_list := (fold_right (fun A B => prod A B) unit).
  Local Notation type_of_list_cps := (fold_right (fun a K => a -> K)).
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

  Fixpoint list_app_type_of_list {ls1 ls2 : list Type} : type_of_list ls1 -> type_of_list ls2 -> type_of_list (ls1 ++ ls2)
    := match ls1 return type_of_list ls1 -> type_of_list ls2 -> type_of_list (ls1 ++ ls2) with
       | nil => fun _ x => x
       | cons T Ts => fun tts rest => (fst tts, @list_app_type_of_list Ts ls2 (snd tts) rest)
       end.

  Fixpoint list_unapp_type_of_list {ls1 ls2 : list Type} : type_of_list (ls1 ++ ls2) -> type_of_list ls1 * type_of_list ls2
    := match ls1 return type_of_list (ls1 ++ ls2) -> type_of_list ls1 * type_of_list ls2 with
       | nil => fun x => (tt, x)
       | cons T Ts
         => fun tts
            => let '(t2, t2s) := @list_unapp_type_of_list Ts ls2 (snd tts) in
               (fst tts, t2, t2s)
       end.

  Fixpoint lift_type_of_list_map {A} {ls : list A} {P1 P2 : A -> Type} (F : forall a, P1 a -> P2 a) {struct ls}
    : type_of_list (List.map P1 ls) -> type_of_list (List.map P2 ls)
    := match ls return type_of_list (List.map P1 ls) -> type_of_list (List.map P2 ls) with
       | nil => fun x => x
       | T :: Ts
         => fun v_vs
            => (F T (fst v_vs),
                @lift_type_of_list_map A Ts P1 P2 F (snd v_vs))
       end.

  Module pattern.
    Notation EvarMap_at base := (PositiveMap.t (Compilers.base.type base)).
    Notation EvarMap := (EvarMap_at _).
    Export Language.Compilers.pattern.
    Module base.
      Local Notation einterp := type.interp.
      Export Language.Compilers.pattern.base.

      Definition reflect_beq {base : Type} {base_beq : base -> base -> bool}
                 {reflect_base_beq : reflect_rel (@eq base) base_beq}
        : reflect_rel (@eq (type base)) (type.type_beq _ base_beq)
        := reflect_of_beq
             (type.internal_type_dec_bl _ _ (proj1 (reflect_to_beq _)))
             (type.internal_type_dec_lb _ _ (proj2 (reflect_to_beq _))).
      Global Hint Extern 1 (reflect (@eq (type ?base) ?x ?y) _) => notypeclasses refine (@reflect_beq base _ _ x y) : typeclass_instances.

      Section with_base.
        Context {base : Type}.

        Local Notation type := (type base).

        Fixpoint relax (t : Compilers.base.type base) : type
          := match t with
             | Compilers.base.type.type_base t => type.type_base t
             | Compilers.base.type.prod A B => type.prod (relax A) (relax B)
             | Compilers.base.type.list A => type.list (relax A)
             | Compilers.base.type.option A => type.option (relax A)
             | Compilers.base.type.unit => type.unit
             end.

        Definition lookup_default (p : positive) (evar_map : EvarMap) : Compilers.base.type base
          := match PositiveMap.find p evar_map with
             | Datatypes.Some t => t
             | Datatypes.None => Compilers.base.type.unit
             end.

        Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : Compilers.base.type base
          := match ptype with
             | type.var p => lookup_default p evar_map
             | type.type_base t => Compilers.base.type.type_base t
             | type.prod A B
               => Compilers.base.type.prod (subst_default A evar_map) (subst_default B evar_map)
             | type.list A => Compilers.base.type.list (subst_default A evar_map)
             | type.option A => Compilers.base.type.option (subst_default A evar_map)
             | type.unit => Compilers.base.type.unit
             end.

        Fixpoint collect_vars (t : type) : PositiveSet.t
          := match t with
             | type.var p => PositiveSet.add p PositiveSet.empty
             | type.unit
             | type.type_base _
               => PositiveSet.empty
             | type.prod A B => PositiveSet.union (collect_vars A) (collect_vars B)
             | type.list A => collect_vars A
             | type.option A => collect_vars A
             end.
      End with_base.
    End base.
    Notation type base := (type.type (base.type base)).

    Module type.
      Section with_base.
        Context {base : Type}.

        Local Notation type := (type base).

        Fixpoint relax (t : type.type (Compilers.base.type base)) : type
          := match t with
             | type.base t => type.base (base.relax t)
             | type.arrow s d => type.arrow (relax s) (relax d)
             end.

        Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : type.type (Compilers.base.type base)
          := match ptype with
             | type.base t => type.base (base.subst_default t evar_map)
             | type.arrow A B => type.arrow (subst_default A evar_map) (subst_default B evar_map)
             end.

        Fixpoint collect_vars (t : type) : PositiveSet.t
          := match t with
             | type.base t => base.collect_vars t
             | type.arrow s d => PositiveSet.union (collect_vars s) (collect_vars d)
             end.
      End with_base.
    End type.

    Section __.
      Context {base : Type}.
      Local Notation ctype := (type.type (Compilers.base.type base)).
      Context {ident : ctype -> Type}
              (all_idents : list { T : Type & T })
              (ident_index : forall t, ident t -> nat)
              (eta_ident_cps_gen
               : forall {T : forall t, ident t -> Type}
                        (f : forall t idc, T t idc),
                  { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }).

      Definition eta_ident_cps_gen2
                 {T0 : forall t, ident t -> Type}
                 (f0 : forall t idc, T0 t idc)
                 {T1 : forall t idc, T0 t idc -> Type}
                 (f1 : forall t idc, T1 t idc (f0 t idc))
        : { f' : forall t idc, T1 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc)
          | forall t idc,
              f' t idc = rew [T1 t idc] (eq_sym (proj2_sig (@eta_ident_cps_gen T0 f0) t idc)) in f1 t idc }.
      Proof. apply eta_ident_cps_gen. Defined.

      Definition eta_ident_cps_gen3
                 {T0 : forall t, ident t -> Type}
                 (f0 : forall t idc, T0 t idc)
                 {T1 : forall t idc, T0 t idc -> Type}
                 (f1 : forall t idc, T1 t idc (f0 t idc))
                 {T2 : forall t idc x, T1 t idc x -> Type}
                 (f2 : forall t idc, T2 t idc (f0 t idc) (f1 t idc))
        : { f' : forall t idc, T2 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc) (proj1_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) t idc)
          | forall t idc,
              f' t idc
              = rew [T2 t idc _] (eq_sym (proj2_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) t idc)) in
                match eq_sym (proj2_sig (@eta_ident_cps_gen _ f0) t idc) as p return T2 t idc _ (rew [T1 t idc] p in f1 t idc) with
                | eq_refl => f2 t idc
                end }.
      Proof. apply eta_ident_cps_gen. Defined.
    End __.

    Module Raw.
      Module ident.
        Inductive kind_of_type := GallinaType (_ : Type) | BaseBaseType | BaseType.
        Definition Type_of_kind_of_type (base : Type) (T : kind_of_type)
          := match T with
             | GallinaType T => T
             | BaseBaseType => base
             | BaseType => Compilers.base.type.type base
             end.

        Notation type_of_list_of_kind base ls
          := (type_of_list (List.map (@Type_of_kind_of_type base) ls)).

        Section with_base.
          Context {base : Type}.
          Local Notation ctype := (type.type (Compilers.base.type base)).
          Context {cident : ctype -> Type}.

          Local Notation Type_of_kind_of_type := (Type_of_kind_of_type base).
          Local Notation type_of_list_of_kind ls := (type_of_list_of_kind base ls).

          Record preident_infos :=
            {
              dep_types : list Type; (* types which show up in the type of other infos *)
              indep_types : list kind_of_type; (* types which show up in the type of the ident, but not in the type of other lists *)
              indep_args : type_of_list dep_types -> list Type;
              to_type : forall d : type_of_list dep_types, type_of_list_of_kind indep_types -> Compilers.type (Compilers.base.type base);
              to_ident : forall (d : type_of_list dep_types) (i : type_of_list_of_kind indep_types), type_of_list (indep_args d) -> cident (to_type d i)
            }.

          Record ident_infos :=
            {
              preinfos :> preident_infos;
              dep_types_dec_transparent : forall x y : type_of_list (dep_types preinfos), {x = y} + {x <> y};
              indep_args_beq : _;
              indep_args_reflect
              : forall x, reflect_rel (@eq (type_of_list (indep_args preinfos x))) (indep_args_beq x);
              indep_types_beq : _;
              indep_types_reflect
              : reflect_rel (@eq (type_of_list_of_kind (indep_types preinfos))) indep_types_beq;
            }.

          Definition ident_args (pi : preident_infos)
            := { t : type_of_list (dep_types pi) & type_of_list_of_kind (indep_types pi) * type_of_list (indep_args pi t) }%type.

          Definition assemble_ident {pi} (args : ident_args pi)
            := to_ident pi (projT1 args) (Datatypes.fst (projT2 args)) (Datatypes.snd (projT2 args)).

          Section __.
            Context (all_pattern_idents : list { T : Type & T })
                    (pattern_ident_index : forall t, cident t -> nat)
                    (eta_pattern_ident_cps_gen
                     : forall {T : forall t, cident t -> Type}
                              (f : forall t idc, T t idc),
                        { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }).
            Context (ident : Set)
                    (all_idents : list ident)
                    (ident_index : ident -> nat)
                    (ident_index_idempotent : forall idc, List.nth_error all_idents (ident_index idc) = Some idc)
                    (eta_ident_cps_gen
                     : forall {T : ident -> Type}
                              (f : forall idc, T idc),
                        { f' : forall idc, T idc | forall idc, f' idc = f idc }).

            Definition eta_ident_cps_gen2
                       {T0 : ident -> Type}
                       (f0 : forall idc, T0 idc)
                       {T1 : forall idc, T0 idc -> Type}
                       (f1 : forall idc, T1 idc (f0 idc))
              : { f' : forall idc, T1 idc (proj1_sig (@eta_ident_cps_gen T0 f0) idc)
                | forall idc,
                    f' idc = rew [T1 idc] (eq_sym (proj2_sig (@eta_ident_cps_gen T0 f0) idc)) in f1 idc }.
            Proof. apply eta_ident_cps_gen. Defined.

            Definition eta_ident_cps_gen3
                       {T0 : ident -> Type}
                       (f0 : forall idc, T0 idc)
                       {T1 : forall idc, T0 idc -> Type}
                       (f1 : forall idc, T1 idc (f0 idc))
                       {T2 : forall idc x, T1 idc x -> Type}
                       (f2 : forall idc, T2 idc (f0 idc) (f1 idc))
              : { f' : forall idc, T2 idc (proj1_sig (@eta_ident_cps_gen T0 f0) idc) (proj1_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) idc)
                | forall idc,
                    f' idc
                    = rew [T2 idc _] (eq_sym (proj2_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) idc)) in
                      match eq_sym (proj2_sig (@eta_ident_cps_gen _ f0) idc) as p return T2 idc _ (rew [T1 idc] p in f1 idc) with
                      | eq_refl => f2 idc
                      end }.
            Proof. apply eta_ident_cps_gen. Defined.

            Definition ident_beq : ident -> ident -> bool
              := fun idc1 idc2
                 => proj1_sig
                      (@eta_ident_cps_gen
                         _
                         (fun idc1
                          => proj1_sig
                               (@eta_ident_cps_gen
                                  _
                                  (fun idc2
                                   => Nat.eqb (ident_index idc1) (ident_index idc2)))
                               idc2))
                      idc1.

            Local Ltac rew_proj2_sig :=
              repeat match goal with
                     | [ |- context[@proj1_sig _ (fun _ => forall x, _ = _) ?p] ]
                       => rewrite !(proj2_sig p)
                     | [ |- context[@proj1_sig _ (fun _ => forall x y, _ = _) ?p] ]
                       => rewrite !(proj2_sig p)
                     end.

            Definition nat_eqb_refl_transparent (x : nat) : Nat.eqb x x = true.
            Proof. induction x; cbn; constructor + assumption. Defined.

            Definition ident_lb (x y : ident) : x = y -> ident_beq x y = true.
            Proof.
              intro H; subst y; cbv [ident_beq];
                rew_proj2_sig; apply nat_eqb_refl_transparent.
            Defined.

            Lemma ident_index_inj idc1 idc2 : ident_index idc1 = ident_index idc2 -> idc1 = idc2.
            Proof.
              intro H.
              pose proof (ident_index_idempotent idc1) as H1.
              pose proof (ident_index_idempotent idc2) as H2.
              rewrite H in H1; rewrite H1 in H2.
              set (sidc1 := Some idc1) in *.
              set (sidc2 := Some idc2) in *.
              change (match sidc1, sidc2 with Some idc1, Some idc2 => idc1 = idc2 | _, _ => True end).
              clearbody sidc2; subst sidc2 sidc1; reflexivity.
            Defined.

            Definition nat_eqb_bl_transparent (x y : nat) : Nat.eqb x y = true -> x = y.
            Proof.
              revert y; induction x, y; cbn; intro; try apply f_equal; auto using eq_refl with nocore;
                exfalso; apply Bool.diff_false_true; assumption.
            Defined.

            Definition ident_bl (x y : ident) : ident_beq x y = true -> x = y.
            Proof.
              cbv [ident_beq]; rew_proj2_sig; intro H.
              apply nat_eqb_bl_transparent in H.
              apply ident_index_inj in H.
              exact H.
            Defined.

            Definition ident_beq_if (x y : ident) : if ident_beq x y then x = y else True.
            Proof.
              generalize (ident_beq x y), (ident_bl x y).
              intros b H; destruct b; exact I + auto using eq_refl with nocore.
            Defined.

            Definition ident_transport_opt (P : ident -> Type) {x y : ident} : P x -> Datatypes.option (P y)
              := fun v
                 => (if ident_beq x y as b return (if b then x = y else True) -> _
                     then fun pf => Datatypes.Some
                                      match pf in (_ = y) return P y with
                                      | eq_refl => v
                                      end
                     else fun _ => Datatypes.None)
                      (@ident_beq_if x y).

            Definition ident_to_cident : ident -> { T : Type & T }
              := proj1_sig
                   (@eta_ident_cps_gen
                      _
                      (fun idc => List.nth_default (@existT Type _ True I) all_pattern_idents (ident_index idc))).

            Context (ident_infos_of : ident -> ident_infos)
                    (split_ident_gen
                     : forall {t} (idc : cident t),
                        { ridc : ident & { args : ident_args (ident_infos_of ridc)
                                         | { pf : _ = _
                                           | idc = rew [cident] pf in assemble_ident args } } }).

            Definition prefull_types : ident -> Type
              := fun idc => ident_args (ident_infos_of idc).
            Definition full_types : ident -> Type
              := proj1_sig (@eta_ident_cps_gen _ prefull_types).
            Definition is_simple : ident -> bool
              := fun idc
                 => let ii := ident_infos_of idc in
                    match dep_types ii, indep_types ii return _ with (* COQBUG(https://github.com/coq/coq/issues/9955) *)
                    | [], [] => true
                    | _, _ => false
                    end.
            Definition type_of : forall (pidc : ident), full_types pidc -> ctype
              := proj1_sig
                   (@eta_ident_cps_gen2
                      _ prefull_types
                      (fun pidc full_types_pidc => full_types_pidc -> ctype)
                      (fun pidc args
                       => to_type (ident_infos_of pidc) (projT1 args) (Datatypes.fst (projT2 args)))).

            Definition folded_invert_bind_args : forall {t} (idc : cident t) (pidc : ident), Datatypes.option (full_types pidc)
              := fun t idc pidc
                 => proj1_sig
                      (@eta_pattern_ident_cps_gen
                         _
                         (fun t idc
                          => proj1_sig
                               (@eta_ident_cps_gen2
                                  _ prefull_types
                                  (fun pidc full_types_pidc => Datatypes.option full_types_pidc)
                                  (fun pidc
                                   => let '(existT ridc (exist args _)) := @split_ident_gen _ idc in
                                      ident_transport_opt
                                        (fun idc => ident_args (ident_infos_of idc))
                                        args))
                               pidc))
                      t idc.

            Definition to_typed : forall (pidc : ident) (args : full_types pidc), cident (type_of pidc args)
              := proj1_sig
                   (@eta_ident_cps_gen3
                      _ prefull_types
                      (fun pidc full_types_pidc => full_types_pidc -> ctype)
                      (fun pidc args => to_type (ident_infos_of pidc) (projT1 args) (Datatypes.fst (projT2 args)))
                      (fun pidc full_types_pidc type_of_pidc => forall args : full_types_pidc, cident (type_of_pidc args))
                      (fun pidc args
                       => to_ident _ _ _ (Datatypes.snd (projT2 args)))).

            Definition try_unify_split_args {ridc1 ridc2 : ident}
              : forall {dt1 : type_of_list (dep_types (preinfos (ident_infos_of ridc1)))}
                       {dt2 : type_of_list (dep_types (preinfos (ident_infos_of ridc2)))}
              (*(idt1 : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc1))))
                   (idt2 : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc2))))*),
                type_of_list (indep_args _ dt1) -> Datatypes.option (type_of_list (indep_args _ dt2))
              := (if ident_beq ridc1 ridc2 as b return (if b then ridc1 = ridc2 else True) -> _
                  then fun pf
                       => match pf in (_ = ridc2) return forall (dt1 : type_of_list (dep_types (preinfos (ident_infos_of ridc1))))
                                                                (dt2 : type_of_list (dep_types (preinfos (ident_infos_of ridc2))))
                            (*(idt1 : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc1))))
                                                            (idt2 : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc2))))*),
                              type_of_list (indep_args _ dt1) -> Datatypes.option (type_of_list (indep_args _ dt2)) with
                          | eq_refl
                            => fun dt1 dt2 (*idt1 idt2*)
                               => match dep_types_dec_transparent _ dt1 dt2 with
                                  | left pf
                                    => match pf in (_ = dt2) return type_of_list (indep_args _ dt1) -> Datatypes.option (type_of_list (indep_args _ dt2)) with
                                       | eq_refl
                                         => (*if indep_types_beq _ idt1 idt2
                                        then*) Datatypes.Some
                                                 (*else fun _ => Datatypes.None*)
                                       end
                                  | right _ => fun _ => Datatypes.None
                                  end
                          end
                  else fun _ _ _ _ (*_ _*) => Datatypes.None)
                   (ident_beq_if ridc1 ridc2).
          End __.
        End with_base.
      End ident.
    End Raw.

    Module ident.
      Definition Type_of_kind_of_type (base : Type) (T : Raw.ident.kind_of_type)
        := match T with
           | Raw.ident.GallinaType T => T
           | Raw.ident.BaseBaseType => base
           | Raw.ident.BaseType => pattern.base.type.type base
           end.

      Notation full_type_of_list_of_kind base ls
        := (type_of_list (List.map (Raw.ident.Type_of_kind_of_type base) ls)).

      Notation type_of_list_of_kind base ls
        := (type_of_list (List.map (Type_of_kind_of_type base) ls)).

      Section with_base.
        Context {base : Type}.
        Local Notation ctype := (type.type (Compilers.base.type base)).
        Local Notation type := (type base).
        Context {cident : ctype -> Type}.

        Local Notation Type_of_kind_of_type := (Type_of_kind_of_type base).
        Local Notation full_type_of_list_of_kind ls := (full_type_of_list_of_kind base ls).
        Local Notation type_of_list_of_kind ls := (type_of_list_of_kind base ls).

        Definition relax_kind_of_type {T} : Raw.ident.Type_of_kind_of_type base T -> Type_of_kind_of_type T
          := match T with
             | Raw.ident.GallinaType _
             | Raw.ident.BaseBaseType
               => fun x => x
             | Raw.ident.BaseType => pattern.base.relax
             end.
        Definition subst_default_kind_of_type (evm : EvarMap) {T} : Type_of_kind_of_type T -> Raw.ident.Type_of_kind_of_type base T
          := match T with
             | Raw.ident.GallinaType _
             | Raw.ident.BaseBaseType
               => fun x => x
             | Raw.ident.BaseType => fun t => pattern.base.subst_default t evm
             end.

        Local Notation dep_types := Raw.ident.dep_types.
        Local Notation preinfos := Raw.ident.preinfos.
        Local Notation indep_types := Raw.ident.indep_types.
        Local Notation indep_args := Raw.ident.indep_args.
        Local Notation iffT A B := ((A -> B) * (B -> A))%type.

        Section __.
          Context (all_pattern_idents : list { T : Type & T })
                  (pattern_ident_index : forall t, cident t -> nat)
                  (eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal
                   : forall {T : forall t, cident t -> Type}
                            (f : forall t idc, T t idc),
                      { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }).
          Context (raw_ident : Set)
                  (all_raw_idents : list raw_ident)
                  (raw_ident_index : raw_ident -> nat)
                  (raw_ident_index_idempotent : forall idc, List.nth_error all_raw_idents (raw_ident_index idc) = Some idc)
                  (eta_raw_ident_cps_gen
                   : forall {T : raw_ident -> Type}
                            (f : forall idc, T idc),
                      { f' : forall idc, T idc | forall idc, f' idc = f idc }).
          Context (raw_ident_infos_of : raw_ident -> Raw.ident.ident_infos)
                  (split_raw_ident_gen
                   : forall {t} (idc : cident t),
                      { ridc : raw_ident
                               & { args : Raw.ident.ident_args (preinfos (raw_ident_infos_of ridc))
                                 | { pf : _ = _
                                   | idc = rew [cident] pf in Raw.ident.assemble_ident args } } }).
          Context (ident : type -> Type)
                  (all_idents : list { T : Type & T })
                  (eta_ident_cps_gen
                   : forall (T : forall t, ident t -> Type)
                            (f : forall t idc, T t idc),
                      { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc })
                  (eta_ident_cps_gen_expand_literal
                   : forall (T : forall t, ident t -> Type)
                            (f : forall t idc, T t idc),
                      { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }).

          Definition eta_ident_cps_gen2
                     {T0 : forall t, ident t -> Type}
                     (f0 : forall t idc, T0 t idc)
                     {T1 : forall t (idc : ident t), T0 t idc -> Type}
                     (f1 : forall t idc, T1 t idc (f0 t idc))
            : { f' : forall t idc, T1 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc)
              | forall t idc,
                  f' t idc = rew [T1 t idc] (eq_sym (proj2_sig (@eta_ident_cps_gen T0 f0) t idc)) in f1 t idc }.
          Proof. apply eta_ident_cps_gen. Defined.

          Definition eta_ident_cps_gen3
                     {T0 : forall t, ident t -> Type}
                     (f0 : forall t idc, T0 t idc)
                     {T1 : forall t idc, T0 t idc -> Type}
                     (f1 : forall t idc, T1 t idc (f0 t idc))
                     {T2 : forall t idc x, T1 t idc x -> Type}
                     (f2 : forall t idc, T2 t idc (f0 t idc) (f1 t idc))
            : { f' : forall t idc, T2 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc) (proj1_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) t idc)
              | forall t idc,
                  f' t idc
                  = rew [T2 t idc _] (eq_sym (proj2_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) t idc)) in
                    match eq_sym (proj2_sig (@eta_ident_cps_gen _ f0) t idc) as p return T2 t idc _ (rew [T1 t idc] p in f1 t idc) with
                    | eq_refl => f2 t idc
                    end }.
          Proof. apply eta_ident_cps_gen. Defined.

          Context (split_types
                   : forall t (idc : ident t), { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc))) }%type)
                  (add_types_from_raw_sig
                   : forall (ridc : raw_ident)
                            (dt : type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))))
                            (idt : type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc)))),
                      { t : _ & { idc : ident t | @split_types _ idc = existT _ ridc (dt, idt) } }).

          Definition split_types_subst_default : forall {t} (idc : ident t) (evm : EvarMap), { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * full_type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc))) }%type
            := fun t idc evm
               => let res := @split_types t idc in
                  existT _ (projT1 res) (Datatypes.fst (projT2 res),
                                         lift_type_of_list_map (@subst_default_kind_of_type evm) (Datatypes.snd (projT2 res))).

          Context (to_type_split_types_subst_default_eq
                   : forall t idc evm,
                      Raw.ident.to_type
                        (preinfos (raw_ident_infos_of (projT1 (@split_types_subst_default t idc evm))))
                        (Datatypes.fst (projT2 (split_types_subst_default idc evm)))
                        (Datatypes.snd (projT2 (split_types_subst_default idc evm)))
                      = type.subst_default t evm)
                  (projT1_add_types_from_raw_sig_eq
                   : forall t idc,
                      projT1
                        (add_types_from_raw_sig
                           (projT1 (split_raw_ident_gen t idc))
                           (projT1 (proj1_sig (projT2 (split_raw_ident_gen t idc))))
                           (lift_type_of_list_map
                              (@relax_kind_of_type)
                              (Datatypes.fst (projT2 (proj1_sig (projT2 (split_raw_ident_gen t idc)))))))
                      = type.relax t).

          Definition prearg_types : forall {t} (idc : ident t), list Type
            := (fun t idc
                => let st := @split_types t idc in
                   let pi := preinfos (raw_ident_infos_of (projT1 st)) in
                   indep_args pi (Datatypes.fst (projT2 st))).

          Definition strip_types : forall {t} (idc : ident t), raw_ident
            := proj1_sig
                 (@eta_ident_cps_gen
                    _
                    (fun t idc => projT1 (@split_types t idc))).
          Definition arg_types : forall {t} (idc : ident t), list Type
            := proj1_sig (@eta_ident_cps_gen _ (@prearg_types)).

          Definition to_typed : forall {t} (idc : ident t) (evm : EvarMap), type_of_list (arg_types idc) -> cident (type.subst_default t evm)
            := fun t (idc : ident t) (evm : EvarMap)
               => proj1_sig
                    (@eta_ident_cps_gen2
                       _ (@prearg_types)
                       (fun t idc arg_types_idc
                        => forall args : type_of_list arg_types_idc,
                            cident (type.subst_default t evm)
                       (*let st := @split_types _ idc in
                           let pi := preinfos (raw_ident_infos_of (projT1 st)) in
                           Raw.ident.to_type
                             pi
                             (Datatypes.fst (projT2 st))
                             (lift_type_of_list_map
                                (@subst_default_kind_of_type evm)
                                (Datatypes.snd (projT2 st)))*))
                       (fun t idc args
                        => rew [cident] to_type_split_types_subst_default_eq t idc evm in
                            let st := @split_types_subst_default _ idc evm in
                            (@Raw.ident.assemble_ident
                               base cident
                               (preinfos (raw_ident_infos_of (projT1 (@split_types_subst_default _ idc evm))))
                               (existT
                                  _ (Datatypes.fst (projT2 st))
                                  (Datatypes.snd (projT2 st), args)))))
                    t idc.

          Definition type_of_list_arg_types_beq : forall t idc, type_of_list (@arg_types t idc) -> type_of_list (@arg_types t idc) -> bool
            := proj1_sig
                 (@eta_ident_cps_gen2
                    _ (@prearg_types)
                    (fun t idc arg_types_idc => type_of_list arg_types_idc -> type_of_list arg_types_idc -> bool)
                    (fun t idc
                     => Raw.ident.indep_args_beq _ _)).

          Definition reflect_type_of_list_arg_types_beq : forall {t idc}, reflect_rel (@eq (type_of_list (@arg_types t idc))) (@type_of_list_arg_types_beq t idc)
            := proj1_sig
                 (@eta_ident_cps_gen3
                    _ (@prearg_types)
                    (fun t idc arg_types_idc => type_of_list arg_types_idc -> type_of_list arg_types_idc -> bool)
                    (fun t idc => Raw.ident.indep_args_beq _ _)
                    (fun t idc arg_types_idc beq => reflect_rel (@eq (type_of_list arg_types_idc)) beq)
                    (fun t idc => Raw.ident.indep_args_reflect _ _)).

          Definition preof_typed_ident_sig : forall {t} (idc : cident t), _
            := fun t idc
               => add_types_from_raw_sig
                    (projT1 (split_raw_ident_gen t idc))
                    (projT1 (proj1_sig (projT2 (split_raw_ident_gen t idc))))
                    (lift_type_of_list_map
                       (@relax_kind_of_type)
                       (Datatypes.fst (projT2 (proj1_sig (projT2 (split_raw_ident_gen t idc)))))).
          Definition preof_typed_ident : forall {t} (idc : cident t), ident (type.relax t)
            := fun t idc
               => rew [ident] projT1_add_types_from_raw_sig_eq t idc in
                   proj1_sig
                     (projT2
                        (@preof_typed_ident_sig t idc)).
          Definition of_typed_ident : forall {t} (idc : cident t), ident (type.relax t)
            := proj1_sig (eta_pattern_ident_cps_gen _ (@preof_typed_ident)).

          Definition arg_types_of_typed_ident : forall {t} (idc : cident t), type_of_list (arg_types (of_typed_ident idc)).
          Proof.
            refine (proj1_sig
                      (@pattern.eta_ident_cps_gen2
                         base cident
                         eta_pattern_ident_cps_gen
                         _ (@preof_typed_ident)
                         (fun t idc of_typed_ident_idc => type_of_list (arg_types of_typed_ident_idc))
                         (fun t idc
                          => match projT1_add_types_from_raw_sig_eq t idc as H'
                                   return type_of_list (arg_types (rew [ident] H' in proj1_sig (projT2 (@preof_typed_ident_sig _ idc))))
                             with
                             | eq_refl
                               => rew <- [type_of_list]
                                      (proj2_sig (eta_ident_cps_gen _ (@prearg_types))
                                                 (projT1 (preof_typed_ident_sig idc))
                                                 (proj1_sig (projT2 (preof_typed_ident_sig idc)))) in
                                   rew <- [fun k' => type_of_list (indep_args (preinfos (raw_ident_infos_of (projT1 k'))) (Datatypes.fst (projT2 k')))]
                                       (proj2_sig (projT2 (@preof_typed_ident_sig t idc))) in
                                   _
                             end))).
            refine (let st := split_raw_ident_gen _ idc in
                    let args := proj1_sig (projT2 st) in
                    Datatypes.snd (projT2 args)).
          Defined.

          Local Notation raw_try_unify_split_args := (@Raw.ident.try_unify_split_args base cident raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of).

          Definition folded_unify : forall {t t'} (pidc : ident t) (idc : cident t') (*evm : EvarMap*), Datatypes.option (type_of_list (@arg_types t pidc))
            := fun t t' (pidc : ident t) (idc : cident t') (*evm : EvarMap*)
               => proj1_sig
                    (eta_ident_cps_gen_expand_literal
                       _
                       (fun t pidc
                        => proj1_sig
                             (eta_pattern_ident_cps_gen_expand_literal
                                _
                                (fun t' idc
                                 => proj1_sig
                                      (@eta_ident_cps_gen2
                                         _ (@prearg_types)
                                         (fun _ idc arg_types_idc => type_of_list arg_types_idc -> Datatypes.option (type_of_list (@arg_types t pidc)))
                                         (fun t idc
                                          => proj1_sig
                                               (@eta_ident_cps_gen2
                                                  _ (@prearg_types)
                                                  (fun _ pidc arg_types_pidc => type_of_list (@prearg_types _ idc) -> Datatypes.option (type_of_list arg_types_pidc))
                                                  (fun t' pidc idc_indep_args
                                                   => raw_try_unify_split_args
                                                        (*(Datatypes.snd (projT2 (@split_types_subst_default _ idc evm)))
                                                    (Datatypes.snd (projT2 (@split_types_subst_default _ pidc evm)))*)
                                                        idc_indep_args))
                                               _ pidc))
                                      _ (of_typed_ident idc) (@arg_types_of_typed_ident _ idc)))
                             _ idc))
                    _ pidc.
        End __.
      End with_base.

      Module GoalType.
        Local Notation dep_types := Raw.ident.dep_types.
        Local Notation preinfos := Raw.ident.preinfos.
        Local Notation indep_types := Raw.ident.indep_types.
        Local Notation indep_args := Raw.ident.indep_args.
        Local Notation iffT A B := ((A -> B) * (B -> A))%type.

        Class package {base : Type} {ident : type.type (Compilers.base.type base) -> Type} :=
          {
            all_idents : list { T : Type & T };
            ident_index : forall t, ident t -> nat;
            eta_ident_cps_gen
            : forall {T : forall t, ident t -> Type}
                     (f : forall t idc, T t idc),
                { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc };
            eta_ident_cps_gen_expand_literal
            : forall {T : forall t, ident t -> Type}
                     (f : forall t idc, T t idc),
                { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc };
            eta_ident_cps
            : forall (T : _ -> Type) t (idc : ident t)
                     (f : forall t', ident t' -> T t'),
                T t;
            simple_idents : list { t : _ & ident t };

            raw_ident : Set;
            all_raw_idents : list raw_ident;
            raw_ident_index : raw_ident -> nat;
            raw_ident_index_idempotent : forall idc, List.nth_error all_raw_idents (raw_ident_index idc) = Some idc;
            eta_raw_ident_cps_gen
            : forall {T : raw_ident -> Type}
                     (f : forall idc, T idc),
                { f' : forall idc, T idc | forall idc, f' idc = f idc };
            raw_ident_infos_of : raw_ident -> Raw.ident.ident_infos;
            split_raw_ident_gen
            : forall {t} (idc : ident t),
                { ridc : raw_ident
                         & { args : Raw.ident.ident_args (preinfos (raw_ident_infos_of ridc))
                           | { pf : _ = _
                             | idc = rew [ident] pf in Raw.ident.assemble_ident args } } };
            invert_bind_args : forall {t} (idc : ident t) (pidc : raw_ident), Datatypes.option (@Raw.ident.full_types base ident raw_ident (@eta_raw_ident_cps_gen) raw_ident_infos_of pidc);
            invert_bind_args_unknown : forall {t} (idc : ident t) (pidc : raw_ident), Datatypes.option (@Raw.ident.full_types base ident raw_ident (@eta_raw_ident_cps_gen) raw_ident_infos_of pidc);


            pattern_ident : type base -> Type;
            all_pattern_idents : list { T : Type & T };
            eta_pattern_ident_cps_gen
            : forall (T : forall t, pattern_ident t -> Type)
                     (f : forall t idc, T t idc),
                { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc };
            eta_pattern_ident_cps_gen_expand_literal
            : forall (T : forall t, pattern_ident t -> Type)
                     (f : forall t idc, T t idc),
                { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc };

            split_types
            : forall t (idc : pattern_ident t), { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * ident.type_of_list_of_kind base (indep_types (preinfos (raw_ident_infos_of ridc))) }%type;
            add_types_from_raw_sig
            : forall (ridc : raw_ident)
                     (dt : type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))))
                     (idt : ident.type_of_list_of_kind base (indep_types (preinfos (raw_ident_infos_of ridc)))),
                { t : _ & { idc : pattern_ident t | @split_types _ idc = existT _ ridc (dt, idt) } };
            to_type_split_types_subst_default_eq
            : forall t idc evm,
                Raw.ident.to_type
                  (preinfos (raw_ident_infos_of (projT1 (@ident.split_types_subst_default base ident raw_ident raw_ident_infos_of pattern_ident split_types t idc evm))))
                  (Datatypes.fst (projT2 (@ident.split_types_subst_default base ident raw_ident raw_ident_infos_of pattern_ident split_types t idc evm)))
                  (Datatypes.snd (projT2 (@ident.split_types_subst_default base ident raw_ident raw_ident_infos_of pattern_ident split_types t idc evm)))
                = type.subst_default t evm;
            projT1_add_types_from_raw_sig_eq
            : forall t idc,
                projT1
                  (add_types_from_raw_sig
                     (projT1 (@split_raw_ident_gen t idc))
                     (projT1 (proj1_sig (projT2 (@split_raw_ident_gen t idc))))
                     (lift_type_of_list_map
                        (@ident.relax_kind_of_type base)
                        (Datatypes.fst (projT2 (proj1_sig (projT2 (@split_raw_ident_gen t idc)))))))
                = type.relax t;
            arg_types_unfolded : forall t (idc : pattern_ident t), list Type;
            to_typed_unfolded : forall t (idc : pattern_ident t) (evm : EvarMap), type_of_list (@arg_types_unfolded _ idc) -> ident (type.subst_default t evm);
            type_of_list_arg_types_beq_unfolded : forall t idc, type_of_list (@arg_types_unfolded t idc) -> type_of_list (@arg_types_unfolded t idc) -> bool;
            of_typed_ident_unfolded : forall t (idc : ident t), pattern_ident (type.relax t);
            arg_types_of_typed_ident_unfolded : forall t (idc : ident t), type_of_list (arg_types_unfolded _ (of_typed_ident_unfolded _ idc));
            unify : forall {t t'} (pidc : pattern_ident t) (idc : ident t') (*evm : EvarMap*), Datatypes.option (type_of_list (@ident.arg_types base ident raw_ident raw_ident_infos_of pattern_ident eta_pattern_ident_cps_gen split_types t pidc));
            unify_unknown : forall {t t'} (pidc : pattern_ident t) (idc : ident t') (*evm : EvarMap*), Datatypes.option (type_of_list (@ident.arg_types base ident raw_ident raw_ident_infos_of pattern_ident eta_pattern_ident_cps_gen split_types t pidc))
          }.

        Definition package_with_args {base} {ident} (ident_package : Basic.GoalType.package) (raw_ident : Type) (pattern_ident : type.type (pattern.base.type base) -> Type)
          := @package base ident.

        Ltac red_proj :=
          cbv [
              all_idents
                ident_index
                eta_ident_cps_gen
                eta_ident_cps_gen_expand_literal
                eta_ident_cps
                simple_idents
                raw_ident
                all_raw_idents
                raw_ident_index
                raw_ident_index_idempotent
                eta_raw_ident_cps_gen
                raw_ident_infos_of
                split_raw_ident_gen
                invert_bind_args
                invert_bind_args_unknown
                pattern_ident
                all_pattern_idents
                eta_pattern_ident_cps_gen
                eta_pattern_ident_cps_gen_expand_literal
                split_types
                add_types_from_raw_sig
                to_type_split_types_subst_default_eq
                projT1_add_types_from_raw_sig_eq
                arg_types_unfolded
                to_typed_unfolded
                type_of_list_arg_types_beq_unfolded
                of_typed_ident_unfolded
                arg_types_of_typed_ident_unfolded
                unify
                unify_unknown
            ] in *.

        Module Export Settings.
          Global Strategy -100 [
                               all_idents
                                 ident_index
                                 eta_ident_cps_gen
                                 eta_ident_cps_gen_expand_literal
                                 eta_ident_cps
                                 simple_idents
                                 raw_ident
                                 all_raw_idents
                                 raw_ident_index
                                 raw_ident_index_idempotent
                                 eta_raw_ident_cps_gen
                                 raw_ident_infos_of
                                 split_raw_ident_gen
                                 invert_bind_args
                                 invert_bind_args_unknown
                                 pattern_ident
                                 all_pattern_idents
                                 eta_pattern_ident_cps_gen
                                 eta_pattern_ident_cps_gen_expand_literal
                                 split_types
                                 add_types_from_raw_sig
                                 to_type_split_types_subst_default_eq
                                 projT1_add_types_from_raw_sig_eq
                                 arg_types_unfolded
                                 to_typed_unfolded
                                 type_of_list_arg_types_beq_unfolded
                                 of_typed_ident_unfolded
                                 arg_types_of_typed_ident_unfolded
                                 unify
                                 unify_unknown
                             ].
        End Settings.

        Notation eta_ident_cps_gen2_of p := (@pattern.eta_ident_cps_gen2 _ _ (@eta_ident_cps_gen _ _ p)).
        Notation eta_ident_cps_gen3_of p := (@pattern.eta_ident_cps_gen3 _ _ (@eta_ident_cps_gen _ _ p)).
        Notation raw_ident_beq_of p := (@Raw.ident.ident_beq (@raw_ident _ _ p) (@raw_ident_index _ _ p) (@eta_raw_ident_cps_gen _ _ p)).
        Notation raw_ident_lb_of p := (@Raw.ident.ident_lb (@raw_ident _ _ p) (@raw_ident_index _ _ p) (@eta_raw_ident_cps_gen _ _ p)).
        Notation raw_ident_index_inj_of p := (@Raw.ident.ident_index_inj (@raw_ident _ _ p) (@all_raw_idents _ _ p) (@raw_ident_index _ _ p) (@raw_ident_index_idempotent _ _ p)).
        Notation raw_ident_bl_of p := (@Raw.ident.ident_bl (@raw_ident _ _ p) (@all_raw_idents _ _ p) (@raw_ident_index _ _ p) (@raw_ident_index_idempotent _ _ p) (@eta_raw_ident_cps_gen _ _ p)).
        Notation raw_ident_beq_if_of p := (@Raw.ident.ident_beq_if (@raw_ident _ _ p) (@all_raw_idents _ _ p) (@raw_ident_index _ _ p) (@raw_ident_index_idempotent _ _ p) (@eta_raw_ident_cps_gen _ _ p)).
        Notation raw_ident_transport_opt_of p := (@Raw.ident.ident_transport_opt (@raw_ident _ _ p) (@all_raw_idents _ _ p) (@raw_ident_index _ _ p) (@raw_ident_index_idempotent _ _ p) (@eta_raw_ident_cps_gen _ _ p)).
        Notation raw_ident_to_cident_of p := (@Raw.ident.ident_to_cident (@all_idents _ _ p) (@raw_ident _ _ p) (@raw_ident_index _ _ p) (@eta_raw_ident_cps_gen _ _ p)).
        Notation prefull_types_of p := (@Raw.ident.prefull_types _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p)).
        Notation full_types_of p := (@Raw.ident.full_types _ _ (@raw_ident _ _ p) (@eta_raw_ident_cps_gen _ _ p) (@raw_ident_infos_of _ _ p)).
        Notation is_simple_of p := (@Raw.ident.is_simple _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p)).
        Notation type_of_of p := (@Raw.ident.type_of _ _ (@raw_ident _ _ p) (@eta_raw_ident_cps_gen _ _ p) (@raw_ident_infos_of _ _ p)).
        Notation folded_invert_bind_args_of p := (@Raw.ident.folded_invert_bind_args _ _ (@eta_ident_cps_gen _ _ p) (@raw_ident _ _ p) (@all_raw_idents _ _ p) (@raw_ident_index _ _ p) (@raw_ident_index_idempotent _ _ p) (@eta_raw_ident_cps_gen _ _ p) (@raw_ident_infos_of _ _ p) (@split_raw_ident_gen _ _ p)).
        Notation raw_to_typed_of p := (@Raw.ident.to_typed _ _ (@raw_ident _ _ p) (@eta_raw_ident_cps_gen _ _ p) (@raw_ident_infos_of _ _ p)).
        Notation try_unify_split_args_of p := (@Raw.ident.try_unify_split_args _ _ (@raw_ident _ _ p) (@all_raw_idents _ _ p) (@raw_ident_index _ _ p) (@raw_ident_index_idempotent _ _ p) (@eta_raw_ident_cps_gen _ _ p) (@raw_ident_infos_of _ _ p)).

        Notation eta_pattern_ident_cps_gen2_of p := (@ident.eta_ident_cps_gen2 _ (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p)).
        Notation eta_pattern_ident_cps_gen3_of p := (@ident.eta_ident_cps_gen3 _ (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p)).
        Notation split_types_subst_default_of p := (@ident.split_types_subst_default _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@pattern_ident _ _ p) (@split_types _ _ p)).
        Notation prearg_types_of p := (@ident.prearg_types _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@pattern_ident _ _ p) (@split_types _ _ p)).
        Notation strip_types_of p := (@ident.strip_types _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p) (@split_types _ _ p)).
        Notation arg_types_of p := (@ident.arg_types _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p) (@split_types _ _ p)).
        Notation to_typed_of p := (@ident.to_typed _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p) (@split_types _ _ p) (@to_type_split_types_subst_default_eq _ _ p)).
        Notation type_of_list_arg_types_beq_of p := (@ident.type_of_list_arg_types_beq _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p) (@split_types _ _ p)).
        Notation reflect_type_of_list_arg_types_beq_of p := (@ident.reflect_type_of_list_arg_types_beq _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p) (@split_types _ _ p)).
        Notation preof_typed_ident_sig_of p := (@ident.preof_typed_ident_sig _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@split_raw_ident_gen _ _ p) (@pattern_ident _ _ p) (@split_types _ _ p) (@add_types_from_raw_sig _ _ p)).
        Notation preof_typed_ident_of p := (@ident.preof_typed_ident _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@split_raw_ident_gen _ _ p) (@pattern_ident _ _ p) (@split_types _ _ p) (@add_types_from_raw_sig _ _ p) (@projT1_add_types_from_raw_sig_eq _ _ p)).
        Notation of_typed_ident_of p := (@ident.of_typed_ident _ _ (@eta_ident_cps_gen _ _ p) (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@split_raw_ident_gen _ _ p) (@pattern_ident _ _ p) (@split_types _ _ p) (@add_types_from_raw_sig _ _ p) (@projT1_add_types_from_raw_sig_eq _ _ p)).
        Notation arg_types_of_typed_ident_of p := (@ident.arg_types_of_typed_ident _ _ (@eta_ident_cps_gen _ _ p) (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@split_raw_ident_gen _ _ p) (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p) (@split_types _ _ p) (@add_types_from_raw_sig _ _ p) (@projT1_add_types_from_raw_sig_eq _ _ p)).
        Notation folded_unify_of p := (@ident.folded_unify _ _ (@eta_ident_cps_gen _ _ p) (@eta_ident_cps_gen_expand_literal _ _ p) (@raw_ident _ _ p) (@all_raw_idents _ _ p) (@raw_ident_index _ _ p) (@raw_ident_index_idempotent _ _ p) (@eta_raw_ident_cps_gen _ _ p) (@raw_ident_infos_of _ _ p) (@split_raw_ident_gen _ _ p) (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p) (@eta_pattern_ident_cps_gen_expand_literal _ _ p) (@split_types _ _ p) (@add_types_from_raw_sig _ _ p) (@projT1_add_types_from_raw_sig_eq _ _ p)).

        Notation eta_ident_cps_gen2 := (@eta_ident_cps_gen2_of _).
        Notation eta_ident_cps_gen3 := (@eta_ident_cps_gen3_of _).
        Notation raw_ident_beq := (@raw_ident_beq_of _).
        Notation raw_ident_lb := (@raw_ident_lb_of _).
        Notation raw_ident_index_inj := (@raw_ident_index_inj_of _).
        Notation raw_ident_bl := (@raw_ident_bl_of _).
        Notation raw_ident_beq_if := (@raw_ident_beq_if_of _).
        Notation raw_ident_transport_opt := (@raw_ident_transport_opt_of _).
        Notation raw_ident_to_cident := (@raw_ident_to_cident_of _).
        Notation prefull_types := (@prefull_types_of _).
        Notation full_types := (@full_types_of _).
        Notation is_simple := (@is_simple_of _).
        Notation type_of := (@type_of_of _).
        Notation folded_invert_bind_args := (@folded_invert_bind_args_of _).
        Notation raw_to_typed := (@raw_to_typed_of _).
        Notation try_unify_split_args := (@try_unify_split_args_of _).
        Notation eta_pattern_ident_cps_gen2 := (@eta_pattern_ident_cps_gen2_of _).
        Notation eta_pattern_ident_cps_gen3 := (@eta_pattern_ident_cps_gen3_of _).
        Notation split_types_subst_default := (@split_types_subst_default_of _).
        Notation prearg_types := (@prearg_types_of _).
        Notation strip_types := (@strip_types_of _).
        Notation arg_types := (@arg_types_of _).
        Notation to_typed := (@to_typed_of _).
        Notation type_of_list_arg_types_beq := (@type_of_list_arg_types_beq_of _).
        Notation reflect_type_of_list_arg_types_beq := (@reflect_type_of_list_arg_types_beq_of _).
        Notation preof_typed_ident_sig := (@preof_typed_ident_sig_of _).
        Notation preof_typed_ident := (@preof_typed_ident_of _).
        Notation of_typed_ident := (@of_typed_ident_of _).
        Notation arg_types_of_typed_ident := (@arg_types_of_typed_ident_of _).
        Notation folded_unify := (@folded_unify_of _).
      End GoalType.
    End ident.
  End pattern.
  Export pattern.base.Notations.
End Compilers.
