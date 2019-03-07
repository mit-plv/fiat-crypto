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
Require Import Crypto.Language.
Import ListNotations. Local Open Scope list_scope.
Import PrimitiveSigma.Primitive.

Module Compilers.
  Set Boolean Equality Schemes.
  Set Decidable Equality Schemes.
  Export Language.Compilers.

  Local Notation type_of_list := (fold_right (fun A B => prod A B) unit).
  Local Notation type_of_list_cps := (fold_right (fun a K => a -> K)).
  Module pattern.
    Notation EvarMap := (PositiveMap.t Compilers.base.type).
    Module base.
      Local Notation einterp := type.interp.
      Module type.
        Inductive type := var (p : positive) | type_base (t : Compilers.base.type.base) | prod (A B : type) | list (A : type) | option (A : type).
      End type.
      Notation type := type.type.

      Fixpoint relax (t : Compilers.base.type) : type
        := match t with
           | Compilers.base.type.type_base t => type.type_base t
           | Compilers.base.type.prod A B => type.prod (relax A) (relax B)
           | Compilers.base.type.list A => type.list (relax A)
           | Compilers.base.type.option A => type.option (relax A)
           end.

      Definition lookup_default (p : positive) (evar_map : EvarMap) : Compilers.base.type
        := match PositiveMap.find p evar_map with
           | Datatypes.Some t => t
           | Datatypes.None => Compilers.base.type.type_base base.type.unit
           end.

      Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : Compilers.base.type
        := match ptype with
           | type.var p => lookup_default p evar_map
           | type.type_base t => Compilers.base.type.type_base t
           | type.prod A B
             => Compilers.base.type.prod (subst_default A evar_map) (subst_default B evar_map)
           | type.list A => Compilers.base.type.list (subst_default A evar_map)
           | type.option A => Compilers.base.type.option (subst_default A evar_map)
           end.

      Fixpoint collect_vars (t : type) : PositiveSet.t
        := match t with
           | type.var p => PositiveSet.add p PositiveSet.empty
           | type.type_base t => PositiveSet.empty
           | type.prod A B => PositiveSet.union (collect_vars A) (collect_vars B)
           | type.list A => collect_vars A
           | type.option A => collect_vars A
           end.

      Module Notations.
        Global Coercion type.type_base : Compilers.base.type.base >-> type.type.
        Bind Scope pbtype_scope with type.type.
        (*Bind Scope ptype_scope with Compilers.type.type type.type.*) (* COQBUG(https://github.com/coq/coq/issues/7699) *)
        Delimit Scope ptype_scope with ptype.
        Delimit Scope pbtype_scope with pbtype.
        Notation "A * B" := (type.prod A%ptype B%ptype) : ptype_scope.
        Notation "A * B" := (type.prod A%pbtype B%pbtype) : pbtype_scope.
        Notation "()" := (type.type_base base.type.unit) : pbtype_scope.
        Notation "()" := (type.base (type.type_base base.type.unit)) : ptype_scope.
        Notation "A -> B" := (type.arrow A%ptype B%ptype) : ptype_scope.
        Notation "' n" := (type.var n) : pbtype_scope.
        Notation "' n" := (type.base (type.var n)) : ptype_scope.
        Notation "'1" := (type.var 1) : pbtype_scope.
        Notation "'2" := (type.var 2) : pbtype_scope.
        Notation "'3" := (type.var 3) : pbtype_scope.
        Notation "'4" := (type.var 4) : pbtype_scope.
        Notation "'5" := (type.var 5) : pbtype_scope.
        Notation "'1" := (type.base (type.var 1)) : ptype_scope.
        Notation "'2" := (type.base (type.var 2)) : ptype_scope.
        Notation "'3" := (type.base (type.var 3)) : ptype_scope.
        Notation "'4" := (type.base (type.var 4)) : ptype_scope.
        Notation "'5" := (type.base (type.var 5)) : ptype_scope.
      End Notations.
    End base.
    Notation type := (type.type base.type).
    Export base.Notations.

    Module type.
      Fixpoint relax (t : type.type Compilers.base.type) : type
        := match t with
           | type.base t => type.base (base.relax t)
           | type.arrow s d => type.arrow (relax s) (relax d)
           end.

      Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : type.type Compilers.base.type
        := match ptype with
           | type.base t => type.base (base.subst_default t evar_map)
           | type.arrow A B => type.arrow (subst_default A evar_map) (subst_default B evar_map)
           end.

      Fixpoint collect_vars (t : type) : PositiveSet.t
        := match t with
           | type.base t => base.collect_vars t
           | type.arrow s d => PositiveSet.union (collect_vars s) (collect_vars d)
           end.
    End type.

    (*
    Set Printing Coercions.
    Redirect "/tmp/pr" Print Compilers.ident.ident.
    Redirect "/tmp/sm" Show Match Compilers.ident.ident.
    *)
    (*
<<<
#!/usr/bin/env python2
import re, os

print_ident = r"""Inductive ident : defaults.type -> Set :=
    Literal : forall t : base.type.base,
              base.interp (Compilers.base.type.type_base t) ->
              ident
                ((fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base t))
  | Nat_succ : ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.nat) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.nat))%ptype
  | Nat_pred : ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.nat) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.nat))%ptype
  | Nat_max : ident
                ((fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat))%ptype
  | Nat_mul : ident
                ((fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat))%ptype
  | Nat_add : ident
                ((fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat))%ptype
  | Nat_sub : ident
                ((fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat))%ptype
  | Nat_eqb : ident
                ((fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.nat) ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.bool))%ptype
  | nil : forall t : Compilers.base.type,
          ident
            ((fun x : Compilers.base.type => type.base x)
               (Compilers.base.type.list t))
  | cons : forall t : Compilers.base.type,
           ident
             ((fun x : Compilers.base.type => type.base x) t ->
              (fun x : Compilers.base.type => type.base x)
                (Compilers.base.type.list t) ->
              (fun x : Compilers.base.type => type.base x)
                (Compilers.base.type.list t))%ptype
  | pair : forall A B : Compilers.base.type,
           ident
             ((fun x : Compilers.base.type => type.base x) A ->
              (fun x : Compilers.base.type => type.base x) B ->
              (fun x : Compilers.base.type => type.base x) (A * B)%etype)%ptype
  | fst : forall A B : Compilers.base.type,
          ident
            ((fun x : Compilers.base.type => type.base x) (A * B)%etype ->
             (fun x : Compilers.base.type => type.base x) A)%ptype
  | snd : forall A B : Compilers.base.type,
          ident
            ((fun x : Compilers.base.type => type.base x) (A * B)%etype ->
             (fun x : Compilers.base.type => type.base x) B)%ptype
  | prod_rect : forall A B T : Compilers.base.type,
                ident
                  (((fun x : Compilers.base.type => type.base x) A ->
                    (fun x : Compilers.base.type => type.base x) B ->
                    (fun x : Compilers.base.type => type.base x) T) ->
                   (fun x : Compilers.base.type => type.base x) (A * B)%etype ->
                   (fun x : Compilers.base.type => type.base x) T)%ptype
  | bool_rect : forall T : Compilers.base.type,
                ident
                  (((fun x : Compilers.base.type => type.base x) ()%etype ->
                    (fun x : Compilers.base.type => type.base x) T) ->
                   ((fun x : Compilers.base.type => type.base x) ()%etype ->
                    (fun x : Compilers.base.type => type.base x) T) ->
                   (fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.bool) ->
                   (fun x : Compilers.base.type => type.base x) T)%ptype
  | nat_rect : forall P : Compilers.base.type,
               ident
                 (((fun x : Compilers.base.type => type.base x) ()%etype ->
                   (fun x : Compilers.base.type => type.base x) P) ->
                  ((fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.nat) ->
                   (fun x : Compilers.base.type => type.base x) P ->
                   (fun x : Compilers.base.type => type.base x) P) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.nat) ->
                  (fun x : Compilers.base.type => type.base x) P)%ptype
  | nat_rect_arrow : forall P Q : Compilers.base.type,
                     ident
                       (((fun x : Compilers.base.type => type.base x) P ->
                         (fun x : Compilers.base.type => type.base x) Q) ->
                        ((fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.type_base base.type.nat) ->
                         ((fun x : Compilers.base.type => type.base x) P ->
                          (fun x : Compilers.base.type => type.base x) Q) ->
                         (fun x : Compilers.base.type => type.base x) P ->
                         (fun x : Compilers.base.type => type.base x) Q) ->
                        (fun x : Compilers.base.type => type.base x)
                          (Compilers.base.type.type_base base.type.nat) ->
                        (fun x : Compilers.base.type => type.base x) P ->
                        (fun x : Compilers.base.type => type.base x) Q)%ptype
  | eager_nat_rect : forall P : Compilers.base.type,
                     ident
                       (((fun x : Compilers.base.type => type.base x)
                           ()%etype ->
                         (fun x : Compilers.base.type => type.base x) P) ->
                        ((fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.type_base base.type.nat) ->
                         (fun x : Compilers.base.type => type.base x) P ->
                         (fun x : Compilers.base.type => type.base x) P) ->
                        (fun x : Compilers.base.type => type.base x)
                          (Compilers.base.type.type_base base.type.nat) ->
                        (fun x : Compilers.base.type => type.base x) P)%ptype
  | eager_nat_rect_arrow : forall P Q : Compilers.base.type,
                           ident
                             (((fun x : Compilers.base.type => type.base x) P ->
                               (fun x : Compilers.base.type => type.base x) Q) ->
                              ((fun x : Compilers.base.type => type.base x)
                                 (Compilers.base.type.type_base base.type.nat) ->
                               ((fun x : Compilers.base.type => type.base x)
                                  P ->
                                (fun x : Compilers.base.type => type.base x)
                                  Q) ->
                               (fun x : Compilers.base.type => type.base x) P ->
                               (fun x : Compilers.base.type => type.base x) Q) ->
                              (fun x : Compilers.base.type => type.base x)
                                (Compilers.base.type.type_base base.type.nat) ->
                              (fun x : Compilers.base.type => type.base x) P ->
                              (fun x : Compilers.base.type => type.base x) Q)%ptype
  | list_rect : forall A P : Compilers.base.type,
                ident
                  (((fun x : Compilers.base.type => type.base x) ()%etype ->
                    (fun x : Compilers.base.type => type.base x) P) ->
                   ((fun x : Compilers.base.type => type.base x) A ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.list A) ->
                    (fun x : Compilers.base.type => type.base x) P ->
                    (fun x : Compilers.base.type => type.base x) P) ->
                   (fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.list A) ->
                   (fun x : Compilers.base.type => type.base x) P)%ptype
  | eager_list_rect : forall A P : Compilers.base.type,
                      ident
                        (((fun x : Compilers.base.type => type.base x)
                            ()%etype ->
                          (fun x : Compilers.base.type => type.base x) P) ->
                         ((fun x : Compilers.base.type => type.base x) A ->
                          (fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.list A) ->
                          (fun x : Compilers.base.type => type.base x) P ->
                          (fun x : Compilers.base.type => type.base x) P) ->
                         (fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.list A) ->
                         (fun x : Compilers.base.type => type.base x) P)%ptype
  | eager_list_rect_arrow : forall A P Q : Compilers.base.type,
                            ident
                              (((fun x : Compilers.base.type => type.base x)
                                  P ->
                                (fun x : Compilers.base.type => type.base x)
                                  Q) ->
                               ((fun x : Compilers.base.type => type.base x)
                                  A ->
                                (fun x : Compilers.base.type => type.base x)
                                  (Compilers.base.type.list A) ->
                                ((fun x : Compilers.base.type => type.base x)
                                   P ->
                                 (fun x : Compilers.base.type => type.base x)
                                   Q) ->
                                (fun x : Compilers.base.type => type.base x)
                                  P ->
                                (fun x : Compilers.base.type => type.base x)
                                  Q) ->
                               (fun x : Compilers.base.type => type.base x)
                                 (Compilers.base.type.list A) ->
                               (fun x : Compilers.base.type => type.base x) P ->
                               (fun x : Compilers.base.type => type.base x) Q)%ptype
  | list_case : forall A P : Compilers.base.type,
                ident
                  (((fun x : Compilers.base.type => type.base x) ()%etype ->
                    (fun x : Compilers.base.type => type.base x) P) ->
                   ((fun x : Compilers.base.type => type.base x) A ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.list A) ->
                    (fun x : Compilers.base.type => type.base x) P) ->
                   (fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.list A) ->
                   (fun x : Compilers.base.type => type.base x) P)%ptype
  | List_length : forall T : Compilers.base.type,
                  ident
                    ((fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.list T) ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.nat))%ptype
  | List_seq : ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.nat) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.nat) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.list
                       (Compilers.base.type.type_base base.type.nat)))%ptype
  | List_firstn : forall A : Compilers.base.type,
                  ident
                    ((fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.nat) ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.list A) ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.list A))%ptype
  | List_skipn : forall A : Compilers.base.type,
                 ident
                   ((fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.nat) ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.list A) ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.list A))%ptype
  | List_repeat : forall A : Compilers.base.type,
                  ident
                    ((fun x : Compilers.base.type => type.base x) A ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.nat) ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.list A))%ptype
  | List_combine : forall A B : Compilers.base.type,
                   ident
                     ((fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.list A) ->
                      (fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.list B) ->
                      (fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.list (A * B)))%ptype
  | List_map : forall A B : Compilers.base.type,
               ident
                 (((fun x : Compilers.base.type => type.base x) A ->
                   (fun x : Compilers.base.type => type.base x) B) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.list A) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.list B))%ptype
  | List_app : forall A : Compilers.base.type,
               ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.list A) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.list A) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.list A))%ptype
  | List_rev : forall A : Compilers.base.type,
               ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.list A) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.list A))%ptype
  | List_flat_map : forall A B : Compilers.base.type,
                    ident
                      (((fun x : Compilers.base.type => type.base x) A ->
                        (fun x : Compilers.base.type => type.base x)
                          (Compilers.base.type.list B)) ->
                       (fun x : Compilers.base.type => type.base x)
                         (Compilers.base.type.list A) ->
                       (fun x : Compilers.base.type => type.base x)
                         (Compilers.base.type.list B))%ptype
  | List_partition : forall A : Compilers.base.type,
                     ident
                       (((fun x : Compilers.base.type => type.base x) A ->
                         (fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.type_base base.type.bool)) ->
                        (fun x : Compilers.base.type => type.base x)
                          (Compilers.base.type.list A) ->
                        (fun x : Compilers.base.type => type.base x)
                          (Compilers.base.type.list A *
                           Compilers.base.type.list A)%etype)%ptype
  | List_fold_right : forall A B : Compilers.base.type,
                      ident
                        (((fun x : Compilers.base.type => type.base x) B ->
                          (fun x : Compilers.base.type => type.base x) A ->
                          (fun x : Compilers.base.type => type.base x) A) ->
                         (fun x : Compilers.base.type => type.base x) A ->
                         (fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.list B) ->
                         (fun x : Compilers.base.type => type.base x) A)%ptype
  | List_update_nth : forall T : Compilers.base.type,
                      ident
                        ((fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.type_base base.type.nat) ->
                         ((fun x : Compilers.base.type => type.base x) T ->
                          (fun x : Compilers.base.type => type.base x) T) ->
                         (fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.list T) ->
                         (fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.list T))%ptype
  | List_nth_default : forall T : Compilers.base.type,
                       ident
                         ((fun x : Compilers.base.type => type.base x) T ->
                          (fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.list T) ->
                          (fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.type_base base.type.nat) ->
                          (fun x : Compilers.base.type => type.base x) T)%ptype
  | Z_add : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_mul : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_pow : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_sub : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_opp : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_div : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_modulo : ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_log2 : ident
               ((fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_log2_up : ident
                  ((fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z) ->
                   (fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_eqb : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.bool))%ptype
  | Z_leb : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.bool))%ptype
  | Z_ltb : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.bool))%ptype
  | Z_geb : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.bool))%ptype
  | Z_gtb : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.bool))%ptype
  | Z_of_nat : ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.nat) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_to_nat : ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.nat))%ptype
  | Z_shiftr : ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_shiftl : ident
                 ((fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z) ->
                  (fun x : Compilers.base.type => type.base x)
                    (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_land : ident
               ((fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_lor : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_min : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_max : ident
              ((fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z) ->
               (fun x : Compilers.base.type => type.base x)
                 (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_bneg : ident
               ((fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_lnot_modulo : ident
                      ((fun x : Compilers.base.type => type.base x)
                         (Compilers.base.type.type_base base.type.Z) ->
                       (fun x : Compilers.base.type => type.base x)
                         (Compilers.base.type.type_base base.type.Z) ->
                       (fun x : Compilers.base.type => type.base x)
                         (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_mul_split : ident
                    ((fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z) ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z) ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z) ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z *
                        Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | Z_add_get_carry : ident
                        ((fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.type_base base.type.Z) ->
                         (fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.type_base base.type.Z) ->
                         (fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.type_base base.type.Z) ->
                         (fun x : Compilers.base.type => type.base x)
                           (Compilers.base.type.type_base base.type.Z *
                            Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | Z_add_with_carry : ident
                         ((fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.type_base base.type.Z) ->
                          (fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.type_base base.type.Z) ->
                          (fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.type_base base.type.Z) ->
                          (fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_add_with_get_carry : ident
                             ((fun x : Compilers.base.type => type.base x)
                                (Compilers.base.type.type_base base.type.Z) ->
                              (fun x : Compilers.base.type => type.base x)
                                (Compilers.base.type.type_base base.type.Z) ->
                              (fun x : Compilers.base.type => type.base x)
                                (Compilers.base.type.type_base base.type.Z) ->
                              (fun x : Compilers.base.type => type.base x)
                                (Compilers.base.type.type_base base.type.Z) ->
                              (fun x : Compilers.base.type => type.base x)
                                (Compilers.base.type.type_base base.type.Z *
                                 Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | Z_sub_get_borrow : ident
                         ((fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.type_base base.type.Z) ->
                          (fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.type_base base.type.Z) ->
                          (fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.type_base base.type.Z) ->
                          (fun x : Compilers.base.type => type.base x)
                            (Compilers.base.type.type_base base.type.Z *
                             Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | Z_sub_with_get_borrow : ident
                              ((fun x : Compilers.base.type => type.base x)
                                 (Compilers.base.type.type_base base.type.Z) ->
                               (fun x : Compilers.base.type => type.base x)
                                 (Compilers.base.type.type_base base.type.Z) ->
                               (fun x : Compilers.base.type => type.base x)
                                 (Compilers.base.type.type_base base.type.Z) ->
                               (fun x : Compilers.base.type => type.base x)
                                 (Compilers.base.type.type_base base.type.Z) ->
                               (fun x : Compilers.base.type => type.base x)
                                 (Compilers.base.type.type_base base.type.Z *
                                  Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | Z_zselect : ident
                  ((fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z) ->
                   (fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z) ->
                   (fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z) ->
                   (fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_add_modulo : ident
                     ((fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.type_base base.type.Z) ->
                      (fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.type_base base.type.Z) ->
                      (fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.type_base base.type.Z) ->
                      (fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_rshi : ident
               ((fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_cc_m : ident
               ((fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_cast : zrange ->
             ident
               ((fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z) ->
                (fun x : Compilers.base.type => type.base x)
                  (Compilers.base.type.type_base base.type.Z))%ptype
  | Z_cast2 : zrange * zrange ->
              ident
                ((fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.Z *
                    Compilers.base.type.type_base base.type.Z)%etype ->
                 (fun x : Compilers.base.type => type.base x)
                   (Compilers.base.type.type_base base.type.Z *
                    Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | option_Some : forall A : Compilers.base.type,
                  ident
                    ((fun x : Compilers.base.type => type.base x) A ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.option A))%ptype
  | option_None : forall A : Compilers.base.type,
                  ident
                    ((fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.option A))
  | option_rect : forall A P : Compilers.base.type,
                  ident
                    (((fun x : Compilers.base.type => type.base x) A ->
                      (fun x : Compilers.base.type => type.base x) P) ->
                     ((fun x : Compilers.base.type => type.base x) ()%etype ->
                      (fun x : Compilers.base.type => type.base x) P) ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.option A) ->
                     (fun x : Compilers.base.type => type.base x) P)%ptype
  | Build_zrange : ident
                     ((fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.type_base base.type.Z) ->
                      (fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.type_base base.type.Z) ->
                      (fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.type_base base.type.zrange))%ptype
  | zrange_rect : forall P : Compilers.base.type,
                  ident
                    (((fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.type_base base.type.Z) ->
                      (fun x : Compilers.base.type => type.base x)
                        (Compilers.base.type.type_base base.type.Z) ->
                      (fun x : Compilers.base.type => type.base x) P) ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.zrange) ->
                     (fun x : Compilers.base.type => type.base x) P)%ptype
  | fancy_add : Z ->
                Z ->
                ident
                  ((fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z *
                      Compilers.base.type.type_base base.type.Z)%etype ->
                   (fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z *
                      Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | fancy_addc : Z ->
                 Z ->
                 ident
                   ((fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z)%etype ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | fancy_sub : Z ->
                Z ->
                ident
                  ((fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z *
                      Compilers.base.type.type_base base.type.Z)%etype ->
                   (fun x : Compilers.base.type => type.base x)
                     (Compilers.base.type.type_base base.type.Z *
                      Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | fancy_subb : Z ->
                 Z ->
                 ident
                   ((fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z)%etype ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z)%etype)%ptype
  | fancy_mulll : Z ->
                  ident
                    ((fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z *
                        Compilers.base.type.type_base base.type.Z)%etype ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z))%ptype
  | fancy_mullh : Z ->
                  ident
                    ((fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z *
                        Compilers.base.type.type_base base.type.Z)%etype ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z))%ptype
  | fancy_mulhl : Z ->
                  ident
                    ((fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z *
                        Compilers.base.type.type_base base.type.Z)%etype ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z))%ptype
  | fancy_mulhh : Z ->
                  ident
                    ((fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z *
                        Compilers.base.type.type_base base.type.Z)%etype ->
                     (fun x : Compilers.base.type => type.base x)
                       (Compilers.base.type.type_base base.type.Z))%ptype
  | fancy_rshi : Z ->
                 Z ->
                 ident
                   ((fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z)%etype ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z))%ptype
  | fancy_selc : ident
                   ((fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z)%etype ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z))%ptype
  | fancy_selm : Z ->
                 ident
                   ((fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z)%etype ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z))%ptype
  | fancy_sell : ident
                   ((fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z)%etype ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z))%ptype
  | fancy_addm : ident
                   ((fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z *
                       Compilers.base.type.type_base base.type.Z)%etype ->
                    (fun x : Compilers.base.type => type.base x)
                      (Compilers.base.type.type_base base.type.Z))%ptype

"""
show_match_ident = r"""match # with
 | ident.Literal t v =>
 | ident.Nat_succ =>
 | ident.Nat_pred =>
 | ident.Nat_max =>
 | ident.Nat_mul =>
 | ident.Nat_add =>
 | ident.Nat_sub =>
 | ident.Nat_eqb =>
 | ident.nil t =>
 | ident.cons t =>
 | ident.pair A B =>
 | ident.fst A B =>
 | ident.snd A B =>
 | ident.prod_rect A B T =>
 | ident.bool_rect T =>
 | ident.nat_rect P =>
 | ident.nat_rect_arrow P Q =>
 | ident.eager_nat_rect P =>
 | ident.eager_nat_rect_arrow P Q =>
 | ident.list_rect A P =>
 | ident.eager_list_rect A P =>
 | ident.eager_list_rect_arrow A P Q =>
 | ident.list_case A P =>
 | ident.List_length T =>
 | ident.List_seq =>
 | ident.List_firstn A =>
 | ident.List_skipn A =>
 | ident.List_repeat A =>
 | ident.List_combine A B =>
 | ident.List_map A B =>
 | ident.List_app A =>
 | ident.List_rev A =>
 | ident.List_flat_map A B =>
 | ident.List_partition A =>
 | ident.List_fold_right A B =>
 | ident.List_update_nth T =>
 | ident.List_nth_default T =>
 | ident.Z_add =>
 | ident.Z_mul =>
 | ident.Z_pow =>
 | ident.Z_sub =>
 | ident.Z_opp =>
 | ident.Z_div =>
 | ident.Z_modulo =>
 | ident.Z_log2 =>
 | ident.Z_log2_up =>
 | ident.Z_eqb =>
 | ident.Z_leb =>
 | ident.Z_ltb =>
 | ident.Z_geb =>
 | ident.Z_gtb =>
 | ident.Z_of_nat =>
 | ident.Z_to_nat =>
 | ident.Z_shiftr =>
 | ident.Z_shiftl =>
 | ident.Z_land =>
 | ident.Z_lor =>
 | ident.Z_min =>
 | ident.Z_max =>
 | ident.Z_bneg =>
 | ident.Z_lnot_modulo =>
 | ident.Z_mul_split =>
 | ident.Z_add_get_carry =>
 | ident.Z_add_with_carry =>
 | ident.Z_add_with_get_carry =>
 | ident.Z_sub_get_borrow =>
 | ident.Z_sub_with_get_borrow =>
 | ident.Z_zselect =>
 | ident.Z_add_modulo =>
 | ident.Z_rshi =>
 | ident.Z_cc_m =>
 | ident.Z_cast range =>
 | ident.Z_cast2 range =>
 | ident.option_Some A =>
 | ident.option_None A =>
 | ident.option_rect A P =>
 | ident.Build_zrange =>
 | ident.zrange_rect P =>
 | ident.fancy_add log2wordmax imm =>
 | ident.fancy_addc log2wordmax imm =>
 | ident.fancy_sub log2wordmax imm =>
 | ident.fancy_subb log2wordmax imm =>
 | ident.fancy_mulll log2wordmax =>
 | ident.fancy_mullh log2wordmax =>
 | ident.fancy_mulhl log2wordmax =>
 | ident.fancy_mulhh log2wordmax =>
 | ident.fancy_rshi log2wordmax x =>
 | ident.fancy_selc =>
 | ident.fancy_selm log2wordmax =>
 | ident.fancy_sell =>
 | ident.fancy_addm =>
 end

"""
remake = False
if remake:
  assert(os.path.exists('/tmp/pr.out'))
  assert(os.path.exists('/tmp/sm.out'))
  with open('/tmp/pr.out', 'r') as f: print_ident = re.sub(r'^For [^ ]*: Argument.*', '', f.read(), flags=re.MULTILINE|re.DOTALL)
  with open('/tmp/sm.out', 'r') as f: show_match_ident = f.read()

prefix = 'Compilers.'
indent0 = '    '
indent1 = '  ' + indent0
indent2 = '  ' + indent1
#exts = ('Unit', 'Z', 'Bool', 'Nat')
base_types = [('%sbase.type.' % prefix) + i for i in ('unit', 'Z', 'bool', 'nat', 'zrange')]
type_or_set = 'Type'
ctors = [i.strip('|=> ').split(' ') for i in show_match_ident.split('\n') if i.strip().startswith('|')]
assert(ctors[0][0] == 'ident.Literal')
assert(len(ctors[0]) > 1)
#ctors = [[ctors[0][0] + ext] + ctors[0][2:] for ext in exts] + ctors[1:]
ctors_with_prefix = [[prefix + i[0]] + i[1:] for i in ctors]
ctors_no_prefix = [[i[0].replace('ident.', '')] + i[1:] for i in ctors]
pctors = [i[0] for i in ctors_no_prefix]
def get_dep_types(case):
  dep_tys = re.findall('forall ([^:]+):([^,]+),', case)
  if len(dep_tys) == 0: return []
  dep_tys = dep_tys[0]
  return [dep_tys[-1].strip()] * len([i for i in dep_tys[0].split(' ') if i.strip()])
split_print_ident = print_ident.replace('  Literal ', ' | Literal ').replace('\n', ' ').split('|')[1:]
ttypes = [get_dep_types(case) for case in split_print_ident]
ctypes = [[i.strip() for i in re.sub(r'forall [^,]+,', '', i[i.find(':')+1:i.find('ident')]).strip(' ->').split('->') if i.strip()]
          for i in split_print_ident]
crettypes = [prefix + 'ident.' + re.sub(r'\(fun x : [^ ]+ => ([^ ]+) x\)', r'\1', re.sub('  +', ' ', i[i.find('ident'):])).strip()
             for i in split_print_ident]
named_ttypes_with_prefix = [[(name, ty) for name, ty in zip(ctor[1:], tys)]
                            for ctor, tys in zip(ctors, ttypes)]
named_ttypes = [[(name, ty.replace(prefix, '')) for name, ty in nt] for nt in named_ttypes_with_prefix]
pctors_with_typed_args = [(pctor + ' ' + ' '.join('{%s : %s}' % name_ty for name_ty in ntys)).strip()
                          for pctor, ntys in zip(pctors, named_ttypes)]
pctors_with_args = [(pctor + ' ' + ' '.join(name for name, ty in ntys)).strip()
                    for pctor, ntys in zip(pctors, named_ttypes)]
pctors_with_underscores = [(pctor + ' ' + ' '.join('_' for name, ty in ntys)).strip()
                           for pctor, ntys in zip(pctors, named_ttypes)]
rettypes = [i.replace(prefix + 'ident.ident', 'ident').replace(prefix, '').replace('%etype', '%pbtype') for i in crettypes]

# N.B. We assume forall-quantification in the types has names that match the arguments from Show Match

retcode = r"""Require Import Coq.ZArith.ZArith.
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
Require Import Crypto.Language.
Import ListNotations. Local Open Scope list_scope.
Import PrimitiveSigma.Primitive.

Module Compilers.
  Set Boolean Equality Schemes.
  Set Decidable Equality Schemes.
  Export Language.Compilers.

  Local Notation type_of_list := (fold_right (fun A B => prod A B) unit).
  Local Notation type_of_list_cps := (fold_right (fun a K => a -> K)).
  Module pattern.
    Notation EvarMap := (PositiveMap.t Compilers.base.type).
    Module base.
      Local Notation einterp := type.interp.
      Module type.
        Inductive type := var (p : positive) | type_base (t : Compilers.base.type.base) | prod (A B : type) | list (A : type) | option (A : type).
      End type.
      Notation type := type.type.

      Fixpoint relax (t : Compilers.base.type) : type
        := match t with
           | Compilers.base.type.type_base t => type.type_base t
           | Compilers.base.type.prod A B => type.prod (relax A) (relax B)
           | Compilers.base.type.list A => type.list (relax A)
           | Compilers.base.type.option A => type.option (relax A)
           end.

      Definition lookup_default (p : positive) (evar_map : EvarMap) : Compilers.base.type
        := match PositiveMap.find p evar_map with
           | Datatypes.Some t => t
           | Datatypes.None => Compilers.base.type.type_base base.type.unit
           end.

      Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : Compilers.base.type
        := match ptype with
           | type.var p => lookup_default p evar_map
           | type.type_base t => Compilers.base.type.type_base t
           | type.prod A B
             => Compilers.base.type.prod (subst_default A evar_map) (subst_default B evar_map)
           | type.list A => Compilers.base.type.list (subst_default A evar_map)
           | type.option A => Compilers.base.type.option (subst_default A evar_map)
           end.

      Fixpoint collect_vars (t : type) : PositiveSet.t
        := match t with
           | type.var p => PositiveSet.add p PositiveSet.empty
           | type.type_base t => PositiveSet.empty
           | type.prod A B => PositiveSet.union (collect_vars A) (collect_vars B)
           | type.list A => collect_vars A
           | type.option A => collect_vars A
           end.

      Module Notations.
        Global Coercion type.type_base : Compilers.base.type.base >-> type.type.
        Bind Scope pbtype_scope with type.type.
        (*Bind Scope ptype_scope with Compilers.type.type type.type.*) (* COQBUG(https://github.com/coq/coq/issues/7699) *)
        Delimit Scope ptype_scope with ptype.
        Delimit Scope pbtype_scope with pbtype.
        Notation "A * B" := (type.prod A%ptype B%ptype) : ptype_scope.
        Notation "A * B" := (type.prod A%pbtype B%pbtype) : pbtype_scope.
        Notation "()" := (type.type_base base.type.unit) : pbtype_scope.
        Notation "()" := (type.base (type.type_base base.type.unit)) : ptype_scope.
        Notation "A -> B" := (type.arrow A%ptype B%ptype) : ptype_scope.
        Notation "' n" := (type.var n) : pbtype_scope.
        Notation "' n" := (type.base (type.var n)) : ptype_scope.
        Notation "'1" := (type.var 1) : pbtype_scope.
        Notation "'2" := (type.var 2) : pbtype_scope.
        Notation "'3" := (type.var 3) : pbtype_scope.
        Notation "'4" := (type.var 4) : pbtype_scope.
        Notation "'5" := (type.var 5) : pbtype_scope.
        Notation "'1" := (type.base (type.var 1)) : ptype_scope.
        Notation "'2" := (type.base (type.var 2)) : ptype_scope.
        Notation "'3" := (type.base (type.var 3)) : ptype_scope.
        Notation "'4" := (type.base (type.var 4)) : ptype_scope.
        Notation "'5" := (type.base (type.var 5)) : ptype_scope.
      End Notations.
    End base.
    Notation type := (type.type base.type).
    Export base.Notations.

    Module type.
      Fixpoint relax (t : type.type Compilers.base.type) : type
        := match t with
           | type.base t => type.base (base.relax t)
           | type.arrow s d => type.arrow (relax s) (relax d)
           end.

      Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : type.type Compilers.base.type
        := match ptype with
           | type.base t => type.base (base.subst_default t evar_map)
           | type.arrow A B => type.arrow (subst_default A evar_map) (subst_default B evar_map)
           end.

      Fixpoint collect_vars (t : type) : PositiveSet.t
        := match t with
           | type.base t => base.collect_vars t
           | type.arrow s d => PositiveSet.union (collect_vars s) (collect_vars d)
           end.
    End type.

    (""" + """*
    Set Printing Coercions.
    Redirect "/tmp/pr" Print Compilers.ident.ident.
    Redirect "/tmp/sm" Show Match Compilers.ident.ident.
    *""" + """)
"""

def fold_right_pair(ls, tt='tt'):
  if len(ls) == 0: return tt
  return '(' + ls[0] + ', ' + fold_right_pair(ls[1:], tt=tt) + ')'

def addnewline(s): return re.sub(r' +$', '', s + '\n', flags=re.MULTILINE)

def get_updated_contents():
  contents = open(__file__).read()
  contents = re.sub(r'^remake = True', r'remake = False', contents, flags=re.MULTILINE)
  contents = re.sub(r'^print_ident = r""".*?"""', r'print_ident = r"""' + print_ident + r'"""', contents, flags=re.MULTILINE | re.DOTALL)
  contents = re.sub(r'^show_match_ident = r""".*?"""', r'show_match_ident = r"""' + show_match_ident + r'"""', contents, flags=re.MULTILINE | re.DOTALL)
  return contents

retcode += addnewline(r"""%s(*
<<<
%s
>>>
%s*)
""" % (indent0, get_updated_contents(), indent0))

maxeta = max([len(ttype + ctype) for ttype, ctype in zip(ttypes, ctypes)])
#if any(len(ttype) > 0 and len(ctype) > 0 for ttype, ctype in zip(ttypes, ctypes)):
#  retcode += addnewline(r"""%sLocal Notation eta_sigT x := (existT _ (projT1 x) (projT2 x)) (only parsing).""" % indent0)
if maxeta >= 2:
  retcode += addnewline(r"""%sLocal Notation eta2 x := (Datatypes.fst x, Datatypes.snd x) (only parsing).""" % indent0)
  retcode += addnewline(r"""%sLocal Notation eta2r x := (Datatypes.fst x, Datatypes.snd x) (only parsing).""" % indent0)
for i in range(3, maxeta+1):
  retcode += addnewline(r"""%sLocal Notation eta%d x := (eta%d (Datatypes.fst x), Datatypes.snd x) (only parsing).""" % (indent0, i, i-1))
  retcode += addnewline(r"""%sLocal Notation eta%dr x := (Datatypes.fst x, eta%dr (Datatypes.snd x)) (only parsing).""" % (indent0, i, i-1))
retcode += addnewline('')

def do_adjust_type(ctor, ctype):
  return len(ctor) > 1 and 'Literal' in ctor[0]

retcode += r"""
    Module Raw.
      Module ident.
"""

retcode += addnewline(r"""%sInductive ident :=
%s| %s.
""" % (indent2, indent2, ('\n' + indent2 + '| ').join(pctors)))

def make_prod_of_types(named_ttype, ctype):
  if len(named_ttype + ctype) == 0: return 'unit'
  if len(ctype) == 0: return ' * '.join(t for n, t in named_ttype)
  if len(named_ttype) == 0: return ' * '.join(ctype)
  if len(named_ttype) == 1: return '{ %s : %s & %s }' % (named_ttype[0][0], named_ttype[0][1], ' * '.join(ctype))
  return "{ tys : %s & let '(%s) := eta%d tys in %s }" % (' * '.join(t for n, t in named_ttype),
                                                          ', '.join(n for n, t in named_ttype),
                                                          len(named_ttype),
                                                          ' * '.join(ctype))

def make_pair_of_types(named_ttype, ctype, ctor):
  if len(named_ttype + ctype) == 0: return 'tt'
  if len(named_ttype + ctype) == 1: return ctor[-1]
  if len(named_ttype) == 0 or len(ctype) == 0: return '(%s)' % ', '.join(ctor[-len(named_ttype + ctype):])
  pr1 = (named_ttype[0][0] if len(named_ttype) == 1 else '(%s)' % ', '.join(n for n, t in named_ttype))
  pr2 = (ctor[-1] if len(ctype) == 1 else '(%s)' % ', '.join(ctor[-len(ctype):]))
  return '(existT _ %s %s)' % (pr1, pr2)

def make_fun_project(named_ttype, ctype, ctor):
  if len(named_ttype + ctype) == 0: return 'fun _ => '
  if len(named_ttype + ctype) == 1: return 'fun ' + ctor[-1] + ' => '
  if len(named_ttype) == 0 or len(ctype) == 0: return "fun arg => let '(%s) := eta%d arg in " % (', '.join(ctor[-len(named_ttype + ctype):]), len(named_ttype + ctype))
  pr1 = (named_ttype[0][0] if len(named_ttype) == 1 else '(%s)' % ', '.join(n for n, t in named_ttype))
  pr2 = (ctor[-1] if len(ctype) == 1 else '(%s)' % ', '.join(ctor[-len(ctype):]))
  pr1_eta = ('projT1 arg' if len(named_ttype) == 1 else 'eta%d (projT1 arg)' % len(named_ttype))
  pr2_eta = ('projT2 arg' if len(ctype) == 1 else 'eta%d (projT2 arg)' % len(ctype))
  return "fun arg => let '(%s, %s) := (%s, %s) in " % (pr1, pr2, pr1_eta, pr2_eta)

def make_fun_project_list(ctype, ctor):
  if len(ctype) == 0: return 'fun _ => '
  return "fun arg => let '%s := eta%dr arg in " % (fold_right_pair(ctor[-len(ctype):], tt='_'), len(ctype)+1)

def make_fun_project_match(named_ttype, ctype, ctor, retty, body):
  if len(named_ttype + ctype) == 0: return 'fun _ => ' + body
  if len(named_ttype + ctype) == 1: return 'fun ' + ctor[-1] + ' => ' + body
  if len(named_ttype) == 0 or len(ctype) == 0:
    return "fun arg => match eta%d arg as arg' return %s with (%s) => %s end" % (len(named_ttype + ctype), retty % "arg'", ', '.join(ctor[-len(named_ttype + ctype):]), body)
  pr1 = (named_ttype[0][0] if len(named_ttype) == 1 else '(%s)' % ', '.join(n for n, t in named_ttype))
  pr2 = (ctor[-1] if len(ctype) == 1 else '(%s)' % ', '.join(ctor[-len(ctype):]))
  pr1_eta = ('projT1 arg' if len(named_ttype) == 1 else 'eta%d (projT1 arg)' % len(named_ttype))
  pr2_eta = ('projT2 arg' if len(ctype) == 1 else 'eta%d (projT2 arg)' % len(ctype))
  return "fun arg => match existT _ (%s) (%s) as arg' return %s with existT %s %s => %s end" % (pr1_eta, pr2_eta, retty % "arg'", pr1, pr2, body)

retcode += addnewline((r"""%sDefinition full_types (idc : ident) : %s
  := match idc return %s with
     | %s
     end%%type.
""" % (indent2, type_or_set, type_or_set,
       '\n     | '.join(pctor + ' => ' + make_prod_of_types(named_ttype, ctype)
                        for pctor, named_ttype, ctype in zip(pctors, named_ttypes_with_prefix, ctypes)))).replace('\n', '\n' + indent2))

retcode += addnewline((r"""%sDefinition is_simple (idc : ident) : bool
  := match idc with
     | %s
     end.
""" % (indent2,
       '\n     | '.join(pctor + ' => ' + ('true' if len(named_ttype) == 0 else 'false')
                        for pctor, named_ttype in zip(pctors, named_ttypes_with_prefix)))).replace('\n', '\n' + indent2))

retcode += addnewline((r"""%sDefinition invert_bind_args {t} (idc : %sident.ident t) (pidc : ident) : Datatypes.option (full_types pidc)
  := match pidc, idc return Datatypes.option (full_types pidc) with
     | %s
     | %s
       => Datatypes.None
     end%%cps.
""" % (indent2, prefix,
       '\n     | '.join(pctor + ', ' + ' '.join(ctor) + ' => Datatypes.Some ' + make_pair_of_types(named_ttype, ctype, ctor)
                        for pctor, ctor, named_ttype, ctype in zip(pctors, ctors_with_prefix, named_ttypes_with_prefix, ctypes)),
       '\n     | '.join(pctor + ', _' for pctor in pctors))).replace('\n', '\n' + indent2))

retcode += addnewline((r"""%sDefinition type_of (pidc : ident) : full_types pidc -> %stype %sbase.type
  := match pidc return full_types pidc -> _ with
     | %s
     end%%etype.
""" % (indent2, prefix, prefix,
       '\n     | '.join(pctor + ' => '
                        + make_fun_project(named_ttype, ctype, ctor) + cretty.replace(prefix + 'ident.ident ', '')
                        for pctor, ctor, named_ttype, ctype, cretty in zip(pctors, ctors_with_prefix, named_ttypes_with_prefix, ctypes, crettypes)))).replace('\n', '\n' + indent2))
retcode += addnewline((r"""%sDefinition to_typed (pidc : ident) : forall args : full_types pidc, %sident.ident (type_of pidc args)
  := match pidc return forall args : full_types pidc, %sident.ident (type_of pidc args) with
     | %s
     end.
""" % (indent2, prefix, prefix,
       '\n     | '.join(pctor + ' => '
                        + make_fun_project_match(named_ttype, ctype, ctor, '%sident.ident (type_of %s %%s)' % (prefix, pctor), ("@" + ' '.join(ctor)))
                        for pctor, ctor, named_ttype, ctype in zip(pctors, ctors_with_prefix, named_ttypes_with_prefix, ctypes)))).replace('\n', '\n' + indent2))

retcode += r"""      End ident.
      Notation ident := ident.ident.
    End Raw.
"""

retcode +=r"""
    Module ident.
"""
retcode += addnewline((r"""%sDefinition eta_ident_cps {T : %stype %sbase.type -> Type} {t} (idc : %sident.ident t)
           (f : forall t', %sident.ident t' -> T t')
  : T t
  := match idc with
     | %s
     end.
""" % (indent1, prefix, prefix, prefix, prefix,
       '\n     | '.join(' '.join(ctor) + ' => f _ '
                        + (('%s' if len(ctor) == 1 else '(@%s)')
                           % ' '.join(ctor))
                        for ctor in ctors_with_prefix))).replace('\n', '\n' + indent1))

retcode += addnewline(r"""%sInductive ident : type -> Set :=
%s| %s.
""" % (indent1, indent1, ('\n' + indent1 + '| ').join('%s : %s' % ct for ct in zip(pctors_with_typed_args, rettypes))))

retcode += addnewline((r"""%sDefinition strip_types {t} (idc : ident t) : Raw.ident
  := match idc with
     | %s
     end.
""" % (indent1, '\n     | '.join('@' + pctor_with_args + ' => Raw.ident.' + pctor for pctor_with_args, pctor in zip(pctors_with_args, pctors)))).replace('\n', '\n' + indent1))

# here we assume that non-dependent arguments do not depend on dependent
# arguments which become generalized to patterns --- that is, only dependent
# arguments of type base.type.base can show up in the types of other identifier
# arguments.

retcode += addnewline((r"""%sDefinition arg_types {t} (idc : ident t) : list %s
  := match idc return list %s with
     | %s
     end%%type.
""" % (indent1, type_or_set, type_or_set,
       '\n     | '.join('@' + pctor + ' => [' + '; '.join(i + ' : ' + type_or_set for i in ctype) + ']'
                        for pctor, ctype in zip(pctors_with_args, ctypes)))).replace('\n', '\n' + indent1))

def to_type_var(name, ty):
  ty = ty.replace(prefix, '')
  return ({'base.type.base': 'type.base (base.type.type_base %s)' % name,
           'base.type': 'type.base %s' % name,
           'type': name,
           'type.type base.type': name})[ty]

#retcode += addnewline((r"""%sDefinition type_vars {t} (idc : ident t) : list type
#  := match idc with
#     | %s
#     end%%type.
#""" % (indent1,
#       '\n     | '.join('@' + pctor + ' => [' + '; '.join(to_type_var(n, t) for n, t in named_ttype) + ']'
#                        for pctor, named_ttype in zip(pctors_with_args, named_ttypes)))).replace('\n', '\n' + indent1))

retcode += addnewline((r"""%sDefinition to_typed {t} (idc : ident t) (evm : EvarMap) : type_of_list (arg_types idc) -> %sident.ident (pattern.type.subst_default t evm)
  := match idc in ident t return type_of_list (arg_types idc) -> %sident.ident (pattern.type.subst_default t evm) with
     | %s
     end.
""" % (indent1, prefix, prefix,
       '\n     | '.join('@' + pctor + ' => '
                        + make_fun_project_list(ctype, ctor)
                        + '@' + ' '.join([ctor[0]] + ['_' for _ in ctor[1:len(ctor)-len(ctype)]] + ctor[len(ctor)-len(ctype):])
                        for pctor, ctor, ctype in zip(pctors_with_args, ctors_with_prefix, ctypes)))).replace('\n', '\n' + indent1))

assert(ctors[0][0] == 'ident.Literal')
assert(len(ctypes[0]) == 1)

retcode += addnewline((r"""%sDefinition unify {t t'} (pidc : ident t) (idc : %sident.ident t') : Datatypes.option (type_of_list (@arg_types t pidc))
  := match pidc, idc return Datatypes.option (type_of_list (arg_types pidc)) with
     | %s
     | %s
     | %s
       => Datatypes.None
     end%%cps.
""" % (indent1, prefix,
       '\n     | '.join('@' + pctor + ' ' + ty + ', ' + ' '.join([ctor[0], ty] + ctor[2:]) + ' => Datatypes.Some ' + fold_right_pair(ctor[-len(ctype):])
                        for pctor, ctor, ctype in zip(pctors[:1], ctors_with_prefix[:1], ctypes[:1])
                        for ty in base_types),
       '\n     | '.join('@' + pctor + ', ' + ' '.join([ctor[0]] + [i + "'" for i in ctor[1:]]) + ' => Datatypes.Some ' + ('tt' if len(ctype) == 0 else fold_right_pair([i + "'" for i in ctor[-len(ctype):]]))
                        for pctor, ctor, ctype in zip(pctors_with_args[1:], ctors_with_prefix[1:], ctypes[1:])),
       '\n     | '.join('@' + pctor + ', _' for pctor, named_ttype in zip(pctors_with_underscores, named_ttypes)))).replace('\n', '\n' + indent1))

def relax_type_var(name, ty):
  ty = ty.replace(prefix, '')
  return ({'base.type.base': name,
           'base.type': '(base.relax %s)' % name,
           'type': '(type.relax %s)' % name,
           'type.type base.type': '(type.relax %s)' % name})[ty]

retcode += addnewline((r"""%sDefinition of_typed_ident {t} (idc : %sident.ident t) : ident (type.relax t)
  := match idc with
     | %s
     end.
""" % (indent1, prefix, '\n     | '.join(' '.join(ctor) + ' => @' + pctor + ' ' + ' '.join(relax_type_var(n, t) for n, t in named_ttype) for ctor, pctor, named_ttype in zip(ctors_with_prefix, pctors, named_ttypes)))).replace('\n', '\n' + indent1))

retcode += addnewline((r"""%sDefinition arg_types_of_typed_ident {t} (idc : %sident.ident t) : type_of_list (arg_types (of_typed_ident idc))
  := match idc in %sident.ident t return type_of_list (arg_types (of_typed_ident idc)) with
     | %s
     end.
""" % (indent1, prefix, prefix,
       '\n     | '.join(' '.join(ctor) + ' => ' + ('tt' if len(ctype) == 0 else fold_right_pair(ctor[-len(ctype):]))
                        for ctor, ctype in zip(ctors_with_prefix, ctypes)))).replace('\n', '\n' + indent1))


#
#
#retcode += addnewline((r"""%sDefinition retype_ident {t} (idc : %sident.ident t) : match arg_types (of_typed_ident idc) return %s with Datatypes.Some t => t | Datatypes.None => unit end -> %sident.ident t
#  := match idc in %sident.ident t return match arg_types (of_typed_ident idc) return %s with Datatypes.Some t => t | Datatypes.None => unit end -> %sident.ident t with
#     | %s
#     end.
#""" % (indent1, prefix, type_or_set, prefix, prefix, type_or_set, prefix,
#       '\n     | '.join(' '.join(ctor) + ' => '
#                        + ('' if not do_adjust_type(ctor, ctype) else '(')
#                        + 'fun ' + ('_ => ' if len(ctype) == 0 else ((ctor[-1] + ' => ') if len(ctype) == 1 else "arg => let '(%s) := eta%d arg in " % (', '.join(ctor[-len(ctype):]), len(ctype)))) + "@" + ' '.join(ctor)
#                        + ('' if not do_adjust_type(ctor, ctype) else
#                           (') : '
#                            + ('match arg_types (of_typed_ident %s) return %s with Datatypes.Some t => t | Datatypes.None => unit end -> _'
#                               % (('%s' if ' ' not in ' '.join(ctor) else '(@%s)') % ' '.join(ctor),
#                                  type_or_set))
#                            + ' (* COQBUG(https://github.com/coq/coq/issues/7726) *)'))
#                        for ctor, ctype in zip(ctors_with_prefix, ctypes)))).replace('\n', '\n' + indent1))




#retcode += addnewline((r"""%sDefinition try_make_transport_ident_cps (P : ident -> Type) (idc1 idc2 : ident) : ~> Datatypes.option (P idc1 -> P idc2)
#  := match idc1, idc2 with
#     | %s
#       => fun T k => k (Datatypes.Some (fun v => v))
#     | %s
#       => fun T k => k Datatypes.None
#     end%%cps.
#""" % (indent2,
#       '\n     | '.join(pctor + ', ' + pctor for pctor in pctors),
#       '\n     | '.join(pctor + ', _' for pctor in pctors))).replace('\n', '\n' + indent2))
#retcode += addnewline((r"""%sDefinition eta_all_option_cps {T} (f : ident -> Datatypes.option T)
#  : Datatypes.option (ident -> T)
#  := (%s;
#      Datatypes.Some (fun c
#            => match c with
#               | %s
#               end))%%option.
#""" % (indent2,
#       ';\n      '.join('f' + pctor + ' <- f ' + ctor[0] for ctor, pctor in zip(ctors_no_prefix, pctors)),
#       '\n               | '.join(ctor[0] + ' => f' + pctor for pctor, ctor in zip(pctors, ctors_no_prefix)))).replace('\n', '\n' + indent2))
#retcode += addnewline((r"""%sDefinition orb (f : ident -> bool) : bool
#  := (%s)%%bool.
#""" % (indent2, ' || '.join('f ' + pctor for pctor in pctors))).replace('\n', '\n' + indent2))

#retcode += addnewline((r"""%sDefinition bind_args {t} (idc : %sident.ident t) : type_of_list (arg_types (of_typed_ident idc))
#  := match idc return type_of_list (arg_types (of_typed_ident idc)) with
#     | %s
#     end%%cps.
#""" % (indent1, prefix,
#       '\n     | '.join(' '.join(ctor) + ' => ' + ('tt' if len(ttype + ctype) == 0 else fold_right_pair(ctor[-len(ttype + ctype):]))
#                        for ctor, ttype, ctype in zip(ctors_with_prefix, ttypes, ctypes)))).replace('\n', '\n' + indent1))
#maxeta = max([1+len(ttype + ctype) for ttype, ctype in zip(ttypes, ctypes)])
#if maxeta >= 2:
#  retcode += addnewline(r"""%sLocal Notation eta2r x := (Datatypes.fst x, Datatypes.snd x) (only parsing).""" % indent1)
#for i in range(3, maxeta+1):
#  retcode += addnewline(r"""%sLocal Notation eta%dr x := (Datatypes.fst x, eta%dr (Datatypes.snd x)) (only parsing).""" % (indent1, i, i-1))
#retcode += addnewline('')
#
#def do_adjust_type(ctor, ctype):
#  return len(ctor) > 1 and 'Literal' in ctor[0]
#
#retcode += addnewline((r"""%sDefinition type_of (pidc : ident) : type_of_list (arg_types pidc) -> %stype %sbase.type
#  := match pidc return type_of_list (arg_types pidc) -> _ with
#     | %s
#     end%%etype.
#""" % (indent1, prefix, prefix,
#       '\n     | '.join(pctor + ' => '
#                        + 'fun ' + ('_ => ' if len(ttype + ctype) == 0 else "arg => let '%s := eta%dr arg in " % (fold_right_pair(ctor[-len(ttype + ctype):], tt='_'), 1+len(ttype + ctype))) + cretty.replace(prefix + 'ident.ident ', '')
#                        for pctor, ctor, ttype, ctype, cretty in zip(pctors, ctors_with_prefix, ttypes, ctypes, crettypes)))).replace('\n', '\n' + indent1))
#retcode += addnewline((r"""%sDefinition to_typed (pidc : ident) : forall args : type_of_list (arg_types pidc), %sident.ident (type_of pidc args)
#  := match pidc return forall args : type_of_list (arg_types pidc), %sident.ident (type_of pidc args) with
#     | %s
#     end.
#""" % (indent1, prefix, prefix,
#       '\n     | '.join(pctor + ' => '
#                        + 'fun ' + (('_ => %s' if len(ttype + ctype) == 0 else "arg => match eta%dr arg as args' return %sident.ident (type_of %s args') with %s => %%s end" % (1+len(ttype + ctype), prefix, pctor, fold_right_pair(ctor[-len(ttype + ctype):], tt='_'))) % ("@" + ' '.join(ctor)))
#                        for pctor, ctor, ttype, ctype in zip(pctors, ctors_with_prefix, ttypes, ctypes)))).replace('\n', '\n' + indent1))



retcode += r"""      Derive type_of_list_arg_types_beq
             SuchThat (forall {t idc}, reflect_rel (@eq (type_of_list (@arg_types t idc))) (@type_of_list_arg_types_beq t idc))
             As reflect_type_of_list_arg_types_beq.
      Proof.
        subst type_of_list_arg_types_beq; intros t idc.
        instantiate (1:=ltac:(intros t idc; destruct idc)); destruct idc; cbn [fold_right arg_types]; try solve [ exact reflect_eq_unit ]; instantiate (1:=ltac:(cbn [fold_right arg_types])); exact _.
      Qed.
"""


retcode += r"""    End ident.
"""

retcode += addnewline(indent0 + '\n' + indent0 + '(*===*)')
retcode += r"""
  End pattern.
End Compilers.
"""
with open('GENERATEDIdentifiersWithoutTypes.v', 'w') as f:
  f.write(retcode)

>>>
    *)

    Local Notation eta2 x := (Datatypes.fst x, Datatypes.snd x) (only parsing).
    Local Notation eta2r x := (Datatypes.fst x, Datatypes.snd x) (only parsing).
    Local Notation eta3 x := (eta2 (Datatypes.fst x), Datatypes.snd x) (only parsing).
    Local Notation eta3r x := (Datatypes.fst x, eta2r (Datatypes.snd x)) (only parsing).


    Module Raw.
      Module ident.
        Inductive ident :=
        | Literal
        | Nat_succ
        | Nat_pred
        | Nat_max
        | Nat_mul
        | Nat_add
        | Nat_sub
        | Nat_eqb
        | nil
        | cons
        | pair
        | fst
        | snd
        | prod_rect
        | bool_rect
        | nat_rect
        | nat_rect_arrow
        | eager_nat_rect
        | eager_nat_rect_arrow
        | list_rect
        | eager_list_rect
        | eager_list_rect_arrow
        | list_case
        | List_length
        | List_seq
        | List_firstn
        | List_skipn
        | List_repeat
        | List_combine
        | List_map
        | List_app
        | List_rev
        | List_flat_map
        | List_partition
        | List_fold_right
        | List_update_nth
        | List_nth_default
        | Z_add
        | Z_mul
        | Z_pow
        | Z_sub
        | Z_opp
        | Z_div
        | Z_modulo
        | Z_log2
        | Z_log2_up
        | Z_eqb
        | Z_leb
        | Z_ltb
        | Z_geb
        | Z_gtb
        | Z_of_nat
        | Z_to_nat
        | Z_shiftr
        | Z_shiftl
        | Z_land
        | Z_lor
        | Z_min
        | Z_max
        | Z_bneg
        | Z_lnot_modulo
        | Z_mul_split
        | Z_add_get_carry
        | Z_add_with_carry
        | Z_add_with_get_carry
        | Z_sub_get_borrow
        | Z_sub_with_get_borrow
        | Z_zselect
        | Z_add_modulo
        | Z_rshi
        | Z_cc_m
        | Z_cast
        | Z_cast2
        | option_Some
        | option_None
        | option_rect
        | Build_zrange
        | zrange_rect
        | fancy_add
        | fancy_addc
        | fancy_sub
        | fancy_subb
        | fancy_mulll
        | fancy_mullh
        | fancy_mulhl
        | fancy_mulhh
        | fancy_rshi
        | fancy_selc
        | fancy_selm
        | fancy_sell
        | fancy_addm.

        Definition full_types (idc : ident) : Type
          := match idc return Type with
             | Literal => { t : base.type.base & base.interp (Compilers.base.type.type_base t) }
             | Nat_succ => unit
             | Nat_pred => unit
             | Nat_max => unit
             | Nat_mul => unit
             | Nat_add => unit
             | Nat_sub => unit
             | Nat_eqb => unit
             | nil => Compilers.base.type
             | cons => Compilers.base.type
             | pair => Compilers.base.type * Compilers.base.type
             | fst => Compilers.base.type * Compilers.base.type
             | snd => Compilers.base.type * Compilers.base.type
             | prod_rect => Compilers.base.type * Compilers.base.type * Compilers.base.type
             | bool_rect => Compilers.base.type
             | nat_rect => Compilers.base.type
             | nat_rect_arrow => Compilers.base.type * Compilers.base.type
             | eager_nat_rect => Compilers.base.type
             | eager_nat_rect_arrow => Compilers.base.type * Compilers.base.type
             | list_rect => Compilers.base.type * Compilers.base.type
             | eager_list_rect => Compilers.base.type * Compilers.base.type
             | eager_list_rect_arrow => Compilers.base.type * Compilers.base.type * Compilers.base.type
             | list_case => Compilers.base.type * Compilers.base.type
             | List_length => Compilers.base.type
             | List_seq => unit
             | List_firstn => Compilers.base.type
             | List_skipn => Compilers.base.type
             | List_repeat => Compilers.base.type
             | List_combine => Compilers.base.type * Compilers.base.type
             | List_map => Compilers.base.type * Compilers.base.type
             | List_app => Compilers.base.type
             | List_rev => Compilers.base.type
             | List_flat_map => Compilers.base.type * Compilers.base.type
             | List_partition => Compilers.base.type
             | List_fold_right => Compilers.base.type * Compilers.base.type
             | List_update_nth => Compilers.base.type
             | List_nth_default => Compilers.base.type
             | Z_add => unit
             | Z_mul => unit
             | Z_pow => unit
             | Z_sub => unit
             | Z_opp => unit
             | Z_div => unit
             | Z_modulo => unit
             | Z_log2 => unit
             | Z_log2_up => unit
             | Z_eqb => unit
             | Z_leb => unit
             | Z_ltb => unit
             | Z_geb => unit
             | Z_gtb => unit
             | Z_of_nat => unit
             | Z_to_nat => unit
             | Z_shiftr => unit
             | Z_shiftl => unit
             | Z_land => unit
             | Z_lor => unit
             | Z_min => unit
             | Z_max => unit
             | Z_bneg => unit
             | Z_lnot_modulo => unit
             | Z_mul_split => unit
             | Z_add_get_carry => unit
             | Z_add_with_carry => unit
             | Z_add_with_get_carry => unit
             | Z_sub_get_borrow => unit
             | Z_sub_with_get_borrow => unit
             | Z_zselect => unit
             | Z_add_modulo => unit
             | Z_rshi => unit
             | Z_cc_m => unit
             | Z_cast => zrange
             | Z_cast2 => zrange * zrange
             | option_Some => Compilers.base.type
             | option_None => Compilers.base.type
             | option_rect => Compilers.base.type * Compilers.base.type
             | Build_zrange => unit
             | zrange_rect => Compilers.base.type
             | fancy_add => Z * Z
             | fancy_addc => Z * Z
             | fancy_sub => Z * Z
             | fancy_subb => Z * Z
             | fancy_mulll => Z
             | fancy_mullh => Z
             | fancy_mulhl => Z
             | fancy_mulhh => Z
             | fancy_rshi => Z * Z
             | fancy_selc => unit
             | fancy_selm => Z
             | fancy_sell => unit
             | fancy_addm => unit
             end%type.

        Definition is_simple (idc : ident) : bool
          := match idc with
             | Literal => false
             | Nat_succ => true
             | Nat_pred => true
             | Nat_max => true
             | Nat_mul => true
             | Nat_add => true
             | Nat_sub => true
             | Nat_eqb => true
             | nil => false
             | cons => false
             | pair => false
             | fst => false
             | snd => false
             | prod_rect => false
             | bool_rect => false
             | nat_rect => false
             | nat_rect_arrow => false
             | eager_nat_rect => false
             | eager_nat_rect_arrow => false
             | list_rect => false
             | eager_list_rect => false
             | eager_list_rect_arrow => false
             | list_case => false
             | List_length => false
             | List_seq => true
             | List_firstn => false
             | List_skipn => false
             | List_repeat => false
             | List_combine => false
             | List_map => false
             | List_app => false
             | List_rev => false
             | List_flat_map => false
             | List_partition => false
             | List_fold_right => false
             | List_update_nth => false
             | List_nth_default => false
             | Z_add => true
             | Z_mul => true
             | Z_pow => true
             | Z_sub => true
             | Z_opp => true
             | Z_div => true
             | Z_modulo => true
             | Z_log2 => true
             | Z_log2_up => true
             | Z_eqb => true
             | Z_leb => true
             | Z_ltb => true
             | Z_geb => true
             | Z_gtb => true
             | Z_of_nat => true
             | Z_to_nat => true
             | Z_shiftr => true
             | Z_shiftl => true
             | Z_land => true
             | Z_lor => true
             | Z_min => true
             | Z_max => true
             | Z_bneg => true
             | Z_lnot_modulo => true
             | Z_mul_split => true
             | Z_add_get_carry => true
             | Z_add_with_carry => true
             | Z_add_with_get_carry => true
             | Z_sub_get_borrow => true
             | Z_sub_with_get_borrow => true
             | Z_zselect => true
             | Z_add_modulo => true
             | Z_rshi => true
             | Z_cc_m => true
             | Z_cast => true
             | Z_cast2 => true
             | option_Some => false
             | option_None => false
             | option_rect => false
             | Build_zrange => true
             | zrange_rect => false
             | fancy_add => true
             | fancy_addc => true
             | fancy_sub => true
             | fancy_subb => true
             | fancy_mulll => true
             | fancy_mullh => true
             | fancy_mulhl => true
             | fancy_mulhh => true
             | fancy_rshi => true
             | fancy_selc => true
             | fancy_selm => true
             | fancy_sell => true
             | fancy_addm => true
             end.

        Definition invert_bind_args {t} (idc : Compilers.ident.ident t) (pidc : ident) : Datatypes.option (full_types pidc)
          := match pidc, idc return Datatypes.option (full_types pidc) with
             | Literal, Compilers.ident.Literal t v => Datatypes.Some (existT _ t v)
             | Nat_succ, Compilers.ident.Nat_succ => Datatypes.Some tt
             | Nat_pred, Compilers.ident.Nat_pred => Datatypes.Some tt
             | Nat_max, Compilers.ident.Nat_max => Datatypes.Some tt
             | Nat_mul, Compilers.ident.Nat_mul => Datatypes.Some tt
             | Nat_add, Compilers.ident.Nat_add => Datatypes.Some tt
             | Nat_sub, Compilers.ident.Nat_sub => Datatypes.Some tt
             | Nat_eqb, Compilers.ident.Nat_eqb => Datatypes.Some tt
             | nil, Compilers.ident.nil t => Datatypes.Some t
             | cons, Compilers.ident.cons t => Datatypes.Some t
             | pair, Compilers.ident.pair A B => Datatypes.Some (A, B)
             | fst, Compilers.ident.fst A B => Datatypes.Some (A, B)
             | snd, Compilers.ident.snd A B => Datatypes.Some (A, B)
             | prod_rect, Compilers.ident.prod_rect A B T => Datatypes.Some (A, B, T)
             | bool_rect, Compilers.ident.bool_rect T => Datatypes.Some T
             | nat_rect, Compilers.ident.nat_rect P => Datatypes.Some P
             | nat_rect_arrow, Compilers.ident.nat_rect_arrow P Q => Datatypes.Some (P, Q)
             | eager_nat_rect, Compilers.ident.eager_nat_rect P => Datatypes.Some P
             | eager_nat_rect_arrow, Compilers.ident.eager_nat_rect_arrow P Q => Datatypes.Some (P, Q)
             | list_rect, Compilers.ident.list_rect A P => Datatypes.Some (A, P)
             | eager_list_rect, Compilers.ident.eager_list_rect A P => Datatypes.Some (A, P)
             | eager_list_rect_arrow, Compilers.ident.eager_list_rect_arrow A P Q => Datatypes.Some (A, P, Q)
             | list_case, Compilers.ident.list_case A P => Datatypes.Some (A, P)
             | List_length, Compilers.ident.List_length T => Datatypes.Some T
             | List_seq, Compilers.ident.List_seq => Datatypes.Some tt
             | List_firstn, Compilers.ident.List_firstn A => Datatypes.Some A
             | List_skipn, Compilers.ident.List_skipn A => Datatypes.Some A
             | List_repeat, Compilers.ident.List_repeat A => Datatypes.Some A
             | List_combine, Compilers.ident.List_combine A B => Datatypes.Some (A, B)
             | List_map, Compilers.ident.List_map A B => Datatypes.Some (A, B)
             | List_app, Compilers.ident.List_app A => Datatypes.Some A
             | List_rev, Compilers.ident.List_rev A => Datatypes.Some A
             | List_flat_map, Compilers.ident.List_flat_map A B => Datatypes.Some (A, B)
             | List_partition, Compilers.ident.List_partition A => Datatypes.Some A
             | List_fold_right, Compilers.ident.List_fold_right A B => Datatypes.Some (A, B)
             | List_update_nth, Compilers.ident.List_update_nth T => Datatypes.Some T
             | List_nth_default, Compilers.ident.List_nth_default T => Datatypes.Some T
             | Z_add, Compilers.ident.Z_add => Datatypes.Some tt
             | Z_mul, Compilers.ident.Z_mul => Datatypes.Some tt
             | Z_pow, Compilers.ident.Z_pow => Datatypes.Some tt
             | Z_sub, Compilers.ident.Z_sub => Datatypes.Some tt
             | Z_opp, Compilers.ident.Z_opp => Datatypes.Some tt
             | Z_div, Compilers.ident.Z_div => Datatypes.Some tt
             | Z_modulo, Compilers.ident.Z_modulo => Datatypes.Some tt
             | Z_log2, Compilers.ident.Z_log2 => Datatypes.Some tt
             | Z_log2_up, Compilers.ident.Z_log2_up => Datatypes.Some tt
             | Z_eqb, Compilers.ident.Z_eqb => Datatypes.Some tt
             | Z_leb, Compilers.ident.Z_leb => Datatypes.Some tt
             | Z_ltb, Compilers.ident.Z_ltb => Datatypes.Some tt
             | Z_geb, Compilers.ident.Z_geb => Datatypes.Some tt
             | Z_gtb, Compilers.ident.Z_gtb => Datatypes.Some tt
             | Z_of_nat, Compilers.ident.Z_of_nat => Datatypes.Some tt
             | Z_to_nat, Compilers.ident.Z_to_nat => Datatypes.Some tt
             | Z_shiftr, Compilers.ident.Z_shiftr => Datatypes.Some tt
             | Z_shiftl, Compilers.ident.Z_shiftl => Datatypes.Some tt
             | Z_land, Compilers.ident.Z_land => Datatypes.Some tt
             | Z_lor, Compilers.ident.Z_lor => Datatypes.Some tt
             | Z_min, Compilers.ident.Z_min => Datatypes.Some tt
             | Z_max, Compilers.ident.Z_max => Datatypes.Some tt
             | Z_bneg, Compilers.ident.Z_bneg => Datatypes.Some tt
             | Z_lnot_modulo, Compilers.ident.Z_lnot_modulo => Datatypes.Some tt
             | Z_mul_split, Compilers.ident.Z_mul_split => Datatypes.Some tt
             | Z_add_get_carry, Compilers.ident.Z_add_get_carry => Datatypes.Some tt
             | Z_add_with_carry, Compilers.ident.Z_add_with_carry => Datatypes.Some tt
             | Z_add_with_get_carry, Compilers.ident.Z_add_with_get_carry => Datatypes.Some tt
             | Z_sub_get_borrow, Compilers.ident.Z_sub_get_borrow => Datatypes.Some tt
             | Z_sub_with_get_borrow, Compilers.ident.Z_sub_with_get_borrow => Datatypes.Some tt
             | Z_zselect, Compilers.ident.Z_zselect => Datatypes.Some tt
             | Z_add_modulo, Compilers.ident.Z_add_modulo => Datatypes.Some tt
             | Z_rshi, Compilers.ident.Z_rshi => Datatypes.Some tt
             | Z_cc_m, Compilers.ident.Z_cc_m => Datatypes.Some tt
             | Z_cast, Compilers.ident.Z_cast range => Datatypes.Some range
             | Z_cast2, Compilers.ident.Z_cast2 range => Datatypes.Some range
             | option_Some, Compilers.ident.option_Some A => Datatypes.Some A
             | option_None, Compilers.ident.option_None A => Datatypes.Some A
             | option_rect, Compilers.ident.option_rect A P => Datatypes.Some (A, P)
             | Build_zrange, Compilers.ident.Build_zrange => Datatypes.Some tt
             | zrange_rect, Compilers.ident.zrange_rect P => Datatypes.Some P
             | fancy_add, Compilers.ident.fancy_add log2wordmax imm => Datatypes.Some (log2wordmax, imm)
             | fancy_addc, Compilers.ident.fancy_addc log2wordmax imm => Datatypes.Some (log2wordmax, imm)
             | fancy_sub, Compilers.ident.fancy_sub log2wordmax imm => Datatypes.Some (log2wordmax, imm)
             | fancy_subb, Compilers.ident.fancy_subb log2wordmax imm => Datatypes.Some (log2wordmax, imm)
             | fancy_mulll, Compilers.ident.fancy_mulll log2wordmax => Datatypes.Some log2wordmax
             | fancy_mullh, Compilers.ident.fancy_mullh log2wordmax => Datatypes.Some log2wordmax
             | fancy_mulhl, Compilers.ident.fancy_mulhl log2wordmax => Datatypes.Some log2wordmax
             | fancy_mulhh, Compilers.ident.fancy_mulhh log2wordmax => Datatypes.Some log2wordmax
             | fancy_rshi, Compilers.ident.fancy_rshi log2wordmax x => Datatypes.Some (log2wordmax, x)
             | fancy_selc, Compilers.ident.fancy_selc => Datatypes.Some tt
             | fancy_selm, Compilers.ident.fancy_selm log2wordmax => Datatypes.Some log2wordmax
             | fancy_sell, Compilers.ident.fancy_sell => Datatypes.Some tt
             | fancy_addm, Compilers.ident.fancy_addm => Datatypes.Some tt
             | Literal, _
             | Nat_succ, _
             | Nat_pred, _
             | Nat_max, _
             | Nat_mul, _
             | Nat_add, _
             | Nat_sub, _
             | Nat_eqb, _
             | nil, _
             | cons, _
             | pair, _
             | fst, _
             | snd, _
             | prod_rect, _
             | bool_rect, _
             | nat_rect, _
             | nat_rect_arrow, _
             | eager_nat_rect, _
             | eager_nat_rect_arrow, _
             | list_rect, _
             | eager_list_rect, _
             | eager_list_rect_arrow, _
             | list_case, _
             | List_length, _
             | List_seq, _
             | List_firstn, _
             | List_skipn, _
             | List_repeat, _
             | List_combine, _
             | List_map, _
             | List_app, _
             | List_rev, _
             | List_flat_map, _
             | List_partition, _
             | List_fold_right, _
             | List_update_nth, _
             | List_nth_default, _
             | Z_add, _
             | Z_mul, _
             | Z_pow, _
             | Z_sub, _
             | Z_opp, _
             | Z_div, _
             | Z_modulo, _
             | Z_log2, _
             | Z_log2_up, _
             | Z_eqb, _
             | Z_leb, _
             | Z_ltb, _
             | Z_geb, _
             | Z_gtb, _
             | Z_of_nat, _
             | Z_to_nat, _
             | Z_shiftr, _
             | Z_shiftl, _
             | Z_land, _
             | Z_lor, _
             | Z_min, _
             | Z_max, _
             | Z_bneg, _
             | Z_lnot_modulo, _
             | Z_mul_split, _
             | Z_add_get_carry, _
             | Z_add_with_carry, _
             | Z_add_with_get_carry, _
             | Z_sub_get_borrow, _
             | Z_sub_with_get_borrow, _
             | Z_zselect, _
             | Z_add_modulo, _
             | Z_rshi, _
             | Z_cc_m, _
             | Z_cast, _
             | Z_cast2, _
             | option_Some, _
             | option_None, _
             | option_rect, _
             | Build_zrange, _
             | zrange_rect, _
             | fancy_add, _
             | fancy_addc, _
             | fancy_sub, _
             | fancy_subb, _
             | fancy_mulll, _
             | fancy_mullh, _
             | fancy_mulhl, _
             | fancy_mulhh, _
             | fancy_rshi, _
             | fancy_selc, _
             | fancy_selm, _
             | fancy_sell, _
             | fancy_addm, _
               => Datatypes.None
             end%cps.

        Definition type_of (pidc : ident) : full_types pidc -> Compilers.type Compilers.base.type
          := match pidc return full_types pidc -> _ with
             | Literal => fun arg => let '(t, v) := (projT1 arg, projT2 arg) in (type.base (Compilers.base.type.type_base t))
             | Nat_succ => fun _ => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat))%ptype
             | Nat_pred => fun _ => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat))%ptype
             | Nat_max => fun _ => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat))%ptype
             | Nat_mul => fun _ => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat))%ptype
             | Nat_add => fun _ => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat))%ptype
             | Nat_sub => fun _ => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat))%ptype
             | Nat_eqb => fun _ => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.bool))%ptype
             | nil => fun t => (type.base (Compilers.base.type.list t))
             | cons => fun t => (type.base t -> type.base (Compilers.base.type.list t) -> type.base (Compilers.base.type.list t))%ptype
             | pair => fun arg => let '(A, B) := eta2 arg in (type.base A -> type.base B -> type.base (A * B)%etype)%ptype
             | fst => fun arg => let '(A, B) := eta2 arg in (type.base (A * B)%etype -> type.base A)%ptype
             | snd => fun arg => let '(A, B) := eta2 arg in (type.base (A * B)%etype -> type.base B)%ptype
             | prod_rect => fun arg => let '(A, B, T) := eta3 arg in ((type.base A -> type.base B -> type.base T) -> type.base (A * B)%etype -> type.base T)%ptype
             | bool_rect => fun T => ((type.base ()%etype -> type.base T) -> (type.base ()%etype -> type.base T) -> type.base (Compilers.base.type.type_base base.type.bool) -> type.base T)%ptype
             | nat_rect => fun P => ((type.base ()%etype -> type.base P) -> (type.base (Compilers.base.type.type_base base.type.nat) -> type.base P -> type.base P) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base P)%ptype
             | nat_rect_arrow => fun arg => let '(P, Q) := eta2 arg in ((type.base P -> type.base Q) -> (type.base (Compilers.base.type.type_base base.type.nat) -> (type.base P -> type.base Q) -> type.base P -> type.base Q) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base P -> type.base Q)%ptype
             | eager_nat_rect => fun P => ((type.base ()%etype -> type.base P) -> (type.base (Compilers.base.type.type_base base.type.nat) -> type.base P -> type.base P) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base P)%ptype
             | eager_nat_rect_arrow => fun arg => let '(P, Q) := eta2 arg in ((type.base P -> type.base Q) -> (type.base (Compilers.base.type.type_base base.type.nat) -> (type.base P -> type.base Q) -> type.base P -> type.base Q) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base P -> type.base Q)%ptype
             | list_rect => fun arg => let '(A, P) := eta2 arg in ((type.base ()%etype -> type.base P) -> (type.base A -> type.base (Compilers.base.type.list A) -> type.base P -> type.base P) -> type.base (Compilers.base.type.list A) -> type.base P)%ptype
             | eager_list_rect => fun arg => let '(A, P) := eta2 arg in ((type.base ()%etype -> type.base P) -> (type.base A -> type.base (Compilers.base.type.list A) -> type.base P -> type.base P) -> type.base (Compilers.base.type.list A) -> type.base P)%ptype
             | eager_list_rect_arrow => fun arg => let '(A, P, Q) := eta3 arg in ((type.base P -> type.base Q) -> (type.base A -> type.base (Compilers.base.type.list A) -> (type.base P -> type.base Q) -> type.base P -> type.base Q) -> type.base (Compilers.base.type.list A) -> type.base P -> type.base Q)%ptype
             | list_case => fun arg => let '(A, P) := eta2 arg in ((type.base ()%etype -> type.base P) -> (type.base A -> type.base (Compilers.base.type.list A) -> type.base P) -> type.base (Compilers.base.type.list A) -> type.base P)%ptype
             | List_length => fun T => (type.base (Compilers.base.type.list T) -> type.base (Compilers.base.type.type_base base.type.nat))%ptype
             | List_seq => fun _ => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.list (Compilers.base.type.type_base base.type.nat)))%ptype
             | List_firstn => fun A => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.list A) -> type.base (Compilers.base.type.list A))%ptype
             | List_skipn => fun A => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.list A) -> type.base (Compilers.base.type.list A))%ptype
             | List_repeat => fun A => (type.base A -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.list A))%ptype
             | List_combine => fun arg => let '(A, B) := eta2 arg in (type.base (Compilers.base.type.list A) -> type.base (Compilers.base.type.list B) -> type.base (Compilers.base.type.list (A * B)))%ptype
             | List_map => fun arg => let '(A, B) := eta2 arg in ((type.base A -> type.base B) -> type.base (Compilers.base.type.list A) -> type.base (Compilers.base.type.list B))%ptype
             | List_app => fun A => (type.base (Compilers.base.type.list A) -> type.base (Compilers.base.type.list A) -> type.base (Compilers.base.type.list A))%ptype
             | List_rev => fun A => (type.base (Compilers.base.type.list A) -> type.base (Compilers.base.type.list A))%ptype
             | List_flat_map => fun arg => let '(A, B) := eta2 arg in ((type.base A -> type.base (Compilers.base.type.list B)) -> type.base (Compilers.base.type.list A) -> type.base (Compilers.base.type.list B))%ptype
             | List_partition => fun A => ((type.base A -> type.base (Compilers.base.type.type_base base.type.bool)) -> type.base (Compilers.base.type.list A) -> type.base (Compilers.base.type.list A * Compilers.base.type.list A)%etype)%ptype
             | List_fold_right => fun arg => let '(A, B) := eta2 arg in ((type.base B -> type.base A -> type.base A) -> type.base A -> type.base (Compilers.base.type.list B) -> type.base A)%ptype
             | List_update_nth => fun T => (type.base (Compilers.base.type.type_base base.type.nat) -> (type.base T -> type.base T) -> type.base (Compilers.base.type.list T) -> type.base (Compilers.base.type.list T))%ptype
             | List_nth_default => fun T => (type.base T -> type.base (Compilers.base.type.list T) -> type.base (Compilers.base.type.type_base base.type.nat) -> type.base T)%ptype
             | Z_add => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_mul => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_pow => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_sub => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_opp => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_div => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_modulo => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_log2 => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_log2_up => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_eqb => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.bool))%ptype
             | Z_leb => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.bool))%ptype
             | Z_ltb => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.bool))%ptype
             | Z_geb => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.bool))%ptype
             | Z_gtb => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.bool))%ptype
             | Z_of_nat => fun _ => (type.base (Compilers.base.type.type_base base.type.nat) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_to_nat => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.nat))%ptype
             | Z_shiftr => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_shiftl => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_land => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_lor => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_min => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_max => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_bneg => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_lnot_modulo => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_mul_split => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | Z_add_get_carry => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | Z_add_with_carry => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_add_with_get_carry => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | Z_sub_get_borrow => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | Z_sub_with_get_borrow => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | Z_zselect => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_add_modulo => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_rshi => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_cc_m => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_cast => fun range => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | Z_cast2 => fun range => (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | option_Some => fun A => (type.base A -> type.base (Compilers.base.type.option A))%ptype
             | option_None => fun A => (type.base (Compilers.base.type.option A))
             | option_rect => fun arg => let '(A, P) := eta2 arg in ((type.base A -> type.base P) -> (type.base ()%etype -> type.base P) -> type.base (Compilers.base.type.option A) -> type.base P)%ptype
             | Build_zrange => fun _ => (type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.zrange))%ptype
             | zrange_rect => fun P => ((type.base (Compilers.base.type.type_base base.type.Z) -> type.base (Compilers.base.type.type_base base.type.Z) -> type.base P) -> type.base (Compilers.base.type.type_base base.type.zrange) -> type.base P)%ptype
             | fancy_add => fun arg => let '(log2wordmax, imm) := eta2 arg in (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | fancy_addc => fun arg => let '(log2wordmax, imm) := eta2 arg in (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | fancy_sub => fun arg => let '(log2wordmax, imm) := eta2 arg in (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | fancy_subb => fun arg => let '(log2wordmax, imm) := eta2 arg in (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype)%ptype
             | fancy_mulll => fun log2wordmax => (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | fancy_mullh => fun log2wordmax => (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | fancy_mulhl => fun log2wordmax => (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | fancy_mulhh => fun log2wordmax => (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | fancy_rshi => fun arg => let '(log2wordmax, x) := eta2 arg in (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | fancy_selc => fun _ => (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | fancy_selm => fun log2wordmax => (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | fancy_sell => fun _ => (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             | fancy_addm => fun _ => (type.base (Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z * Compilers.base.type.type_base base.type.Z)%etype -> type.base (Compilers.base.type.type_base base.type.Z))%ptype
             end%etype.

        Definition to_typed (pidc : ident) : forall args : full_types pidc, Compilers.ident.ident (type_of pidc args)
          := match pidc return forall args : full_types pidc, Compilers.ident.ident (type_of pidc args) with
             | Literal => fun arg => match existT _ (projT1 arg) (projT2 arg) as arg' return Compilers.ident.ident (type_of Literal arg') with existT t v => @Compilers.ident.Literal t v end
             | Nat_succ => fun _ => @Compilers.ident.Nat_succ
             | Nat_pred => fun _ => @Compilers.ident.Nat_pred
             | Nat_max => fun _ => @Compilers.ident.Nat_max
             | Nat_mul => fun _ => @Compilers.ident.Nat_mul
             | Nat_add => fun _ => @Compilers.ident.Nat_add
             | Nat_sub => fun _ => @Compilers.ident.Nat_sub
             | Nat_eqb => fun _ => @Compilers.ident.Nat_eqb
             | nil => fun t => @Compilers.ident.nil t
             | cons => fun t => @Compilers.ident.cons t
             | pair => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of pair arg') with (A, B) => @Compilers.ident.pair A B end
             | fst => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of fst arg') with (A, B) => @Compilers.ident.fst A B end
             | snd => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of snd arg') with (A, B) => @Compilers.ident.snd A B end
             | prod_rect => fun arg => match eta3 arg as arg' return Compilers.ident.ident (type_of prod_rect arg') with (A, B, T) => @Compilers.ident.prod_rect A B T end
             | bool_rect => fun T => @Compilers.ident.bool_rect T
             | nat_rect => fun P => @Compilers.ident.nat_rect P
             | nat_rect_arrow => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of nat_rect_arrow arg') with (P, Q) => @Compilers.ident.nat_rect_arrow P Q end
             | eager_nat_rect => fun P => @Compilers.ident.eager_nat_rect P
             | eager_nat_rect_arrow => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of eager_nat_rect_arrow arg') with (P, Q) => @Compilers.ident.eager_nat_rect_arrow P Q end
             | list_rect => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of list_rect arg') with (A, P) => @Compilers.ident.list_rect A P end
             | eager_list_rect => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of eager_list_rect arg') with (A, P) => @Compilers.ident.eager_list_rect A P end
             | eager_list_rect_arrow => fun arg => match eta3 arg as arg' return Compilers.ident.ident (type_of eager_list_rect_arrow arg') with (A, P, Q) => @Compilers.ident.eager_list_rect_arrow A P Q end
             | list_case => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of list_case arg') with (A, P) => @Compilers.ident.list_case A P end
             | List_length => fun T => @Compilers.ident.List_length T
             | List_seq => fun _ => @Compilers.ident.List_seq
             | List_firstn => fun A => @Compilers.ident.List_firstn A
             | List_skipn => fun A => @Compilers.ident.List_skipn A
             | List_repeat => fun A => @Compilers.ident.List_repeat A
             | List_combine => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of List_combine arg') with (A, B) => @Compilers.ident.List_combine A B end
             | List_map => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of List_map arg') with (A, B) => @Compilers.ident.List_map A B end
             | List_app => fun A => @Compilers.ident.List_app A
             | List_rev => fun A => @Compilers.ident.List_rev A
             | List_flat_map => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of List_flat_map arg') with (A, B) => @Compilers.ident.List_flat_map A B end
             | List_partition => fun A => @Compilers.ident.List_partition A
             | List_fold_right => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of List_fold_right arg') with (A, B) => @Compilers.ident.List_fold_right A B end
             | List_update_nth => fun T => @Compilers.ident.List_update_nth T
             | List_nth_default => fun T => @Compilers.ident.List_nth_default T
             | Z_add => fun _ => @Compilers.ident.Z_add
             | Z_mul => fun _ => @Compilers.ident.Z_mul
             | Z_pow => fun _ => @Compilers.ident.Z_pow
             | Z_sub => fun _ => @Compilers.ident.Z_sub
             | Z_opp => fun _ => @Compilers.ident.Z_opp
             | Z_div => fun _ => @Compilers.ident.Z_div
             | Z_modulo => fun _ => @Compilers.ident.Z_modulo
             | Z_log2 => fun _ => @Compilers.ident.Z_log2
             | Z_log2_up => fun _ => @Compilers.ident.Z_log2_up
             | Z_eqb => fun _ => @Compilers.ident.Z_eqb
             | Z_leb => fun _ => @Compilers.ident.Z_leb
             | Z_ltb => fun _ => @Compilers.ident.Z_ltb
             | Z_geb => fun _ => @Compilers.ident.Z_geb
             | Z_gtb => fun _ => @Compilers.ident.Z_gtb
             | Z_of_nat => fun _ => @Compilers.ident.Z_of_nat
             | Z_to_nat => fun _ => @Compilers.ident.Z_to_nat
             | Z_shiftr => fun _ => @Compilers.ident.Z_shiftr
             | Z_shiftl => fun _ => @Compilers.ident.Z_shiftl
             | Z_land => fun _ => @Compilers.ident.Z_land
             | Z_lor => fun _ => @Compilers.ident.Z_lor
             | Z_min => fun _ => @Compilers.ident.Z_min
             | Z_max => fun _ => @Compilers.ident.Z_max
             | Z_bneg => fun _ => @Compilers.ident.Z_bneg
             | Z_lnot_modulo => fun _ => @Compilers.ident.Z_lnot_modulo
             | Z_mul_split => fun _ => @Compilers.ident.Z_mul_split
             | Z_add_get_carry => fun _ => @Compilers.ident.Z_add_get_carry
             | Z_add_with_carry => fun _ => @Compilers.ident.Z_add_with_carry
             | Z_add_with_get_carry => fun _ => @Compilers.ident.Z_add_with_get_carry
             | Z_sub_get_borrow => fun _ => @Compilers.ident.Z_sub_get_borrow
             | Z_sub_with_get_borrow => fun _ => @Compilers.ident.Z_sub_with_get_borrow
             | Z_zselect => fun _ => @Compilers.ident.Z_zselect
             | Z_add_modulo => fun _ => @Compilers.ident.Z_add_modulo
             | Z_rshi => fun _ => @Compilers.ident.Z_rshi
             | Z_cc_m => fun _ => @Compilers.ident.Z_cc_m
             | Z_cast => fun range => @Compilers.ident.Z_cast range
             | Z_cast2 => fun range => @Compilers.ident.Z_cast2 range
             | option_Some => fun A => @Compilers.ident.option_Some A
             | option_None => fun A => @Compilers.ident.option_None A
             | option_rect => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of option_rect arg') with (A, P) => @Compilers.ident.option_rect A P end
             | Build_zrange => fun _ => @Compilers.ident.Build_zrange
             | zrange_rect => fun P => @Compilers.ident.zrange_rect P
             | fancy_add => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of fancy_add arg') with (log2wordmax, imm) => @Compilers.ident.fancy_add log2wordmax imm end
             | fancy_addc => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of fancy_addc arg') with (log2wordmax, imm) => @Compilers.ident.fancy_addc log2wordmax imm end
             | fancy_sub => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of fancy_sub arg') with (log2wordmax, imm) => @Compilers.ident.fancy_sub log2wordmax imm end
             | fancy_subb => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of fancy_subb arg') with (log2wordmax, imm) => @Compilers.ident.fancy_subb log2wordmax imm end
             | fancy_mulll => fun log2wordmax => @Compilers.ident.fancy_mulll log2wordmax
             | fancy_mullh => fun log2wordmax => @Compilers.ident.fancy_mullh log2wordmax
             | fancy_mulhl => fun log2wordmax => @Compilers.ident.fancy_mulhl log2wordmax
             | fancy_mulhh => fun log2wordmax => @Compilers.ident.fancy_mulhh log2wordmax
             | fancy_rshi => fun arg => match eta2 arg as arg' return Compilers.ident.ident (type_of fancy_rshi arg') with (log2wordmax, x) => @Compilers.ident.fancy_rshi log2wordmax x end
             | fancy_selc => fun _ => @Compilers.ident.fancy_selc
             | fancy_selm => fun log2wordmax => @Compilers.ident.fancy_selm log2wordmax
             | fancy_sell => fun _ => @Compilers.ident.fancy_sell
             | fancy_addm => fun _ => @Compilers.ident.fancy_addm
             end.

      End ident.
      Notation ident := ident.ident.
    End Raw.

    Module ident.
      Definition eta_ident_cps {T : Compilers.type Compilers.base.type -> Type} {t} (idc : Compilers.ident.ident t)
                 (f : forall t', Compilers.ident.ident t' -> T t')
        : T t
        := match idc with
           | Compilers.ident.Literal t v => f _ (@Compilers.ident.Literal t v)
           | Compilers.ident.Nat_succ => f _ Compilers.ident.Nat_succ
           | Compilers.ident.Nat_pred => f _ Compilers.ident.Nat_pred
           | Compilers.ident.Nat_max => f _ Compilers.ident.Nat_max
           | Compilers.ident.Nat_mul => f _ Compilers.ident.Nat_mul
           | Compilers.ident.Nat_add => f _ Compilers.ident.Nat_add
           | Compilers.ident.Nat_sub => f _ Compilers.ident.Nat_sub
           | Compilers.ident.Nat_eqb => f _ Compilers.ident.Nat_eqb
           | Compilers.ident.nil t => f _ (@Compilers.ident.nil t)
           | Compilers.ident.cons t => f _ (@Compilers.ident.cons t)
           | Compilers.ident.pair A B => f _ (@Compilers.ident.pair A B)
           | Compilers.ident.fst A B => f _ (@Compilers.ident.fst A B)
           | Compilers.ident.snd A B => f _ (@Compilers.ident.snd A B)
           | Compilers.ident.prod_rect A B T => f _ (@Compilers.ident.prod_rect A B T)
           | Compilers.ident.bool_rect T => f _ (@Compilers.ident.bool_rect T)
           | Compilers.ident.nat_rect P => f _ (@Compilers.ident.nat_rect P)
           | Compilers.ident.nat_rect_arrow P Q => f _ (@Compilers.ident.nat_rect_arrow P Q)
           | Compilers.ident.eager_nat_rect P => f _ (@Compilers.ident.eager_nat_rect P)
           | Compilers.ident.eager_nat_rect_arrow P Q => f _ (@Compilers.ident.eager_nat_rect_arrow P Q)
           | Compilers.ident.list_rect A P => f _ (@Compilers.ident.list_rect A P)
           | Compilers.ident.eager_list_rect A P => f _ (@Compilers.ident.eager_list_rect A P)
           | Compilers.ident.eager_list_rect_arrow A P Q => f _ (@Compilers.ident.eager_list_rect_arrow A P Q)
           | Compilers.ident.list_case A P => f _ (@Compilers.ident.list_case A P)
           | Compilers.ident.List_length T => f _ (@Compilers.ident.List_length T)
           | Compilers.ident.List_seq => f _ Compilers.ident.List_seq
           | Compilers.ident.List_firstn A => f _ (@Compilers.ident.List_firstn A)
           | Compilers.ident.List_skipn A => f _ (@Compilers.ident.List_skipn A)
           | Compilers.ident.List_repeat A => f _ (@Compilers.ident.List_repeat A)
           | Compilers.ident.List_combine A B => f _ (@Compilers.ident.List_combine A B)
           | Compilers.ident.List_map A B => f _ (@Compilers.ident.List_map A B)
           | Compilers.ident.List_app A => f _ (@Compilers.ident.List_app A)
           | Compilers.ident.List_rev A => f _ (@Compilers.ident.List_rev A)
           | Compilers.ident.List_flat_map A B => f _ (@Compilers.ident.List_flat_map A B)
           | Compilers.ident.List_partition A => f _ (@Compilers.ident.List_partition A)
           | Compilers.ident.List_fold_right A B => f _ (@Compilers.ident.List_fold_right A B)
           | Compilers.ident.List_update_nth T => f _ (@Compilers.ident.List_update_nth T)
           | Compilers.ident.List_nth_default T => f _ (@Compilers.ident.List_nth_default T)
           | Compilers.ident.Z_add => f _ Compilers.ident.Z_add
           | Compilers.ident.Z_mul => f _ Compilers.ident.Z_mul
           | Compilers.ident.Z_pow => f _ Compilers.ident.Z_pow
           | Compilers.ident.Z_sub => f _ Compilers.ident.Z_sub
           | Compilers.ident.Z_opp => f _ Compilers.ident.Z_opp
           | Compilers.ident.Z_div => f _ Compilers.ident.Z_div
           | Compilers.ident.Z_modulo => f _ Compilers.ident.Z_modulo
           | Compilers.ident.Z_log2 => f _ Compilers.ident.Z_log2
           | Compilers.ident.Z_log2_up => f _ Compilers.ident.Z_log2_up
           | Compilers.ident.Z_eqb => f _ Compilers.ident.Z_eqb
           | Compilers.ident.Z_leb => f _ Compilers.ident.Z_leb
           | Compilers.ident.Z_ltb => f _ Compilers.ident.Z_ltb
           | Compilers.ident.Z_geb => f _ Compilers.ident.Z_geb
           | Compilers.ident.Z_gtb => f _ Compilers.ident.Z_gtb
           | Compilers.ident.Z_of_nat => f _ Compilers.ident.Z_of_nat
           | Compilers.ident.Z_to_nat => f _ Compilers.ident.Z_to_nat
           | Compilers.ident.Z_shiftr => f _ Compilers.ident.Z_shiftr
           | Compilers.ident.Z_shiftl => f _ Compilers.ident.Z_shiftl
           | Compilers.ident.Z_land => f _ Compilers.ident.Z_land
           | Compilers.ident.Z_lor => f _ Compilers.ident.Z_lor
           | Compilers.ident.Z_min => f _ Compilers.ident.Z_min
           | Compilers.ident.Z_max => f _ Compilers.ident.Z_max
           | Compilers.ident.Z_bneg => f _ Compilers.ident.Z_bneg
           | Compilers.ident.Z_lnot_modulo => f _ Compilers.ident.Z_lnot_modulo
           | Compilers.ident.Z_mul_split => f _ Compilers.ident.Z_mul_split
           | Compilers.ident.Z_add_get_carry => f _ Compilers.ident.Z_add_get_carry
           | Compilers.ident.Z_add_with_carry => f _ Compilers.ident.Z_add_with_carry
           | Compilers.ident.Z_add_with_get_carry => f _ Compilers.ident.Z_add_with_get_carry
           | Compilers.ident.Z_sub_get_borrow => f _ Compilers.ident.Z_sub_get_borrow
           | Compilers.ident.Z_sub_with_get_borrow => f _ Compilers.ident.Z_sub_with_get_borrow
           | Compilers.ident.Z_zselect => f _ Compilers.ident.Z_zselect
           | Compilers.ident.Z_add_modulo => f _ Compilers.ident.Z_add_modulo
           | Compilers.ident.Z_rshi => f _ Compilers.ident.Z_rshi
           | Compilers.ident.Z_cc_m => f _ Compilers.ident.Z_cc_m
           | Compilers.ident.Z_cast range => f _ (@Compilers.ident.Z_cast range)
           | Compilers.ident.Z_cast2 range => f _ (@Compilers.ident.Z_cast2 range)
           | Compilers.ident.option_Some A => f _ (@Compilers.ident.option_Some A)
           | Compilers.ident.option_None A => f _ (@Compilers.ident.option_None A)
           | Compilers.ident.option_rect A P => f _ (@Compilers.ident.option_rect A P)
           | Compilers.ident.Build_zrange => f _ Compilers.ident.Build_zrange
           | Compilers.ident.zrange_rect P => f _ (@Compilers.ident.zrange_rect P)
           | Compilers.ident.fancy_add log2wordmax imm => f _ (@Compilers.ident.fancy_add log2wordmax imm)
           | Compilers.ident.fancy_addc log2wordmax imm => f _ (@Compilers.ident.fancy_addc log2wordmax imm)
           | Compilers.ident.fancy_sub log2wordmax imm => f _ (@Compilers.ident.fancy_sub log2wordmax imm)
           | Compilers.ident.fancy_subb log2wordmax imm => f _ (@Compilers.ident.fancy_subb log2wordmax imm)
           | Compilers.ident.fancy_mulll log2wordmax => f _ (@Compilers.ident.fancy_mulll log2wordmax)
           | Compilers.ident.fancy_mullh log2wordmax => f _ (@Compilers.ident.fancy_mullh log2wordmax)
           | Compilers.ident.fancy_mulhl log2wordmax => f _ (@Compilers.ident.fancy_mulhl log2wordmax)
           | Compilers.ident.fancy_mulhh log2wordmax => f _ (@Compilers.ident.fancy_mulhh log2wordmax)
           | Compilers.ident.fancy_rshi log2wordmax x => f _ (@Compilers.ident.fancy_rshi log2wordmax x)
           | Compilers.ident.fancy_selc => f _ Compilers.ident.fancy_selc
           | Compilers.ident.fancy_selm log2wordmax => f _ (@Compilers.ident.fancy_selm log2wordmax)
           | Compilers.ident.fancy_sell => f _ Compilers.ident.fancy_sell
           | Compilers.ident.fancy_addm => f _ Compilers.ident.fancy_addm
           end.

      Inductive ident : type -> Set :=
      | Literal {t : base.type.base} : ident (type.base (base.type.type_base t))
      | Nat_succ : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))%ptype
      | Nat_pred : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))%ptype
      | Nat_max : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))%ptype
      | Nat_mul : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))%ptype
      | Nat_add : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))%ptype
      | Nat_sub : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))%ptype
      | Nat_eqb : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.bool))%ptype
      | nil {t : base.type} : ident (type.base (base.type.list t))
      | cons {t : base.type} : ident (type.base t -> type.base (base.type.list t) -> type.base (base.type.list t))%ptype
      | pair {A : base.type} {B : base.type} : ident (type.base A -> type.base B -> type.base (A * B)%pbtype)%ptype
      | fst {A : base.type} {B : base.type} : ident (type.base (A * B)%pbtype -> type.base A)%ptype
      | snd {A : base.type} {B : base.type} : ident (type.base (A * B)%pbtype -> type.base B)%ptype
      | prod_rect {A : base.type} {B : base.type} {T : base.type} : ident ((type.base A -> type.base B -> type.base T) -> type.base (A * B)%pbtype -> type.base T)%ptype
      | bool_rect {T : base.type} : ident ((type.base ()%pbtype -> type.base T) -> (type.base ()%pbtype -> type.base T) -> type.base (base.type.type_base base.type.bool) -> type.base T)%ptype
      | nat_rect {P : base.type} : ident ((type.base ()%pbtype -> type.base P) -> (type.base (base.type.type_base base.type.nat) -> type.base P -> type.base P) -> type.base (base.type.type_base base.type.nat) -> type.base P)%ptype
      | nat_rect_arrow {P : base.type} {Q : base.type} : ident ((type.base P -> type.base Q) -> (type.base (base.type.type_base base.type.nat) -> (type.base P -> type.base Q) -> type.base P -> type.base Q) -> type.base (base.type.type_base base.type.nat) -> type.base P -> type.base Q)%ptype
      | eager_nat_rect {P : base.type} : ident ((type.base ()%pbtype -> type.base P) -> (type.base (base.type.type_base base.type.nat) -> type.base P -> type.base P) -> type.base (base.type.type_base base.type.nat) -> type.base P)%ptype
      | eager_nat_rect_arrow {P : base.type} {Q : base.type} : ident ((type.base P -> type.base Q) -> (type.base (base.type.type_base base.type.nat) -> (type.base P -> type.base Q) -> type.base P -> type.base Q) -> type.base (base.type.type_base base.type.nat) -> type.base P -> type.base Q)%ptype
      | list_rect {A : base.type} {P : base.type} : ident ((type.base ()%pbtype -> type.base P) -> (type.base A -> type.base (base.type.list A) -> type.base P -> type.base P) -> type.base (base.type.list A) -> type.base P)%ptype
      | eager_list_rect {A : base.type} {P : base.type} : ident ((type.base ()%pbtype -> type.base P) -> (type.base A -> type.base (base.type.list A) -> type.base P -> type.base P) -> type.base (base.type.list A) -> type.base P)%ptype
      | eager_list_rect_arrow {A : base.type} {P : base.type} {Q : base.type} : ident ((type.base P -> type.base Q) -> (type.base A -> type.base (base.type.list A) -> (type.base P -> type.base Q) -> type.base P -> type.base Q) -> type.base (base.type.list A) -> type.base P -> type.base Q)%ptype
      | list_case {A : base.type} {P : base.type} : ident ((type.base ()%pbtype -> type.base P) -> (type.base A -> type.base (base.type.list A) -> type.base P) -> type.base (base.type.list A) -> type.base P)%ptype
      | List_length {T : base.type} : ident (type.base (base.type.list T) -> type.base (base.type.type_base base.type.nat))%ptype
      | List_seq : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.list (base.type.type_base base.type.nat)))%ptype
      | List_firstn {A : base.type} : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.list A) -> type.base (base.type.list A))%ptype
      | List_skipn {A : base.type} : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.list A) -> type.base (base.type.list A))%ptype
      | List_repeat {A : base.type} : ident (type.base A -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.list A))%ptype
      | List_combine {A : base.type} {B : base.type} : ident (type.base (base.type.list A) -> type.base (base.type.list B) -> type.base (base.type.list (A * B)))%ptype
      | List_map {A : base.type} {B : base.type} : ident ((type.base A -> type.base B) -> type.base (base.type.list A) -> type.base (base.type.list B))%ptype
      | List_app {A : base.type} : ident (type.base (base.type.list A) -> type.base (base.type.list A) -> type.base (base.type.list A))%ptype
      | List_rev {A : base.type} : ident (type.base (base.type.list A) -> type.base (base.type.list A))%ptype
      | List_flat_map {A : base.type} {B : base.type} : ident ((type.base A -> type.base (base.type.list B)) -> type.base (base.type.list A) -> type.base (base.type.list B))%ptype
      | List_partition {A : base.type} : ident ((type.base A -> type.base (base.type.type_base base.type.bool)) -> type.base (base.type.list A) -> type.base (base.type.list A * base.type.list A)%pbtype)%ptype
      | List_fold_right {A : base.type} {B : base.type} : ident ((type.base B -> type.base A -> type.base A) -> type.base A -> type.base (base.type.list B) -> type.base A)%ptype
      | List_update_nth {T : base.type} : ident (type.base (base.type.type_base base.type.nat) -> (type.base T -> type.base T) -> type.base (base.type.list T) -> type.base (base.type.list T))%ptype
      | List_nth_default {T : base.type} : ident (type.base T -> type.base (base.type.list T) -> type.base (base.type.type_base base.type.nat) -> type.base T)%ptype
      | Z_add : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_mul : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_pow : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_sub : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_opp : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_div : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_modulo : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_log2 : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_log2_up : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_eqb : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.bool))%ptype
      | Z_leb : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.bool))%ptype
      | Z_ltb : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.bool))%ptype
      | Z_geb : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.bool))%ptype
      | Z_gtb : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.bool))%ptype
      | Z_of_nat : ident (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_to_nat : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.nat))%ptype
      | Z_shiftr : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_shiftl : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_land : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_lor : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_min : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_max : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_bneg : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_lnot_modulo : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_mul_split : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | Z_add_get_carry : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | Z_add_with_carry : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_add_with_get_carry : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | Z_sub_get_borrow : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | Z_sub_with_get_borrow : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | Z_zselect : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_add_modulo : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_rshi : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_cc_m : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_cast : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))%ptype
      | Z_cast2 : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | option_Some {A : base.type} : ident (type.base A -> type.base (base.type.option A))%ptype
      | option_None {A : base.type} : ident (type.base (base.type.option A))
      | option_rect {A : base.type} {P : base.type} : ident ((type.base A -> type.base P) -> (type.base ()%pbtype -> type.base P) -> type.base (base.type.option A) -> type.base P)%ptype
      | Build_zrange : ident (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.zrange))%ptype
      | zrange_rect {P : base.type} : ident ((type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base P) -> type.base (base.type.type_base base.type.zrange) -> type.base P)%ptype
      | fancy_add : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | fancy_addc : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | fancy_sub : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | fancy_subb : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype)%ptype
      | fancy_mulll : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z))%ptype
      | fancy_mullh : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z))%ptype
      | fancy_mulhl : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z))%ptype
      | fancy_mulhh : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z))%ptype
      | fancy_rshi : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z))%ptype
      | fancy_selc : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z))%ptype
      | fancy_selm : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z))%ptype
      | fancy_sell : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z))%ptype
      | fancy_addm : ident (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%pbtype -> type.base (base.type.type_base base.type.Z))%ptype.

      Definition strip_types {t} (idc : ident t) : Raw.ident
        := match idc with
           | @Literal t => Raw.ident.Literal
           | @Nat_succ => Raw.ident.Nat_succ
           | @Nat_pred => Raw.ident.Nat_pred
           | @Nat_max => Raw.ident.Nat_max
           | @Nat_mul => Raw.ident.Nat_mul
           | @Nat_add => Raw.ident.Nat_add
           | @Nat_sub => Raw.ident.Nat_sub
           | @Nat_eqb => Raw.ident.Nat_eqb
           | @nil t => Raw.ident.nil
           | @cons t => Raw.ident.cons
           | @pair A B => Raw.ident.pair
           | @fst A B => Raw.ident.fst
           | @snd A B => Raw.ident.snd
           | @prod_rect A B T => Raw.ident.prod_rect
           | @bool_rect T => Raw.ident.bool_rect
           | @nat_rect P => Raw.ident.nat_rect
           | @nat_rect_arrow P Q => Raw.ident.nat_rect_arrow
           | @eager_nat_rect P => Raw.ident.eager_nat_rect
           | @eager_nat_rect_arrow P Q => Raw.ident.eager_nat_rect_arrow
           | @list_rect A P => Raw.ident.list_rect
           | @eager_list_rect A P => Raw.ident.eager_list_rect
           | @eager_list_rect_arrow A P Q => Raw.ident.eager_list_rect_arrow
           | @list_case A P => Raw.ident.list_case
           | @List_length T => Raw.ident.List_length
           | @List_seq => Raw.ident.List_seq
           | @List_firstn A => Raw.ident.List_firstn
           | @List_skipn A => Raw.ident.List_skipn
           | @List_repeat A => Raw.ident.List_repeat
           | @List_combine A B => Raw.ident.List_combine
           | @List_map A B => Raw.ident.List_map
           | @List_app A => Raw.ident.List_app
           | @List_rev A => Raw.ident.List_rev
           | @List_flat_map A B => Raw.ident.List_flat_map
           | @List_partition A => Raw.ident.List_partition
           | @List_fold_right A B => Raw.ident.List_fold_right
           | @List_update_nth T => Raw.ident.List_update_nth
           | @List_nth_default T => Raw.ident.List_nth_default
           | @Z_add => Raw.ident.Z_add
           | @Z_mul => Raw.ident.Z_mul
           | @Z_pow => Raw.ident.Z_pow
           | @Z_sub => Raw.ident.Z_sub
           | @Z_opp => Raw.ident.Z_opp
           | @Z_div => Raw.ident.Z_div
           | @Z_modulo => Raw.ident.Z_modulo
           | @Z_log2 => Raw.ident.Z_log2
           | @Z_log2_up => Raw.ident.Z_log2_up
           | @Z_eqb => Raw.ident.Z_eqb
           | @Z_leb => Raw.ident.Z_leb
           | @Z_ltb => Raw.ident.Z_ltb
           | @Z_geb => Raw.ident.Z_geb
           | @Z_gtb => Raw.ident.Z_gtb
           | @Z_of_nat => Raw.ident.Z_of_nat
           | @Z_to_nat => Raw.ident.Z_to_nat
           | @Z_shiftr => Raw.ident.Z_shiftr
           | @Z_shiftl => Raw.ident.Z_shiftl
           | @Z_land => Raw.ident.Z_land
           | @Z_lor => Raw.ident.Z_lor
           | @Z_min => Raw.ident.Z_min
           | @Z_max => Raw.ident.Z_max
           | @Z_bneg => Raw.ident.Z_bneg
           | @Z_lnot_modulo => Raw.ident.Z_lnot_modulo
           | @Z_mul_split => Raw.ident.Z_mul_split
           | @Z_add_get_carry => Raw.ident.Z_add_get_carry
           | @Z_add_with_carry => Raw.ident.Z_add_with_carry
           | @Z_add_with_get_carry => Raw.ident.Z_add_with_get_carry
           | @Z_sub_get_borrow => Raw.ident.Z_sub_get_borrow
           | @Z_sub_with_get_borrow => Raw.ident.Z_sub_with_get_borrow
           | @Z_zselect => Raw.ident.Z_zselect
           | @Z_add_modulo => Raw.ident.Z_add_modulo
           | @Z_rshi => Raw.ident.Z_rshi
           | @Z_cc_m => Raw.ident.Z_cc_m
           | @Z_cast => Raw.ident.Z_cast
           | @Z_cast2 => Raw.ident.Z_cast2
           | @option_Some A => Raw.ident.option_Some
           | @option_None A => Raw.ident.option_None
           | @option_rect A P => Raw.ident.option_rect
           | @Build_zrange => Raw.ident.Build_zrange
           | @zrange_rect P => Raw.ident.zrange_rect
           | @fancy_add => Raw.ident.fancy_add
           | @fancy_addc => Raw.ident.fancy_addc
           | @fancy_sub => Raw.ident.fancy_sub
           | @fancy_subb => Raw.ident.fancy_subb
           | @fancy_mulll => Raw.ident.fancy_mulll
           | @fancy_mullh => Raw.ident.fancy_mullh
           | @fancy_mulhl => Raw.ident.fancy_mulhl
           | @fancy_mulhh => Raw.ident.fancy_mulhh
           | @fancy_rshi => Raw.ident.fancy_rshi
           | @fancy_selc => Raw.ident.fancy_selc
           | @fancy_selm => Raw.ident.fancy_selm
           | @fancy_sell => Raw.ident.fancy_sell
           | @fancy_addm => Raw.ident.fancy_addm
           end.

      Definition arg_types {t} (idc : ident t) : list Type
        := match idc return list Type with
           | @Literal t => [base.interp (Compilers.base.type.type_base t) : Type]
           | @Nat_succ => []
           | @Nat_pred => []
           | @Nat_max => []
           | @Nat_mul => []
           | @Nat_add => []
           | @Nat_sub => []
           | @Nat_eqb => []
           | @nil t => []
           | @cons t => []
           | @pair A B => []
           | @fst A B => []
           | @snd A B => []
           | @prod_rect A B T => []
           | @bool_rect T => []
           | @nat_rect P => []
           | @nat_rect_arrow P Q => []
           | @eager_nat_rect P => []
           | @eager_nat_rect_arrow P Q => []
           | @list_rect A P => []
           | @eager_list_rect A P => []
           | @eager_list_rect_arrow A P Q => []
           | @list_case A P => []
           | @List_length T => []
           | @List_seq => []
           | @List_firstn A => []
           | @List_skipn A => []
           | @List_repeat A => []
           | @List_combine A B => []
           | @List_map A B => []
           | @List_app A => []
           | @List_rev A => []
           | @List_flat_map A B => []
           | @List_partition A => []
           | @List_fold_right A B => []
           | @List_update_nth T => []
           | @List_nth_default T => []
           | @Z_add => []
           | @Z_mul => []
           | @Z_pow => []
           | @Z_sub => []
           | @Z_opp => []
           | @Z_div => []
           | @Z_modulo => []
           | @Z_log2 => []
           | @Z_log2_up => []
           | @Z_eqb => []
           | @Z_leb => []
           | @Z_ltb => []
           | @Z_geb => []
           | @Z_gtb => []
           | @Z_of_nat => []
           | @Z_to_nat => []
           | @Z_shiftr => []
           | @Z_shiftl => []
           | @Z_land => []
           | @Z_lor => []
           | @Z_min => []
           | @Z_max => []
           | @Z_bneg => []
           | @Z_lnot_modulo => []
           | @Z_mul_split => []
           | @Z_add_get_carry => []
           | @Z_add_with_carry => []
           | @Z_add_with_get_carry => []
           | @Z_sub_get_borrow => []
           | @Z_sub_with_get_borrow => []
           | @Z_zselect => []
           | @Z_add_modulo => []
           | @Z_rshi => []
           | @Z_cc_m => []
           | @Z_cast => [zrange : Type]
           | @Z_cast2 => [zrange * zrange : Type]
           | @option_Some A => []
           | @option_None A => []
           | @option_rect A P => []
           | @Build_zrange => []
           | @zrange_rect P => []
           | @fancy_add => [Z : Type; Z : Type]
           | @fancy_addc => [Z : Type; Z : Type]
           | @fancy_sub => [Z : Type; Z : Type]
           | @fancy_subb => [Z : Type; Z : Type]
           | @fancy_mulll => [Z : Type]
           | @fancy_mullh => [Z : Type]
           | @fancy_mulhl => [Z : Type]
           | @fancy_mulhh => [Z : Type]
           | @fancy_rshi => [Z : Type; Z : Type]
           | @fancy_selc => []
           | @fancy_selm => [Z : Type]
           | @fancy_sell => []
           | @fancy_addm => []
           end%type.

      Definition to_typed {t} (idc : ident t) (evm : EvarMap) : type_of_list (arg_types idc) -> Compilers.ident.ident (pattern.type.subst_default t evm)
        := match idc in ident t return type_of_list (arg_types idc) -> Compilers.ident.ident (pattern.type.subst_default t evm) with
           | @Literal t => fun arg => let '(v, _) := eta2r arg in @Compilers.ident.Literal _ v
           | @Nat_succ => fun _ => @Compilers.ident.Nat_succ
           | @Nat_pred => fun _ => @Compilers.ident.Nat_pred
           | @Nat_max => fun _ => @Compilers.ident.Nat_max
           | @Nat_mul => fun _ => @Compilers.ident.Nat_mul
           | @Nat_add => fun _ => @Compilers.ident.Nat_add
           | @Nat_sub => fun _ => @Compilers.ident.Nat_sub
           | @Nat_eqb => fun _ => @Compilers.ident.Nat_eqb
           | @nil t => fun _ => @Compilers.ident.nil _
           | @cons t => fun _ => @Compilers.ident.cons _
           | @pair A B => fun _ => @Compilers.ident.pair _ _
           | @fst A B => fun _ => @Compilers.ident.fst _ _
           | @snd A B => fun _ => @Compilers.ident.snd _ _
           | @prod_rect A B T => fun _ => @Compilers.ident.prod_rect _ _ _
           | @bool_rect T => fun _ => @Compilers.ident.bool_rect _
           | @nat_rect P => fun _ => @Compilers.ident.nat_rect _
           | @nat_rect_arrow P Q => fun _ => @Compilers.ident.nat_rect_arrow _ _
           | @eager_nat_rect P => fun _ => @Compilers.ident.eager_nat_rect _
           | @eager_nat_rect_arrow P Q => fun _ => @Compilers.ident.eager_nat_rect_arrow _ _
           | @list_rect A P => fun _ => @Compilers.ident.list_rect _ _
           | @eager_list_rect A P => fun _ => @Compilers.ident.eager_list_rect _ _
           | @eager_list_rect_arrow A P Q => fun _ => @Compilers.ident.eager_list_rect_arrow _ _ _
           | @list_case A P => fun _ => @Compilers.ident.list_case _ _
           | @List_length T => fun _ => @Compilers.ident.List_length _
           | @List_seq => fun _ => @Compilers.ident.List_seq
           | @List_firstn A => fun _ => @Compilers.ident.List_firstn _
           | @List_skipn A => fun _ => @Compilers.ident.List_skipn _
           | @List_repeat A => fun _ => @Compilers.ident.List_repeat _
           | @List_combine A B => fun _ => @Compilers.ident.List_combine _ _
           | @List_map A B => fun _ => @Compilers.ident.List_map _ _
           | @List_app A => fun _ => @Compilers.ident.List_app _
           | @List_rev A => fun _ => @Compilers.ident.List_rev _
           | @List_flat_map A B => fun _ => @Compilers.ident.List_flat_map _ _
           | @List_partition A => fun _ => @Compilers.ident.List_partition _
           | @List_fold_right A B => fun _ => @Compilers.ident.List_fold_right _ _
           | @List_update_nth T => fun _ => @Compilers.ident.List_update_nth _
           | @List_nth_default T => fun _ => @Compilers.ident.List_nth_default _
           | @Z_add => fun _ => @Compilers.ident.Z_add
           | @Z_mul => fun _ => @Compilers.ident.Z_mul
           | @Z_pow => fun _ => @Compilers.ident.Z_pow
           | @Z_sub => fun _ => @Compilers.ident.Z_sub
           | @Z_opp => fun _ => @Compilers.ident.Z_opp
           | @Z_div => fun _ => @Compilers.ident.Z_div
           | @Z_modulo => fun _ => @Compilers.ident.Z_modulo
           | @Z_log2 => fun _ => @Compilers.ident.Z_log2
           | @Z_log2_up => fun _ => @Compilers.ident.Z_log2_up
           | @Z_eqb => fun _ => @Compilers.ident.Z_eqb
           | @Z_leb => fun _ => @Compilers.ident.Z_leb
           | @Z_ltb => fun _ => @Compilers.ident.Z_ltb
           | @Z_geb => fun _ => @Compilers.ident.Z_geb
           | @Z_gtb => fun _ => @Compilers.ident.Z_gtb
           | @Z_of_nat => fun _ => @Compilers.ident.Z_of_nat
           | @Z_to_nat => fun _ => @Compilers.ident.Z_to_nat
           | @Z_shiftr => fun _ => @Compilers.ident.Z_shiftr
           | @Z_shiftl => fun _ => @Compilers.ident.Z_shiftl
           | @Z_land => fun _ => @Compilers.ident.Z_land
           | @Z_lor => fun _ => @Compilers.ident.Z_lor
           | @Z_min => fun _ => @Compilers.ident.Z_min
           | @Z_max => fun _ => @Compilers.ident.Z_max
           | @Z_bneg => fun _ => @Compilers.ident.Z_bneg
           | @Z_lnot_modulo => fun _ => @Compilers.ident.Z_lnot_modulo
           | @Z_mul_split => fun _ => @Compilers.ident.Z_mul_split
           | @Z_add_get_carry => fun _ => @Compilers.ident.Z_add_get_carry
           | @Z_add_with_carry => fun _ => @Compilers.ident.Z_add_with_carry
           | @Z_add_with_get_carry => fun _ => @Compilers.ident.Z_add_with_get_carry
           | @Z_sub_get_borrow => fun _ => @Compilers.ident.Z_sub_get_borrow
           | @Z_sub_with_get_borrow => fun _ => @Compilers.ident.Z_sub_with_get_borrow
           | @Z_zselect => fun _ => @Compilers.ident.Z_zselect
           | @Z_add_modulo => fun _ => @Compilers.ident.Z_add_modulo
           | @Z_rshi => fun _ => @Compilers.ident.Z_rshi
           | @Z_cc_m => fun _ => @Compilers.ident.Z_cc_m
           | @Z_cast => fun arg => let '(range, _) := eta2r arg in @Compilers.ident.Z_cast range
           | @Z_cast2 => fun arg => let '(range, _) := eta2r arg in @Compilers.ident.Z_cast2 range
           | @option_Some A => fun _ => @Compilers.ident.option_Some _
           | @option_None A => fun _ => @Compilers.ident.option_None _
           | @option_rect A P => fun _ => @Compilers.ident.option_rect _ _
           | @Build_zrange => fun _ => @Compilers.ident.Build_zrange
           | @zrange_rect P => fun _ => @Compilers.ident.zrange_rect _
           | @fancy_add => fun arg => let '(log2wordmax, (imm, _)) := eta3r arg in @Compilers.ident.fancy_add log2wordmax imm
           | @fancy_addc => fun arg => let '(log2wordmax, (imm, _)) := eta3r arg in @Compilers.ident.fancy_addc log2wordmax imm
           | @fancy_sub => fun arg => let '(log2wordmax, (imm, _)) := eta3r arg in @Compilers.ident.fancy_sub log2wordmax imm
           | @fancy_subb => fun arg => let '(log2wordmax, (imm, _)) := eta3r arg in @Compilers.ident.fancy_subb log2wordmax imm
           | @fancy_mulll => fun arg => let '(log2wordmax, _) := eta2r arg in @Compilers.ident.fancy_mulll log2wordmax
           | @fancy_mullh => fun arg => let '(log2wordmax, _) := eta2r arg in @Compilers.ident.fancy_mullh log2wordmax
           | @fancy_mulhl => fun arg => let '(log2wordmax, _) := eta2r arg in @Compilers.ident.fancy_mulhl log2wordmax
           | @fancy_mulhh => fun arg => let '(log2wordmax, _) := eta2r arg in @Compilers.ident.fancy_mulhh log2wordmax
           | @fancy_rshi => fun arg => let '(log2wordmax, (x, _)) := eta3r arg in @Compilers.ident.fancy_rshi log2wordmax x
           | @fancy_selc => fun _ => @Compilers.ident.fancy_selc
           | @fancy_selm => fun arg => let '(log2wordmax, _) := eta2r arg in @Compilers.ident.fancy_selm log2wordmax
           | @fancy_sell => fun _ => @Compilers.ident.fancy_sell
           | @fancy_addm => fun _ => @Compilers.ident.fancy_addm
           end.

      Definition unify {t t'} (pidc : ident t) (idc : Compilers.ident.ident t') : Datatypes.option (type_of_list (@arg_types t pidc))
        := match pidc, idc return Datatypes.option (type_of_list (arg_types pidc)) with
           | @Literal Compilers.base.type.unit, Compilers.ident.Literal Compilers.base.type.unit v => Datatypes.Some (v, tt)
           | @Literal Compilers.base.type.Z, Compilers.ident.Literal Compilers.base.type.Z v => Datatypes.Some (v, tt)
           | @Literal Compilers.base.type.bool, Compilers.ident.Literal Compilers.base.type.bool v => Datatypes.Some (v, tt)
           | @Literal Compilers.base.type.nat, Compilers.ident.Literal Compilers.base.type.nat v => Datatypes.Some (v, tt)
           | @Literal Compilers.base.type.zrange, Compilers.ident.Literal Compilers.base.type.zrange v => Datatypes.Some (v, tt)
           | @Nat_succ, Compilers.ident.Nat_succ => Datatypes.Some tt
           | @Nat_pred, Compilers.ident.Nat_pred => Datatypes.Some tt
           | @Nat_max, Compilers.ident.Nat_max => Datatypes.Some tt
           | @Nat_mul, Compilers.ident.Nat_mul => Datatypes.Some tt
           | @Nat_add, Compilers.ident.Nat_add => Datatypes.Some tt
           | @Nat_sub, Compilers.ident.Nat_sub => Datatypes.Some tt
           | @Nat_eqb, Compilers.ident.Nat_eqb => Datatypes.Some tt
           | @nil t, Compilers.ident.nil t' => Datatypes.Some tt
           | @cons t, Compilers.ident.cons t' => Datatypes.Some tt
           | @pair A B, Compilers.ident.pair A' B' => Datatypes.Some tt
           | @fst A B, Compilers.ident.fst A' B' => Datatypes.Some tt
           | @snd A B, Compilers.ident.snd A' B' => Datatypes.Some tt
           | @prod_rect A B T, Compilers.ident.prod_rect A' B' T' => Datatypes.Some tt
           | @bool_rect T, Compilers.ident.bool_rect T' => Datatypes.Some tt
           | @nat_rect P, Compilers.ident.nat_rect P' => Datatypes.Some tt
           | @nat_rect_arrow P Q, Compilers.ident.nat_rect_arrow P' Q' => Datatypes.Some tt
           | @eager_nat_rect P, Compilers.ident.eager_nat_rect P' => Datatypes.Some tt
           | @eager_nat_rect_arrow P Q, Compilers.ident.eager_nat_rect_arrow P' Q' => Datatypes.Some tt
           | @list_rect A P, Compilers.ident.list_rect A' P' => Datatypes.Some tt
           | @eager_list_rect A P, Compilers.ident.eager_list_rect A' P' => Datatypes.Some tt
           | @eager_list_rect_arrow A P Q, Compilers.ident.eager_list_rect_arrow A' P' Q' => Datatypes.Some tt
           | @list_case A P, Compilers.ident.list_case A' P' => Datatypes.Some tt
           | @List_length T, Compilers.ident.List_length T' => Datatypes.Some tt
           | @List_seq, Compilers.ident.List_seq => Datatypes.Some tt
           | @List_firstn A, Compilers.ident.List_firstn A' => Datatypes.Some tt
           | @List_skipn A, Compilers.ident.List_skipn A' => Datatypes.Some tt
           | @List_repeat A, Compilers.ident.List_repeat A' => Datatypes.Some tt
           | @List_combine A B, Compilers.ident.List_combine A' B' => Datatypes.Some tt
           | @List_map A B, Compilers.ident.List_map A' B' => Datatypes.Some tt
           | @List_app A, Compilers.ident.List_app A' => Datatypes.Some tt
           | @List_rev A, Compilers.ident.List_rev A' => Datatypes.Some tt
           | @List_flat_map A B, Compilers.ident.List_flat_map A' B' => Datatypes.Some tt
           | @List_partition A, Compilers.ident.List_partition A' => Datatypes.Some tt
           | @List_fold_right A B, Compilers.ident.List_fold_right A' B' => Datatypes.Some tt
           | @List_update_nth T, Compilers.ident.List_update_nth T' => Datatypes.Some tt
           | @List_nth_default T, Compilers.ident.List_nth_default T' => Datatypes.Some tt
           | @Z_add, Compilers.ident.Z_add => Datatypes.Some tt
           | @Z_mul, Compilers.ident.Z_mul => Datatypes.Some tt
           | @Z_pow, Compilers.ident.Z_pow => Datatypes.Some tt
           | @Z_sub, Compilers.ident.Z_sub => Datatypes.Some tt
           | @Z_opp, Compilers.ident.Z_opp => Datatypes.Some tt
           | @Z_div, Compilers.ident.Z_div => Datatypes.Some tt
           | @Z_modulo, Compilers.ident.Z_modulo => Datatypes.Some tt
           | @Z_log2, Compilers.ident.Z_log2 => Datatypes.Some tt
           | @Z_log2_up, Compilers.ident.Z_log2_up => Datatypes.Some tt
           | @Z_eqb, Compilers.ident.Z_eqb => Datatypes.Some tt
           | @Z_leb, Compilers.ident.Z_leb => Datatypes.Some tt
           | @Z_ltb, Compilers.ident.Z_ltb => Datatypes.Some tt
           | @Z_geb, Compilers.ident.Z_geb => Datatypes.Some tt
           | @Z_gtb, Compilers.ident.Z_gtb => Datatypes.Some tt
           | @Z_of_nat, Compilers.ident.Z_of_nat => Datatypes.Some tt
           | @Z_to_nat, Compilers.ident.Z_to_nat => Datatypes.Some tt
           | @Z_shiftr, Compilers.ident.Z_shiftr => Datatypes.Some tt
           | @Z_shiftl, Compilers.ident.Z_shiftl => Datatypes.Some tt
           | @Z_land, Compilers.ident.Z_land => Datatypes.Some tt
           | @Z_lor, Compilers.ident.Z_lor => Datatypes.Some tt
           | @Z_min, Compilers.ident.Z_min => Datatypes.Some tt
           | @Z_max, Compilers.ident.Z_max => Datatypes.Some tt
           | @Z_bneg, Compilers.ident.Z_bneg => Datatypes.Some tt
           | @Z_lnot_modulo, Compilers.ident.Z_lnot_modulo => Datatypes.Some tt
           | @Z_mul_split, Compilers.ident.Z_mul_split => Datatypes.Some tt
           | @Z_add_get_carry, Compilers.ident.Z_add_get_carry => Datatypes.Some tt
           | @Z_add_with_carry, Compilers.ident.Z_add_with_carry => Datatypes.Some tt
           | @Z_add_with_get_carry, Compilers.ident.Z_add_with_get_carry => Datatypes.Some tt
           | @Z_sub_get_borrow, Compilers.ident.Z_sub_get_borrow => Datatypes.Some tt
           | @Z_sub_with_get_borrow, Compilers.ident.Z_sub_with_get_borrow => Datatypes.Some tt
           | @Z_zselect, Compilers.ident.Z_zselect => Datatypes.Some tt
           | @Z_add_modulo, Compilers.ident.Z_add_modulo => Datatypes.Some tt
           | @Z_rshi, Compilers.ident.Z_rshi => Datatypes.Some tt
           | @Z_cc_m, Compilers.ident.Z_cc_m => Datatypes.Some tt
           | @Z_cast, Compilers.ident.Z_cast range' => Datatypes.Some (range', tt)
           | @Z_cast2, Compilers.ident.Z_cast2 range' => Datatypes.Some (range', tt)
           | @option_Some A, Compilers.ident.option_Some A' => Datatypes.Some tt
           | @option_None A, Compilers.ident.option_None A' => Datatypes.Some tt
           | @option_rect A P, Compilers.ident.option_rect A' P' => Datatypes.Some tt
           | @Build_zrange, Compilers.ident.Build_zrange => Datatypes.Some tt
           | @zrange_rect P, Compilers.ident.zrange_rect P' => Datatypes.Some tt
           | @fancy_add, Compilers.ident.fancy_add log2wordmax' imm' => Datatypes.Some (log2wordmax', (imm', tt))
           | @fancy_addc, Compilers.ident.fancy_addc log2wordmax' imm' => Datatypes.Some (log2wordmax', (imm', tt))
           | @fancy_sub, Compilers.ident.fancy_sub log2wordmax' imm' => Datatypes.Some (log2wordmax', (imm', tt))
           | @fancy_subb, Compilers.ident.fancy_subb log2wordmax' imm' => Datatypes.Some (log2wordmax', (imm', tt))
           | @fancy_mulll, Compilers.ident.fancy_mulll log2wordmax' => Datatypes.Some (log2wordmax', tt)
           | @fancy_mullh, Compilers.ident.fancy_mullh log2wordmax' => Datatypes.Some (log2wordmax', tt)
           | @fancy_mulhl, Compilers.ident.fancy_mulhl log2wordmax' => Datatypes.Some (log2wordmax', tt)
           | @fancy_mulhh, Compilers.ident.fancy_mulhh log2wordmax' => Datatypes.Some (log2wordmax', tt)
           | @fancy_rshi, Compilers.ident.fancy_rshi log2wordmax' x' => Datatypes.Some (log2wordmax', (x', tt))
           | @fancy_selc, Compilers.ident.fancy_selc => Datatypes.Some tt
           | @fancy_selm, Compilers.ident.fancy_selm log2wordmax' => Datatypes.Some (log2wordmax', tt)
           | @fancy_sell, Compilers.ident.fancy_sell => Datatypes.Some tt
           | @fancy_addm, Compilers.ident.fancy_addm => Datatypes.Some tt
           | @Literal _, _
           | @Nat_succ, _
           | @Nat_pred, _
           | @Nat_max, _
           | @Nat_mul, _
           | @Nat_add, _
           | @Nat_sub, _
           | @Nat_eqb, _
           | @nil _, _
           | @cons _, _
           | @pair _ _, _
           | @fst _ _, _
           | @snd _ _, _
           | @prod_rect _ _ _, _
           | @bool_rect _, _
           | @nat_rect _, _
           | @nat_rect_arrow _ _, _
           | @eager_nat_rect _, _
           | @eager_nat_rect_arrow _ _, _
           | @list_rect _ _, _
           | @eager_list_rect _ _, _
           | @eager_list_rect_arrow _ _ _, _
           | @list_case _ _, _
           | @List_length _, _
           | @List_seq, _
           | @List_firstn _, _
           | @List_skipn _, _
           | @List_repeat _, _
           | @List_combine _ _, _
           | @List_map _ _, _
           | @List_app _, _
           | @List_rev _, _
           | @List_flat_map _ _, _
           | @List_partition _, _
           | @List_fold_right _ _, _
           | @List_update_nth _, _
           | @List_nth_default _, _
           | @Z_add, _
           | @Z_mul, _
           | @Z_pow, _
           | @Z_sub, _
           | @Z_opp, _
           | @Z_div, _
           | @Z_modulo, _
           | @Z_log2, _
           | @Z_log2_up, _
           | @Z_eqb, _
           | @Z_leb, _
           | @Z_ltb, _
           | @Z_geb, _
           | @Z_gtb, _
           | @Z_of_nat, _
           | @Z_to_nat, _
           | @Z_shiftr, _
           | @Z_shiftl, _
           | @Z_land, _
           | @Z_lor, _
           | @Z_min, _
           | @Z_max, _
           | @Z_bneg, _
           | @Z_lnot_modulo, _
           | @Z_mul_split, _
           | @Z_add_get_carry, _
           | @Z_add_with_carry, _
           | @Z_add_with_get_carry, _
           | @Z_sub_get_borrow, _
           | @Z_sub_with_get_borrow, _
           | @Z_zselect, _
           | @Z_add_modulo, _
           | @Z_rshi, _
           | @Z_cc_m, _
           | @Z_cast, _
           | @Z_cast2, _
           | @option_Some _, _
           | @option_None _, _
           | @option_rect _ _, _
           | @Build_zrange, _
           | @zrange_rect _, _
           | @fancy_add, _
           | @fancy_addc, _
           | @fancy_sub, _
           | @fancy_subb, _
           | @fancy_mulll, _
           | @fancy_mullh, _
           | @fancy_mulhl, _
           | @fancy_mulhh, _
           | @fancy_rshi, _
           | @fancy_selc, _
           | @fancy_selm, _
           | @fancy_sell, _
           | @fancy_addm, _
             => Datatypes.None
           end%cps.

      Definition of_typed_ident {t} (idc : Compilers.ident.ident t) : ident (type.relax t)
        := match idc with
           | Compilers.ident.Literal t v => @Literal t
           | Compilers.ident.Nat_succ => @Nat_succ
           | Compilers.ident.Nat_pred => @Nat_pred
           | Compilers.ident.Nat_max => @Nat_max
           | Compilers.ident.Nat_mul => @Nat_mul
           | Compilers.ident.Nat_add => @Nat_add
           | Compilers.ident.Nat_sub => @Nat_sub
           | Compilers.ident.Nat_eqb => @Nat_eqb
           | Compilers.ident.nil t => @nil (base.relax t)
           | Compilers.ident.cons t => @cons (base.relax t)
           | Compilers.ident.pair A B => @pair (base.relax A) (base.relax B)
           | Compilers.ident.fst A B => @fst (base.relax A) (base.relax B)
           | Compilers.ident.snd A B => @snd (base.relax A) (base.relax B)
           | Compilers.ident.prod_rect A B T => @prod_rect (base.relax A) (base.relax B) (base.relax T)
           | Compilers.ident.bool_rect T => @bool_rect (base.relax T)
           | Compilers.ident.nat_rect P => @nat_rect (base.relax P)
           | Compilers.ident.nat_rect_arrow P Q => @nat_rect_arrow (base.relax P) (base.relax Q)
           | Compilers.ident.eager_nat_rect P => @eager_nat_rect (base.relax P)
           | Compilers.ident.eager_nat_rect_arrow P Q => @eager_nat_rect_arrow (base.relax P) (base.relax Q)
           | Compilers.ident.list_rect A P => @list_rect (base.relax A) (base.relax P)
           | Compilers.ident.eager_list_rect A P => @eager_list_rect (base.relax A) (base.relax P)
           | Compilers.ident.eager_list_rect_arrow A P Q => @eager_list_rect_arrow (base.relax A) (base.relax P) (base.relax Q)
           | Compilers.ident.list_case A P => @list_case (base.relax A) (base.relax P)
           | Compilers.ident.List_length T => @List_length (base.relax T)
           | Compilers.ident.List_seq => @List_seq
           | Compilers.ident.List_firstn A => @List_firstn (base.relax A)
           | Compilers.ident.List_skipn A => @List_skipn (base.relax A)
           | Compilers.ident.List_repeat A => @List_repeat (base.relax A)
           | Compilers.ident.List_combine A B => @List_combine (base.relax A) (base.relax B)
           | Compilers.ident.List_map A B => @List_map (base.relax A) (base.relax B)
           | Compilers.ident.List_app A => @List_app (base.relax A)
           | Compilers.ident.List_rev A => @List_rev (base.relax A)
           | Compilers.ident.List_flat_map A B => @List_flat_map (base.relax A) (base.relax B)
           | Compilers.ident.List_partition A => @List_partition (base.relax A)
           | Compilers.ident.List_fold_right A B => @List_fold_right (base.relax A) (base.relax B)
           | Compilers.ident.List_update_nth T => @List_update_nth (base.relax T)
           | Compilers.ident.List_nth_default T => @List_nth_default (base.relax T)
           | Compilers.ident.Z_add => @Z_add
           | Compilers.ident.Z_mul => @Z_mul
           | Compilers.ident.Z_pow => @Z_pow
           | Compilers.ident.Z_sub => @Z_sub
           | Compilers.ident.Z_opp => @Z_opp
           | Compilers.ident.Z_div => @Z_div
           | Compilers.ident.Z_modulo => @Z_modulo
           | Compilers.ident.Z_log2 => @Z_log2
           | Compilers.ident.Z_log2_up => @Z_log2_up
           | Compilers.ident.Z_eqb => @Z_eqb
           | Compilers.ident.Z_leb => @Z_leb
           | Compilers.ident.Z_ltb => @Z_ltb
           | Compilers.ident.Z_geb => @Z_geb
           | Compilers.ident.Z_gtb => @Z_gtb
           | Compilers.ident.Z_of_nat => @Z_of_nat
           | Compilers.ident.Z_to_nat => @Z_to_nat
           | Compilers.ident.Z_shiftr => @Z_shiftr
           | Compilers.ident.Z_shiftl => @Z_shiftl
           | Compilers.ident.Z_land => @Z_land
           | Compilers.ident.Z_lor => @Z_lor
           | Compilers.ident.Z_min => @Z_min
           | Compilers.ident.Z_max => @Z_max
           | Compilers.ident.Z_bneg => @Z_bneg
           | Compilers.ident.Z_lnot_modulo => @Z_lnot_modulo
           | Compilers.ident.Z_mul_split => @Z_mul_split
           | Compilers.ident.Z_add_get_carry => @Z_add_get_carry
           | Compilers.ident.Z_add_with_carry => @Z_add_with_carry
           | Compilers.ident.Z_add_with_get_carry => @Z_add_with_get_carry
           | Compilers.ident.Z_sub_get_borrow => @Z_sub_get_borrow
           | Compilers.ident.Z_sub_with_get_borrow => @Z_sub_with_get_borrow
           | Compilers.ident.Z_zselect => @Z_zselect
           | Compilers.ident.Z_add_modulo => @Z_add_modulo
           | Compilers.ident.Z_rshi => @Z_rshi
           | Compilers.ident.Z_cc_m => @Z_cc_m
           | Compilers.ident.Z_cast range => @Z_cast
           | Compilers.ident.Z_cast2 range => @Z_cast2
           | Compilers.ident.option_Some A => @option_Some (base.relax A)
           | Compilers.ident.option_None A => @option_None (base.relax A)
           | Compilers.ident.option_rect A P => @option_rect (base.relax A) (base.relax P)
           | Compilers.ident.Build_zrange => @Build_zrange
           | Compilers.ident.zrange_rect P => @zrange_rect (base.relax P)
           | Compilers.ident.fancy_add log2wordmax imm => @fancy_add
           | Compilers.ident.fancy_addc log2wordmax imm => @fancy_addc
           | Compilers.ident.fancy_sub log2wordmax imm => @fancy_sub
           | Compilers.ident.fancy_subb log2wordmax imm => @fancy_subb
           | Compilers.ident.fancy_mulll log2wordmax => @fancy_mulll
           | Compilers.ident.fancy_mullh log2wordmax => @fancy_mullh
           | Compilers.ident.fancy_mulhl log2wordmax => @fancy_mulhl
           | Compilers.ident.fancy_mulhh log2wordmax => @fancy_mulhh
           | Compilers.ident.fancy_rshi log2wordmax x => @fancy_rshi
           | Compilers.ident.fancy_selc => @fancy_selc
           | Compilers.ident.fancy_selm log2wordmax => @fancy_selm
           | Compilers.ident.fancy_sell => @fancy_sell
           | Compilers.ident.fancy_addm => @fancy_addm
           end.

      Definition arg_types_of_typed_ident {t} (idc : Compilers.ident.ident t) : type_of_list (arg_types (of_typed_ident idc))
        := match idc in Compilers.ident.ident t return type_of_list (arg_types (of_typed_ident idc)) with
           | Compilers.ident.Literal t v => (v, tt)
           | Compilers.ident.Nat_succ => tt
           | Compilers.ident.Nat_pred => tt
           | Compilers.ident.Nat_max => tt
           | Compilers.ident.Nat_mul => tt
           | Compilers.ident.Nat_add => tt
           | Compilers.ident.Nat_sub => tt
           | Compilers.ident.Nat_eqb => tt
           | Compilers.ident.nil t => tt
           | Compilers.ident.cons t => tt
           | Compilers.ident.pair A B => tt
           | Compilers.ident.fst A B => tt
           | Compilers.ident.snd A B => tt
           | Compilers.ident.prod_rect A B T => tt
           | Compilers.ident.bool_rect T => tt
           | Compilers.ident.nat_rect P => tt
           | Compilers.ident.nat_rect_arrow P Q => tt
           | Compilers.ident.eager_nat_rect P => tt
           | Compilers.ident.eager_nat_rect_arrow P Q => tt
           | Compilers.ident.list_rect A P => tt
           | Compilers.ident.eager_list_rect A P => tt
           | Compilers.ident.eager_list_rect_arrow A P Q => tt
           | Compilers.ident.list_case A P => tt
           | Compilers.ident.List_length T => tt
           | Compilers.ident.List_seq => tt
           | Compilers.ident.List_firstn A => tt
           | Compilers.ident.List_skipn A => tt
           | Compilers.ident.List_repeat A => tt
           | Compilers.ident.List_combine A B => tt
           | Compilers.ident.List_map A B => tt
           | Compilers.ident.List_app A => tt
           | Compilers.ident.List_rev A => tt
           | Compilers.ident.List_flat_map A B => tt
           | Compilers.ident.List_partition A => tt
           | Compilers.ident.List_fold_right A B => tt
           | Compilers.ident.List_update_nth T => tt
           | Compilers.ident.List_nth_default T => tt
           | Compilers.ident.Z_add => tt
           | Compilers.ident.Z_mul => tt
           | Compilers.ident.Z_pow => tt
           | Compilers.ident.Z_sub => tt
           | Compilers.ident.Z_opp => tt
           | Compilers.ident.Z_div => tt
           | Compilers.ident.Z_modulo => tt
           | Compilers.ident.Z_log2 => tt
           | Compilers.ident.Z_log2_up => tt
           | Compilers.ident.Z_eqb => tt
           | Compilers.ident.Z_leb => tt
           | Compilers.ident.Z_ltb => tt
           | Compilers.ident.Z_geb => tt
           | Compilers.ident.Z_gtb => tt
           | Compilers.ident.Z_of_nat => tt
           | Compilers.ident.Z_to_nat => tt
           | Compilers.ident.Z_shiftr => tt
           | Compilers.ident.Z_shiftl => tt
           | Compilers.ident.Z_land => tt
           | Compilers.ident.Z_lor => tt
           | Compilers.ident.Z_min => tt
           | Compilers.ident.Z_max => tt
           | Compilers.ident.Z_bneg => tt
           | Compilers.ident.Z_lnot_modulo => tt
           | Compilers.ident.Z_mul_split => tt
           | Compilers.ident.Z_add_get_carry => tt
           | Compilers.ident.Z_add_with_carry => tt
           | Compilers.ident.Z_add_with_get_carry => tt
           | Compilers.ident.Z_sub_get_borrow => tt
           | Compilers.ident.Z_sub_with_get_borrow => tt
           | Compilers.ident.Z_zselect => tt
           | Compilers.ident.Z_add_modulo => tt
           | Compilers.ident.Z_rshi => tt
           | Compilers.ident.Z_cc_m => tt
           | Compilers.ident.Z_cast range => (range, tt)
           | Compilers.ident.Z_cast2 range => (range, tt)
           | Compilers.ident.option_Some A => tt
           | Compilers.ident.option_None A => tt
           | Compilers.ident.option_rect A P => tt
           | Compilers.ident.Build_zrange => tt
           | Compilers.ident.zrange_rect P => tt
           | Compilers.ident.fancy_add log2wordmax imm => (log2wordmax, (imm, tt))
           | Compilers.ident.fancy_addc log2wordmax imm => (log2wordmax, (imm, tt))
           | Compilers.ident.fancy_sub log2wordmax imm => (log2wordmax, (imm, tt))
           | Compilers.ident.fancy_subb log2wordmax imm => (log2wordmax, (imm, tt))
           | Compilers.ident.fancy_mulll log2wordmax => (log2wordmax, tt)
           | Compilers.ident.fancy_mullh log2wordmax => (log2wordmax, tt)
           | Compilers.ident.fancy_mulhl log2wordmax => (log2wordmax, tt)
           | Compilers.ident.fancy_mulhh log2wordmax => (log2wordmax, tt)
           | Compilers.ident.fancy_rshi log2wordmax x => (log2wordmax, (x, tt))
           | Compilers.ident.fancy_selc => tt
           | Compilers.ident.fancy_selm log2wordmax => (log2wordmax, tt)
           | Compilers.ident.fancy_sell => tt
           | Compilers.ident.fancy_addm => tt
           end.

      Derive type_of_list_arg_types_beq
             SuchThat (forall {t idc}, reflect_rel (@eq (type_of_list (@arg_types t idc))) (@type_of_list_arg_types_beq t idc))
             As reflect_type_of_list_arg_types_beq.
      Proof.
        subst type_of_list_arg_types_beq; intros t idc.
        instantiate (1:=ltac:(intros t idc; destruct idc)); destruct idc; cbn [fold_right arg_types]; try solve [ exact reflect_eq_unit ]; instantiate (1:=ltac:(cbn [fold_right arg_types])); exact _.
      Qed.
    End ident.

    (*===*)

  End pattern.
End Compilers.
