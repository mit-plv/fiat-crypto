Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Experiments.NewPipeline.Language.

Module Compilers.
  Export Language.Compilers.

  Module pattern.
    Module ident.
      Set Boolean Equality Schemes.
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
              base.interp (base.type.type_base t) ->
              ident
                ((fun x : base.type => type.base x) (base.type.type_base t))
  | Nat_succ : ident
                 ((fun x : base.type => type.base x)
                    (base.type.type_base base.type.nat) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.nat))
  | Nat_pred : ident
                 ((fun x : base.type => type.base x)
                    (base.type.type_base base.type.nat) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.nat))
  | Nat_max : ident
                ((fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat) ->
                 (fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat) ->
                 (fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat))
  | Nat_mul : ident
                ((fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat) ->
                 (fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat) ->
                 (fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat))
  | Nat_add : ident
                ((fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat) ->
                 (fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat) ->
                 (fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat))
  | Nat_sub : ident
                ((fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat) ->
                 (fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat) ->
                 (fun x : base.type => type.base x)
                   (base.type.type_base base.type.nat))
  | nil : forall t : base.type,
          ident ((fun x : base.type => type.base x) (base.type.list t))
  | cons : forall t : base.type,
           ident
             ((fun x : base.type => type.base x) t ->
              (fun x : base.type => type.base x) (base.type.list t) ->
              (fun x : base.type => type.base x) (base.type.list t))
  | pair : forall A B : base.type,
           ident
             ((fun x : base.type => type.base x) A ->
              (fun x : base.type => type.base x) B ->
              (fun x : base.type => type.base x) (A * B)%etype)
  | fst : forall A B : base.type,
          ident
            ((fun x : base.type => type.base x) (A * B)%etype ->
             (fun x : base.type => type.base x) A)
  | snd : forall A B : base.type,
          ident
            ((fun x : base.type => type.base x) (A * B)%etype ->
             (fun x : base.type => type.base x) B)
  | prod_rect : forall A B T : base.type,
                ident
                  (((fun x : base.type => type.base x) A ->
                    (fun x : base.type => type.base x) B ->
                    (fun x : base.type => type.base x) T) ->
                   (fun x : base.type => type.base x) (A * B)%etype ->
                   (fun x : base.type => type.base x) T)
  | bool_rect : forall T : base.type,
                ident
                  (((fun x : base.type => type.base x) ()%etype ->
                    (fun x : base.type => type.base x) T) ->
                   ((fun x : base.type => type.base x) ()%etype ->
                    (fun x : base.type => type.base x) T) ->
                   (fun x : base.type => type.base x)
                     (base.type.type_base base.type.bool) ->
                   (fun x : base.type => type.base x) T)
  | nat_rect : forall P : base.type,
               ident
                 (((fun x : base.type => type.base x) ()%etype ->
                   (fun x : base.type => type.base x) P) ->
                  ((fun x : base.type => type.base x)
                     (base.type.type_base base.type.nat) ->
                   (fun x : base.type => type.base x) P ->
                   (fun x : base.type => type.base x) P) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.nat) ->
                  (fun x : base.type => type.base x) P)
  | nat_rect_arrow : forall P Q : base.type,
                     ident
                       (((fun x : base.type => type.base x) P ->
                         (fun x : base.type => type.base x) Q) ->
                        ((fun x : base.type => type.base x)
                           (base.type.type_base base.type.nat) ->
                         ((fun x : base.type => type.base x) P ->
                          (fun x : base.type => type.base x) Q) ->
                         (fun x : base.type => type.base x) P ->
                         (fun x : base.type => type.base x) Q) ->
                        (fun x : base.type => type.base x)
                          (base.type.type_base base.type.nat) ->
                        (fun x : base.type => type.base x) P ->
                        (fun x : base.type => type.base x) Q)
  | list_rect : forall A P : base.type,
                ident
                  (((fun x : base.type => type.base x) ()%etype ->
                    (fun x : base.type => type.base x) P) ->
                   ((fun x : base.type => type.base x) A ->
                    (fun x : base.type => type.base x) (base.type.list A) ->
                    (fun x : base.type => type.base x) P ->
                    (fun x : base.type => type.base x) P) ->
                   (fun x : base.type => type.base x) (base.type.list A) ->
                   (fun x : base.type => type.base x) P)
  | list_case : forall A P : base.type,
                ident
                  (((fun x : base.type => type.base x) ()%etype ->
                    (fun x : base.type => type.base x) P) ->
                   ((fun x : base.type => type.base x) A ->
                    (fun x : base.type => type.base x) (base.type.list A) ->
                    (fun x : base.type => type.base x) P) ->
                   (fun x : base.type => type.base x) (base.type.list A) ->
                   (fun x : base.type => type.base x) P)
  | List_length : forall T : base.type,
                  ident
                    ((fun x : base.type => type.base x) (base.type.list T) ->
                     (fun x : base.type => type.base x)
                       (base.type.type_base base.type.nat))
  | List_seq : ident
                 ((fun x : base.type => type.base x)
                    (base.type.type_base base.type.nat) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.nat) ->
                  (fun x : base.type => type.base x)
                    (base.type.list (base.type.type_base base.type.nat)))
  | List_firstn : forall A : base.type,
                  ident
                    ((fun x : base.type => type.base x)
                       (base.type.type_base base.type.nat) ->
                     (fun x : base.type => type.base x) (base.type.list A) ->
                     (fun x : base.type => type.base x) (base.type.list A))
  | List_skipn : forall A : base.type,
                 ident
                   ((fun x : base.type => type.base x)
                      (base.type.type_base base.type.nat) ->
                    (fun x : base.type => type.base x) (base.type.list A) ->
                    (fun x : base.type => type.base x) (base.type.list A))
  | List_repeat : forall A : base.type,
                  ident
                    ((fun x : base.type => type.base x) A ->
                     (fun x : base.type => type.base x)
                       (base.type.type_base base.type.nat) ->
                     (fun x : base.type => type.base x) (base.type.list A))
  | List_combine : forall A B : base.type,
                   ident
                     ((fun x : base.type => type.base x) (base.type.list A) ->
                      (fun x : base.type => type.base x) (base.type.list B) ->
                      (fun x : base.type => type.base x)
                        (base.type.list (A * B)))
  | List_map : forall A B : base.type,
               ident
                 (((fun x : base.type => type.base x) A ->
                   (fun x : base.type => type.base x) B) ->
                  (fun x : base.type => type.base x) (base.type.list A) ->
                  (fun x : base.type => type.base x) (base.type.list B))
  | List_app : forall A : base.type,
               ident
                 ((fun x : base.type => type.base x) (base.type.list A) ->
                  (fun x : base.type => type.base x) (base.type.list A) ->
                  (fun x : base.type => type.base x) (base.type.list A))
  | List_rev : forall A : base.type,
               ident
                 ((fun x : base.type => type.base x) (base.type.list A) ->
                  (fun x : base.type => type.base x) (base.type.list A))
  | List_flat_map : forall A B : base.type,
                    ident
                      (((fun x : base.type => type.base x) A ->
                        (fun x : base.type => type.base x) (base.type.list B)) ->
                       (fun x : base.type => type.base x) (base.type.list A) ->
                       (fun x : base.type => type.base x) (base.type.list B))
  | List_partition : forall A : base.type,
                     ident
                       (((fun x : base.type => type.base x) A ->
                         (fun x : base.type => type.base x)
                           (base.type.type_base base.type.bool)) ->
                        (fun x : base.type => type.base x) (base.type.list A) ->
                        (fun x : base.type => type.base x)
                          (base.type.list A * base.type.list A)%etype)
  | List_fold_right : forall A B : base.type,
                      ident
                        (((fun x : base.type => type.base x) B ->
                          (fun x : base.type => type.base x) A ->
                          (fun x : base.type => type.base x) A) ->
                         (fun x : base.type => type.base x) A ->
                         (fun x : base.type => type.base x)
                           (base.type.list B) ->
                         (fun x : base.type => type.base x) A)
  | List_update_nth : forall T : base.type,
                      ident
                        ((fun x : base.type => type.base x)
                           (base.type.type_base base.type.nat) ->
                         ((fun x : base.type => type.base x) T ->
                          (fun x : base.type => type.base x) T) ->
                         (fun x : base.type => type.base x)
                           (base.type.list T) ->
                         (fun x : base.type => type.base x)
                           (base.type.list T))
  | List_nth_default : forall T : base.type,
                       ident
                         ((fun x : base.type => type.base x) T ->
                          (fun x : base.type => type.base x)
                            (base.type.list T) ->
                          (fun x : base.type => type.base x)
                            (base.type.type_base base.type.nat) ->
                          (fun x : base.type => type.base x) T)
  | Z_add : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z))
  | Z_mul : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z))
  | Z_pow : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z))
  | Z_sub : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z))
  | Z_opp : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z))
  | Z_div : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z))
  | Z_modulo : ident
                 ((fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z))
  | Z_log2 : ident
               ((fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z))
  | Z_log2_up : ident
                  ((fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z) ->
                   (fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z))
  | Z_eqb : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.bool))
  | Z_leb : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.bool))
  | Z_geb : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.bool))
  | Z_of_nat : ident
                 ((fun x : base.type => type.base x)
                    (base.type.type_base base.type.nat) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z))
  | Z_to_nat : ident
                 ((fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.nat))
  | Z_shiftr : ident
                 ((fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z))
  | Z_shiftl : ident
                 ((fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z) ->
                  (fun x : base.type => type.base x)
                    (base.type.type_base base.type.Z))
  | Z_land : ident
               ((fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z))
  | Z_lor : ident
              ((fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z) ->
               (fun x : base.type => type.base x)
                 (base.type.type_base base.type.Z))
  | Z_bneg : ident
               ((fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z))
  | Z_lnot_modulo : ident
                      ((fun x : base.type => type.base x)
                         (base.type.type_base base.type.Z) ->
                       (fun x : base.type => type.base x)
                         (base.type.type_base base.type.Z) ->
                       (fun x : base.type => type.base x)
                         (base.type.type_base base.type.Z))
  | Z_mul_split : ident
                    ((fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z) ->
                     (fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z) ->
                     (fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z) ->
                     (fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z *
                        base.type.type_base base.type.Z)%etype)
  | Z_add_get_carry : ident
                        ((fun x : base.type => type.base x)
                           (base.type.type_base base.type.Z) ->
                         (fun x : base.type => type.base x)
                           (base.type.type_base base.type.Z) ->
                         (fun x : base.type => type.base x)
                           (base.type.type_base base.type.Z) ->
                         (fun x : base.type => type.base x)
                           (base.type.type_base base.type.Z *
                            base.type.type_base base.type.Z)%etype)
  | Z_add_with_carry : ident
                         ((fun x : base.type => type.base x)
                            (base.type.type_base base.type.Z) ->
                          (fun x : base.type => type.base x)
                            (base.type.type_base base.type.Z) ->
                          (fun x : base.type => type.base x)
                            (base.type.type_base base.type.Z) ->
                          (fun x : base.type => type.base x)
                            (base.type.type_base base.type.Z))
  | Z_add_with_get_carry : ident
                             ((fun x : base.type => type.base x)
                                (base.type.type_base base.type.Z) ->
                              (fun x : base.type => type.base x)
                                (base.type.type_base base.type.Z) ->
                              (fun x : base.type => type.base x)
                                (base.type.type_base base.type.Z) ->
                              (fun x : base.type => type.base x)
                                (base.type.type_base base.type.Z) ->
                              (fun x : base.type => type.base x)
                                (base.type.type_base base.type.Z *
                                 base.type.type_base base.type.Z)%etype)
  | Z_sub_get_borrow : ident
                         ((fun x : base.type => type.base x)
                            (base.type.type_base base.type.Z) ->
                          (fun x : base.type => type.base x)
                            (base.type.type_base base.type.Z) ->
                          (fun x : base.type => type.base x)
                            (base.type.type_base base.type.Z) ->
                          (fun x : base.type => type.base x)
                            (base.type.type_base base.type.Z *
                             base.type.type_base base.type.Z)%etype)
  | Z_sub_with_get_borrow : ident
                              ((fun x : base.type => type.base x)
                                 (base.type.type_base base.type.Z) ->
                               (fun x : base.type => type.base x)
                                 (base.type.type_base base.type.Z) ->
                               (fun x : base.type => type.base x)
                                 (base.type.type_base base.type.Z) ->
                               (fun x : base.type => type.base x)
                                 (base.type.type_base base.type.Z) ->
                               (fun x : base.type => type.base x)
                                 (base.type.type_base base.type.Z *
                                  base.type.type_base base.type.Z)%etype)
  | Z_zselect : ident
                  ((fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z) ->
                   (fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z) ->
                   (fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z) ->
                   (fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z))
  | Z_add_modulo : ident
                     ((fun x : base.type => type.base x)
                        (base.type.type_base base.type.Z) ->
                      (fun x : base.type => type.base x)
                        (base.type.type_base base.type.Z) ->
                      (fun x : base.type => type.base x)
                        (base.type.type_base base.type.Z) ->
                      (fun x : base.type => type.base x)
                        (base.type.type_base base.type.Z))
  | Z_rshi : ident
               ((fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z))
  | Z_cc_m : ident
               ((fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z))
  | Z_cast : zrange ->
             ident
               ((fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z) ->
                (fun x : base.type => type.base x)
                  (base.type.type_base base.type.Z))
  | Z_cast2 : zrange * zrange ->
              ident
                ((fun x : base.type => type.base x)
                   (base.type.type_base base.type.Z *
                    base.type.type_base base.type.Z)%etype ->
                 (fun x : base.type => type.base x)
                   (base.type.type_base base.type.Z *
                    base.type.type_base base.type.Z)%etype)
  | fancy_add : Z ->
                Z ->
                ident
                  ((fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z *
                      base.type.type_base base.type.Z)%etype ->
                   (fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z *
                      base.type.type_base base.type.Z)%etype)
  | fancy_addc : Z ->
                 Z ->
                 ident
                   ((fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z)%etype ->
                    (fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z)%etype)
  | fancy_sub : Z ->
                Z ->
                ident
                  ((fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z *
                      base.type.type_base base.type.Z)%etype ->
                   (fun x : base.type => type.base x)
                     (base.type.type_base base.type.Z *
                      base.type.type_base base.type.Z)%etype)
  | fancy_subb : Z ->
                 Z ->
                 ident
                   ((fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z)%etype ->
                    (fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z)%etype)
  | fancy_mulll : Z ->
                  ident
                    ((fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z *
                        base.type.type_base base.type.Z)%etype ->
                     (fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z))
  | fancy_mullh : Z ->
                  ident
                    ((fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z *
                        base.type.type_base base.type.Z)%etype ->
                     (fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z))
  | fancy_mulhl : Z ->
                  ident
                    ((fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z *
                        base.type.type_base base.type.Z)%etype ->
                     (fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z))
  | fancy_mulhh : Z ->
                  ident
                    ((fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z *
                        base.type.type_base base.type.Z)%etype ->
                     (fun x : base.type => type.base x)
                       (base.type.type_base base.type.Z))
  | fancy_rshi : Z ->
                 Z ->
                 ident
                   ((fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z)%etype ->
                    (fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z))
  | fancy_selc : ident
                   ((fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z)%etype ->
                    (fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z))
  | fancy_selm : Z ->
                 ident
                   ((fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z)%etype ->
                    (fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z))
  | fancy_sell : ident
                   ((fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z)%etype ->
                    (fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z))
  | fancy_addm : ident
                   ((fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z *
                       base.type.type_base base.type.Z)%etype ->
                    (fun x : base.type => type.base x)
                      (base.type.type_base base.type.Z))

"""
show_match_ident = r"""match # with
 | ident.Literal t v =>
 | ident.Nat_succ =>
 | ident.Nat_pred =>
 | ident.Nat_max =>
 | ident.Nat_mul =>
 | ident.Nat_add =>
 | ident.Nat_sub =>
 | ident.nil t =>
 | ident.cons t =>
 | ident.pair A B =>
 | ident.fst A B =>
 | ident.snd A B =>
 | ident.prod_rect A B T =>
 | ident.bool_rect T =>
 | ident.nat_rect P =>
 | ident.nat_rect_arrow P Q =>
 | ident.list_rect A P =>
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
 | ident.Z_geb =>
 | ident.Z_of_nat =>
 | ident.Z_to_nat =>
 | ident.Z_shiftr =>
 | ident.Z_shiftl =>
 | ident.Z_land =>
 | ident.Z_lor =>
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
  with open('/tmp/pr.out', 'r') as f: print_ident = re.sub(r'^For.*\n', '', f.read(), flags=re.MULTILINE)
  with open('/tmp/sm.out', 'r') as f: show_match_ident = f.read()

prefix = 'Compilers.'
indent = '      '
exts = ('Unit', 'Z', 'Bool', 'Nat')
tys = [('%sbase.type.' % prefix) + i for i in ('unit', 'Z', 'bool', 'nat')]
type_or_set = 'Type'
ctors = [i.strip('|=> ').split(' ') for i in show_match_ident.split('\n') if i.strip().startswith('|')]
assert(ctors[0][0] == 'ident.Literal')
assert(len(ctors[0]) > 1)
ctors = [[ctors[0][0] + ext] + ctors[0][2:] for ext in exts] + ctors[1:]
ctors_with_prefix = [[prefix + i[0]] + i[1:] for i in ctors]
ctors_no_prefix = [[i[0].replace('ident.', '')] + i[1:] for i in ctors]
pctors = [i[0] for i in ctors_no_prefix]
def get_dep_types(case):
  dep_tys = re.findall('forall ([^:]+):([^,]+),', case)
  if len(dep_tys) == 0: return []
  dep_tys = dep_tys[0]
  return [dep_tys[-1].strip()] * len([i for i in dep_tys[0].split(' ') if i.strip()])
ttypes = ([[] for ty in tys]
          + [get_dep_types(case)
             for case in print_ident.replace('\n', ' ').split('|')[1:]])
ctypes = ([['base.interp ' + ty] for ty in tys]
          + [[i.strip() for i in re.sub(r'forall [^:]+ : base.type,', '', i[i.find(':')+1:i.find('ident')]).strip(' ->').split('->') if i.strip()]
             for i in print_ident.replace('\n', ' ').split('|')[1:]])
crettypes = ([('%sident.ident (type.base (%sbase.type.type_base ' + ty + '))') % (prefix, prefix) for ty in tys]
             + [prefix + 'ident.' + re.sub(r'\(fun x : [^ ]+ => ([^ ]+) x\)', r'\1', re.sub('  +', ' ', i[i.find('ident'):]))
                for i in print_ident.replace('\n', ' ').split('|')[1:]])

retcode = r"""Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Experiments.NewPipeline.Language.

Module Compilers.
  Export Language.Compilers.

  Module pattern.
    Module ident.
      Set Boolean Equality Schemes.
      (""" + """*
      Set Printing Coercions.
      Redirect "/tmp/pr" Print Compilers.ident.ident.
      Redirect "/tmp/sm" Show Match Compilers.ident.ident.
      *""" + """)
"""

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
""" % (indent, get_updated_contents(), indent))
retcode += addnewline(r"""%sInductive ident :=
%s| %s.
""" % (indent, indent, ('\n' + indent + '| ').join(pctors)))
#retcode += addnewline((r"""%sDefinition beq_typed {t} (X : ident) (Y : %sident.ident t) : bool
#  := match X, Y with
#     | %s
#       => true
#     | %s
#       => false
#     end.
#""" % (indent, prefix,
#       '\n     | '.join(pctor + ', ' + ' '.join([ctor[0]] + ['_'] * (len(ctor)-1))
#                        for pctor, ctor in zip(pctors, ctors_with_prefix)),
#       '\n     | '.join(pctor + ', _' for pctor in pctors))).replace('\n', '\n' + indent))
retcode += addnewline((r"""%sDefinition try_make_transport_ident_cps (P : ident -> Type) (idc1 idc2 : ident) : ~> option (P idc1 -> P idc2)
  := match idc1, idc2 with
     | %s
       => fun T k => k (Some (fun v => v))
     | %s
       => fun T k => k None
     end%%cps.
""" % (indent,
       '\n     | '.join(pctor + ', ' + pctor for pctor in pctors),
       '\n     | '.join(pctor + ', _' for pctor in pctors))).replace('\n', '\n' + indent))
retcode += addnewline((r"""%sDefinition eta_ident_cps {T : %stype %sbase.type -> Type} {t} (idc : %sident.ident t)
           (f : forall t', %sident.ident t' -> T t')
  : T t
  := match idc with
     | %s
     end.
""" % (indent, prefix, prefix, prefix, prefix,
       '\n     | '.join(' '.join(ctor) + ' => f _ '
                        + (('%s' if len(ctor) == 1 else '(@%s)')
                           % ' '.join(ctor))
                        for ctor in ctors_with_prefix))).replace('\n', '\n' + indent))
#retcode += addnewline((r"""%sDefinition eta_all_option_cps {T} (f : ident -> option T)
#  : option (ident -> T)
#  := (%s;
#      Some (fun c
#            => match c with
#               | %s
#               end))%%option.
#""" % (indent,
#       ';\n      '.join('f' + pctor + ' <- f ' + ctor[0] for ctor, pctor in zip(ctors_no_prefix, pctors)),
#       '\n               | '.join(ctor[0] + ' => f' + pctor for pctor, ctor in zip(pctors, ctors_no_prefix)))).replace('\n', '\n' + indent))
retcode += addnewline((r"""%sDefinition of_typed_ident {t} (idc : %sident.ident t) : ident
  := match idc with
     | %s
     end.
""" % (indent, prefix, '\n     | '.join(' '.join(ctor) + ' => ' + pctor for ctor, pctor in zip(ctors_with_prefix, pctors)))).replace('\n', '\n' + indent))
#retcode += addnewline((r"""%sDefinition orb (f : ident -> bool) : bool
#  := (%s)%%bool.
#""" % (indent, ' || '.join('f ' + pctor for pctor in pctors))).replace('\n', '\n' + indent))
retcode += addnewline((r"""%sDefinition arg_types (idc : ident) : option %s
  := match idc return option %s with
     | %s
     end%%type.
""" % (indent, type_or_set, type_or_set,
       '\n     | '.join(pctor + ' => ' + ('None' if len(ctype) == 0 else '@Some ' + type_or_set + ' ' + (ctype[0] if ' ' not in ' * '.join(ctype) else '(%s)' % ' * '.join(ctype)))
                        for pctor, ctype in zip(pctors, ctypes)))).replace('\n', '\n' + indent))
retcode += addnewline((r"""%sDefinition full_types (idc : ident) : %s
  := match idc return %s with
     | %s
     end%%type.
""" % (indent, type_or_set, type_or_set,
       '\n     | '.join(pctor + ' => ' + (' * '.join(ttype + ctype) if len(ttype + ctype) > 0 else 'unit')
                        for pctor, ttype, ctype in zip(pctors, ttypes, ctypes)))).replace('\n', '\n' + indent))

retcode += addnewline((r"""%sDefinition bind_args {t} (idc : %sident.ident t) : match arg_types (of_typed_ident idc) return %s with Some t => t | None => unit end
  := match idc return match arg_types (of_typed_ident idc) return %s with Some t => t | None => unit end with
     | %s
     end%%cps.
""" % (indent, prefix, type_or_set, type_or_set,
       '\n     | '.join(' '.join(ctor) + ' => ' + ('tt' if len(ctype) == 0 else (ctor[-1] if len(ctype) == 1 else '(%s)' % ', '.join(ctor[-len(ctype):])))
                        for ctor, ctype in zip(ctors_with_prefix, ctypes)))).replace('\n', '\n' + indent))
retcode += addnewline((r"""%sDefinition invert_bind_args {t} (idc : %sident.ident t) (pidc : ident) : option (full_types pidc)
  := match pidc, idc return option (full_types pidc) with
     | %s
     | %s
       => None
     end%%cps.
""" % (indent, prefix,
       '\n     | '.join(pctor + ', ' + ' '.join(ctor) + ' => Some ' + ('tt' if len(ttype + ctype) == 0 else (ctor[-1] if len(ttype + ctype) == 1 else '(%s)' % ', '.join(ctor[-len(ttype + ctype):])))
                        for pctor, ctor, ttype, ctype in zip(pctors, ctors_with_prefix, ttypes, ctypes)),
       '\n     | '.join(pctor + ', _' for pctor in pctors))).replace('\n', '\n' + indent))

maxeta = max([len(ttype + ctype) for ttype, ctype in zip(ttypes, ctypes)])
if maxeta >= 2:
  retcode += addnewline(r"""%sLocal Notation eta2 x := (Datatypes.fst x, Datatypes.snd x) (only parsing).""" % indent)
for i in range(3, maxeta+1):
  retcode += addnewline(r"""%sLocal Notation eta%d x := (eta%d (Datatypes.fst x), Datatypes.snd x) (only parsing).""" % (indent, i, i-1))
retcode += addnewline('')

def do_adjust_type(ctor, ctype):
  return len(ctor) > 1 and 'Literal' in ctor[0]

retcode += addnewline((r"""%sDefinition type_of (pidc : ident) : full_types pidc -> %stype %sbase.type
  := match pidc return full_types pidc -> _ with
     | %s
     end%%etype.
""" % (indent, prefix, prefix,
       '\n     | '.join(pctor + ' => '
                        + 'fun ' + ('_ => ' if len(ttype + ctype) == 0 else ((ctor[-1] + ' => ') if len(ttype + ctype) == 1 else "arg => let '(%s) := eta%d arg in " % (', '.join(ctor[-len(ttype + ctype):]), len(ttype + ctype)))) + cretty.replace(prefix + 'ident.ident ', '')
                        for pctor, ctor, ttype, ctype, cretty in zip(pctors, ctors_with_prefix, ttypes, ctypes, crettypes)))).replace('\n', '\n' + indent))
retcode += addnewline((r"""%sDefinition to_typed (pidc : ident) : forall args : full_types pidc, %sident.ident (type_of pidc args)
  := match pidc return forall args : full_types pidc, %sident.ident (type_of pidc args) with
     | %s
     end.
""" % (indent, prefix, prefix,
       '\n     | '.join(pctor + ' => '
                        + 'fun ' + (('_ => %s' if len(ttype + ctype) == 0 else ((ctor[-1] + ' => %s') if len(ttype + ctype) == 1 else "arg => match eta%d arg as args' return %sident.ident (type_of %s args') with (%s) => %%s end" % (len(ttype + ctype), prefix, pctor, ', '.join(ctor[-len(ttype + ctype):])))) % ("@" + ' '.join(ctor)))
                        for pctor, ctor, ttype, ctype in zip(pctors, ctors_with_prefix, ttypes, ctypes)))).replace('\n', '\n' + indent))
retcode += addnewline((r"""%sDefinition retype_ident {t} (idc : %sident.ident t) : match arg_types (of_typed_ident idc) return %s with Some t => t | None => unit end -> %sident.ident t
  := match idc in %sident.ident t return match arg_types (of_typed_ident idc) return %s with Some t => t | None => unit end -> %sident.ident t with
     | %s
     end.
""" % (indent, prefix, type_or_set, prefix, prefix, type_or_set, prefix,
       '\n     | '.join(' '.join(ctor) + ' => '
                        + ('' if not do_adjust_type(ctor, ctype) else '(')
                        + 'fun ' + ('_ => ' if len(ctype) == 0 else ((ctor[-1] + ' => ') if len(ctype) == 1 else "arg => let '(%s) := eta%d arg in " % (', '.join(ctor[-len(ctype):]), len(ctype)))) + "@" + ' '.join(ctor)
                        + ('' if not do_adjust_type(ctor, ctype) else
                           (') : '
                            + ('match arg_types (of_typed_ident %s) return %s with Some t => t | None => unit end -> _'
                               % (('%s' if ' ' not in ' '.join(ctor) else '(@%s)') % ' '.join(ctor),
                                  type_or_set))
                            + ' (* COQBUG(https://github.com/coq/coq/issues/7726) *)'))
                        for ctor, ctype in zip(ctors_with_prefix, ctypes)))).replace('\n', '\n' + indent))
# ctor[:len(ctor)-len(ctype)] + ['_'] * len(ctype)

retcode += addnewline(indent + '\n' + indent + '(*===*)')

retcode += r"""    End ident.
  End pattern.
End Compilers.
"""
with open('GENERATEDIdentifiersWithoutTypes.v', 'w') as f:
  f.write(retcode)

>>>
      *)

      Inductive ident :=
      | LiteralUnit
      | LiteralZ
      | LiteralBool
      | LiteralNat
      | Nat_succ
      | Nat_pred
      | Nat_max
      | Nat_mul
      | Nat_add
      | Nat_sub
      | nil
      | cons
      | pair
      | fst
      | snd
      | prod_rect
      | bool_rect
      | nat_rect
      | nat_rect_arrow
      | list_rect
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
      | Z_geb
      | Z_of_nat
      | Z_to_nat
      | Z_shiftr
      | Z_shiftl
      | Z_land
      | Z_lor
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

      Definition try_make_transport_ident_cps (P : ident -> Type) (idc1 idc2 : ident) : ~> option (P idc1 -> P idc2)
        := match idc1, idc2 with
           | LiteralUnit, LiteralUnit
           | LiteralZ, LiteralZ
           | LiteralBool, LiteralBool
           | LiteralNat, LiteralNat
           | Nat_succ, Nat_succ
           | Nat_pred, Nat_pred
           | Nat_max, Nat_max
           | Nat_mul, Nat_mul
           | Nat_add, Nat_add
           | Nat_sub, Nat_sub
           | nil, nil
           | cons, cons
           | pair, pair
           | fst, fst
           | snd, snd
           | prod_rect, prod_rect
           | bool_rect, bool_rect
           | nat_rect, nat_rect
           | nat_rect_arrow, nat_rect_arrow
           | list_rect, list_rect
           | list_case, list_case
           | List_length, List_length
           | List_seq, List_seq
           | List_firstn, List_firstn
           | List_skipn, List_skipn
           | List_repeat, List_repeat
           | List_combine, List_combine
           | List_map, List_map
           | List_app, List_app
           | List_rev, List_rev
           | List_flat_map, List_flat_map
           | List_partition, List_partition
           | List_fold_right, List_fold_right
           | List_update_nth, List_update_nth
           | List_nth_default, List_nth_default
           | Z_add, Z_add
           | Z_mul, Z_mul
           | Z_pow, Z_pow
           | Z_sub, Z_sub
           | Z_opp, Z_opp
           | Z_div, Z_div
           | Z_modulo, Z_modulo
           | Z_log2, Z_log2
           | Z_log2_up, Z_log2_up
           | Z_eqb, Z_eqb
           | Z_leb, Z_leb
           | Z_geb, Z_geb
           | Z_of_nat, Z_of_nat
           | Z_to_nat, Z_to_nat
           | Z_shiftr, Z_shiftr
           | Z_shiftl, Z_shiftl
           | Z_land, Z_land
           | Z_lor, Z_lor
           | Z_bneg, Z_bneg
           | Z_lnot_modulo, Z_lnot_modulo
           | Z_mul_split, Z_mul_split
           | Z_add_get_carry, Z_add_get_carry
           | Z_add_with_carry, Z_add_with_carry
           | Z_add_with_get_carry, Z_add_with_get_carry
           | Z_sub_get_borrow, Z_sub_get_borrow
           | Z_sub_with_get_borrow, Z_sub_with_get_borrow
           | Z_zselect, Z_zselect
           | Z_add_modulo, Z_add_modulo
           | Z_rshi, Z_rshi
           | Z_cc_m, Z_cc_m
           | Z_cast, Z_cast
           | Z_cast2, Z_cast2
           | fancy_add, fancy_add
           | fancy_addc, fancy_addc
           | fancy_sub, fancy_sub
           | fancy_subb, fancy_subb
           | fancy_mulll, fancy_mulll
           | fancy_mullh, fancy_mullh
           | fancy_mulhl, fancy_mulhl
           | fancy_mulhh, fancy_mulhh
           | fancy_rshi, fancy_rshi
           | fancy_selc, fancy_selc
           | fancy_selm, fancy_selm
           | fancy_sell, fancy_sell
           | fancy_addm, fancy_addm
             => fun T k => k (Some (fun v => v))
           | LiteralUnit, _
           | LiteralZ, _
           | LiteralBool, _
           | LiteralNat, _
           | Nat_succ, _
           | Nat_pred, _
           | Nat_max, _
           | Nat_mul, _
           | Nat_add, _
           | Nat_sub, _
           | nil, _
           | cons, _
           | pair, _
           | fst, _
           | snd, _
           | prod_rect, _
           | bool_rect, _
           | nat_rect, _
           | nat_rect_arrow, _
           | list_rect, _
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
           | Z_geb, _
           | Z_of_nat, _
           | Z_to_nat, _
           | Z_shiftr, _
           | Z_shiftl, _
           | Z_land, _
           | Z_lor, _
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
             => fun T k => k None
           end%cps.

      Definition eta_ident_cps {T : Compilers.type Compilers.base.type -> Type} {t} (idc : Compilers.ident.ident t)
                 (f : forall t', Compilers.ident.ident t' -> T t')
        : T t
        := match idc with
           | Compilers.ident.LiteralUnit v => f _ (@Compilers.ident.LiteralUnit v)
           | Compilers.ident.LiteralZ v => f _ (@Compilers.ident.LiteralZ v)
           | Compilers.ident.LiteralBool v => f _ (@Compilers.ident.LiteralBool v)
           | Compilers.ident.LiteralNat v => f _ (@Compilers.ident.LiteralNat v)
           | Compilers.ident.Nat_succ => f _ Compilers.ident.Nat_succ
           | Compilers.ident.Nat_pred => f _ Compilers.ident.Nat_pred
           | Compilers.ident.Nat_max => f _ Compilers.ident.Nat_max
           | Compilers.ident.Nat_mul => f _ Compilers.ident.Nat_mul
           | Compilers.ident.Nat_add => f _ Compilers.ident.Nat_add
           | Compilers.ident.Nat_sub => f _ Compilers.ident.Nat_sub
           | Compilers.ident.nil t => f _ (@Compilers.ident.nil t)
           | Compilers.ident.cons t => f _ (@Compilers.ident.cons t)
           | Compilers.ident.pair A B => f _ (@Compilers.ident.pair A B)
           | Compilers.ident.fst A B => f _ (@Compilers.ident.fst A B)
           | Compilers.ident.snd A B => f _ (@Compilers.ident.snd A B)
           | Compilers.ident.prod_rect A B T => f _ (@Compilers.ident.prod_rect A B T)
           | Compilers.ident.bool_rect T => f _ (@Compilers.ident.bool_rect T)
           | Compilers.ident.nat_rect P => f _ (@Compilers.ident.nat_rect P)
           | Compilers.ident.nat_rect_arrow P Q => f _ (@Compilers.ident.nat_rect_arrow P Q)
           | Compilers.ident.list_rect A P => f _ (@Compilers.ident.list_rect A P)
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
           | Compilers.ident.Z_geb => f _ Compilers.ident.Z_geb
           | Compilers.ident.Z_of_nat => f _ Compilers.ident.Z_of_nat
           | Compilers.ident.Z_to_nat => f _ Compilers.ident.Z_to_nat
           | Compilers.ident.Z_shiftr => f _ Compilers.ident.Z_shiftr
           | Compilers.ident.Z_shiftl => f _ Compilers.ident.Z_shiftl
           | Compilers.ident.Z_land => f _ Compilers.ident.Z_land
           | Compilers.ident.Z_lor => f _ Compilers.ident.Z_lor
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

      Definition of_typed_ident {t} (idc : Compilers.ident.ident t) : ident
        := match idc with
           | Compilers.ident.LiteralUnit v => LiteralUnit
           | Compilers.ident.LiteralZ v => LiteralZ
           | Compilers.ident.LiteralBool v => LiteralBool
           | Compilers.ident.LiteralNat v => LiteralNat
           | Compilers.ident.Nat_succ => Nat_succ
           | Compilers.ident.Nat_pred => Nat_pred
           | Compilers.ident.Nat_max => Nat_max
           | Compilers.ident.Nat_mul => Nat_mul
           | Compilers.ident.Nat_add => Nat_add
           | Compilers.ident.Nat_sub => Nat_sub
           | Compilers.ident.nil t => nil
           | Compilers.ident.cons t => cons
           | Compilers.ident.pair A B => pair
           | Compilers.ident.fst A B => fst
           | Compilers.ident.snd A B => snd
           | Compilers.ident.prod_rect A B T => prod_rect
           | Compilers.ident.bool_rect T => bool_rect
           | Compilers.ident.nat_rect P => nat_rect
           | Compilers.ident.nat_rect_arrow P Q => nat_rect_arrow
           | Compilers.ident.list_rect A P => list_rect
           | Compilers.ident.list_case A P => list_case
           | Compilers.ident.List_length T => List_length
           | Compilers.ident.List_seq => List_seq
           | Compilers.ident.List_firstn A => List_firstn
           | Compilers.ident.List_skipn A => List_skipn
           | Compilers.ident.List_repeat A => List_repeat
           | Compilers.ident.List_combine A B => List_combine
           | Compilers.ident.List_map A B => List_map
           | Compilers.ident.List_app A => List_app
           | Compilers.ident.List_rev A => List_rev
           | Compilers.ident.List_flat_map A B => List_flat_map
           | Compilers.ident.List_partition A => List_partition
           | Compilers.ident.List_fold_right A B => List_fold_right
           | Compilers.ident.List_update_nth T => List_update_nth
           | Compilers.ident.List_nth_default T => List_nth_default
           | Compilers.ident.Z_add => Z_add
           | Compilers.ident.Z_mul => Z_mul
           | Compilers.ident.Z_pow => Z_pow
           | Compilers.ident.Z_sub => Z_sub
           | Compilers.ident.Z_opp => Z_opp
           | Compilers.ident.Z_div => Z_div
           | Compilers.ident.Z_modulo => Z_modulo
           | Compilers.ident.Z_log2 => Z_log2
           | Compilers.ident.Z_log2_up => Z_log2_up
           | Compilers.ident.Z_eqb => Z_eqb
           | Compilers.ident.Z_leb => Z_leb
           | Compilers.ident.Z_geb => Z_geb
           | Compilers.ident.Z_of_nat => Z_of_nat
           | Compilers.ident.Z_to_nat => Z_to_nat
           | Compilers.ident.Z_shiftr => Z_shiftr
           | Compilers.ident.Z_shiftl => Z_shiftl
           | Compilers.ident.Z_land => Z_land
           | Compilers.ident.Z_lor => Z_lor
           | Compilers.ident.Z_bneg => Z_bneg
           | Compilers.ident.Z_lnot_modulo => Z_lnot_modulo
           | Compilers.ident.Z_mul_split => Z_mul_split
           | Compilers.ident.Z_add_get_carry => Z_add_get_carry
           | Compilers.ident.Z_add_with_carry => Z_add_with_carry
           | Compilers.ident.Z_add_with_get_carry => Z_add_with_get_carry
           | Compilers.ident.Z_sub_get_borrow => Z_sub_get_borrow
           | Compilers.ident.Z_sub_with_get_borrow => Z_sub_with_get_borrow
           | Compilers.ident.Z_zselect => Z_zselect
           | Compilers.ident.Z_add_modulo => Z_add_modulo
           | Compilers.ident.Z_rshi => Z_rshi
           | Compilers.ident.Z_cc_m => Z_cc_m
           | Compilers.ident.Z_cast range => Z_cast
           | Compilers.ident.Z_cast2 range => Z_cast2
           | Compilers.ident.fancy_add log2wordmax imm => fancy_add
           | Compilers.ident.fancy_addc log2wordmax imm => fancy_addc
           | Compilers.ident.fancy_sub log2wordmax imm => fancy_sub
           | Compilers.ident.fancy_subb log2wordmax imm => fancy_subb
           | Compilers.ident.fancy_mulll log2wordmax => fancy_mulll
           | Compilers.ident.fancy_mullh log2wordmax => fancy_mullh
           | Compilers.ident.fancy_mulhl log2wordmax => fancy_mulhl
           | Compilers.ident.fancy_mulhh log2wordmax => fancy_mulhh
           | Compilers.ident.fancy_rshi log2wordmax x => fancy_rshi
           | Compilers.ident.fancy_selc => fancy_selc
           | Compilers.ident.fancy_selm log2wordmax => fancy_selm
           | Compilers.ident.fancy_sell => fancy_sell
           | Compilers.ident.fancy_addm => fancy_addm
           end.

      Definition arg_types (idc : ident) : option Type
        := match idc return option Type with
           | LiteralUnit => @Some Type (base.interp Compilers.base.type.unit)
           | LiteralZ => @Some Type (base.interp Compilers.base.type.Z)
           | LiteralBool => @Some Type (base.interp Compilers.base.type.bool)
           | LiteralNat => @Some Type (base.interp Compilers.base.type.nat)
           | Nat_succ => None
           | Nat_pred => None
           | Nat_max => None
           | Nat_mul => None
           | Nat_add => None
           | Nat_sub => None
           | nil => None
           | cons => None
           | pair => None
           | fst => None
           | snd => None
           | prod_rect => None
           | bool_rect => None
           | nat_rect => None
           | nat_rect_arrow => None
           | list_rect => None
           | list_case => None
           | List_length => None
           | List_seq => None
           | List_firstn => None
           | List_skipn => None
           | List_repeat => None
           | List_combine => None
           | List_map => None
           | List_app => None
           | List_rev => None
           | List_flat_map => None
           | List_partition => None
           | List_fold_right => None
           | List_update_nth => None
           | List_nth_default => None
           | Z_add => None
           | Z_mul => None
           | Z_pow => None
           | Z_sub => None
           | Z_opp => None
           | Z_div => None
           | Z_modulo => None
           | Z_log2 => None
           | Z_log2_up => None
           | Z_eqb => None
           | Z_leb => None
           | Z_geb => None
           | Z_of_nat => None
           | Z_to_nat => None
           | Z_shiftr => None
           | Z_shiftl => None
           | Z_land => None
           | Z_lor => None
           | Z_bneg => None
           | Z_lnot_modulo => None
           | Z_mul_split => None
           | Z_add_get_carry => None
           | Z_add_with_carry => None
           | Z_add_with_get_carry => None
           | Z_sub_get_borrow => None
           | Z_sub_with_get_borrow => None
           | Z_zselect => None
           | Z_add_modulo => None
           | Z_rshi => None
           | Z_cc_m => None
           | Z_cast => @Some Type zrange
           | Z_cast2 => @Some Type (zrange * zrange)
           | fancy_add => @Some Type (Z * Z)
           | fancy_addc => @Some Type (Z * Z)
           | fancy_sub => @Some Type (Z * Z)
           | fancy_subb => @Some Type (Z * Z)
           | fancy_mulll => @Some Type Z
           | fancy_mullh => @Some Type Z
           | fancy_mulhl => @Some Type Z
           | fancy_mulhh => @Some Type Z
           | fancy_rshi => @Some Type (Z * Z)
           | fancy_selc => None
           | fancy_selm => @Some Type Z
           | fancy_sell => None
           | fancy_addm => None
           end%type.

      Definition full_types (idc : ident) : Type
        := match idc return Type with
           | LiteralUnit => base.interp Compilers.base.type.unit
           | LiteralZ => base.interp Compilers.base.type.Z
           | LiteralBool => base.interp Compilers.base.type.bool
           | LiteralNat => base.interp Compilers.base.type.nat
           | Nat_succ => unit
           | Nat_pred => unit
           | Nat_max => unit
           | Nat_mul => unit
           | Nat_add => unit
           | Nat_sub => unit
           | nil => base.type
           | cons => base.type
           | pair => base.type * base.type
           | fst => base.type * base.type
           | snd => base.type * base.type
           | prod_rect => base.type * base.type * base.type
           | bool_rect => base.type
           | nat_rect => base.type
           | nat_rect_arrow => base.type * base.type
           | list_rect => base.type * base.type
           | list_case => base.type * base.type
           | List_length => base.type
           | List_seq => unit
           | List_firstn => base.type
           | List_skipn => base.type
           | List_repeat => base.type
           | List_combine => base.type * base.type
           | List_map => base.type * base.type
           | List_app => base.type
           | List_rev => base.type
           | List_flat_map => base.type * base.type
           | List_partition => base.type
           | List_fold_right => base.type * base.type
           | List_update_nth => base.type
           | List_nth_default => base.type
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
           | Z_geb => unit
           | Z_of_nat => unit
           | Z_to_nat => unit
           | Z_shiftr => unit
           | Z_shiftl => unit
           | Z_land => unit
           | Z_lor => unit
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

      Definition bind_args {t} (idc : Compilers.ident.ident t) : match arg_types (of_typed_ident idc) return Type with Some t => t | None => unit end
        := match idc return match arg_types (of_typed_ident idc) return Type with Some t => t | None => unit end with
           | Compilers.ident.LiteralUnit v => v
           | Compilers.ident.LiteralZ v => v
           | Compilers.ident.LiteralBool v => v
           | Compilers.ident.LiteralNat v => v
           | Compilers.ident.Nat_succ => tt
           | Compilers.ident.Nat_pred => tt
           | Compilers.ident.Nat_max => tt
           | Compilers.ident.Nat_mul => tt
           | Compilers.ident.Nat_add => tt
           | Compilers.ident.Nat_sub => tt
           | Compilers.ident.nil t => tt
           | Compilers.ident.cons t => tt
           | Compilers.ident.pair A B => tt
           | Compilers.ident.fst A B => tt
           | Compilers.ident.snd A B => tt
           | Compilers.ident.prod_rect A B T => tt
           | Compilers.ident.bool_rect T => tt
           | Compilers.ident.nat_rect P => tt
           | Compilers.ident.nat_rect_arrow P Q => tt
           | Compilers.ident.list_rect A P => tt
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
           | Compilers.ident.Z_geb => tt
           | Compilers.ident.Z_of_nat => tt
           | Compilers.ident.Z_to_nat => tt
           | Compilers.ident.Z_shiftr => tt
           | Compilers.ident.Z_shiftl => tt
           | Compilers.ident.Z_land => tt
           | Compilers.ident.Z_lor => tt
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
           | Compilers.ident.Z_cast range => range
           | Compilers.ident.Z_cast2 range => range
           | Compilers.ident.fancy_add log2wordmax imm => (log2wordmax, imm)
           | Compilers.ident.fancy_addc log2wordmax imm => (log2wordmax, imm)
           | Compilers.ident.fancy_sub log2wordmax imm => (log2wordmax, imm)
           | Compilers.ident.fancy_subb log2wordmax imm => (log2wordmax, imm)
           | Compilers.ident.fancy_mulll log2wordmax => log2wordmax
           | Compilers.ident.fancy_mullh log2wordmax => log2wordmax
           | Compilers.ident.fancy_mulhl log2wordmax => log2wordmax
           | Compilers.ident.fancy_mulhh log2wordmax => log2wordmax
           | Compilers.ident.fancy_rshi log2wordmax x => (log2wordmax, x)
           | Compilers.ident.fancy_selc => tt
           | Compilers.ident.fancy_selm log2wordmax => log2wordmax
           | Compilers.ident.fancy_sell => tt
           | Compilers.ident.fancy_addm => tt
           end%cps.

      Definition invert_bind_args {t} (idc : Compilers.ident.ident t) (pidc : ident) : option (full_types pidc)
        := match pidc, idc return option (full_types pidc) with
           | LiteralUnit, Compilers.ident.LiteralUnit v => Some v
           | LiteralZ, Compilers.ident.LiteralZ v => Some v
           | LiteralBool, Compilers.ident.LiteralBool v => Some v
           | LiteralNat, Compilers.ident.LiteralNat v => Some v
           | Nat_succ, Compilers.ident.Nat_succ => Some tt
           | Nat_pred, Compilers.ident.Nat_pred => Some tt
           | Nat_max, Compilers.ident.Nat_max => Some tt
           | Nat_mul, Compilers.ident.Nat_mul => Some tt
           | Nat_add, Compilers.ident.Nat_add => Some tt
           | Nat_sub, Compilers.ident.Nat_sub => Some tt
           | nil, Compilers.ident.nil t => Some t
           | cons, Compilers.ident.cons t => Some t
           | pair, Compilers.ident.pair A B => Some (A, B)
           | fst, Compilers.ident.fst A B => Some (A, B)
           | snd, Compilers.ident.snd A B => Some (A, B)
           | prod_rect, Compilers.ident.prod_rect A B T => Some (A, B, T)
           | bool_rect, Compilers.ident.bool_rect T => Some T
           | nat_rect, Compilers.ident.nat_rect P => Some P
           | nat_rect_arrow, Compilers.ident.nat_rect_arrow P Q => Some (P, Q)
           | list_rect, Compilers.ident.list_rect A P => Some (A, P)
           | list_case, Compilers.ident.list_case A P => Some (A, P)
           | List_length, Compilers.ident.List_length T => Some T
           | List_seq, Compilers.ident.List_seq => Some tt
           | List_firstn, Compilers.ident.List_firstn A => Some A
           | List_skipn, Compilers.ident.List_skipn A => Some A
           | List_repeat, Compilers.ident.List_repeat A => Some A
           | List_combine, Compilers.ident.List_combine A B => Some (A, B)
           | List_map, Compilers.ident.List_map A B => Some (A, B)
           | List_app, Compilers.ident.List_app A => Some A
           | List_rev, Compilers.ident.List_rev A => Some A
           | List_flat_map, Compilers.ident.List_flat_map A B => Some (A, B)
           | List_partition, Compilers.ident.List_partition A => Some A
           | List_fold_right, Compilers.ident.List_fold_right A B => Some (A, B)
           | List_update_nth, Compilers.ident.List_update_nth T => Some T
           | List_nth_default, Compilers.ident.List_nth_default T => Some T
           | Z_add, Compilers.ident.Z_add => Some tt
           | Z_mul, Compilers.ident.Z_mul => Some tt
           | Z_pow, Compilers.ident.Z_pow => Some tt
           | Z_sub, Compilers.ident.Z_sub => Some tt
           | Z_opp, Compilers.ident.Z_opp => Some tt
           | Z_div, Compilers.ident.Z_div => Some tt
           | Z_modulo, Compilers.ident.Z_modulo => Some tt
           | Z_log2, Compilers.ident.Z_log2 => Some tt
           | Z_log2_up, Compilers.ident.Z_log2_up => Some tt
           | Z_eqb, Compilers.ident.Z_eqb => Some tt
           | Z_leb, Compilers.ident.Z_leb => Some tt
           | Z_geb, Compilers.ident.Z_geb => Some tt
           | Z_of_nat, Compilers.ident.Z_of_nat => Some tt
           | Z_to_nat, Compilers.ident.Z_to_nat => Some tt
           | Z_shiftr, Compilers.ident.Z_shiftr => Some tt
           | Z_shiftl, Compilers.ident.Z_shiftl => Some tt
           | Z_land, Compilers.ident.Z_land => Some tt
           | Z_lor, Compilers.ident.Z_lor => Some tt
           | Z_bneg, Compilers.ident.Z_bneg => Some tt
           | Z_lnot_modulo, Compilers.ident.Z_lnot_modulo => Some tt
           | Z_mul_split, Compilers.ident.Z_mul_split => Some tt
           | Z_add_get_carry, Compilers.ident.Z_add_get_carry => Some tt
           | Z_add_with_carry, Compilers.ident.Z_add_with_carry => Some tt
           | Z_add_with_get_carry, Compilers.ident.Z_add_with_get_carry => Some tt
           | Z_sub_get_borrow, Compilers.ident.Z_sub_get_borrow => Some tt
           | Z_sub_with_get_borrow, Compilers.ident.Z_sub_with_get_borrow => Some tt
           | Z_zselect, Compilers.ident.Z_zselect => Some tt
           | Z_add_modulo, Compilers.ident.Z_add_modulo => Some tt
           | Z_rshi, Compilers.ident.Z_rshi => Some tt
           | Z_cc_m, Compilers.ident.Z_cc_m => Some tt
           | Z_cast, Compilers.ident.Z_cast range => Some range
           | Z_cast2, Compilers.ident.Z_cast2 range => Some range
           | fancy_add, Compilers.ident.fancy_add log2wordmax imm => Some (log2wordmax, imm)
           | fancy_addc, Compilers.ident.fancy_addc log2wordmax imm => Some (log2wordmax, imm)
           | fancy_sub, Compilers.ident.fancy_sub log2wordmax imm => Some (log2wordmax, imm)
           | fancy_subb, Compilers.ident.fancy_subb log2wordmax imm => Some (log2wordmax, imm)
           | fancy_mulll, Compilers.ident.fancy_mulll log2wordmax => Some log2wordmax
           | fancy_mullh, Compilers.ident.fancy_mullh log2wordmax => Some log2wordmax
           | fancy_mulhl, Compilers.ident.fancy_mulhl log2wordmax => Some log2wordmax
           | fancy_mulhh, Compilers.ident.fancy_mulhh log2wordmax => Some log2wordmax
           | fancy_rshi, Compilers.ident.fancy_rshi log2wordmax x => Some (log2wordmax, x)
           | fancy_selc, Compilers.ident.fancy_selc => Some tt
           | fancy_selm, Compilers.ident.fancy_selm log2wordmax => Some log2wordmax
           | fancy_sell, Compilers.ident.fancy_sell => Some tt
           | fancy_addm, Compilers.ident.fancy_addm => Some tt
           | LiteralUnit, _
           | LiteralZ, _
           | LiteralBool, _
           | LiteralNat, _
           | Nat_succ, _
           | Nat_pred, _
           | Nat_max, _
           | Nat_mul, _
           | Nat_add, _
           | Nat_sub, _
           | nil, _
           | cons, _
           | pair, _
           | fst, _
           | snd, _
           | prod_rect, _
           | bool_rect, _
           | nat_rect, _
           | nat_rect_arrow, _
           | list_rect, _
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
           | Z_geb, _
           | Z_of_nat, _
           | Z_to_nat, _
           | Z_shiftr, _
           | Z_shiftl, _
           | Z_land, _
           | Z_lor, _
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
             => None
           end%cps.

      Local Notation eta2 x := (Datatypes.fst x, Datatypes.snd x) (only parsing).
      Local Notation eta3 x := (eta2 (Datatypes.fst x), Datatypes.snd x) (only parsing).

      Definition type_of (pidc : ident) : full_types pidc -> Compilers.type Compilers.base.type
        := match pidc return full_types pidc -> _ with
           | LiteralUnit => fun v => (type.base (Compilers.base.type.type_base Compilers.base.type.unit))
           | LiteralZ => fun v => (type.base (Compilers.base.type.type_base Compilers.base.type.Z))
           | LiteralBool => fun v => (type.base (Compilers.base.type.type_base Compilers.base.type.bool))
           | LiteralNat => fun v => (type.base (Compilers.base.type.type_base Compilers.base.type.nat))
           | Nat_succ => fun _ => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))
           | Nat_pred => fun _ => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))
           | Nat_max => fun _ => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))
           | Nat_mul => fun _ => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))
           | Nat_add => fun _ => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))
           | Nat_sub => fun _ => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat))
           | nil => fun t => (type.base (base.type.list t))
           | cons => fun t => (type.base t -> type.base (base.type.list t) -> type.base (base.type.list t))
           | pair => fun arg => let '(A, B) := eta2 arg in (type.base A -> type.base B -> type.base (A * B)%etype)
           | fst => fun arg => let '(A, B) := eta2 arg in (type.base (A * B)%etype -> type.base A)
           | snd => fun arg => let '(A, B) := eta2 arg in (type.base (A * B)%etype -> type.base B)
           | prod_rect => fun arg => let '(A, B, T) := eta3 arg in ((type.base A -> type.base B -> type.base T) -> type.base (A * B)%etype -> type.base T)
           | bool_rect => fun T => ((type.base ()%etype -> type.base T) -> (type.base ()%etype -> type.base T) -> type.base (base.type.type_base base.type.bool) -> type.base T)
           | nat_rect => fun P => ((type.base ()%etype -> type.base P) -> (type.base (base.type.type_base base.type.nat) -> type.base P -> type.base P) -> type.base (base.type.type_base base.type.nat) -> type.base P)
           | nat_rect_arrow => fun arg => let '(P, Q) := eta2 arg in ((type.base P -> type.base Q) -> (type.base (base.type.type_base base.type.nat) -> (type.base P -> type.base Q) -> type.base P -> type.base Q) -> type.base (base.type.type_base base.type.nat) -> type.base P -> type.base Q)
           | list_rect => fun arg => let '(A, P) := eta2 arg in ((type.base ()%etype -> type.base P) -> (type.base A -> type.base (base.type.list A) -> type.base P -> type.base P) -> type.base (base.type.list A) -> type.base P)
           | list_case => fun arg => let '(A, P) := eta2 arg in ((type.base ()%etype -> type.base P) -> (type.base A -> type.base (base.type.list A) -> type.base P) -> type.base (base.type.list A) -> type.base P)
           | List_length => fun T => (type.base (base.type.list T) -> type.base (base.type.type_base base.type.nat))
           | List_seq => fun _ => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.list (base.type.type_base base.type.nat)))
           | List_firstn => fun A => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.list A) -> type.base (base.type.list A))
           | List_skipn => fun A => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.list A) -> type.base (base.type.list A))
           | List_repeat => fun A => (type.base A -> type.base (base.type.type_base base.type.nat) -> type.base (base.type.list A))
           | List_combine => fun arg => let '(A, B) := eta2 arg in (type.base (base.type.list A) -> type.base (base.type.list B) -> type.base (base.type.list (A * B)))
           | List_map => fun arg => let '(A, B) := eta2 arg in ((type.base A -> type.base B) -> type.base (base.type.list A) -> type.base (base.type.list B))
           | List_app => fun A => (type.base (base.type.list A) -> type.base (base.type.list A) -> type.base (base.type.list A))
           | List_rev => fun A => (type.base (base.type.list A) -> type.base (base.type.list A))
           | List_flat_map => fun arg => let '(A, B) := eta2 arg in ((type.base A -> type.base (base.type.list B)) -> type.base (base.type.list A) -> type.base (base.type.list B))
           | List_partition => fun A => ((type.base A -> type.base (base.type.type_base base.type.bool)) -> type.base (base.type.list A) -> type.base (base.type.list A * base.type.list A)%etype)
           | List_fold_right => fun arg => let '(A, B) := eta2 arg in ((type.base B -> type.base A -> type.base A) -> type.base A -> type.base (base.type.list B) -> type.base A)
           | List_update_nth => fun T => (type.base (base.type.type_base base.type.nat) -> (type.base T -> type.base T) -> type.base (base.type.list T) -> type.base (base.type.list T))
           | List_nth_default => fun T => (type.base T -> type.base (base.type.list T) -> type.base (base.type.type_base base.type.nat) -> type.base T)
           | Z_add => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_mul => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_pow => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_sub => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_opp => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_div => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_modulo => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_log2 => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_log2_up => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_eqb => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.bool))
           | Z_leb => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.bool))
           | Z_geb => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.bool))
           | Z_of_nat => fun _ => (type.base (base.type.type_base base.type.nat) -> type.base (base.type.type_base base.type.Z))
           | Z_to_nat => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.nat))
           | Z_shiftr => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_shiftl => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_land => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_lor => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_bneg => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_lnot_modulo => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_mul_split => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | Z_add_get_carry => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | Z_add_with_carry => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_add_with_get_carry => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | Z_sub_get_borrow => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | Z_sub_with_get_borrow => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | Z_zselect => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_add_modulo => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_rshi => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_cc_m => fun _ => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_cast => fun range => (type.base (base.type.type_base base.type.Z) -> type.base (base.type.type_base base.type.Z))
           | Z_cast2 => fun range => (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | fancy_add => fun arg => let '(log2wordmax, imm) := eta2 arg in (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | fancy_addc => fun arg => let '(log2wordmax, imm) := eta2 arg in (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | fancy_sub => fun arg => let '(log2wordmax, imm) := eta2 arg in (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | fancy_subb => fun arg => let '(log2wordmax, imm) := eta2 arg in (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)
           | fancy_mulll => fun log2wordmax => (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z))
           | fancy_mullh => fun log2wordmax => (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z))
           | fancy_mulhl => fun log2wordmax => (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z))
           | fancy_mulhh => fun log2wordmax => (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z))
           | fancy_rshi => fun arg => let '(log2wordmax, x) := eta2 arg in (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z))
           | fancy_selc => fun _ => (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z))
           | fancy_selm => fun log2wordmax => (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z))
           | fancy_sell => fun _ => (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z))
           | fancy_addm => fun _ => (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype -> type.base (base.type.type_base base.type.Z))
           end%etype.

      Definition to_typed (pidc : ident) : forall args : full_types pidc, Compilers.ident.ident (type_of pidc args)
        := match pidc return forall args : full_types pidc, Compilers.ident.ident (type_of pidc args) with
           | LiteralUnit => fun v => @Compilers.ident.LiteralUnit v
           | LiteralZ => fun v => @Compilers.ident.LiteralZ v
           | LiteralBool => fun v => @Compilers.ident.LiteralBool v
           | LiteralNat => fun v => @Compilers.ident.LiteralNat v
           | Nat_succ => fun _ => @Compilers.ident.Nat_succ
           | Nat_pred => fun _ => @Compilers.ident.Nat_pred
           | Nat_max => fun _ => @Compilers.ident.Nat_max
           | Nat_mul => fun _ => @Compilers.ident.Nat_mul
           | Nat_add => fun _ => @Compilers.ident.Nat_add
           | Nat_sub => fun _ => @Compilers.ident.Nat_sub
           | nil => fun t => @Compilers.ident.nil t
           | cons => fun t => @Compilers.ident.cons t
           | pair => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of pair args') with (A, B) => @Compilers.ident.pair A B end
           | fst => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of fst args') with (A, B) => @Compilers.ident.fst A B end
           | snd => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of snd args') with (A, B) => @Compilers.ident.snd A B end
           | prod_rect => fun arg => match eta3 arg as args' return Compilers.ident.ident (type_of prod_rect args') with (A, B, T) => @Compilers.ident.prod_rect A B T end
           | bool_rect => fun T => @Compilers.ident.bool_rect T
           | nat_rect => fun P => @Compilers.ident.nat_rect P
           | nat_rect_arrow => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of nat_rect_arrow args') with (P, Q) => @Compilers.ident.nat_rect_arrow P Q end
           | list_rect => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of list_rect args') with (A, P) => @Compilers.ident.list_rect A P end
           | list_case => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of list_case args') with (A, P) => @Compilers.ident.list_case A P end
           | List_length => fun T => @Compilers.ident.List_length T
           | List_seq => fun _ => @Compilers.ident.List_seq
           | List_firstn => fun A => @Compilers.ident.List_firstn A
           | List_skipn => fun A => @Compilers.ident.List_skipn A
           | List_repeat => fun A => @Compilers.ident.List_repeat A
           | List_combine => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of List_combine args') with (A, B) => @Compilers.ident.List_combine A B end
           | List_map => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of List_map args') with (A, B) => @Compilers.ident.List_map A B end
           | List_app => fun A => @Compilers.ident.List_app A
           | List_rev => fun A => @Compilers.ident.List_rev A
           | List_flat_map => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of List_flat_map args') with (A, B) => @Compilers.ident.List_flat_map A B end
           | List_partition => fun A => @Compilers.ident.List_partition A
           | List_fold_right => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of List_fold_right args') with (A, B) => @Compilers.ident.List_fold_right A B end
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
           | Z_geb => fun _ => @Compilers.ident.Z_geb
           | Z_of_nat => fun _ => @Compilers.ident.Z_of_nat
           | Z_to_nat => fun _ => @Compilers.ident.Z_to_nat
           | Z_shiftr => fun _ => @Compilers.ident.Z_shiftr
           | Z_shiftl => fun _ => @Compilers.ident.Z_shiftl
           | Z_land => fun _ => @Compilers.ident.Z_land
           | Z_lor => fun _ => @Compilers.ident.Z_lor
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
           | fancy_add => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of fancy_add args') with (log2wordmax, imm) => @Compilers.ident.fancy_add log2wordmax imm end
           | fancy_addc => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of fancy_addc args') with (log2wordmax, imm) => @Compilers.ident.fancy_addc log2wordmax imm end
           | fancy_sub => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of fancy_sub args') with (log2wordmax, imm) => @Compilers.ident.fancy_sub log2wordmax imm end
           | fancy_subb => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of fancy_subb args') with (log2wordmax, imm) => @Compilers.ident.fancy_subb log2wordmax imm end
           | fancy_mulll => fun log2wordmax => @Compilers.ident.fancy_mulll log2wordmax
           | fancy_mullh => fun log2wordmax => @Compilers.ident.fancy_mullh log2wordmax
           | fancy_mulhl => fun log2wordmax => @Compilers.ident.fancy_mulhl log2wordmax
           | fancy_mulhh => fun log2wordmax => @Compilers.ident.fancy_mulhh log2wordmax
           | fancy_rshi => fun arg => match eta2 arg as args' return Compilers.ident.ident (type_of fancy_rshi args') with (log2wordmax, x) => @Compilers.ident.fancy_rshi log2wordmax x end
           | fancy_selc => fun _ => @Compilers.ident.fancy_selc
           | fancy_selm => fun log2wordmax => @Compilers.ident.fancy_selm log2wordmax
           | fancy_sell => fun _ => @Compilers.ident.fancy_sell
           | fancy_addm => fun _ => @Compilers.ident.fancy_addm
           end.

      Definition retype_ident {t} (idc : Compilers.ident.ident t) : match arg_types (of_typed_ident idc) return Type with Some t => t | None => unit end -> Compilers.ident.ident t
        := match idc in Compilers.ident.ident t return match arg_types (of_typed_ident idc) return Type with Some t => t | None => unit end -> Compilers.ident.ident t with
           | Compilers.ident.LiteralUnit v => (fun v => @Compilers.ident.LiteralUnit v) : match arg_types (of_typed_ident (@Compilers.ident.LiteralUnit v)) return Type with Some t => t | None => unit end -> _ (* COQBUG(https://github.com/coq/coq/issues/7726) *)
           | Compilers.ident.LiteralZ v => (fun v => @Compilers.ident.LiteralZ v) : match arg_types (of_typed_ident (@Compilers.ident.LiteralZ v)) return Type with Some t => t | None => unit end -> _ (* COQBUG(https://github.com/coq/coq/issues/7726) *)
           | Compilers.ident.LiteralBool v => (fun v => @Compilers.ident.LiteralBool v) : match arg_types (of_typed_ident (@Compilers.ident.LiteralBool v)) return Type with Some t => t | None => unit end -> _ (* COQBUG(https://github.com/coq/coq/issues/7726) *)
           | Compilers.ident.LiteralNat v => (fun v => @Compilers.ident.LiteralNat v) : match arg_types (of_typed_ident (@Compilers.ident.LiteralNat v)) return Type with Some t => t | None => unit end -> _ (* COQBUG(https://github.com/coq/coq/issues/7726) *)
           | Compilers.ident.Nat_succ => fun _ => @Compilers.ident.Nat_succ
           | Compilers.ident.Nat_pred => fun _ => @Compilers.ident.Nat_pred
           | Compilers.ident.Nat_max => fun _ => @Compilers.ident.Nat_max
           | Compilers.ident.Nat_mul => fun _ => @Compilers.ident.Nat_mul
           | Compilers.ident.Nat_add => fun _ => @Compilers.ident.Nat_add
           | Compilers.ident.Nat_sub => fun _ => @Compilers.ident.Nat_sub
           | Compilers.ident.nil t => fun _ => @Compilers.ident.nil t
           | Compilers.ident.cons t => fun _ => @Compilers.ident.cons t
           | Compilers.ident.pair A B => fun _ => @Compilers.ident.pair A B
           | Compilers.ident.fst A B => fun _ => @Compilers.ident.fst A B
           | Compilers.ident.snd A B => fun _ => @Compilers.ident.snd A B
           | Compilers.ident.prod_rect A B T => fun _ => @Compilers.ident.prod_rect A B T
           | Compilers.ident.bool_rect T => fun _ => @Compilers.ident.bool_rect T
           | Compilers.ident.nat_rect P => fun _ => @Compilers.ident.nat_rect P
           | Compilers.ident.nat_rect_arrow P Q => fun _ => @Compilers.ident.nat_rect_arrow P Q
           | Compilers.ident.list_rect A P => fun _ => @Compilers.ident.list_rect A P
           | Compilers.ident.list_case A P => fun _ => @Compilers.ident.list_case A P
           | Compilers.ident.List_length T => fun _ => @Compilers.ident.List_length T
           | Compilers.ident.List_seq => fun _ => @Compilers.ident.List_seq
           | Compilers.ident.List_firstn A => fun _ => @Compilers.ident.List_firstn A
           | Compilers.ident.List_skipn A => fun _ => @Compilers.ident.List_skipn A
           | Compilers.ident.List_repeat A => fun _ => @Compilers.ident.List_repeat A
           | Compilers.ident.List_combine A B => fun _ => @Compilers.ident.List_combine A B
           | Compilers.ident.List_map A B => fun _ => @Compilers.ident.List_map A B
           | Compilers.ident.List_app A => fun _ => @Compilers.ident.List_app A
           | Compilers.ident.List_rev A => fun _ => @Compilers.ident.List_rev A
           | Compilers.ident.List_flat_map A B => fun _ => @Compilers.ident.List_flat_map A B
           | Compilers.ident.List_partition A => fun _ => @Compilers.ident.List_partition A
           | Compilers.ident.List_fold_right A B => fun _ => @Compilers.ident.List_fold_right A B
           | Compilers.ident.List_update_nth T => fun _ => @Compilers.ident.List_update_nth T
           | Compilers.ident.List_nth_default T => fun _ => @Compilers.ident.List_nth_default T
           | Compilers.ident.Z_add => fun _ => @Compilers.ident.Z_add
           | Compilers.ident.Z_mul => fun _ => @Compilers.ident.Z_mul
           | Compilers.ident.Z_pow => fun _ => @Compilers.ident.Z_pow
           | Compilers.ident.Z_sub => fun _ => @Compilers.ident.Z_sub
           | Compilers.ident.Z_opp => fun _ => @Compilers.ident.Z_opp
           | Compilers.ident.Z_div => fun _ => @Compilers.ident.Z_div
           | Compilers.ident.Z_modulo => fun _ => @Compilers.ident.Z_modulo
           | Compilers.ident.Z_log2 => fun _ => @Compilers.ident.Z_log2
           | Compilers.ident.Z_log2_up => fun _ => @Compilers.ident.Z_log2_up
           | Compilers.ident.Z_eqb => fun _ => @Compilers.ident.Z_eqb
           | Compilers.ident.Z_leb => fun _ => @Compilers.ident.Z_leb
           | Compilers.ident.Z_geb => fun _ => @Compilers.ident.Z_geb
           | Compilers.ident.Z_of_nat => fun _ => @Compilers.ident.Z_of_nat
           | Compilers.ident.Z_to_nat => fun _ => @Compilers.ident.Z_to_nat
           | Compilers.ident.Z_shiftr => fun _ => @Compilers.ident.Z_shiftr
           | Compilers.ident.Z_shiftl => fun _ => @Compilers.ident.Z_shiftl
           | Compilers.ident.Z_land => fun _ => @Compilers.ident.Z_land
           | Compilers.ident.Z_lor => fun _ => @Compilers.ident.Z_lor
           | Compilers.ident.Z_bneg => fun _ => @Compilers.ident.Z_bneg
           | Compilers.ident.Z_lnot_modulo => fun _ => @Compilers.ident.Z_lnot_modulo
           | Compilers.ident.Z_mul_split => fun _ => @Compilers.ident.Z_mul_split
           | Compilers.ident.Z_add_get_carry => fun _ => @Compilers.ident.Z_add_get_carry
           | Compilers.ident.Z_add_with_carry => fun _ => @Compilers.ident.Z_add_with_carry
           | Compilers.ident.Z_add_with_get_carry => fun _ => @Compilers.ident.Z_add_with_get_carry
           | Compilers.ident.Z_sub_get_borrow => fun _ => @Compilers.ident.Z_sub_get_borrow
           | Compilers.ident.Z_sub_with_get_borrow => fun _ => @Compilers.ident.Z_sub_with_get_borrow
           | Compilers.ident.Z_zselect => fun _ => @Compilers.ident.Z_zselect
           | Compilers.ident.Z_add_modulo => fun _ => @Compilers.ident.Z_add_modulo
           | Compilers.ident.Z_rshi => fun _ => @Compilers.ident.Z_rshi
           | Compilers.ident.Z_cc_m => fun _ => @Compilers.ident.Z_cc_m
           | Compilers.ident.Z_cast range => fun range => @Compilers.ident.Z_cast range
           | Compilers.ident.Z_cast2 range => fun range => @Compilers.ident.Z_cast2 range
           | Compilers.ident.fancy_add log2wordmax imm => fun arg => let '(log2wordmax, imm) := eta2 arg in @Compilers.ident.fancy_add log2wordmax imm
           | Compilers.ident.fancy_addc log2wordmax imm => fun arg => let '(log2wordmax, imm) := eta2 arg in @Compilers.ident.fancy_addc log2wordmax imm
           | Compilers.ident.fancy_sub log2wordmax imm => fun arg => let '(log2wordmax, imm) := eta2 arg in @Compilers.ident.fancy_sub log2wordmax imm
           | Compilers.ident.fancy_subb log2wordmax imm => fun arg => let '(log2wordmax, imm) := eta2 arg in @Compilers.ident.fancy_subb log2wordmax imm
           | Compilers.ident.fancy_mulll log2wordmax => fun log2wordmax => @Compilers.ident.fancy_mulll log2wordmax
           | Compilers.ident.fancy_mullh log2wordmax => fun log2wordmax => @Compilers.ident.fancy_mullh log2wordmax
           | Compilers.ident.fancy_mulhl log2wordmax => fun log2wordmax => @Compilers.ident.fancy_mulhl log2wordmax
           | Compilers.ident.fancy_mulhh log2wordmax => fun log2wordmax => @Compilers.ident.fancy_mulhh log2wordmax
           | Compilers.ident.fancy_rshi log2wordmax x => fun arg => let '(log2wordmax, x) := eta2 arg in @Compilers.ident.fancy_rshi log2wordmax x
           | Compilers.ident.fancy_selc => fun _ => @Compilers.ident.fancy_selc
           | Compilers.ident.fancy_selm log2wordmax => fun log2wordmax => @Compilers.ident.fancy_selm log2wordmax
           | Compilers.ident.fancy_sell => fun _ => @Compilers.ident.fancy_sell
           | Compilers.ident.fancy_addm => fun _ => @Compilers.ident.fancy_addm
           end.


      (*===*)
    End ident.
  End pattern.
End Compilers.
