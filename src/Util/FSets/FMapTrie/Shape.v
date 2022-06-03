Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Classes.RelationPairs.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.ListUtil.SetoidListFlatMap.
Require Import Crypto.Util.ListUtil.StdlibCompat.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.

Local Set Implicit Arguments.
Local Set Primitive Projections.
Local Unset Strict Implicit.
(* TODO: move to global settings *)
Local Set Keyed Unification.
Import ListNotations.
Local Open Scope option_scope.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.

Module Type TypFunctor.
  Parameter t : Type -> Type.
End TypFunctor.

Module Import EverythingGen.
  Polymorphic Definition id_fix {T} (x : T) := x.
  Polymorphic Definition id_fix_2 {T} (x : T) := x.
  Polymorphic Definition id_case {T} (x : T) := x.
  Section __.
    Context (t : Type -> Type)
            (map_key : Type)
            (map_t : Type -> Type)
            (map_empty : forall elt, map_t elt)
            (map_is_empty : forall elt, map_t elt -> bool)
            (map_fold : forall elt A : Type, (map_key -> elt -> A -> A) -> map_t elt -> A -> A)
            (map_mapi : forall elt elt' : Type, (map_key -> elt -> elt') -> map_t elt -> map_t elt')
            (map_map2 : forall elt elt' elt'' : Type, (option elt -> option elt' -> option elt'') -> map_t elt -> map_t elt' -> map_t elt'')
            (map_find : forall elt : Type, map_key -> map_t elt -> option elt).

    Local Notation t' elt := (option (t elt)).
    Local Notation node_NonEmpty x y := match x, y with None, None => False | _, _ => True end.
    Local Notation node_NonEmpty' x y := match y, x with None, None => False | _, _ => True end.
    Local Notation map_t_t elt := (map_t (t elt)).

    Section step.
      Context (Node : forall elt (d : option elt) (m : option (map_t_t elt)), node_NonEmpty d m -> t elt)
              (t_case_nd : forall (elt : Type) (P : Type),
                  (forall (v : option elt) (m : option (map_t_t elt)), node_NonEmpty v m -> P)
                  -> t elt -> P)
              (map_xmap2_l : forall elt elt' elt'', (option elt -> option elt' -> option elt'') -> map_t elt -> map_t elt'')
              (map_xmap2_r : forall elt elt' elt'', (option elt -> option elt' -> option elt'') -> map_t elt' -> map_t elt'').

      Local Arguments Node {_} _ _ _.

      Definition empty' : forall elt, t' elt
        := fun _ => None.

      Definition mapi_step elt elt'
                 (mapi : (list map_key -> elt -> elt') -> t elt -> t elt')
                 (f : list map_key -> elt -> elt')
        : t elt -> t elt'
        := let d_of d := option_map (f nil) d in
           let m_of m
             := option_map
                  (@map_mapi _ _ (fun k => mapi (fun ks => f (k :: ks))))
                  m in
           t_case_nd
             (fun d m pf
              => Node
                   (d_of d) (m_of m)
                   (match d, m return node_NonEmpty d m -> node_NonEmpty (d_of d) (m_of m) with
                    | None, None => fun pf => pf
                    | _, _ => fun 'I => I
                    end pf)).

      Local Notation dec_empty m := (if map_is_empty m then None else Some m).

      Definition map2_step
                 elt elt' elt'' (f : option elt -> option elt' -> option elt'')
                 (map2_l : t elt -> t' elt'')
                 (map2_r : t elt' -> t' elt'')
                 (map2 : t elt -> t elt' -> t' elt'')
                 (m1 : t elt) (m2 : t elt')
        : t' elt''
        := let F := (fun m1 m2
                     => match m1, m2 with
                        | Some m1, Some m2 => map2 m1 m2
                        | Some m1, None => map2_l m1
                        | None, Some m2 => map2_r m2
                        | None, None => None
                        end) in
           let f' x y := match x, y with
                         | None, None => None
                         | x, y => f x y
                         end in
           t_case_nd
             (fun d1 m1 pf1
              => t_case_nd
                   (fun d2 m2 pf2
                    => let m := match m1, m2 with
                                | Some m1, Some m2
                                  => dec_empty (@map_map2 _ _ _ F m1 m2)
                                | Some m1, None
                                  => dec_empty (map_xmap2_l F m1)
                                | None, Some m2
                                  => dec_empty (map_xmap2_r F m2)
                                | None, None => None
                                end in
                       match f' d1 d2, m with
                       | None, None => None
                       | d, m => Some (Node d m I)
                       end)
                   m2)
             m1.
      Definition map2_l_step
                 elt elt' elt'' (f : option elt -> option elt' -> option elt'')
                 (map2_l : t elt -> t' elt'')
                 (m1 : t elt)
        : t' elt''
        := let f' x y := match x, y with
                         | None, None => None
                         | x, y => f x y
                         end in
           t_case_nd
             (fun d1 m1 pf1
              => let m := match m1 with
                          | Some m1
                            => dec_empty
                                 (@map_xmap2_l
                                    (t elt) (t elt') (t elt'')
                                    (fun m1 _ => match m1 with
                                                 | None => None
                                                 | Some m1 => map2_l m1
                                                 end)
                                    m1)
                          | None => None
                          end in
                 match f' d1 None, m with
                 | None, None => None
                 | d, m => Some (Node d m I)
                 end)
             m1.
      Definition map2_r_step
                 elt elt' elt'' (f : option elt -> option elt' -> option elt'')
                 (map2_r : t elt' -> t' elt'')
                 (m2 : t elt')
        : t' elt''
        := let f' x y := match x, y with
                         | None, None => None
                         | x, y => f x y
                         end in
           t_case_nd
             (fun d2 m2 pf2
              => let m := match m2 with
                          | Some m2
                            => dec_empty
                                 (@map_xmap2_r
                                    (t elt) (t elt') (t elt'')
                                    (fun _ m2 => match m2 with
                                                 | None => None
                                                 | Some m2 => map2_r m2
                                                 end)
                                    m2)
                          | None => None
                          end in
                 match f' None d2, m with
                 | None, None => None
                 | d, m => Some (Node d m I)
                 end)
             m2.
      Definition fold_step elt A
                 (fold : (list map_key -> elt -> A -> A) -> t elt -> A -> A)
                 (f : list map_key -> elt -> A -> A)
                 (m : t elt)
                 (a : A)
        : A
        := t_case_nd
             (fun d m pf
              => let a := match d with
                          | None => a
                          | Some d => f [] d a
                          end in
                 match m with
                 | Some m
                   => @map_fold
                        _ _
                        (fun k => fold (fun ks => f (k :: ks)))
                        m
                        a
                 | None => a
                 end)
             m.
      Definition recursively_non_empty_step elt
                 (recursively_non_empty : t elt -> bool)
                 (m : t elt)
        : bool
        := t_case_nd
             (fun d m pf
              => match m with
                 | Some m
                   => @map_fold
                        _ _
                        (fun _ m P => andb P (recursively_non_empty m))
                        m
                        (negb (map_is_empty m))
                 | None => true
                 end)
             m.
    End step.

    Class EverythingGen
      := { Node : forall elt (d : option elt) (m : option (map_t_t elt)), node_NonEmpty d m -> t elt
         ; t_case : forall elt (P : t elt -> Type),
             (forall d m pf, P (@Node elt d m pf))
             -> forall m, P m
         ; t_case_beta : forall elt P rec d m pf, @t_case elt P rec (@Node elt d m pf) = rec d m pf
         ; t_case_nd
           := fun elt P => @t_case elt (fun _ => P)
         ; t_ind : forall elt (P : t elt -> Prop),
             (forall d m pf, (forall k v, match m with Some m => @map_find _ k m = Some v -> P v | None => True end) -> P (@Node elt d m pf))
             -> forall m, P m
         ; empty : forall elt, t' elt
           := fun _ => None
         ; mapi : forall elt elt', id_fix_2 ((list map_key -> elt -> elt') -> t elt -> t elt')
         ; mapi_beta : forall elt elt' f m, @mapi elt elt' f m = mapi_step Node t_case_nd (@mapi elt elt') f m

         ; map_xmap2_l : forall elt elt' elt'', (option elt -> option elt' -> option elt'') -> map_t elt -> map_t elt''
         ; map_xmap2_r : forall elt elt' elt'', (option elt -> option elt' -> option elt'') -> map_t elt' -> map_t elt''
         ; map_xmap2_lr : forall A B (f g : option A -> option A -> option B) m,
             (forall i j, f i j = g j i) -> map_xmap2_l f m = map_xmap2_r g m
         ; map_xgmap2_l : forall A B C (f : option A -> option B -> option C) i m,
             f None None = None -> @map_find _ i (map_xmap2_l f m) = f (@map_find _ i m) None
         ; map_xgmap2_r : forall A B C (f : option A -> option B -> option C) i m,
             f None None = None -> @map_find _ i (map_xmap2_r f m) = f None (@map_find _ i m)

         ; map2_l : forall elt elt' elt'', (option elt -> option elt' -> option elt'') -> id_fix (t elt -> t' elt'')
         ; map2_r : forall elt elt' elt'', (option elt -> option elt' -> option elt'') -> id_fix (t elt' -> t' elt'')
         ; map2 : forall elt elt' elt'', (option elt -> option elt' -> option elt'') -> id_fix (t elt -> t elt' -> t' elt'')
         ; map2_l_beta : forall elt elt' elt'' f m,
             @map2_l elt elt' elt'' f m = map2_l_step Node t_case_nd map_xmap2_l f (map2_l f) m
         ; map2_r_beta : forall elt elt' elt'' f m,
             @map2_r elt elt' elt'' f m = map2_r_step Node t_case_nd map_xmap2_r f (map2_r f) m
         ; map2_beta : forall elt elt' elt'' f m1 m2,
             @map2 elt elt' elt'' f m1 m2 = map2_step Node t_case_nd map_xmap2_l map_xmap2_r f (map2_l f) (map2_r f) (map2 f) m1 m2
         ; fold : forall elt (A : Type), id_fix_2 ((list map_key -> elt -> A -> A) -> t elt -> A -> A)
         ; fold_beta : forall elt A f m a,
             @fold elt A f m a = fold_step t_case_nd (@fold elt A) f m a
         ; recursively_non_empty : forall elt, id_fix (t elt -> bool)
         ; recursively_non_empty_beta : forall elt m,
             @recursively_non_empty elt m = recursively_non_empty_step t_case_nd (@recursively_non_empty elt) m
      }.
    Definition Node' {E : EverythingGen} elt (d : option elt) (m : option (map_t_t elt)) : node_NonEmpty' d m -> t elt
      := match d, m return node_NonEmpty' d m -> _ with
         | None, None => fun pf => match pf with end
         | d, (Some _ | None) as m => @Node E elt d m
         end.
    Definition oNode_dec_empty {E : EverythingGen} elt (d : option elt) (m : map_t (t elt)) : option (t elt)
      := match d, (if map_is_empty m then None else Some m) with
         | None, None => None
         | d, (None | Some _) as m
           => Some (Node (d:=d) (m:=m) I)
         end.
  End __.
End EverythingGen.
Global Arguments Node {t _ _ _ _ _ _ _ _ _} d m _.
Global Arguments Node' {t _ _ _ _ _ _ _ _ _} d m _.

Create HintDb trie_db discriminated.

Hint Rewrite
     t_case_beta
     mapi_beta
     map2_beta
     map2_l_beta
     map2_r_beta
     fold_beta
     recursively_non_empty_beta
  : trie_db.

Hint Unfold
     id_fix
     id_fix_2
     id_case
     Node'
     oNode_dec_empty
     empty'
     mapi_step
     map2_step
     map2_l_step
     map2_r_step
     fold_step
     recursively_non_empty_step
     t_case_nd
     empty
  : trie_db.

Module Type TrieShape (label : DecidableType) (map : FMapInterface.WSfun label) (Import T : TypFunctor).
  Notation Everything := (@EverythingGen t map.key map.t map.is_empty map.fold map.mapi map.map2 map.find).
End TrieShape.

Module Type Trie (label : DecidableType) (map : FMapInterface.WSfun label).
  Include TypFunctor.
  Include TrieShape label map.
  Parameter Inline everything : Everything.
  Existing Instance everything.
End Trie.

Module TrieTactics.
  Ltac t_destr_conj_step :=
    first [ progress subst
          | progress destruct_head'_False
          | progress destruct_head'_and
          | progress destruct_head'_ex
          | progress destruct_head'_True
          | progress destruct_head'_unit
          | progress destruct_head' sig
          | progress inversion_option
          | progress inversion_sigma
          | progress inversion_list
          | progress inversion_pair
          | progress cbn [fst snd proj1_sig proj2_sig] in *
          | match goal with
            | [ H : eqlistA _ nil _ |- _ ] => inversion H; clear H
            | [ H : eqlistA _ _ nil |- _ ] => inversion H; clear H
            | [ H : eqlistA _ (_ :: _) _ |- _ ] => inversion H; clear H
            | [ H : eqlistA _ _ (_ :: _) |- _ ] => inversion H; clear H
            | [ H : InA _ _ (_ :: _) |- _ ] => inversion H; clear H
            | [ H : InA _ _ nil |- _ ] => inversion H; clear H
            | [ H : List.In _ (List.map _ _) |- _ ] => rewrite in_map_iff in H
            | [ H : List.In _ (List.flat_map _ _) |- _ ] => rewrite in_flat_map in H
            | [ H : ?x = ?x |- _ ] => clear H
            | [ H : ?T, H' : ?T |- _ ] => clear H
            | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
            | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
            | [ H : Some _ = ?x |- _ ] => symmetry in H
            | [ H : None = ?x |- _ ] => symmetry in H
            end
          | discriminate ].
  Ltac t_destr_step :=
    first [ t_destr_conj_step
          | progress destruct_head'_or
          | progress destruct_head' option
          | break_innermost_match_hyps_step
          | break_innermost_match_step ].
  Ltac t_specialize_safe_step :=
    first [ progress specialize_by_assumption
          | progress cbv [not] in *
          | progress specialize_by reflexivity
          | progress specialize_under_binders_by apply conj
          | progress specialize_under_binders_by eapply ex_intro
          | progress specialize_under_binders_by apply eqlistA_cons ].

  Ltac inversion_Node_step :=
    match goal with
    | [ H : Node _ _ _ = Node _ _ _ |- _ ]
      => let H' := fresh in
         pose proof (f_equal (t_case_nd (fun d m pf => (d, m))) H) as H';
         clear H;
         cbv [t_case_nd] in *;
         autorewrite with trie_db in H'
    end.
  Ltac inversion_Node := repeat inversion_Node_step.
End TrieTactics.
