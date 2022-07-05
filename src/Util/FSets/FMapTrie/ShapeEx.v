Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.PArith.PArith.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Structures.OrdersEx.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.FSets.FMapTrie.Shape.
Require Import Crypto.Util.FSets.FMapN.
Require Import Crypto.Util.FSets.FMapZ.
Import EqNotations.
Import EverythingGen.

Local Set Implicit Arguments.
Local Set Primitive Projections.
Local Unset Strict Implicit.
(* TODO: move to global settings *)
Local Set Keyed Unification.

Inductive option_dep A : bool -> Type :=
| Some_dep b : A -> option_dep b
| None_dep : option_dep false.
Arguments Some_dep {A b} _.
Arguments None_dep {A}.

Local Ltac t :=
  first [ instantiate (1:=ltac:(eassumption)); reflexivity
        | match goal with
          | [ |- ?LHS = (fun b : ?T => @?RHS b) ]
            => lazymatch RHS with
               | fun '(a, b) => _
                 => is_evar LHS; instantiate (1:=ltac:(first [ intros [a b] | intros [? ?] ]));
                    try t
               end
          end
        | try instantiate (1:=ltac:(intros)); progress cbv beta iota; t
        | instantiate (1:=ltac:(intros)); cbv beta;
          first [ reflexivity | apply f_equal | apply f_equal2 | apply f_equal3 | apply fg_equal
                | match goal with
                  | [ |- ?LHS = (fun b : ?T => @?RHS b) ]
                    => cut (forall a : T, LHS a = RHS a); [ shelve | intro ]
                  end
                | break_innermost_match_step ];
          instantiate (1:=ltac:(intros)); cbv beta iota;
          t
        | idtac ].

Local Ltac handle_id_fix :=
  intros;
  cbv beta;
  set_evars;
  (tryif (match goal with |- context[id_fix] => idtac | |- context[id_fix_2] => idtac end)
    then (intros;
          let m := fresh "m" in
          let x := fresh "x" in
          let IH := fresh "IH" in
          lazymatch goal with
          | [ |- id_fix   _ ] => cbv [id_fix  ]; fix IH 1; intros m; revert m
          | [ |- id_fix_2 _ ] => cbv [id_fix_2]; fix IH 2; intros x m; revert x m
          end;
          revert IH)
    else idtac);
  shelve_unifiable.

Local Ltac subst_partial_evars :=
  repeat match goal with
         | [ H := ?ev |- _ ]
           => has_evar ev; assert_fails is_evar ev; revert H; set_evars; intro
         end.
Local Ltac partial_unify e :=
  let do_rep evb e m IH IHm eIHm
    := (is_evar evb;
        let v1 := fresh in
        let v2 := fresh in
        set (v1 := IHm);
        pose eIHm as v2;
        destruct m;
        change v1 with v2; subst v1 v2 e) in
  lazymatch goal with
  | [ ev := ?evb, IH := _ : id_fix _ |- _ ]
    => let m := lazymatch goal with |- context G[IH ?m] => m end in
       do_rep evb e m IH (IH m) (e IH m)
  | [ ev := ?evb, IH := _ : id_fix_2 _ |- _ ]
    => let x := lazymatch goal with |- context[IH ?x ?m] => x end in
       let m := lazymatch goal with |- context[IH x ?m] => m end in
       do_rep evb e m IH (IH x m) (e IH x m)
  | _ => idtac
  end.

Module PositiveMapTypFunctor <: TypFunctor.
  Local Unset Primitive Projections.
  Local Set Nonrecursive Elimination Schemes.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Inductive t' (elt : Type) := Node' { data : option elt ; map : option_dep (PositiveMap.t (t' elt)) (Option.is_None data) }.
  Definition t := t'.
  Local Notation node_NonEmpty x y := match x, y with None, None => False | _, _ => True end.
  Definition Node elt (data : option elt) (map : option (PositiveMap.t (t elt))) (pf : node_NonEmpty data map) : t elt
    := @Node' _ data (match map, data return node_NonEmpty data map -> option_dep _ (Option.is_None data) with
                      | Some m, _ => fun _ => Some_dep m
                      | None, Some _ => fun _ => None_dep
                      | None, None => fun pf => match pf with end
                      end pf).
  Global Arguments Node [elt] _ _ _.
  Definition t_rect elt (P : t elt -> Type)
             (val : forall (v : option elt) (m : option (PositiveMap.t (t elt))) (pf : node_NonEmpty v m), P (Node v m pf))
             (m : t elt)
    : P m
    := Eval cbv beta in
      match m return P m with
      | {| data := d ; map := m |}
        => match m in option_dep _ b, d return forall pf : is_None d = b, P {| data := d ; map := rew <- [option_dep _] pf in m |} with
           | None_dep, None
             => fun pf => match pf with
                          | eq_refl => I
                          end
           | Some_dep _ m, Some d
             => fun pf => match pf with
                          | eq_refl => val (Some d) (Some m) I
                          end
           | None_dep as m, Some d
             => fun pf => match pf with
                          | eq_refl => ltac:(refine (fun x => x)) (val (Some d) None I)
                          end
           | Some_dep _ m, None
             => fun pf => match pf with
                          | eq_refl => val None (Some m) I
                          end
           end eq_refl
      end.
End PositiveMapTypFunctor.

Module PositiveMapTrieInd <: Trie PositiveOrderedTypeBits PositiveMap.
  Definition t := PositiveMapTypFunctor.t.
  Include TrieShape PositiveOrderedTypeBits PositiveMap.

  Definition PositiveMap_find_alt A
    := fix find (i : PositiveMap.key) (m : PositiveMap.t A) {struct m} : option A :=
      match m with
      | @PositiveMap.Leaf _ => None
      | PositiveMap.Node l o r =>
          match i with
          | BinNums.xI ii => find ii r
          | BinNums.xO ii => find ii l
          | BinNums.xH => o
          end
      end.
  Lemma eq_PositiveMap_find_alt A : forall i m, @PositiveMap.find A i m = @PositiveMap_find_alt A i m.
  Proof using Type.
    induction i, m; cbn in *; auto.
  Qed.

  Definition t_ind_full elt (P : t elt -> Prop)
             (H : forall d m pf,
                 (forall k v, match m with Some m => PositiveMap.find k m = Some v -> P v | None => True end)
                 -> P (PositiveMapTypFunctor.Node d m pf))
    : forall m, P m.
  Proof using Type.
    fix t_ind_full 1.
    induction m as [d m pf] using PositiveMapTypFunctor.t_rect.
    specialize (H d m pf).
    apply H; clear H.
    destruct m as [m|]; [ | intros; exact I ].
    induction m;
      [ clear t_ind_full
      | match goal with
        | [ H : option _ |- _ ]
          => let x := fresh "x" in
             destruct H as [x|];
             [ specialize (t_ind_full x)
             | clear t_ind_full ]
        end ].
    all: intros k v H.
    all: try solve [ exfalso; clear -H; abstract (destruct k; cbn in H; inversion_option) ].
    all: destruct k; cbn [PositiveMap.find] in *.
    all: lazymatch goal with
         | [ H : None = Some _ |- _ ] => exfalso; clear -H; abstract inversion_option
         | [ H : ?P ?x, H' : Some ?x = Some ?y |- ?P ?y ]
           => refine (rew [P] (f_equal (fun v => Option.value v x) H') in H)
         | _ => idtac
         end.
    all: eauto with nocore.
  Defined.

  Section everything.
    Let everything' : Everything.
    Proof.
      unshelve esplit.
      all: try exact PositiveMapTypFunctor.Node.
      all: try exact PositiveMapTypFunctor.t_rect.
      all: try exact t_ind_full.
      all: try exact PositiveMapAdditionalFacts.xmap2_lr.
      all: try exact PositiveMap.xgmap2_l.
      all: try exact PositiveMap.xgmap2_r.
      all: handle_id_fix.
      all: subst_partial_evars.
      all: try (destruct_head' option; destruct_head'_True; destruct_head'_False; reflexivity).
      all: partial_unify e.
      all: try reflexivity.
    Defined.
    Definition everything := Eval cbv [everything'] in everything'.
  End everything.
End PositiveMapTrieInd.

Module NMapTypFunctor <: TypFunctor.
  Local Unset Primitive Projections.
  Local Set Nonrecursive Elimination Schemes.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Inductive t' (elt : Type) := Node' { data : option elt ; map : option_dep (NMap.t (t' elt)) (Option.is_None data) }.
  Definition t := t'.
  Local Notation node_NonEmpty x y := match x, y with None, None => False | _, _ => True end.
  Definition Node elt (data : option elt) (map : option (NMap.t (t elt))) (pf : node_NonEmpty data map) : t elt
    := @Node' _ data (match map, data return node_NonEmpty data map -> option_dep _ (Option.is_None data) with
                      | Some m, _ => fun _ => Some_dep m
                      | None, Some _ => fun _ => None_dep
                      | None, None => fun pf => match pf with end
                      end pf).
  Global Arguments Node [elt] _ _ _.
  Definition t_rect elt (P : t elt -> Type)
             (val : forall (v : option elt) (m : option (NMap.t (t elt))) (pf : node_NonEmpty v m), P (Node v m pf))
             (m : t elt)
    : P m
    := Eval cbv beta in
      match m return P m with
      | {| data := d ; map := m |}
        => match m in option_dep _ b, d return forall pf : is_None d = b, P {| data := d ; map := rew <- [option_dep _] pf in m |} with
           | None_dep, None
             => fun pf => match pf with
                          | eq_refl => I
                          end
           | Some_dep _ m, Some d
             => fun pf => match pf with
                          | eq_refl => val (Some d) (Some m) I
                          end
           | None_dep as m, Some d
             => fun pf => match pf with
                          | eq_refl => ltac:(refine (fun x => x)) (val (Some d) None I)
                          end
           | Some_dep _ m, None
             => fun pf => match pf with
                          | eq_refl => val None (Some m) I
                          end
           end eq_refl
      end.
End NMapTypFunctor.

Module NMapTrieInd <: Trie NOrderedTypeBits NMap.
  Definition t := NMapTypFunctor.t.
  Include TrieShape NOrderedTypeBits NMap.

  Definition NMap_find_alt
    := ltac:(let v := (eval cbv -[PositiveMap.find fst snd] in NMap.find) in
             lazymatch (eval pattern PositiveMap.find in v) with
             | ?P _ => let v := (eval cbv beta in (P PositiveMapTrieInd.PositiveMap_find_alt)) in
                       exact v
             end).

  Lemma eq_NMap_find_alt A : forall i m, @NMap.find A i m = @NMap_find_alt A i m.
  Proof using Type.
    cbv -[PositiveMap.find PositiveMapTrieInd.PositiveMap_find_alt].
    intros; break_innermost_match; rewrite ?PositiveMapTrieInd.eq_PositiveMap_find_alt; reflexivity.
  Qed.

  Definition t_ind_full elt (P : t elt -> Prop)
             (H : forall d m pf,
                 (forall k v, match m with Some m => NMap.find k m = Some v -> P v | None => True end)
                 -> P (NMapTypFunctor.Node d m pf))
    : forall m, P m.
  Proof using Type.
    fix t_ind_full 1.
    induction m as [d m pf] using NMapTypFunctor.t_rect.
    specialize (H d m pf).
    apply H; clear H.
    destruct m as [[[m0 m]]|]; [ | intros; exact I ].
    intros [|k]; [ | revert k ].
    { cbn.
      destruct m0 as [m0|]; [ | clear; intros; inversion_option ].
      specialize (t_ind_full m0).
      intro v.
      refine (fun pf => match pf with
                        | eq_refl => t_ind_full
                        end). }
    cbv -[PositiveMap.find t].
    induction m;
      [ clear t_ind_full
      | match goal with
        | [ H : option _ |- _ ]
          => let x := fresh "x" in
             destruct H as [x|];
             [ specialize (t_ind_full x)
             | clear t_ind_full ]
        end ].
    all: intros k v H.
    all: try solve [ exfalso; clear -H; abstract (destruct k; cbn in H; inversion_option) ].
    all: destruct k; cbn [PositiveMap.find] in *.
    all: lazymatch goal with
         | [ H : None = Some _ |- _ ] => exfalso; clear -H; abstract inversion_option
         | [ H : ?P ?x, H' : Some ?x = Some ?y |- ?P ?y ]
           => refine (rew [P] (f_equal (fun v => Option.value v x) H') in H)
         | _ => idtac
         end.
    all: eauto with nocore.
  Defined.

  Section map2.
    Variable A B C : Type.
    Variable f : option A -> option B -> option C.

    Definition NMap_xmap2_l (m : NMap.t A) : NMap.t C
      := ltac:(let v := (eval cbv -[PositiveMap.map2] in (NMap.map2 f m (@NMap.empty _))) in
               lazymatch (eval pattern (PositiveMap.map2 f) in v) with
               | ?P _ => let v := (eval cbv beta in (P (fun m _ => PositiveMap.xmap2_l f m))) in
                         exact v
               end).

    Definition NMap_xmap2_r (m : NMap.t B) : NMap.t C
      := ltac:(let v := (eval cbv -[PositiveMap.map2] in (NMap.map2 f (@NMap.empty _) m)) in
               lazymatch (eval pattern (PositiveMap.map2 f) in v) with
               | ?P _ => let v := (eval cbv beta in (P (fun _ m => PositiveMap.xmap2_r f m))) in
                         exact v
               end).

    Lemma NMap_xgmap2_l : forall (i : NMap.key) (m : NMap.t A),
        f None None = None -> NMap.find i (NMap_xmap2_l m) = f (NMap.find i m) None.
    Proof using Type.
      cbv -[PositiveMap.find PositiveMap.xmap2_l]; intros; break_innermost_match; eauto.
      all: now rewrite PositiveMap.xgmap2_l by assumption.
    Qed.

    Lemma NMap_xgmap2_r : forall (i : NMap.key) (m : NMap.t B),
        f None None = None -> NMap.find i (NMap_xmap2_r m) = f None (NMap.find i m).
    Proof using Type.
      cbv -[PositiveMap.find PositiveMap.xmap2_r]; intros; break_innermost_match; eauto.
      all: now rewrite PositiveMap.xgmap2_r by assumption.
    Qed.
  End map2.
  Lemma NMap_xmap2_lr :
    forall (A B : Type)(f g: option A -> option A -> option B)(m : NMap.t A),
      (forall (i j : option A), f i j = g j i) ->
      NMap_xmap2_l f m = NMap_xmap2_r g m.
  Proof.
    cbv -[PositiveMap.xmap2_r PositiveMap.xmap2_l].
    intros; break_innermost_match; repeat (f_equal; eauto using PositiveMapAdditionalFacts.xmap2_lr).
  Qed.

  Section everything.
    Let everything' : Everything.
    Proof.
      unshelve esplit.
      all: try exact NMapTypFunctor.Node.
      all: try exact NMapTypFunctor.t_rect.
      all: try exact t_ind_full.
      all: try exact NMap_xmap2_lr.
      all: try exact NMap_xgmap2_l.
      all: try exact NMap_xgmap2_r.
      all: handle_id_fix.
      all: subst_partial_evars.
      all: try (destruct_head' option; destruct_head'_True; destruct_head'_False; reflexivity).
      all: partial_unify e.
      all: try reflexivity.
    Defined.
    Definition everything := Eval cbv [everything'] in everything'.
  End everything.
End NMapTrieInd.

Module ZMapTypFunctor <: TypFunctor.
  Local Unset Primitive Projections.
  Local Set Nonrecursive Elimination Schemes.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Inductive t' (elt : Type) := Node' { data : option elt ; map : option_dep (ZMap.t (t' elt)) (Option.is_None data) }.
  Definition t := t'.
  Local Notation node_NonEmpty x y := match x, y with None, None => False | _, _ => True end.
  Definition Node elt (data : option elt) (map : option (ZMap.t (t elt))) (pf : node_NonEmpty data map) : t elt
    := @Node' _ data (match map, data return node_NonEmpty data map -> option_dep _ (Option.is_None data) with
                      | Some m, _ => fun _ => Some_dep m
                      | None, Some _ => fun _ => None_dep
                      | None, None => fun pf => match pf with end
                      end pf).
  Global Arguments Node [elt] _ _ _.
  Definition t_rect elt (P : t elt -> Type)
             (val : forall (v : option elt) (m : option (ZMap.t (t elt))) (pf : node_NonEmpty v m), P (Node v m pf))
             (m : t elt)
    : P m
    := Eval cbv beta in
      match m return P m with
      | {| data := d ; map := m |}
        => match m in option_dep _ b, d return forall pf : is_None d = b, P {| data := d ; map := rew <- [option_dep _] pf in m |} with
           | None_dep, None
             => fun pf => match pf with
                          | eq_refl => I
                          end
           | Some_dep _ m, Some d
             => fun pf => match pf with
                          | eq_refl => val (Some d) (Some m) I
                          end
           | None_dep as m, Some d
             => fun pf => match pf with
                          | eq_refl => ltac:(refine (fun x => x)) (val (Some d) None I)
                          end
           | Some_dep _ m, None
             => fun pf => match pf with
                          | eq_refl => val None (Some m) I
                          end
           end eq_refl
      end.
End ZMapTypFunctor.

Module ZMapTrieInd <: Trie ZOrderedTypeBits ZMap.
  Definition t := ZMapTypFunctor.t.
  Include TrieShape ZOrderedTypeBits ZMap.

  Definition ZMap_find_alt
    := ltac:(let v := (eval cbv -[PositiveMap.find fst snd] in ZMap.find) in
             lazymatch (eval pattern PositiveMap.find in v) with
             | ?P _ => let v := (eval cbv beta in (P PositiveMapTrieInd.PositiveMap_find_alt)) in
                       exact v
             end).

  Lemma eq_ZMap_find_alt A : forall i m, @ZMap.find A i m = @ZMap_find_alt A i m.
  Proof using Type.
    cbv -[PositiveMap.find PositiveMapTrieInd.PositiveMap_find_alt].
    intros; break_innermost_match; rewrite ?PositiveMapTrieInd.eq_PositiveMap_find_alt; reflexivity.
  Qed.

  Definition t_ind_full elt (P : t elt -> Prop)
             (H : forall d m pf,
                 (forall k v, match m with Some m => ZMap.find k m = Some v -> P v | None => True end)
                 -> P (ZMapTypFunctor.Node d m pf))
    : forall m, P m.
  Proof using Type.
    fix t_ind_full 1.
    induction m as [d m pf] using ZMapTypFunctor.t_rect.
    specialize (H d m pf).
    apply H; clear H.
    destruct m as [[[mn [[m0 m]]]]|]; [ | intros; exact I ].
    intros [|k|k]; [ | revert k | revert k ].
    all: cbv -[PositiveMap.find t].
    { destruct m0 as [m0|]; [ | clear; intros; inversion_option ].
      specialize (t_ind_full m0).
      intro v.
      refine (fun pf => match pf with
                        | eq_refl => t_ind_full
                        end). }
    all: let m := lazymatch goal with |- context[PositiveMap.find _ ?m] => m end in
         induction m;
         [ clear t_ind_full
         | match goal with
           | [ H : option _ |- _ ]
             => let x := fresh "x" in
                destruct H as [x|];
                [ specialize (t_ind_full x)
                | clear t_ind_full ]
           end ].
    all: intros k v H.
    all: try solve [ exfalso; clear -H; abstract (destruct k; cbn in H; inversion_option) ].
    all: destruct k; cbn [PositiveMap.find] in *.
    all: lazymatch goal with
         | [ H : None = Some _ |- _ ] => exfalso; clear -H; abstract inversion_option
         | [ H : ?P ?x, H' : Some ?x = Some ?y |- ?P ?y ]
           => refine (rew [P] (f_equal (fun v => Option.value v x) H') in H)
         | _ => idtac
         end.
    all: eauto with nocore.
  Defined.

  Section map2.
    Variable A B C : Type.
    Variable f : option A -> option B -> option C.

    Definition ZMap_xmap2_l (m : ZMap.t A) : ZMap.t C
      := ltac:(let v := (eval cbv -[PositiveMap.map2] in (ZMap.map2 f m (@ZMap.empty _))) in
               lazymatch (eval pattern (PositiveMap.map2 f) in v) with
               | ?P _ => let v := (eval cbv beta in (P (fun m _ => PositiveMap.xmap2_l f m))) in
                         exact v
               end).

    Definition ZMap_xmap2_r (m : ZMap.t B) : ZMap.t C
      := ltac:(let v := (eval cbv -[PositiveMap.map2] in (ZMap.map2 f (@ZMap.empty _) m)) in
               lazymatch (eval pattern (PositiveMap.map2 f) in v) with
               | ?P _ => let v := (eval cbv beta in (P (fun _ m => PositiveMap.xmap2_r f m))) in
                         exact v
               end).

    Lemma ZMap_xgmap2_l : forall (i : ZMap.key) (m : ZMap.t A),
        f None None = None -> ZMap.find i (ZMap_xmap2_l m) = f (ZMap.find i m) None.
    Proof using Type.
      cbv -[PositiveMap.find PositiveMap.xmap2_l]; intros; break_innermost_match; eauto.
      all: now rewrite PositiveMap.xgmap2_l by assumption.
    Qed.

    Lemma ZMap_xgmap2_r : forall (i : ZMap.key) (m : ZMap.t B),
        f None None = None -> ZMap.find i (ZMap_xmap2_r m) = f None (ZMap.find i m).
    Proof using Type.
      cbv -[PositiveMap.find PositiveMap.xmap2_r]; intros; break_innermost_match; eauto.
      all: now rewrite PositiveMap.xgmap2_r by assumption.
    Qed.
  End map2.
  Lemma ZMap_xmap2_lr :
    forall (A B : Type)(f g: option A -> option A -> option B)(m : ZMap.t A),
      (forall (i j : option A), f i j = g j i) ->
      ZMap_xmap2_l f m = ZMap_xmap2_r g m.
  Proof.
    cbv -[PositiveMap.xmap2_r PositiveMap.xmap2_l].
    intros; break_innermost_match; repeat (f_equal; eauto using PositiveMapAdditionalFacts.xmap2_lr).
  Qed.

  Section everything.
    Let everything' : Everything.
    Proof.
      unshelve esplit.
      all: try exact ZMapTypFunctor.Node.
      all: try exact ZMapTypFunctor.t_rect.
      all: try exact t_ind_full.
      all: try exact ZMap_xmap2_lr.
      all: try exact ZMap_xgmap2_l.
      all: try exact ZMap_xgmap2_r.
      all: handle_id_fix.
      all: subst_partial_evars.
      all: try (destruct_head' option; destruct_head'_True; destruct_head'_False; reflexivity).
      all: partial_unify e.
      all: try reflexivity.
    Defined.
    Definition everything := Eval cbv [everything'] in everything'.
  End everything.
End ZMapTrieInd.
