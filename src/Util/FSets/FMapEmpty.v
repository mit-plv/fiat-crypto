From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Orders.
From Coq Require Import OrdersEx.
From Coq Require Import FMapInterface.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.Compose.
Require Import Crypto.Util.Logic.Forall.
Require Import Crypto.Util.Logic.Exists.
Require Import Crypto.Util.Structures.Equalities.Empty.
Require Import Crypto.Util.Structures.Equalities.Unit.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Structures.Orders.Empty.
Require Import Crypto.Util.Structures.Orders.Unit.
Require Import Crypto.Util.Sorting.Sorted.Proper.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.

Local Set Implicit Arguments.
(* TODO: move to global settings *)
Local Set Keyed Unification.
Local Set Keep Proof Equalities.

Local Ltac t_safe_step :=
  first [ progress cbv in *
        | progress intros
        | reflexivity
        | progress subst
        | progress destruct_head'_ex
        | progress destruct_head'_unit
        | progress destruct_head'_and
        | progress destruct_head'_False
        | progress destruct_head'_or
        | progress break_innermost_match
        | progress break_innermost_match_hyps
        | progress specialize_under_binders_by exact tt
        | progress specialize_under_binders_by eapply ex_intro
        | apply conj
        | congruence
        | progress invlist InA
        | match goal with
          | [ |- NoDupA _ (_ :: _) ] => constructor
          | [ |- NoDupA _ nil ] => constructor
          | [ H : ?x = ?y :> Compare _ _ _ _ |- _ = _ ]
            => let x := head x in
               let y := head y in
               is_constructor x;
               is_constructor y;
               inversion H; clear H
          end
        | solve [ eauto ] ].
Local Ltac t :=
  repeat first [ t_safe_step
               | progress specialize_under_binders_by reflexivity ].

Module EmptyMap <: S with Module E := EmptyOrderedTypeOrig.
  Module E := EmptyOrderedTypeOrig.
  Definition key := Empty_set.
  Definition t (elt : Type) := unit.

  Section Types.

    Variable elt:Type.

    Definition empty : t elt := tt.
    Definition is_empty (m : t elt) : bool := true.
    Definition add (k : key) (v : elt) (m : t elt) : t elt := match k with end.
    Definition find (k : key) (m : t elt) : option elt := match k with end.
    Definition remove (k : key) (m : t elt) : t elt := match k with end.
    Definition mem (k : key) (m : t elt) : bool := match k with end.
    Variable elt' elt'' : Type.

    Definition map : (elt -> elt') -> t elt -> t elt' := fun _ m => m.
    Definition mapi (f : key -> elt -> elt') : t elt -> t elt' := fun m => m.
    Definition map2 (f : option elt -> option elt' -> option elt'') (m : t elt) (m' : t elt') : t elt''
      := tt.
    Definition elements (m : t elt) : list (key*elt) := nil.
    Definition cardinal (m : t elt) : nat := 0%nat.
    Definition fold A (f : key -> elt -> A -> A) (m : t elt) (acc : A) : A := acc.
    Definition equal : (elt -> elt -> bool) -> t elt -> t elt -> bool := fun _ _ _ => true.
    Section Spec.

      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.

      Local Hint Constructors NoDupA : core.

      Definition MapsTo (k : key) (v : elt) (m : t elt) : Prop := match k with end.

      Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.

      Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

      Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').

      Definition eq_key_elt (p p':key*elt) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

      Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
      Proof using Type. clear; t. Qed.
      Lemma mem_1 : In x m -> mem x m = true.
      Proof using Type. clear; t. Qed.
      Lemma mem_2 : mem x m = true -> In x m.
      Proof using Type. clear; t. Qed.
      Lemma empty_1 : Empty empty.
      Proof using Type. clear; t. Qed.
      Lemma is_empty_1 : Empty m -> is_empty m = true.
      Proof using Type. clear; t. Qed.
      Lemma is_empty_2 : is_empty m = true -> Empty m.
      Proof using Type. clear; t. Qed.
      Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
      Proof using Type. clear; t. Qed.
      Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      Proof using Type. clear; t. Qed.
      Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
      Proof using Type. clear; t. Qed.
      Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
      Proof using Type. clear; t. Qed.
      Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      Proof using Type. clear; t. Qed.
      Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
      Proof using Type. clear; t. Qed.
      Lemma find_1 : MapsTo x e m -> find x m = Some e.
      Proof using Type. clear; t. Qed.
      Lemma find_2 : find x m = Some e -> MapsTo x e m.
      Proof using Type. clear; t. Qed.
      Lemma elements_1 :
        MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
      Proof using Type. clear; t. Qed.
      Lemma elements_2 :
        InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
      Proof using Type. clear; t. Qed.
      Lemma elements_3w : NoDupA eq_key (elements m).
      Proof using Type. clear; t. Qed.
      Lemma cardinal_1 : cardinal m = length (elements m).
      Proof using Type. clear; t. Qed.
      Lemma fold_1 :
	forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
      Proof using Type. clear; t. Qed.
      Definition Equal m m' := forall y, find y m = find y m'.
      Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
        (forall k, In k m <-> In k m') /\
          (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
      Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

      Variable cmp : elt -> elt -> bool.

      Lemma equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
      Proof using Type. clear; t. Qed.
      Lemma equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
      Proof using Type. clear; t. Qed.
    End Spec.
  End Types.

  Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
      MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof using Type. clear; t. Qed.
  Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
      In x (map f m) -> In x m.
  Proof using Type. clear; t. Qed.

  Lemma mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
                        (f:key->elt->elt'), MapsTo x e m ->
                                            exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof using Type. clear; t. Qed.
  Lemma mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
                        (f:key->elt->elt'), In x (mapi f m) -> In x m.
  Proof using Type. clear; t. Qed.
  Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	                (x:key)(f:option elt->option elt'->option elt''),
      In x m \/ In x m' ->
      find x (map2 f m m') = f (find x m) (find x m').
  Proof using Type. clear; t. Qed.

  Lemma map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	                (x:key)(f:option elt->option elt'->option elt''),
      In x (map2 f m m') -> In x m \/ In x m'.
  Proof using Type. clear; t. Qed.
  Section elt.
    Variable elt:Type.
    Definition lt_key (p p':key*elt) := E.lt (fst p) (fst p').
    Lemma elements_3 : forall m, sort lt_key (elements m).
    Proof using Type. clear; t. Qed.
  End elt.
End EmptyMap.

Module EmptyMapOrd (D : OrderedTypeOrig) <: Sord
                                           with Module Data := D
                                           with Module MapS := EmptyMap.
  Module Data <: OrderedTypeOrig := D.
  Module MapS <: S := EmptyMap.
  Import MapS.

  Definition t := EmptyMap.t Data.t.
  Include UnitHasEq.
  Include UnitHasLt.
  Include UnitIsEqOrig.
  Include UnitIsStrOrderOrig.
  Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.
  Lemma eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
  Proof. t. Qed.
  Lemma eq_2 : forall m m', eq m m' -> Equivb cmp m m'.
  Proof. pose proof Data.lt_not_eq. pose proof Data.eq_sym. t. Qed.

  Definition compare : forall m1 m2, Compare lt eq m1 m2.
  Proof.
    constructor; destruct_head'_unit; reflexivity.
  Defined.

End EmptyMapOrd.
