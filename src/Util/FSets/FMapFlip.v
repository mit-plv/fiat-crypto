Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.FSets.FMapInterface.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.ListUtil.SetoidListRev.
Require Import Crypto.Util.Compose.
Require Import Crypto.Util.Logic.Forall.
Require Import Crypto.Util.Logic.Exists.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Structures.Orders.Flip.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.Sorting.Sorted.Proper.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.

Local Set Implicit Arguments.
(* TODO: move to global settings *)
Local Set Keyed Unification.

Module FlipWSfun (E : DecidableTypeOrig) (W' : WSfun E) <: WSfun E.
  Module E' := E <+ UpdateEq.
  Global Remove Hints E'.eq_refl E'.eq_sym E'.eq_trans : core.
  Local Hint Resolve E'.eq_refl E'.eq_sym E'.eq_trans : core.

  Local Instance W'_eq_key_equiv elt : Equivalence (@W'.eq_key elt) | 10. split; cbv; eauto. Qed.
  Local Instance W'_eq_key_elt_equiv elt : Equivalence (@W'.eq_key_elt elt) | 10. split; repeat intros [? ?]; cbv in *; subst; eauto. Qed.

  Definition key := W'.key.
  Definition t := W'.t.
  Definition empty := W'.empty.
  Definition is_empty := W'.is_empty.
  Definition add := W'.add.
  Definition find := W'.find.
  Definition remove := W'.remove.
  Definition mem := W'.mem.
  Definition map := W'.map.
  Definition mapi := W'.mapi.
  Definition map2 := W'.map2.
  Definition cardinal := W'.cardinal.
  Definition equal := W'.equal.
  Definition MapsTo := W'.MapsTo.
  Definition In := W'.In.
  Definition eq_key := W'.eq_key.
  Definition eq_key_elt := W'.eq_key_elt.
  Definition MapsTo_1 := W'.MapsTo_1.
  Definition mem_1 := W'.mem_1.
  Definition mem_2 := W'.mem_2.
  Definition empty_1 := W'.empty_1.
  Definition is_empty_1 := W'.is_empty_1.
  Definition is_empty_2 := W'.is_empty_2.
  Definition add_1 := W'.add_1.
  Definition add_2 := W'.add_2.
  Definition add_3 := W'.add_3.
  Definition remove_1 := W'.remove_1.
  Definition remove_2 := W'.remove_2.
  Definition remove_3 := W'.remove_3.
  Definition find_1 := W'.find_1.
  Definition find_2 := W'.find_2.
  Definition Empty := W'.Empty.
  Definition Equal := W'.Equal.
  Definition Equiv := W'.Equiv.
  Definition Equivb := W'.Equivb.
  Definition equal_1 := W'.equal_1.
  Definition equal_2 := W'.equal_2.
  Definition map_1 := W'.map_1.
  Definition map_2 := W'.map_2.
  Definition mapi_1 := W'.mapi_1.
  Definition mapi_2 := W'.mapi_2.
  Definition map2_1 := W'.map2_1.
  Definition map2_2 := W'.map2_2.

  Definition elements elt (v : t elt) : list (key * elt)
    := List.rev_append (W'.elements v) nil.
  Definition fold elt A (f : key -> elt -> A -> A) (m : t elt) (a : A) : A
    := W'.fold (fun k v acc a => acc (f k v a)) m id a.

  Section Spec.
    Variable elt : Type.
    Variable m m' m'' : t elt.
    Variable x y z : key.
    Variable e e' : elt.

    Lemma elements_1 :
      MapsTo x e m -> InA (@eq_key_elt _) (x,e) (elements m).
    Proof using Type.
      clear; cbv [elements]; rewrite <- rev_alt, InA_rev.
      apply W'.elements_1.
    Qed.
    Lemma elements_2 :
      InA (@eq_key_elt _) (x,e) (elements m) -> MapsTo x e m.
    Proof using Type.
      clear; cbv [elements]; rewrite <- rev_alt, InA_rev.
      apply W'.elements_2.
    Qed.
    Lemma elements_3w : NoDupA (@eq_key _) (elements m).
    Proof using Type.
      clear; cbv [elements]; rewrite <- rev_alt.
      apply NoDupA_rev; try exact _.
      apply W'.elements_3w.
    Qed.
    Lemma cardinal_1 : cardinal m = length (elements m).
    Proof using Type.
      clear; cbv [elements]; rewrite <- rev_alt, rev_length.
      apply W'.cardinal_1.
    Qed.
    Lemma fold_1 :
      forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
    Proof using Type.
      clear; cbv [fold elements]; intros; rewrite <- rev_alt, W'.fold_1, fold_left_rev_higher_order.
      reflexivity.
    Qed.
  End Spec.
End FlipWSfun.

Module FlipWeakMap (W' : WS) <: WS.
  Module E := W'.E.
  Global Remove Hints E.eq_refl E.eq_sym E.eq_trans : core.
  Include FlipWSfun W'.E W'.
End FlipWeakMap.

Module FlipUsualWeakMap (W' : UsualWS) <: UsualWS := FlipWeakMap W'.

Module FlipSfun (E' : OrderedTypeOrig) (W' : Sfun E').
  Include FlipWSfun E' W'.
  Section elt.
    Variable elt:Type.
    Definition lt_key (p p':key*elt) := flip E'.lt (fst p) (fst p').

    Lemma elements_3 m : sort lt_key (elements m).
    Proof using Type.
      cbv [elements lt_key].
      rewrite <- rev_alt, SortA_rev_iff.
      apply W'.elements_3.
    Qed.
  End elt.
End FlipSfun.

Module FlipUsualMap (S' : UsualS) <: UsualS.
  Module E <: UsualOrderedTypeOrig := FlipUsualOrderedTypeOrig S'.E.
  Global Remove Hints E.eq_refl E.eq_sym E.eq_trans : core.
  Include FlipSfun S'.E S'.
End FlipUsualMap.

Module FlipMap (S' : S) <: S.
  Module E <: OrderedTypeOrig := FlipOrderedTypeOrig S'.E.
  Global Remove Hints E.eq_refl E.eq_sym E.eq_trans : core.
  Include FlipSfun S'.E S'.
End FlipMap.

Module FlipSord (S' : Sord) <: Sord.
  Module Data <: OrderedTypeOrig := FlipOrderedTypeOrig S'.Data.
  Module MapS <: S := FlipMap S'.MapS.
  Import MapS.

  Definition t := S'.t.
  Definition eq := S'.eq.
  Definition lt := flip S'.lt.
  Definition eq_refl := S'.eq_refl.
  Definition eq_sym := S'.eq_sym.
  Definition eq_trans := S'.eq_trans.
  Lemma lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Proof. cbv [lt flip]; intros; eapply S'.lt_trans; eassumption. Qed.
  Lemma lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.
  Proof. cbv [lt flip]; intros * H H'; apply S'.lt_not_eq in H; apply H, S'.eq_sym, H'. Qed.

  Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.

  Lemma cmp_iff : forall e e', cmp e e' = flip S'.cmp e e'.
  Proof.
    cbv [cmp flip S'.cmp].
    intros e e'.
    destruct Data.compare, S'.Data.compare; try reflexivity.
    all: cbv [flip] in *.
    all: match goal with
         | [ H : _ |- _ ] => apply S'.Data.lt_not_eq in H; []
         end.
    all: try now exfalso; eauto using S'.Data.eq_sym.
  Qed.

  Lemma compare : forall m1 m2, Compare lt eq m1 m2.
  Proof.
    intros m1 m2.
    destruct (S'.compare m2 m1).
    all: constructor; (idtac + apply S'.eq_sym); assumption.
  Defined.

  Lemma eq_iff : forall m m', Equivb cmp m m' <-> eq m m'.
  Proof.
    intros m m'; cbv [eq].
    rewrite (conj (@eq_sym m m') (@eq_sym m' m) : iff _ _).
    rewrite <- (conj (@S'.eq_1 m' m) (@S'.eq_2 m' m) : iff _ _).
    cbv [Equivb S'.MapS.Equivb S'.MapS.Equiv Cmp eq flip] in *.
    firstorder; first [ rewrite cmp_iff | setoid_rewrite <- cmp_iff ]; cbv [flip].
    all: eauto.
  Qed.

  Lemma eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
  Proof. intros *; apply eq_iff. Qed.
  Lemma eq_2 : forall m m', eq m m' -> Equivb cmp m m'.
  Proof. intros *; apply eq_iff. Qed.
End FlipSord.
