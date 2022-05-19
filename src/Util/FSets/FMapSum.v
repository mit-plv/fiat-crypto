Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.FSets.FMapInterface.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.Compose.
Require Import Crypto.Util.Logic.Forall.
Require Import Crypto.Util.Logic.Exists.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Relations.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.Prod.
Require Import Crypto.Util.Structures.Equalities.Sum.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Structures.Orders.Prod.
Require Import Crypto.Util.Structures.Orders.Sum.
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
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope type_scope.

Module SumWSfun_gen (E1 : DecidableTypeOrig) (E2 : DecidableTypeOrig) (M1 : WSfun E1) (M2 : WSfun E2).
  Module Type ESig := SumTyp E1 E2 <+ HasEq <+ IsEqOrig <+ HasEqDec.
  Module Type ESigCompat (E : ESig).
    Axiom eq_alt : forall x y, E.eq x y <-> sumwise E1.eq E2.eq x y.
  End ESigCompat.
  Module E1 <: DecidableTypeBoth := E1 <+ UpdateEq.
  Module E2 <: DecidableTypeBoth := E2 <+ UpdateEq.
  Module SumWSfun_gen (E : ESig) (ECompat : ESigCompat E) <: WSfun E.
    Module E' <: DecidableTypeBoth := E <+ UpdateEq <+ ECompat.
    Local Instance M1_eq_key_equiv elt : Equivalence (@M1.eq_key elt) | 10. split; cbv; eauto. Qed.
    Local Instance M1_eq_key_elt_equiv elt : Equivalence (@M1.eq_key_elt elt) | 10. split; repeat intros [? ?]; cbv in *; subst; eauto. Qed.
    Local Instance M2_eq_key_equiv elt : Equivalence (@M2.eq_key elt) | 10. split; cbv; eauto. Qed.
    Local Instance M2_eq_key_elt_equiv elt : Equivalence (@M2.eq_key_elt elt) | 10. split; repeat intros [? ?]; cbv in *; subst; eauto. Qed.

    Definition key := E.t.

    Global Hint Transparent key : core.

    Definition t elt := M1.t elt * M2.t elt.

    Definition liftK {A} (f1 : M1.key -> A) (f2 : M2.key -> A) : key -> A
      := fun x => match x with
                  | inl x => f1 x
                  | inr x => f2 x
                  end.
    Definition liftT {elt} (f1 : M1.t elt) (f2 : M2.t elt) : t elt
      := (f1, f2).
    Definition liftTT {elt elt'}
               (f1 : M1.t elt -> M1.t elt')
               (f2 : M2.t elt -> M2.t elt')
      : t elt -> t elt'
      := fun m => (f1 (fst m), f2 (snd m)).
    Definition lift_TT {elt elt' A}
               (f1 : A -> M1.t elt -> M1.t elt')
               (f2 : A -> M2.t elt -> M2.t elt')
      : A -> t elt -> t elt'
      := fun a => liftTT (f1 a) (f2 a).
    Definition liftTTT {elt elt' elt''}
               (f1 : M1.t elt -> M1.t elt' -> M1.t elt'')
               (f2 : M2.t elt -> M2.t elt' -> M2.t elt'')
      : t elt -> t elt' -> t elt''
      := fun m m' => (f1 (fst m) (fst m'), f2 (snd m) (snd m')).
    Definition lift_TTT {elt elt' elt'' A}
               (f1 : A -> M1.t elt -> M1.t elt' -> M1.t elt'')
               (f2 : A -> M2.t elt -> M2.t elt' -> M2.t elt'')
      : A -> t elt -> t elt' -> t elt''
      := fun a => liftTTT (f1 a) (f2 a).
    Definition liftK_TT {A elt}
               (f1 : M1.key -> A -> M1.t elt -> M1.t elt)
               (f2 : M2.key -> A -> M2.t elt -> M2.t elt)
      : key -> A -> t elt -> t elt
      := fun k a m => (match k with
                       | inl k => f1 k a (fst m)
                       | inr _ => fst m
                       end,
                        match k with
                        | inl _ => snd m
                        | inr k => f2 k a (snd m)
                        end).
    Definition liftKT_ {A elt}
               (f1 : M1.key -> M1.t elt -> A)
               (f2 : M2.key -> M2.t elt -> A)
      : key -> t elt -> A
      := fun k m => match k with
                    | inl k => f1 k (fst m)
                    | inr k => f2 k (snd m)
                    end.
    Definition liftK_T_ {A B elt}
               (f1 : M1.key -> A -> M1.t elt -> B)
               (f2 : M2.key -> A -> M2.t elt -> B)
      : key -> A -> t elt -> B
      := fun k a m => match k with
                      | inl k => f1 k a (fst m)
                      | inr k => f2 k a (snd m)
                      end.
    Definition liftKTT {elt}
               (f1 : M1.key -> M1.t elt -> M1.t elt)
               (f2 : M2.key -> M2.t elt -> M2.t elt)
      : key -> t elt -> t elt
      := fun k m => (match k with
                     | inl k => f1 k (fst m)
                     | inr _ => fst m
                     end,
                      match k with
                      | inl _ => snd m
                      | inr k => f2 k (snd m)
                      end).
    Definition lifthoTT {elt elt' A}
               (f1 : (M1.key -> A) -> M1.t elt -> M1.t elt')
               (f2 : (M2.key -> A) -> M2.t elt -> M2.t elt')
      : (key -> A) -> t elt -> t elt'
      := fun f m => (f1 (fun k => f (inl k)) (fst m),
                      f2 (fun k => f (inr k)) (snd m)).

    Definition empty elt : t elt := liftT (@M1.empty _) (@M2.empty _).
    Definition is_empty elt (m : t elt) : bool := M1.is_empty (fst m) &&& M2.is_empty (snd m).
    Definition add elt : key -> elt -> t elt -> t elt := liftK_TT (@M1.add elt) (@M2.add elt).
    Definition find elt : key -> t elt -> option elt := liftKT_ (@M1.find elt) (@M2.find elt).
    Definition remove elt : key -> t elt -> t elt := liftKTT (@M1.remove elt) (@M2.remove elt).
    Definition mem elt : key -> t elt -> bool := liftKT_ (@M1.mem elt) (@M2.mem elt).
    Definition map elt elt' : (elt -> elt') -> t elt -> t elt' := lift_TT (@M1.map elt elt') (@M2.map elt elt').
    Definition mapi elt elt' : (key -> elt -> elt') -> t elt -> t elt' := lifthoTT (@M1.mapi elt elt') (@M2.mapi elt elt').
    Definition map2 elt elt' elt'' : (option elt -> option elt' -> option elt'') -> t elt -> t elt' -> t elt'' := lift_TTT (@M1.map2 elt elt' elt'') (@M2.map2 elt elt' elt'').
    Definition elements elt (v : t elt) : list (key * elt)
      := (List.map (fun kv => (inl (fst kv), snd kv)) (M1.elements (fst v)))
           ++ List.map (fun kv => (inr (fst kv), snd kv)) (M2.elements (snd v)).
    Definition cardinal elt (m : t elt) : nat := M1.cardinal (fst m) + M2.cardinal (snd m).
    Definition fold elt A (f : key -> elt -> A -> A) (m : t elt) (i : A) : A
      := M2.fold (fun k => f (inr k)) (snd m) (M1.fold (fun k => f (inl k)) (fst m) i).
    Definition equal elt (eqb : elt -> elt -> bool) (m m' : t elt) : bool
      := M1.equal eqb (fst m) (fst m') &&& M2.equal eqb (snd m) (snd m').
    Definition MapsTo elt : key -> elt -> t elt -> Prop := liftK_T_ (@M1.MapsTo elt) (@M2.MapsTo elt).
    Definition eq_key elt (p p':key*elt) := E.eq (fst p) (fst p').
    Definition eq_key_elt elt (p p':key*elt) :=
      E.eq (fst p) (fst p') /\ (snd p) = (snd p').

    Local Instance Proper_M1_eq_key_elt_iff elt
      : Proper (eq ==> RelationPairs.RelProd E1.eq eq ==> iff) (@M1.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M1_eq_key_elt_impl elt
      : Proper (eq ==> RelationPairs.RelProd E1.eq eq ==> impl) (@M1.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M1_eq_key_elt_flip_impl elt
      : Proper (eq ==> RelationPairs.RelProd E1.eq eq ==> flip impl) (@M1.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M1_eq_key_elt_iff' elt
      : Proper (@M1.eq_key_elt elt ==> @M1.eq_key_elt elt ==> iff) (@M1.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M1_eq_key_elt_impl' elt
      : Proper (@M1.eq_key_elt elt ==> @M1.eq_key_elt elt ==> impl) (@M1.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M1_eq_key_elt_flip_impl' elt
      : Proper (@M1.eq_key_elt elt ==> @M1.eq_key_elt elt ==> flip impl) (@M1.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M1_eq_key_iff elt
      : Proper (@M1.eq_key elt ==> @M1.eq_key elt ==> iff) (@M1.eq_key elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M1_eq_key_impl elt
      : Proper (@M1.eq_key elt ==> @M1.eq_key elt ==> impl) (@M1.eq_key elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M1_eq_key_flip_impl elt
      : Proper (@M1.eq_key elt ==> @M1.eq_key elt ==> flip impl) (@M1.eq_key elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance M1_Equal_Equivalence elt : Equivalence (@M1.Equal elt) | 10.
    Proof. split; cbv; firstorder eauto using eq_trans. Qed.


    Local Instance Proper_M2_eq_key_elt_iff elt
      : Proper (eq ==> RelationPairs.RelProd E2.eq eq ==> iff) (@M2.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M2_eq_key_elt_impl elt
      : Proper (eq ==> RelationPairs.RelProd E2.eq eq ==> impl) (@M2.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M2_eq_key_elt_flip_impl elt
      : Proper (eq ==> RelationPairs.RelProd E2.eq eq ==> flip impl) (@M2.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M2_eq_key_elt_iff' elt
      : Proper (@M2.eq_key_elt elt ==> @M2.eq_key_elt elt ==> iff) (@M2.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M2_eq_key_elt_impl' elt
      : Proper (@M2.eq_key_elt elt ==> @M2.eq_key_elt elt ==> impl) (@M2.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M2_eq_key_elt_flip_impl' elt
      : Proper (@M2.eq_key_elt elt ==> @M2.eq_key_elt elt ==> flip impl) (@M2.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M2_eq_key_iff elt
      : Proper (@M2.eq_key elt ==> @M2.eq_key elt ==> iff) (@M2.eq_key elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M2_eq_key_impl elt
      : Proper (@M2.eq_key elt ==> @M2.eq_key elt ==> impl) (@M2.eq_key elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M2_eq_key_flip_impl elt
      : Proper (@M2.eq_key elt ==> @M2.eq_key elt ==> flip impl) (@M2.eq_key elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance M2_Equal_Equivalence elt : Equivalence (@M1.Equal elt) | 10.
    Proof. split; cbv; firstorder eauto using eq_trans. Qed.


    Local Ltac t_Proper_helper :=
      cbv [M1.Equal M1.In M2.Equal M2.In Proper respectful option_eq];
      repeat first [ progress intros
                   | progress subst
                   | progress destruct_head'_ex
                   | congruence
                   | reflexivity
                   | eassumption
                   | progress break_innermost_match_hyps
                   | progress break_innermost_match
                   | apply M1.find_2
                   | apply M2.find_2
                   | match goal with
                     | [ H : E1.eq ?x ?y |- _ ]
                       => (idtac + symmetry in H); eapply M1.MapsTo_1 in H; [ | apply M1.find_2; eassumption ]
                     | [ H : E2.eq ?x ?y |- _ ]
                       => (idtac + symmetry in H); eapply M2.MapsTo_1 in H; [ | apply M2.find_2; eassumption ]
                     | [ H : _ |- _ ] => apply M1.find_1 in H
                     | [ H : _ |- _ ] => apply M2.find_1 in H
                     | [ |- Some _ = None ] => exfalso
                     | [ |- ?x = None ] => destruct x eqn:?
                     | [ |- _ <-> _ ] => split
                     | [ H : M1.find ?k ?m = Some ?v, H' : forall k', M1.find k' ?m = M1.find k' ?m' |- _ ]
                       => unique assert (M1.find k m' = Some v) by now rewrite <- H
                     | [ H : M2.find ?k ?m = Some ?v, H' : forall k', M2.find k' ?m = M2.find k' ?m' |- _ ]
                       => unique assert (M2.find k m' = Some v) by now rewrite <- H
                     | [ H : M1.find ?k ?m' = Some ?v, H' : forall k', M1.find k' ?m = M1.find k' ?m' |- _ ]
                       => unique assert (M1.find k m = Some v) by now rewrite <- H
                     | [ H : M2.find ?k ?m' = Some ?v, H' : forall k', M2.find k' ?m = M2.find k' ?m' |- _ ]
                       => unique assert (M2.find k m = Some v) by now rewrite <- H
                     end
                   | eexists ].

    Local Instance M1_find_Proper_eq elt : Proper (E1.eq ==> @M1.Equal _ ==> option_eq eq) (@M1.find elt) | 10.
    Proof. t_Proper_helper. Qed.

    Local Instance M1_MapsTo_Proper_eq_iff elt : Proper (E1.eq ==> eq ==> @M1.Equal _ ==> iff) (@M1.MapsTo elt) | 10.
    Proof. t_Proper_helper. Qed.

    Local Instance M1_In_compat elt : Proper (E1.eq ==> @M1.Equal _ ==> iff) (@M1.In elt) | 10.
    Proof. t_Proper_helper. Qed.

    Local Instance M2_find_Proper_eq elt : Proper (E2.eq ==> @M2.Equal _ ==> option_eq eq) (@M2.find elt) | 10.
    Proof. t_Proper_helper. Qed.

    Local Instance M2_MapsTo_Proper_eq_iff elt : Proper (E2.eq ==> eq ==> @M2.Equal _ ==> iff) (@M2.MapsTo elt) | 10.
    Proof. t_Proper_helper. Qed.

    Local Instance M2_In_compat elt : Proper (E2.eq ==> @M2.Equal _ ==> iff) (@M2.In elt) | 10.
    Proof. t_Proper_helper. Qed.

    Local Instance eq_key_equiv elt : Equivalence (@eq_key elt) | 10.
    Proof.
      split; cbv; intros; break_innermost_match; break_innermost_match_hyps; try ((idtac + symmetry + etransitivity + exfalso); (eassumption + reflexivity)).
    Qed.
    Local Instance eq_key_elt_equiv elt : Equivalence (@eq_key_elt elt) | 10.
    Proof.
      split; cbv; intros; break_innermost_match; break_innermost_match_hyps; destruct_head'_and; split; try ((idtac + symmetry + etransitivity + exfalso); (eassumption + reflexivity)).
    Qed.

    Definition In elt (k : key) (m : t elt) := exists e, MapsTo k e m.
    Definition Empty elt (m : t elt) := forall a e, ~ MapsTo a e m.
    Definition Equal elt (m m' : t elt) := forall y, find y m = find y m'.
    Definition Equiv elt (eq_elt:elt->elt->Prop) m m' :=
      (forall k, In k m <-> In k m') /\
        (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
    Definition Equivb elt (cmp: elt->elt->bool) := Equiv (Cmp cmp).

    Definition In_alt elt : key -> t elt -> Prop := liftKT_ (@M1.In elt) (@M2.In elt).
    Definition Empty_alt elt (m : t elt) : Prop := M1.Empty (fst m) /\ M2.Empty (snd m).
    Definition Equal_alt elt (m m' : t elt) : Prop := M1.Equal (fst m) (fst m') /\ M2.Equal (snd m) (snd m').
    Definition Equiv_alt elt (cmp : elt -> elt -> Prop) (m m' : t elt) : Prop := M1.Equiv cmp (fst m) (fst m') /\ M2.Equiv cmp (snd m) (snd m').
    Definition Equivb_alt elt (cmp : elt -> elt -> bool) (m m' : t elt) : Prop := M1.Equivb cmp (fst m) (fst m') /\ M2.Equivb cmp (snd m) (snd m').

    Local Ltac t_alt_iff :=
      cbv [find MapsTo
                In_alt Equal_alt Empty_alt Equiv_alt Equivb_alt
                In Equal Empty Equiv Equivb
                M1.In M1.Equal M1.Empty M1.Equiv M1.Equivb
                M2.In M2.Equal M2.Empty M2.Equiv M2.Equivb
                liftK_T_ liftKT_];
      repeat first [ progress destruct_head' key
                   | reflexivity
                   | apply conj
                   | progress intros
                   | assumption
                   | progress destruct_head'_and
                   | progress destruct_head'_ex
                   | progress destruct_head' iff
                   | progress specialize_by eauto
                   | progress cbv beta iota in *
                   | match goal with
                     | [ H : forall a : M1.key, _, k : _ |- _ ] => specialize (H k)
                     | [ H : forall a : M2.key, _, k : _ |- _ ] => specialize (H k)
                     | [ H : _, k : _ |- _ ] => specialize (H (inl k))
                     | [ H : _, k : _ |- _ ] => specialize (H (inr k))
                     end
                   | solve [ eauto with nocore ] ].

    Lemma In_alt_iff elt k (s : t elt) : In k s <-> In_alt k s.
    Proof. t_alt_iff. Qed.
    Lemma Equal_alt_iff elt (s s' : t elt) : Equal s s' <-> Equal_alt s s'.
    Proof. t_alt_iff. Qed.
    Lemma Empty_alt_iff elt (s : t elt) : Empty s <-> Empty_alt s.
    Proof. t_alt_iff. Qed.
    Lemma Equiv_alt_iff elt eq_elt (s s' : t elt) : Equiv eq_elt s s' <-> Equiv_alt eq_elt s s'.
    Proof. t_alt_iff. Qed.
    Lemma Equivb_alt_iff elt cmp (s s' : t elt) : Equivb cmp s s' <-> Equivb_alt cmp s s'.
    Proof. t_alt_iff. Qed.

    Create HintDb sum_map_alt discriminated.
    Create HintDb sum_map_alt1 discriminated.
    Create HintDb sum_map_alt2 discriminated.
    Create HintDb sum_map_alt3 discriminated.

    Global
      Hint Unfold
      In_alt
      empty
      is_empty
      mem
      add
      find
      remove
      mem
      map
      mapi
      map2
      elements
      cardinal
      fold
      equal
      MapsTo
      In
      Empty
      Empty_alt
      Equiv_alt
      Equivb_alt
      eq_key
      eq_key_elt
      M1.eq_key
      M1.eq_key_elt
      M2.eq_key
      M2.eq_key_elt
      option_map
      lift
      liftK
      liftT
      liftTT
      lift_TT
      liftTTT
      lift_TTT
      liftK_TT
      liftKT_
      liftK_T_
      liftKTT
      lifthoTT
      sumwise
      : sum_map_alt.

    Hint Rewrite In_alt_iff Empty_alt_iff Equal_alt_iff Equiv_alt_iff Equivb_alt_iff
         M1.cardinal_1
         M1.fold_1
         M2.cardinal_1
         M2.fold_1
         E'.eq_alt
         Bool.andb_true_iff
         InA_app_iff
         map_length
         app_length
         fold_left_map
         fold_left_app
      : sum_map_alt.

    Global Hint Resolve
           M1.MapsTo_1
           M1.mem_1
           M1.empty_1
           M1.is_empty_1
           M1.add_1
           M1.remove_1
           M1.find_1
           M1.elements_1
           M1.equal_1
           M1.map_1
           M1.mapi_1
           M1.map2_1
           M2.MapsTo_1
           M2.mem_1
           M2.empty_1
           M2.is_empty_1
           M2.add_1
           M2.remove_1
           M2.find_1
           M2.elements_1
           M2.equal_1
           M2.map_1
           M2.mapi_1
           M2.map2_1
      : sum_map_alt1.
    Global Hint Resolve
           M1.mem_2
           M1.is_empty_2
           M1.add_2
           M1.remove_2
           M1.find_2
           M1.elements_2
           M1.equal_2
           M1.map_2
           M1.mapi_2
           M1.map2_2
           M2.mem_2
           M2.is_empty_2
           M2.add_2
           M2.remove_2
           M2.find_2
           M2.elements_2
           M2.equal_2
           M2.map_2
           M2.mapi_2
           M2.map2_2
      : sum_map_alt2.
    Global Hint Resolve
           M1.add_3
           M1.remove_3
           M1.elements_3w
           M2.add_3
           M2.remove_3
           M2.elements_3w
      : sum_map_alt3.

    Hint Constructors ex and or
      : sum_map_alt1 sum_map_alt2 sum_map_alt3.
    Hint Extern 10
         => progress unfold M1.In, M2.In in *
             : sum_map_alt1 sum_map_alt2 sum_map_alt3.

    Local Ltac spec_t_step_quick
      := first [ progress intros
               | progress cbn [fst snd] in *
               | apply (f_equal2 (@pair _ _))
               | progress destruct_head'_False
               | rewrite <- andb_lazy_alt
               | progress repeat autorewrite with sum_map_alt in *
               | progress change E1.t with M1.key in *
               | progress change E2.t with M2.key in *
               | progress repeat autounfold with sum_map_alt in *
               | match goal with H : _ |- _ => refine H end
               | congruence
               | reflexivity
               | progress auto
               | exact _
               | progress destruct_head'_and
               | progress destruct_head'_ex
               | progress break_innermost_match_hyps
               | progress break_innermost_match
               | progress destruct_head'_or
               | progress specialize_under_binders_by eassumption
               | progress subst ].

    Global Hint Extern 100
           => spec_t_step_quick
             : sum_map_alt1 sum_map_alt2 sum_map_alt3.

    Local Ltac spec_t
      := repeat first [ spec_t_step_quick
                      | solve [ eauto with sum_map_alt1 nocore ]
                      | solve [ eauto with sum_map_alt2 nocore ]
                      | solve [ eauto with sum_map_alt3 nocore ] ].

    Local Hint Extern 2 => Proper_compose_hint : typeclass_instances.

    Section Spec.

      Variable elt:Type.
      Variable elt' elt'' : Type.
      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.

      Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
      Proof using Type. clear; spec_t. Qed.
      Lemma mem_1 : In x m -> mem x m = true.
      Proof using Type. clear; spec_t. Qed.
      Lemma mem_2 : mem x m = true -> In x m.
      Proof using Type. clear; spec_t. Qed.
      Lemma empty_1 : Empty (@empty elt).
      Proof using Type. clear; spec_t. Qed.
      Lemma is_empty_1 : Empty m -> is_empty m = true.
      Proof using Type. clear; spec_t. Qed.
      Lemma is_empty_2 : is_empty m = true -> Empty m.
      Proof using Type. clear; spec_t. Qed.
      Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
      Proof using Type. clear; spec_t. Qed.
      Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      Proof using Type. clear; spec_t. Qed.
      Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
      Proof using Type. clear; spec_t. Qed.
      Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
      Proof using Type. clear; spec_t. Qed.
      Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      Proof using Type. clear; spec_t. Qed.
      Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
      Proof using Type. clear; spec_t. Qed.
      Lemma find_1 : MapsTo x e m -> find x m = Some e.
      Proof using Type. clear; spec_t. Qed.
      Lemma find_2 : find x m = Some e -> MapsTo x e m.
      Proof using Type. clear; spec_t. Qed.
      Lemma elements_1 :
        MapsTo x e m -> InA (@eq_key_elt _) (x,e) (elements m).
      Proof using Type.
        clear; spec_t.
        all: [ > left | right ]; rewrite InA_map_iff; spec_t.
      Qed.
      Lemma elements_2 :
        InA (@eq_key_elt _) (x,e) (elements m) -> MapsTo x e m.
      Proof using Type.
        clear; spec_t.
        all: try solve [ rewrite InA_map_iff in *; spec_t ].
        all: rewrite InA_alt in *; destruct_head'_ex; rewrite in_map_iff in *.
        all: spec_t.
      Qed.
      Lemma elements_3w : NoDupA (@eq_key _) (elements m).
      Proof using Type.
        pose proof (M1.elements_3w (fst m)).
        pose proof (M2.elements_3w (snd m)).
        spec_t; apply NoDupA_app; try exact _.
        all:
          [ >
          |
          | now intros *; rewrite !InA_alt; setoid_rewrite in_map_iff; spec_t ].
        all: eapply NoDupA_map_inv'; [ | eassumption ]; spec_t.
      Qed.
      Lemma cardinal_1 : cardinal m = length (elements m).
      Proof using Type. clear; spec_t. Qed.

      Lemma fold_1 :
        forall (A : Type) (i : A) (f : key -> elt -> A -> A),
          fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
      Proof using Type. clear; spec_t. Qed.

      Variable cmp : elt -> elt -> bool.

      Lemma equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
      Proof using Type. clear; spec_t. Qed.
      Lemma equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
      Proof using Type. clear; spec_t. Qed.
    End Spec.

    Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
    Proof. clear; spec_t. Qed.
    Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
        In x (map f m) -> In x m.
    Proof. clear; spec_t. Qed.
    Lemma mapi_1 (elt elt':Type)(m: t elt)(x:key)(e:elt)
          (f:key->elt->elt')
      : MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
    Proof.
      pose proof (fun x => @M1.mapi_1 elt elt' (fst m) x e (fun x => f (inl x))).
      pose proof (fun x => @M2.mapi_1 elt elt' (snd m) x e (fun x => f (inr x))).
      spec_t.
      all: eexists.
      all: split; [ | eassumption ].
      all: spec_t.
    Qed.
    Lemma mapi_2
      : forall (elt elt':Type)(m: t elt)(x:key)
               (f:key->elt->elt'), In x (mapi f m) -> In x m.
    Proof. clear; spec_t. Qed.
    Lemma map2_1
      : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	       (x:key)(f:option elt->option elt'->option elt''),
        In x m \/ In x m' ->
        find x (map2 f m m') = f (find x m) (find x m').
    Proof. clear; spec_t. Qed.
    Lemma map2_2
      : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	       (x:key)(f:option elt->option elt'->option elt''),
        In x (map2 f m m') -> In x m \/ In x m'.
    Proof. clear; spec_t. Qed.
  End SumWSfun_gen.
End SumWSfun_gen.

Module SumWSfun (E1 : DecidableTypeOrig) (E2 : DecidableTypeOrig) (M1 : WSfun E1) (M2 : WSfun E2).
  Module _SumWSfun.
    Module Outer := SumWSfun_gen E1 E2 M1 M2.
    Module E := SumDecidableTypeOrig E1 E2.
    Module ECompat <: Outer.ESigCompat E.
      Lemma eq_alt : forall x y, E.eq x y <-> sumwise E1.eq E2.eq x y.
      Proof. cbv [E.eq]; reflexivity. Qed.
    End ECompat.
    Module Inner := Outer.SumWSfun_gen E ECompat.
  End _SumWSfun.
  Include _SumWSfun.Inner.
End SumWSfun.

Module SumUsualWeakMap (E1 : UsualDecidableTypeOrig) (E2 : UsualDecidableTypeOrig) (M1 : WSfun E1) (M2 : WSfun E2).
  Module SumUsualWeakMap <: WS.
    Module Outer := SumWSfun_gen E1 E2 M1 M2.
    Module E := SumUsualDecidableTypeOrig E1 E2.
    Module ECompat <: Outer.ESigCompat E.
      Lemma eq_alt : forall x y, E.eq x y <-> sumwise E1.eq E2.eq x y.
      Proof. cbv [E.eq sumwise E1.eq E2.eq]; intros; break_innermost_match; intuition congruence. Qed.
    End ECompat.
    Module Inner := Outer.SumWSfun_gen E ECompat.
    Include Inner.
  End SumUsualWeakMap.
  Include SumUsualWeakMap.Inner.
End SumUsualWeakMap.

Module SumWeakMap (M1 : WS) (M2 : WS) <: WS.
  Include SumWSfun M1.E M2.E M1 M2.
  Module E := _SumWSfun.E.
End SumWeakMap.

Module SumSfun_gen (E1 : OrderedTypeOrig) (E2 : OrderedTypeOrig) (M1 : Sfun E1) (M2 : Sfun E2).
  Module SumWSfun := SumWSfun_gen E1 E2 M1 M2.
  Module Type ESig := SumWSfun.ESig <+ HasLt <+ HasMiniOrderedType.
  Module Type ESigCompat (E : ESig).
    Include SumWSfun.ESigCompat E.
    Axiom lt_alt : forall x y, E.lt x y <-> sum_le E1.lt E2.lt x y.
  End ESigCompat.
  Module SumSfun_gen (E : ESig) (ECompat : ESigCompat E) <: Sfun E.
    Include SumWSfun.SumWSfun_gen E ECompat.
    Local Existing Instances eq_key_equiv eq_key_elt_equiv.
    Section elt.
      Variable elt:Type.
      Definition lt_key (p p':key*elt) := E.lt (fst p) (fst p').

      Lemma elements_3 m : sort lt_key (elements m).
      Proof using Type.
        pose proof (M1.elements_3 (fst m)).
        pose proof (M2.elements_3 (snd m)).
        cbv [elements lt_key M1.lt_key M2.lt_key] in *.
        setoid_rewrite ECompat.lt_alt; cbv [sum_le].
        eapply SortA_app with (eqA:=@eq_key _); try exact _;
          intros *;
          rewrite ?Sorted_map_iff, ?InA_alt;
          cbn [fst snd]; cbv [eq_key]; try assumption.
        setoid_rewrite in_map_iff.
        setoid_rewrite ECompat.eq_alt.
        cbv [sumwise].
        repeat first [ progress intros
                     | progress subst
                     | progress cbn [fst snd] in *
                     | progress destruct_head'_and
                     | progress destruct_head'_ex
                     | progress break_innermost_match
                     | exact I
                     | exfalso; assumption ].
      Qed.
    End elt.
  End SumSfun_gen.
End SumSfun_gen.

Module SumSfun (E1 : OrderedTypeOrig) (E2 : OrderedTypeOrig) (M1 : Sfun E1) (M2 : Sfun E2).
  Module _SumSfun.
    Module Outer := SumSfun_gen E1 E2 M1 M2.
    Module E := SumOrderedTypeOrig E1 E2.
    Module ECompat <: Outer.ESigCompat E.
      Lemma eq_alt : forall x y, E.eq x y <-> sumwise E1.eq E2.eq x y.
      Proof. cbv [E.eq]; reflexivity. Qed.
      Lemma lt_alt : forall x y, E.lt x y <-> sum_le E1.lt E2.lt x y.
      Proof. cbv [E.lt]; reflexivity. Qed.
    End ECompat.
    Module Inner := Outer.SumSfun_gen E ECompat.
  End _SumSfun.
  Include _SumSfun.Inner.
End SumSfun.

Module SumUsualMap (E1 : UsualOrderedTypeOrig) (E2 : UsualOrderedTypeOrig) (M1 : Sfun E1) (M2 : Sfun E2).
  Module SumUsualMap <: S.
    Module Outer := SumSfun_gen E1 E2 M1 M2.
    Module E := SumUsualOrderedTypeOrig E1 E2.
    Module ECompat <: Outer.ESigCompat E.
      Lemma eq_alt : forall x y, E.eq x y <-> sumwise E1.eq E2.eq x y.
      Proof. cbv [E.eq sumwise E1.eq E2.eq]; intros; break_innermost_match; intuition congruence. Qed.
      Lemma lt_alt : forall x y, E.lt x y <-> sum_le E1.lt E2.lt x y.
      Proof. cbv [E.lt]; reflexivity. Qed.
    End ECompat.
    Module Inner := Outer.SumSfun_gen E ECompat.
    Include Inner.
  End SumUsualMap.
  Include SumUsualMap.Inner.
End SumUsualMap.

Module SumMap (M1 : S) (M2 : S) <: S.
  Include SumSfun M1.E M2.E M1 M2.
  Module E := _SumSfun.E.
End SumMap.

(* TODO:
Module IsoSord (S' : Sord) (Data' : IsoMiniOrderedType S'.Data) (E : IsoMiniOrderedType S'.MapS.E) (S'_iso : IsoMiniOrderedType S') <: Sord <: IsoOrderedType S'.
  Module Data <: IsoOrderedType S'.Data := Data' <+ OT_of_MOT.
  Module MapS <: S := IsoS S'.MapS E.
  Import MapS.

  Definition t := MapS.t Data.t.

  Definition eq : t -> t -> Prop.
    refine (_ S'.eq).
    compute.
    pose MapS.E.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : forall m : t, eq m m.
  Axiom eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Axiom eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Axiom lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Axiom lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

  Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.

  Parameter eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
  Parameter eq_2 : forall m m', eq m m' -> Equivb cmp m m'.

  Parameter compare : forall m1 m2, Compare lt eq m1 m2.
  (** Total ordering between maps. [Data.compare] is a total ordering
      used to compare data associated with equal keys in the two maps. *)


  Include S.
  Include OT_of_MOT.
End IsoSord.
  Definition t := MapS.t Data.t.

  Print IsoMiniOrderedType.
  Definition eq : t -> t -> Prop := S'.eq.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : forall m : t, eq m m.
  Axiom eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Axiom eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Axiom lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Axiom lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

  Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.

  Parameter eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
  Parameter eq_2 : forall m m', eq m m' -> Equivb cmp m m'.

  Parameter compare : forall m1 m2, Compare lt eq m1 m2.
  (** Total ordering between maps. [Data.compare] is a total ordering
      used to compare data associated with equal keys in the two maps. *)

End Sord.

*)
