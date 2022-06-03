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
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Structures.Orders.Iso.
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

Module IsoWSfun (E' : DecidableType) (W' : WSfun E')
       (E : IsoDecidableTypeOrig E') <: WSfun E.
  Local Existing Instances E.Proper_to_ E.Proper_of_.

  Local Instance E_eq_equiv : Equivalence E.eq | 10. split; hnf; eauto. Qed.
  Local Instance E'_eq_equiv : Equivalence E'.eq | 10. split; hnf; eauto. Qed.
  Local Instance W'_eq_key_equiv elt : Equivalence (@W'.eq_key elt) | 10. split; cbv; eauto. Qed.
  Local Instance W'_eq_key_elt_equiv elt : Equivalence (@W'.eq_key_elt elt) | 10. split; repeat intros [? ?]; cbv in *; subst; eauto. Qed.

  Definition key := E.t.

  Global Hint Transparent key : core.

  Definition t := W'.t.

  Definition lift {A} (f : W'.key -> A) : key -> A
    := fun x => f (E.to_ x).
  Definition liftho {A B} (f : (W'.key -> A) -> B) : (key -> A) -> B
    := fun f' => f (fun x => f' (E.of_ x)).

  Definition empty : forall elt, t elt := W'.empty.
  Definition is_empty : forall elt, t elt -> bool := W'.is_empty.
  Definition add elt : key -> elt -> t elt -> t elt := lift (@W'.add elt).
  Definition find elt : key -> t elt -> option elt := lift (@W'.find elt).
  Definition remove elt : key -> t elt -> t elt := lift (@W'.remove elt).
  Definition mem elt : key -> t elt -> bool := lift (@W'.mem elt).
  Definition map : forall elt elt', (elt -> elt') -> t elt -> t elt' := W'.map.
  Definition mapi elt elt' : (key -> elt -> elt') -> t elt -> t elt' := liftho (@W'.mapi elt elt').
  Definition map2 : forall elt elt' elt'', (option elt -> option elt' -> option elt'') -> t elt -> t elt' -> t elt'' := W'.map2.
  Definition elements elt (v : t elt) : list (key * elt) := List.map (fun kv => (E.of_ (fst kv), snd kv)) (W'.elements v).
  Definition cardinal : forall elt, t elt -> nat := W'.cardinal.
  Definition fold elt A : (key -> elt -> A -> A) -> t elt -> A -> A := liftho (@W'.fold elt A).
  Definition equal : forall elt, (elt -> elt -> bool) -> t elt -> t elt -> bool := W'.equal.
  Definition MapsTo elt : key -> elt -> t elt -> Prop := lift (@W'.MapsTo elt).
  Definition In elt : key -> t elt -> Prop := lift (@W'.In elt).
  Definition eq_key elt (p p' : key * elt) : Prop := E.eq (fst p) (fst p'). (* W'.eq_key (E.to_ (fst p), snd p) (E.to_ (fst p'), snd p').*)
  Definition eq_key_elt elt (p p' : key * elt) : Prop := E.eq (fst p) (fst p') /\ snd p = snd p'. (*W'.eq_key_elt (E.to_ (fst p), snd p) (E.to_ (fst p'), snd p').*)

  Local Instance Proper_lift {A R f}
        {f_Proper : Proper (E'.eq ==> R) f}
    : Proper (E.eq ==> R) (@lift A f).
  Proof.
    cbv [lift]; repeat intro; do 2 f_equiv; assumption.
  Qed.

  Local Instance Proper_liftho {A B RA RB f}
        {f_Proper : Proper ((E'.eq ==> RA) ==> RB) f}
    : Proper ((E.eq ==> RA) ==> RB) (@liftho A B f).
  Proof.
    cbv [liftho]; do 3 (repeat intro; f_equiv; try eassumption).
  Qed.

  Local Instance Proper_W'_eq_key_elt_iff elt
    : Proper (eq ==> RelationPairs.RelProd E'.eq eq ==> iff) (@W'.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_W'_eq_key_elt_impl elt
    : Proper (eq ==> RelationPairs.RelProd E'.eq eq ==> impl) (@W'.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_W'_eq_key_elt_flip_impl elt
    : Proper (eq ==> RelationPairs.RelProd E'.eq eq ==> flip impl) (@W'.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_W'_eq_key_elt_iff' elt
    : Proper (@W'.eq_key_elt elt ==> @W'.eq_key_elt elt ==> iff) (@W'.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_W'_eq_key_elt_impl' elt
    : Proper (@W'.eq_key_elt elt ==> @W'.eq_key_elt elt ==> impl) (@W'.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_W'_eq_key_elt_flip_impl' elt
    : Proper (@W'.eq_key_elt elt ==> @W'.eq_key_elt elt ==> flip impl) (@W'.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_W'_eq_key_iff elt
    : Proper (@W'.eq_key elt ==> @W'.eq_key elt ==> iff) (@W'.eq_key elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_W'_eq_key_impl elt
    : Proper (@W'.eq_key elt ==> @W'.eq_key elt ==> impl) (@W'.eq_key elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_W'_eq_key_flip_impl elt
    : Proper (@W'.eq_key elt ==> @W'.eq_key elt ==> flip impl) (@W'.eq_key elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Lemma eq_to_iff x y : E'.eq (E.to_ x) (E.to_ y) <-> E.eq x y.
  Proof.
    split; intro H; [ | now f_equiv ].
    etransitivity; rewrite <- E.of_to; [ | reflexivity ]; f_equiv; assumption.
  Qed.

  Lemma eq_to_of_iff x y
    : E'.eq (E.to_ x) y <-> E.eq x (E.of_ y).
  Proof.
    split; intro H; (rewrite -> H || rewrite <- H);
      (rewrite E.to_of || rewrite E.of_to);
      reflexivity.
  Qed.

  Lemma eq_to_of_iff' x y
    : E'.eq y (E.to_ x) <-> E.eq (E.of_ y) x.
  Proof. split; symmetry; apply eq_to_of_iff; symmetry; assumption. Qed.

  Local Instance W'_Equal_Equivalence elt : Equivalence (@W'.Equal elt) | 10.
  Proof. split; cbv; firstorder eauto using eq_trans. Qed.

  Local Ltac t_Proper_helper :=
    cbv [W'.Equal W'.In Proper respectful option_eq];
    repeat first [ progress intros
                 | progress subst
                 | progress destruct_head'_ex
                 | congruence
                 | reflexivity
                 | eassumption
                 | progress break_innermost_match_hyps
                 | progress break_innermost_match
                 | apply W'.find_2
                 | match goal with
                   | [ H : E'.eq ?x ?y |- _ ]
                     => (idtac + symmetry in H); eapply W'.MapsTo_1 in H; [ | apply W'.find_2; eassumption ]
                   | [ H : _ |- _ ] => apply W'.find_1 in H
                   | [ |- Some _ = None ] => exfalso
                   | [ |- ?x = None ] => destruct x eqn:?
                   | [ |- _ <-> _ ] => split
                   | [ H : W'.find ?k ?m = Some ?v, H' : forall k', W'.find k' ?m = W'.find k' ?m' |- _ ]
                     => unique assert (W'.find k m' = Some v) by now rewrite <- H
                   | [ H : W'.find ?k ?m' = Some ?v, H' : forall k', W'.find k' ?m = W'.find k' ?m' |- _ ]
                     => unique assert (W'.find k m = Some v) by now rewrite <- H
                   end
                 | eexists ].

  Local Instance W'_find_Proper_eq elt : Proper (E'.eq ==> @W'.Equal _ ==> option_eq eq) (@W'.find elt) | 10.
  Proof. t_Proper_helper. Qed.

  Local Instance W'_MapsTo_Proper_eq_iff elt : Proper (E'.eq ==> eq ==> @W'.Equal _ ==> iff) (@W'.MapsTo elt) | 10.
  Proof. t_Proper_helper. Qed.

  Local Instance W'_In_compat elt : Proper (E'.eq ==> @W'.Equal _ ==> iff) (@W'.In elt) | 10.
  Proof. t_Proper_helper. Qed.

  Definition Empty elt (m : t elt) := forall a e, ~ MapsTo a e m.
  Definition Equal elt (m m' : t elt) := forall y, find y m = find y m'.
  Definition Equiv elt (eq_elt:elt->elt->Prop) m m' :=
    (forall k, In k m <-> In k m') /\
      (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
  Definition Equivb elt (cmp: elt->elt->bool) := Equiv (Cmp cmp).

  Definition Empty_alt : forall elt, t elt -> Prop := W'.Empty.
  Definition Equal_alt : forall elt, t elt -> t elt -> Prop := W'.Equal.
  Definition Equiv_alt : forall elt, (elt -> elt -> Prop) -> t elt -> t elt -> Prop := W'.Equiv.
  Definition Equivb_alt : forall elt, (elt->elt->bool) -> t elt -> t elt -> Prop := W'.Equivb.

  Lemma forall_lift_key_dep {A} f (P : key -> A -> Prop) R
        (f_Proper : Proper (E'.eq ==> R) f)
        (P_Proper : Proper (E.eq ==> R ==> Basics.impl) P)
    : (forall a : key, P a (@lift A f a)) <-> (forall a : W'.key, P (E.of_ a) (f a)).
  Proof.
    cbv [lift].
    split; intro H; intro x; [ specialize (H (E.of_ x)) | specialize (H (E.to_ x)) ].
    all: eapply P_Proper; try eassumption.
    all: f_equiv.
    all: apply E.to_of + apply E.of_to.
  Qed.

  Local Ltac t_alt_iff :=
    cbv [In find MapsTo
            Equal_alt Empty_alt Equiv_alt Equivb_alt
            Equal Empty Equiv Equivb];
    let rec get_P lift_f P :=
      lazymatch P with
      | fun a : ?A => ?P
        => let P' := fresh in
           let a' := fresh in
           constr:(fun a' : A
                   => ltac:(let P := constr:(match a' with a => P end) in
                            let res := get_P (lift_f a') P in
                            exact res))
      | _
        => lazymatch (eval pattern lift_f in P) with
           | ?P _ => exact P
           end
      end in
    let rec handle_one_lift LHS :=
      lazymatch LHS with
      | ?G1 /\ ?G2
        => handle_one_lift G1; [ handle_one_lift G2 | .. ]
      | context[lift ?f]
        => lazymatch LHS with
           | (forall a : key, @?P a)
             => let P' := get_P (lift f) P in
                setoid_rewrite (@forall_lift_key_dep _ f P')
           | _ => fail 0 "unhandled" LHS (*
|
         | [ |-                (exists a : elt, @?P a) <-> _ ]
           => let P' := get_P (lift f) P in
              setoid_rewrite (@exists_lift_dep _ f P')*)
           end
      | _ => idtac
      end in
    let rec handle_lift _ :=
      let LHS := lazymatch goal with |- ?LHS <-> _ => LHS end in
      lazymatch LHS with
      | context[lift ?f] => handle_one_lift LHS; [ handle_lift () | .. ]
      | _ => idtac
      end in
    handle_lift ();
    try exact _;
    [ try reflexivity
    | try solve [ cbv [Proper respectful Basics.impl Basics.flip option_eq];
                  intros; split_iff;
                  specialize_under_binders_by reflexivity;
                  specialize_all_ways; break_innermost_match_hyps; inversion_option; subst;
                  firstorder eauto; congruence ]..
    ].

  Lemma Equal_alt_iff elt (s s' : t elt) : Equal s s' <-> Equal_alt s s'.
  Proof. t_alt_iff. Qed.
  Lemma Empty_alt_iff elt (s : t elt) : Empty s <-> Empty_alt s.
  Proof. t_alt_iff. Qed.
  Lemma Equiv_alt_iff elt eq_elt (s s' : t elt) : Equiv eq_elt s s' <-> Equiv_alt eq_elt s s'.
  Proof. t_alt_iff. Qed.
  Lemma Equivb_alt_iff elt cmp (s s' : t elt) : Equivb cmp s s' <-> Equivb_alt cmp s s'.
  Proof. t_alt_iff. Qed.

  Create HintDb iso_map_alt discriminated.
  Create HintDb iso_map_alt1 discriminated.
  Create HintDb iso_map_alt2 discriminated.
  Create HintDb iso_map_alt3 discriminated.

  Global
  Hint Unfold
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
       W'.eq_key
       W'.eq_key_elt
       option_map
       lift
       liftho
    : iso_map_alt.

  Hint Rewrite Empty_alt_iff Equal_alt_iff Equiv_alt_iff Equivb_alt_iff
       eq_to_iff
       eq_to_of_iff
       eq_to_of_iff'
       (*W'.is_empty_spec
       W'.mem_spec
       W'.add_spec
       W'.remove_spec
       W'.singleton_spec
       W'.union_spec
       W'.inter_spec
       W'.diff_spec
       W'.equal_spec
       W'.subset_spec
       W'.fold_spec
       W'.for_all_spec
       W'.exists_spec
       W'.partition_spec1
       W'.partition_spec2
       W'.filter_spec
       W'.cardinal_spec *)
       W'.cardinal_1
       W'.fold_1
       E.of_to
       E.to_of
       map_length
       fold_left_map
    : iso_map_alt.

  Global Hint Resolve
         W'.MapsTo_1
         W'.mem_1
         W'.empty_1
         W'.is_empty_1
         W'.add_1
         W'.remove_1
         W'.find_1
         W'.elements_1
         W'.equal_1
         W'.map_1
         W'.mapi_1
         W'.map2_1
    : iso_map_alt1.
  Global Hint Resolve
         W'.mem_2
         W'.is_empty_2
         W'.add_2
         W'.remove_2
         W'.find_2
         W'.elements_2
         W'.equal_2
         W'.map_2
         W'.mapi_2
         W'.map2_2
    : iso_map_alt2.
  Global Hint Resolve
         W'.add_3
         W'.remove_3
         W'.elements_3w
    : iso_map_alt3.
  Global Hint Extern 10 => rewrite eq_to_iff in *
             : iso_map_alt1 iso_map_alt2 iso_map_alt3.

  (*Local Hint Resolve
        W'.empty_spec
        W'.elements_spec2w
        W'.choose_spec1
        W'.choose_spec2
    : core.*)

  Local Ltac spec_t_step_quick
    := first [ progress intros
             | progress cbn [fst snd] in *
             | apply (f_equal2 (@pair _ _))
             | progress repeat autorewrite with iso_map_alt in *
             | progress repeat autounfold with iso_map_alt in *
             | match goal with H : _ |- _ => refine H end
             | reflexivity
             | progress auto
             | exact _
             | progress destruct_head'_and
             | progress destruct_head'_ex
             | progress specialize_under_binders_by eassumption ].

  Global Hint Extern 100
         => spec_t_step_quick
           : iso_map_alt1 iso_map_alt2 iso_map_alt3.

  Local Ltac spec_t
    := repeat first [ spec_t_step_quick
                    | solve [ eauto with iso_map_alt1 nocore ]
                    | solve [ eauto with iso_map_alt2 nocore ]
                    | solve [ eauto with iso_map_alt3 nocore ] ].

  Local Hint Extern 2 => Proper_compose_hint : typeclass_instances.

  Section Spec.

    Variable elt:Type.
    Variable elt' elt'' : Type.
    Variable m m' m'' : t elt.
    Variable x y z : key.
    Variable e e' : elt.

    Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
    Proof using Type. spec_t. Qed.
    Lemma mem_1 : In x m -> mem x m = true.
    Proof using Type. spec_t. Qed.
    Lemma mem_2 : mem x m = true -> In x m.
    Proof using Type. spec_t. Qed.
    Lemma empty_1 : Empty (@empty elt).
    Proof using Type. spec_t. Qed.
    Lemma is_empty_1 : Empty m -> is_empty m = true.
    Proof using Type. spec_t. Qed.
    Lemma is_empty_2 : is_empty m = true -> Empty m.
    Proof using Type. spec_t. Qed.
    Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
    Proof using Type. spec_t. Qed.
    Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
    Proof using Type. spec_t. Qed.
    Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
    Proof using Type. spec_t. Qed.
    Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
    Proof using Type. spec_t. Qed.
    Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
    Proof using Type. spec_t. Qed.
    Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
    Proof using Type. spec_t. Qed.
    Lemma find_1 : MapsTo x e m -> find x m = Some e.
    Proof using Type. spec_t. Qed.
    Lemma find_2 : find x m = Some e -> MapsTo x e m.
    Proof using Type. spec_t. Qed.
    Lemma elements_1 :
      MapsTo x e m -> InA (@eq_key_elt _) (x,e) (elements m).
    Proof using Type. spec_t. rewrite InA_map_iff; spec_t. Qed.
    Lemma elements_2 :
      InA (@eq_key_elt _) (x,e) (elements m) -> MapsTo x e m.
    Proof using Type. spec_t. rewrite InA_map_iff in *; spec_t. Qed.
    Lemma elements_3w : NoDupA (@eq_key _) (elements m).
    Proof using Type.
      pose proof (W'.elements_3w m).
      spec_t.
      apply NoDupA_map_inv with (f:=fun p => (E.to_ (fst p), snd p)) (eqB:=@W'.eq_key _); [ cbv; intros *; break_innermost_match; now spec_t | ].
      rewrite List.map_map.
      setoid_rewrite (_ : eqlistA (@W'.eq_key _) (List.map _ _) _);
        [
        | eapply Proper_map; [ | reflexivity ] ];
        [ rewrite List.map_id; eassumption
        | cbv -[fst snd]; cbn ].
      spec_t.
    Qed.
    Lemma cardinal_1 : cardinal m = length (elements m).
    Proof using Type. spec_t. Qed.

    Lemma fold_1 :
      forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
    Proof using Type. spec_t. Qed.

    Variable cmp : elt -> elt -> bool.

    Lemma equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
    Proof using Type. spec_t. Qed.
    Lemma equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
    Proof using Type. spec_t. Qed.
  End Spec.

  Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
      MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof. spec_t. Qed.
  Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
      In x (map f m) -> In x m.
  Proof. spec_t. Qed.
  Lemma mapi_1 (elt elt':Type)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt')
    : MapsTo x e m ->
      exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof.
    pose proof (fun x => @W'.mapi_1 elt elt' m x e (fun x => f (E.of_ x))).
    spec_t.
    eexists.
    split; [ | eassumption ].
    spec_t.
  Qed.
  Lemma mapi_2
    : forall (elt elt':Type)(m: t elt)(x:key)
             (f:key->elt->elt'), In x (mapi f m) -> In x m.
  Proof. spec_t. Qed.
  Lemma map2_1
    : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	     (x:key)(f:option elt->option elt'->option elt''),
      In x m \/ In x m' ->
      find x (map2 f m m') = f (find x m) (find x m').
  Proof. spec_t. Qed.
  Lemma map2_2
    : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	     (x:key)(f:option elt->option elt'->option elt''),
      In x (map2 f m m') -> In x m \/ In x m'.
  Proof. spec_t. Qed.
End IsoWSfun.

Module IsoWS (W' : WS) (E : IsoDecidableTypeOrig W'.E) <: WS.
  Module E := E.
  Global Remove Hints E.eq_refl E.eq_sym E.eq_trans : core.
  Include IsoWSfun W'.E W' E.
End IsoWS.

Module IsoSfun (E' : OrderedTypeOrig) (W' : Sfun E') (E : IsoOrderedTypeOrig E') <: Sfun E.
  Include IsoWSfun E' W' E.
  Section elt.
    Variable elt:Type.
    Definition lt_key (p p':key*elt) := E.lt (fst p) (fst p').

    Lemma elements_3 m : sort lt_key (elements m).
    Proof using Type.
      pose proof (W'.elements_3 m).
      cbv [elements lt_key W'.lt_key] in *.
      rewrite Sorted_map_iff.
      cbn [fst snd].
      eapply Sorted_Proper_impl; [ .. | reflexivity | eassumption ].
      cbv; intros; destruct_head'_prod; destruct_head'_and; subst.
      apply E.Proper_of_lt; assumption.
    Qed.
  End elt.
End IsoSfun.

Module IsoS (S' : S) (E' : IsoMiniOrderedType S'.E) <: S.
  Module E <: IsoOrderedTypeOrig S'.E := E' <+ OT_of_MOT.
  Global Remove Hints E.eq_refl E.eq_sym E.eq_trans : core.
  Include IsoSfun S'.E S' E.
End IsoS.

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
