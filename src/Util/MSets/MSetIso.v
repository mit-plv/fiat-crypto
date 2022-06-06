Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.MSets.MSetInterface.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.Compose.
Require Import Crypto.Util.Logic.Forall.
Require Import Crypto.Util.Logic.Exists.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.

Local Set Implicit Arguments.

Module IsoWSetsOn (E' : Equalities.DecidableType) (W' : WSetsOn E')
       (E : IsoDecidableType E') <: WSetsOn E.
  Local Existing Instances E.Proper_to_ E.Proper_of_ W'.In_compat.

  Definition elt := E.t.
  Definition t := W'.t.

  Definition lift {A} (f : W'.elt -> A) : elt -> A
    := fun x => f (E.to_ x).
  Definition liftho {A B} (f : (W'.elt -> A) -> B) : (elt -> A) -> B
    := fun f' => f (fun x => f' (E.of_ x)).

  Definition empty : t := W'.empty.
  Definition is_empty : t -> bool := W'.is_empty.
  Definition mem : elt -> t -> bool := lift W'.mem.
  Definition add : elt -> t -> t := lift W'.add.
  Definition remove : elt -> t -> t := lift W'.remove.
  Definition singleton : elt -> t := lift W'.singleton.
  Definition union : t -> t -> t := W'.union.
  Definition inter : t -> t -> t := W'.inter.
  Definition diff : t -> t -> t := W'.diff.
  Definition equal : t -> t -> bool := W'.equal.
  Definition subset : t -> t -> bool := W'.subset.
  Definition fold B : (elt -> B -> B) -> t -> B -> B := liftho (@W'.fold B).
  Definition for_all : (elt -> bool) -> t -> bool := liftho W'.for_all.
  Definition exists_ : (elt -> bool) -> t -> bool := liftho W'.exists_.
  Definition filter : (elt -> bool) -> t -> t := liftho W'.filter.
  Definition partition : (elt -> bool) -> t -> t * t := liftho W'.partition.
  Definition cardinal : t -> nat := W'.cardinal.
  Definition elements (v : t) : list elt := List.map E.of_ (W'.elements v).
  Definition choose (v : t) : option elt := option_map E.of_ (W'.choose v).
  Definition In : elt -> t -> Prop := lift W'.In.

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

  Local Instance In_compat : Proper (E.eq ==> eq ==> iff) In := _.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Definition Equal_alt : t -> t -> Prop := W'.Equal.
  Definition Subset_alt : t -> t -> Prop := W'.Subset.
  Definition Empty_alt : t -> Prop := W'.Empty.
  Definition For_all_alt : (elt -> Prop) -> t -> Prop := liftho W'.For_all.
  Definition Exists_alt : (elt -> Prop) -> t -> Prop := liftho W'.Exists.

  Lemma forall_lift_dep {A} f (P : elt -> A -> Prop) R
        (f_Proper : Proper (E'.eq ==> R) f)
        (P_Proper : Proper (E.eq ==> R ==> Basics.impl) P)
    : (forall a : elt, P a (@lift A f a)) <-> (forall a : W'.elt, P (E.of_ a) (f a)).
  Proof.
    cbv [lift].
    split; intro H; intro x; [ specialize (H (E.of_ x)) | specialize (H (E.to_ x)) ].
    all: eapply P_Proper; try eassumption.
    all: f_equiv.
    all: apply E.to_of + apply E.of_to.
  Qed.

  Lemma forall_lift {A} f (P : A -> Prop) R
        (f_Proper : Proper (E'.eq ==> R) f)
        (P_Proper : Proper (R ==> Basics.impl) P)
    : (forall a : elt, P (@lift A f a)) <-> (forall a : W'.elt, P (f a)).
  Proof.
    apply (@forall_lift_dep A f (fun _ => P) R); [ | intros ??? ]; assumption.
  Qed.

  Lemma exists_lift_dep {A} f (P : elt -> A -> Prop) R
        (f_Proper : Proper (E'.eq ==> R) f)
        (P_Proper : Proper (E.eq ==> R ==> Basics.impl) P)
    : (exists a : elt, P a (@lift A f a)) <-> (exists a : W'.elt, P (E.of_ a) (f a)).
  Proof.
    cbv [lift].
    split; intros [x H]; [ exists (E.to_ x) | exists (E.of_ x) ].
    all: eapply P_Proper; try eassumption.
    all: f_equiv.
    all: symmetry; apply E.to_of + apply E.of_to.
  Qed.

  Lemma exists_lift {A} f (P : A -> Prop) R
        (f_Proper : Proper (E'.eq ==> R) f)
        (P_Proper : Proper (R ==> Basics.impl) P)
    : (exists a : elt, P (@lift A f a)) <-> (exists a : W'.elt, P (f a)).
  Proof.
    apply (@exists_lift_dep A f (fun _ => P) R); [ | intros ??? ]; assumption.
  Qed.

  Local Ltac t_alt_iff :=
    cbv [In
           Equal_alt Subset_alt Empty_alt For_all_alt Exists_alt
           Equal Subset Empty For_all Exists];
    let get_P lift_f P :=
        lazymatch P with
        | fun a : ?A => ?P
          => let P' := fresh in
             constr:(
               fun a : elt
               => match P return _ with
                  | P'
                    => ltac:(let P := (eval cbv delta [P'] in P') in
                             clear P';
                             lazymatch (eval pattern (lift_f a) in P) with
                             | ?P _ => exact P
                             end)
                  end)
        end in
    lazymatch goal with
    | [ |- context[lift ?f] ]
      => lazymatch goal with
         | [ |- (forall a : elt, @?P a) <-> _ ]
           => let P' := get_P (lift f) P in
              setoid_rewrite (@forall_lift_dep _ f P')
         | [ |- (exists a : elt, @?P a) <-> _ ]
           => let P' := get_P (lift f) P in
              setoid_rewrite (@exists_lift_dep _ f P')
         end
    end;
    try exact _;
    [ try reflexivity
    | try solve [ cbv [Proper respectful Basics.impl Basics.flip];
                  intros; split_iff;
                  repeat match goal with
                         | [ H : forall x y, x = y -> _ |- _ ] => specialize (fun x => H x x eq_refl)
                         end;
                  firstorder eauto ]..
    ].

  Lemma Equal_alt_iff s s' : Equal s s' <-> Equal_alt s s'.
  Proof. t_alt_iff. Qed.
  Lemma Subset_alt_iff s s' : Subset s s' <-> Subset_alt s s'.
  Proof. t_alt_iff. Qed.
  Lemma Empty_alt_iff s : Empty s <-> Empty_alt s.
  Proof. t_alt_iff. Qed.
  Lemma For_all_alt_iff P s
        (P_Proper : Proper (E.eq ==> iff) P)
    : For_all P s <-> For_all_alt P s.
  Proof. t_alt_iff. Qed.
  Lemma Exists_alt_iff P s
        (P_Proper : Proper (E.eq ==> iff) P)
    : Exists P s <-> Exists_alt P s.
  Proof. t_alt_iff. Qed.

  Local Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Local Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).

  Definition eq := Equal.
  Local Instance eq_equiv : Equivalence eq.
  Proof.
    cbv [eq Equal]; split; repeat intro.
    { reflexivity. }
    { symmetry; auto. }
    { etransitivity; eauto. }
  Qed.
  Lemma eq_dec (x y : t) : {eq x y} + {~eq x y}.
  Proof.
    destruct (W'.eq_dec x y) as [H|H]; [ left | right ];
      cbv [eq]; rewrite Equal_alt_iff; cbv [Equal_alt]; assumption.
  Defined.

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

  Create HintDb iso_set_alt discriminated.

  Hint Unfold
       empty
       is_empty
       mem
       add
       remove
       singleton
       union
       inter
       diff
       equal
       subset
       fold
       for_all
       exists_
       filter
       partition
       cardinal
       elements
       choose
       In
       option_map
       lift
       liftho
       Empty_alt Equal_alt
    : iso_set_alt.

  Hint Rewrite Empty_alt_iff Equal_alt_iff Subset_alt_iff For_all_alt_iff Exists_alt_iff
       eq_to_iff
       W'.is_empty_spec
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
       W'.cardinal_spec
       E.of_to
       E.to_of
       map_length
       fold_left_map
    : iso_set_alt.

  Local Hint Resolve
        W'.empty_spec
        W'.elements_spec2w
        W'.choose_spec1
        W'.choose_spec2
    : core.

  Local Ltac spec_t
    := repeat first [ reflexivity
                    | progress intros
                    | progress repeat autorewrite with iso_set_alt
                    | progress repeat autounfold with iso_set_alt in *
                    | progress auto
                    | exact _ ].

  Local Hint Extern 2 => Proper_compose_hint : typeclass_instances.

  Section Spec.
    Variable s s': t.
    Variable x y : elt.
    Variable f : elt -> bool.
    Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).
    Lemma mem_spec : mem x s = true <-> In x s.
    Proof using Type. spec_t. Qed.
    Lemma equal_spec : equal s s' = true <-> s[=]s'.
    Proof using Type. spec_t. Qed.
    Lemma subset_spec : subset s s' = true <-> s[<=]s'.
    Proof using Type. spec_t. Qed.
    Lemma empty_spec : Empty empty.
    Proof using Type. spec_t. Qed.
    Lemma is_empty_spec : is_empty s = true <-> Empty s.
    Proof using Type. spec_t. Qed.
    Lemma add_spec : In y (add x s) <-> E.eq y x \/ In y s.
    Proof using Type. spec_t. Qed.
    Lemma remove_spec : In y (remove x s) <-> In y s /\ ~E.eq y x.
    Proof using Type. spec_t. Qed.
    Lemma singleton_spec : In y (singleton x) <-> E.eq y x.
    Proof using Type. spec_t. Qed.
    Lemma union_spec : In x (union s s') <-> In x s \/ In x s'.
    Proof using Type. spec_t. Qed.
    Lemma inter_spec : In x (inter s s') <-> In x s /\ In x s'.
    Proof using Type. spec_t. Qed.
    Lemma diff_spec : In x (diff s s') <-> In x s /\ ~In x s'.
    Proof using Type. spec_t. Qed.
    Lemma fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A),
        fold f s i = fold_left (flip f) (elements s) i.
    Proof using Type. spec_t. Qed.
    Lemma cardinal_spec : cardinal s = length (elements s).
    Proof using Type. spec_t. Qed.
    Lemma filter_spec : compatb f ->
                        (In x (filter f s) <-> In x s /\ f x = true).
    Proof using Type. spec_t. Qed.
    Lemma for_all_spec : compatb f ->
                         (for_all f s = true <-> For_all (fun x => f x = true) s).
    Proof using Type. spec_t. repeat intro; repeat (f_equiv; trivial). Qed.
    Lemma exists_spec : compatb f ->
                        (exists_ f s = true <-> Exists (fun x => f x = true) s).
    Proof using Type. spec_t. repeat intro; repeat (f_equiv; trivial). Qed.
    Lemma partition_spec1 : compatb f ->
                            fst (partition f s) [=] filter f s.
    Proof using Type. spec_t. Qed.
    Lemma partition_spec2 : compatb f ->
                            snd (partition f s) [=] filter (fun x => negb (f x)) s.
    Proof using Type. spec_t. Qed.
    Lemma elements_spec1 : InA E.eq x (elements s) <-> In x s.
    Proof using Type.
      cbv [In lift elements]; rewrite <- W'.elements_spec1.
      spec_t.
      apply InA_map_iff, eq_to_of_iff.
    Qed.
    Lemma elements_spec2w : NoDupA E.eq (elements s).
    Proof using Type.
      spec_t.
      apply NoDupA_map_inv with (f:=E.to_) (eqB:=E'.eq); try exact _; [].
      rewrite List.map_map.
      setoid_rewrite (Proper_map _ _ _ _ _ _);
        [ rewrite List.map_id
        | intros ???; etransitivity; [ eapply E.to_of | eassumption ]
        | reflexivity ].
      apply W'.elements_spec2w.
    Qed.
    Lemma choose_spec1 : choose s = Some x -> In x s.
    Proof using Type.
      cbv [In choose option_map lift].
      break_innermost_match; intros; inversion_option; subst.
      rewrite E.to_of; auto.
    Qed.
    Lemma choose_spec2 : choose s = None -> Empty s.
    Proof using Type. spec_t; break_innermost_match_hyps; inversion_option; auto. Qed.
  End Spec.
End IsoWSetsOn.

Module IsoSetsOn (E' : Orders.OrderedType) (W' : SetsOn E')
       (E : IsoOrderedType E') <: SetsOn E.
  Local Existing Instances E.Proper_to_ E.Proper_of_ E.Proper_of_lt E.Proper_to_lt W'.In_compat.
  Include (IsoWSetsOn E' W' E).

  Definition compare : t -> t -> comparison := W'.compare.
  Definition min_elt (v : t) : option elt := option_map E.of_ (W'.min_elt v).
  Definition max_elt (v : t) : option elt := option_map E.of_ (W'.max_elt v).
  Definition lt : t -> t -> Prop := W'.lt.
  Instance lt_strorder : StrictOrder lt | 1 := W'.lt_strorder.
  Instance lt_compat : Proper (eq==>eq==>iff) lt | 1.
  Proof.
    cbv [eq]; intros ?? H ?? H'; apply W'.lt_compat;
      autorewrite with iso_set_alt in *;
      assumption.
  Qed.

  Hint Unfold compare min_elt max_elt lt : iso_set_alt.

  Local Ltac spec_t'
    := repeat first [ reflexivity
                    | progress intros
                    | progress repeat autorewrite with iso_set_alt in *
                    | progress repeat autounfold with iso_set_alt in *
                    | progress auto
                    | exact _
                    | progress break_innermost_match_hyps
                    | progress subst
                    | progress inversion_option
                    | match goal with
                      | [ H : E'.lt ?x (E.to_ ?y) |- E.lt (E.of_ ?x) ?y ]
                        => rewrite <- (E.of_to y); apply E.Proper_of_lt; assumption
                      | [ H : E.lt ?x (E.of_ ?y) |- E'.lt (E.to_ ?x) ?y ]
                        => rewrite <- (E.to_of y); apply E.Proper_to_lt; assumption
                      | [ H : E'.lt (E.to_ ?y) ?x |- E.lt ?y (E.of_ ?x) ]
                        => rewrite <- (E.of_to y); apply E.Proper_of_lt; assumption
                      | [ H : E.lt (E.of_ ?y) ?x |- E'.lt ?y (E.to_ ?x) ]
                        => rewrite <- (E.to_of y); apply E.Proper_to_lt; assumption
                      end ].

  Section Spec.
    Variable s s': t.
    Variable x y : elt.

    Lemma compare_spec : CompSpec eq lt s s' (compare s s').
    Proof using Type.
      cbv [compare eq lt].
      destruct (W'.compare_spec s s'); constructor; now spec_t'.
    Qed.

    Lemma elements_spec2 : sort E.lt (elements s).
    Proof using Type.
      cbv [elements].
      induction (W'.elements_spec2 s); cbn [List.map]; constructor;
        try assumption.
      rewrite InfA_alt with (eqA:=E'.eq) in * by (assumption || exact _).
      rewrite InfA_alt with (eqA:=E.eq) in * by (assumption || exact _).
      intros v H'.
      let H := match goal with H : forall y, InA _ y _ -> E'.lt _ y |- _ => H end in
      specialize (H (E.to_ v));
        rewrite InA_map_iff in H'; [ specialize (H H') | apply eq_to_of_iff ].
      spec_t'.
    Qed.

    Ltac elt_spec lem :=
      spec_t';
      match goal with H : _ = _ :> option _ |- _ => eapply lem in H; [ | eassumption.. ] end;
      try match goal with H : ~ ?R _ _ |- ~ _ => intro; apply H; clear H end;
      spec_t'.

    Lemma min_elt_spec1 : min_elt s = Some x -> In x s.
    Proof using Type. elt_spec W'.min_elt_spec1. Qed.
    Lemma min_elt_spec2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
    Proof using Type. elt_spec W'.min_elt_spec2. Qed.
    Lemma min_elt_spec3 : min_elt s = None -> Empty s.
    Proof using Type. elt_spec W'.min_elt_spec3. Qed.

    Lemma max_elt_spec1 : max_elt s = Some x -> In x s.
    Proof using Type. elt_spec W'.max_elt_spec1. Qed.
    Lemma max_elt_spec2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
    Proof using Type. elt_spec W'.max_elt_spec2. Qed.
    Lemma max_elt_spec3 : max_elt s = None -> Empty s.
    Proof using Type. elt_spec W'.max_elt_spec3. Qed.

    Lemma choose_spec3 : choose s = Some x -> choose s' = Some y ->
                         Equal s s' -> E.eq x y.
    Proof using Type.
      spec_t'.
      eapply E.Proper_of_, W'.choose_spec3; eassumption.
    Qed.
  End Spec.
End IsoSetsOn.

Module IsoWSets (W' : WSets) (E0 : IsoDecidableType W'.E) <: WSets.
  Module E := E0.
  Include IsoWSetsOn W'.E W' E.
End IsoWSets.

Module IsoSets (W' : Sets) (E0 : IsoOrderedType W'.E) <: Sets.
  Module E := E0.
  Include IsoSetsOn W'.E W' E.
End IsoSets.
