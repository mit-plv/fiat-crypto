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
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Structures.Equalities.Sum.
Require Import Crypto.Util.Structures.Orders.Sum.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.

Local Set Implicit Arguments.

Module WSumSetsOn (E1 : Equalities.DecidableType) (E2 : Equalities.DecidableType)
       (W1 : WSetsOn E1) (W2 : WSetsOn E2). (* <: WSetsOn (SumDecidableType E1 E2). *)
  Module Import WSumSetsOn_E.
    Module E := SumDecidableType E1 E2.
  End WSumSetsOn_E.
  Local Existing Instances E.eq_equiv W1.In_compat W2.In_compat.

  Definition elt := E.t.
  Definition t := (W1.t * W2.t)%type.

  Definition lift_tT {A B C} (F : A -> B -> C)
             (f1 : W1.t -> A) (f2 : W2.t -> B)
    : t -> C
    := fun x => F (f1 (fst x)) (f2 (snd x)).

  Definition lift_ttT {A B C} (F : A -> B -> C)
             (f1 : W1.t -> W1.t -> A) (f2 : W2.t -> W2.t -> B)
    : t -> t -> C
    := fun x y => F (f1 (fst x) (fst y)) (f2 (snd x) (snd y)).

  Definition lift_eT {A} (f1 : E1.t -> A) (f2 : E2.t -> A)
    : elt -> A
    := fun e => match e with
                | inl e => f1 e
                | inr e => f2 e
                end.

  Definition drop_eT {A} (f : elt -> A)
    : (E1.t -> A) * (E2.t -> A)
    := (fun e => f (inl e), fun e => f (inr e)).

  Definition lift_et (f1 : E1.t -> W1.t) (f2 : E2.t -> W2.t)
    : elt -> t
    := fun e => (match e with
                 | inl e => f1 e
                 | inr _ => W1.empty
                 end,
                 match e with
                 | inl _ => W2.empty
                 | inr e => f2 e
                 end).

  Definition lift_etT {A} (f1 : E1.t -> W1.t -> A) (f2 : E2.t -> W2.t -> A)
    : elt -> t -> A
    := fun e x => match e with
                  | inl e => f1 e (fst x)
                  | inr e => f2 e (snd x)
                  end.

  Definition lift_ett (f1 : E1.t -> W1.t -> W1.t) (f2 : E2.t -> W2.t -> W2.t)
    : elt -> t -> t
    := fun e x => (match e with
                   | inl e => f1 e (fst x)
                   | inr _ => fst x
                   end,
                   match e with
                   | inl _ => snd x
                   | inr e => f2 e (snd x)
                   end).

  Definition lift_ttt (f1 : W1.t -> W1.t -> W1.t) (f2 : W2.t -> W2.t -> W2.t)
    : t -> t -> t
    := fun x y => (f1 (fst x) (fst y), f2 (snd x) (snd y)).

  Definition lift_eT_tT {A B} (F : B -> B -> B)
             (f1 : (E1.t -> A) -> W1.t -> B) (f2 : (E2.t -> A) -> W2.t -> B)
    : (elt -> A) -> t -> B
    := fun f x => F (f1 (fst (drop_eT f)) (fst x))
                    (f2 (snd (drop_eT f)) (snd x)).

  Definition lift_eT_tt {A}
             (f1 : (E1.t -> A) -> W1.t -> W1.t) (f2 : (E2.t -> A) -> W2.t -> W2.t)
    : (elt -> A) -> t -> t
    := fun f x => (f1 (fst (drop_eT f)) (fst x),
                   f2 (snd (drop_eT f)) (snd x)).

  Definition lift_eT_tt2 {A}
             (f1 : (E1.t -> A) -> W1.t -> W1.t * W1.t) (f2 : (E2.t -> A) -> W2.t -> W2.t * W2.t)
    : (elt -> A) -> t -> t * t
    := fun f x => let f1v := f1 (fst (drop_eT f)) (fst x) in
                  let f2v := f2 (snd (drop_eT f)) (snd x) in
                  ((fst f1v, fst f2v), (snd f1v, snd f2v)).

  Definition choose_option {A} (x : option A) (y : option A) : option A
    := match x, y with
       | Some v, _ | _, Some v => Some v
       | None, None => None
       end.

  Definition choose_option_sum {A B} (v1 : option A) (v2 : option B)
    := choose_option
         (option_map (@inl _ _) v1)
         (option_map (@inr _ _) v2).

  Definition choose_option_sum_rev {A B} (v1 : option A) (v2 : option B)
    := choose_option
         (option_map (@inr _ _) v2)
         (option_map (@inl _ _) v1).

  Definition empty : t := (W1.empty, W2.empty).
  Definition is_empty : t -> bool := lift_tT andb W1.is_empty W2.is_empty.
  Definition mem : elt -> t -> bool := lift_etT W1.mem W2.mem.
  Definition add : elt -> t -> t := lift_ett W1.add W2.add.
  Definition remove : elt -> t -> t := lift_ett W1.remove W2.remove.
  Definition singleton : elt -> t := lift_et W1.singleton W2.singleton.
  Definition union : t -> t -> t := lift_ttt W1.union W2.union.
  Definition inter : t -> t -> t := lift_ttt W1.inter W2.inter.
  Definition diff : t -> t -> t := lift_ttt W1.diff W2.diff.
  Definition equal : t -> t -> bool := lift_ttT andb W1.equal W2.equal.
  Definition subset : t -> t -> bool := lift_ttT andb W1.subset W2.subset.
  Definition fold B : (elt -> B -> B) -> t -> B -> B
    := fun f v i
       => @W2.fold
            B (snd (drop_eT f)) (snd v)
            (@W1.fold
               B (fst (drop_eT f)) (fst v)
               i).
  Definition for_all : (elt -> bool) -> t -> bool := lift_eT_tT andb W1.for_all W2.for_all.
  Definition exists_ : (elt -> bool) -> t -> bool := lift_eT_tT orb W1.exists_ W2.exists_.
  Definition filter : (elt -> bool) -> t -> t := lift_eT_tt W1.filter W2.filter.
  Definition partition : (elt -> bool) -> t -> t * t := lift_eT_tt2 W1.partition W2.partition.
  Definition cardinal : t -> nat := lift_tT Nat.add W1.cardinal W2.cardinal.
  Definition elements : t -> list elt
    := lift_tT (fun l1 l2 => List.map (@inl _ _) l1 ++ List.map (@inr _ _) l2)
               W1.elements
               W2.elements.
  Definition choose : t -> option elt
    := lift_tT choose_option_sum W1.choose W2.choose.
  Definition In : elt -> t -> Prop := lift_etT W1.In W2.In.

  Local Ltac t_Proper :=
    cbv -[fst snd] in *;
    repeat first [ progress cbn [fst snd] in *
                 | progress intros
                 | progress destruct_head'_sum
                 | progress split_and
                 | progress firstorder
                 | match goal with
                   | [ H : forall x y : _ + _, _ |- _ ]
                     => pose proof (fun x y => H (inl x) (inl y));
                        pose proof (fun x y => H (inl x) (inr y));
                        pose proof (fun x y => H (inr x) (inl y));
                        pose proof (fun x y => H (inr x) (inr y));
                        clear H
                   end ].

  Local Instance Proper_lift_tT {A B C RA RB RC R1 R2}
    : Proper ((RA ==> RB ==> RC) ==> (R1 ==> RA) ==> (R2 ==> RB) ==> RelProd R1 R2 ==> RC) (@lift_tT A B C).
  Proof. t_Proper. Qed.

  Local Instance Proper_lift_ttT {A B C RA RB RC R1 R2}
    : Proper ((RA ==> RB ==> RC) ==> (R1 ==> R1 ==> RA) ==> (R2 ==> R2 ==> RB) ==> RelProd R1 R2 ==> RelProd R1 R2 ==> RC) (@lift_ttT A B C).
  Proof. t_Proper. Qed.

  Local Instance Proper_lift_eT {A RA}
    : Proper ((E1.eq ==> RA) ==> (E2.eq ==> RA) ==> E.eq ==> RA) (@lift_eT A).
  Proof. t_Proper. Qed.

  Local Instance Proper_drop_eT {A RA}
    : Proper ((E.eq ==> RA) ==> RelProd (E1.eq ==> RA) (E2.eq ==> RA)) (@drop_eT A).
  Proof. t_Proper. Qed.

  Local Instance Proper_lift_et {R1 R2}
        {R1_empty : Proper R1 W1.empty}
        {R2_empty : Proper R2 W2.empty}
    : Proper ((E1.eq ==> R1) ==> (E2.eq ==> R2) ==> E.eq ==> RelProd R1 R2) lift_et.
  Proof. t_Proper. Qed.

  Local Instance Proper_lift_etT {A RA R1 R2}
    : Proper ((E1.eq ==> R1 ==> RA) ==> (E2.eq ==> R2 ==> RA) ==> E.eq ==> RelProd R1 R2 ==> RA) (@lift_etT A).
  Proof. t_Proper. Qed.

  Local Instance Proper_lift_ett {R1 R2}
    : Proper ((E1.eq ==> R1 ==> R1) ==> (E2.eq ==> R2 ==> R2) ==> E.eq ==> RelProd R1 R2 ==> RelProd R1 R2)
             lift_ett.
  Proof. t_Proper. Qed.

  Local Instance Proper_lift_ttt {R1 R2}
    : Proper ((R1 ==> R1 ==> R1) ==> (R2 ==> R2 ==> R2) ==> (RelProd R1 R2 ==> RelProd R1 R2 ==> RelProd R1 R2))
             lift_ttt.
  Proof. t_Proper. Qed.

  Local Instance Proper_lift_eT_tT {A B RA RB R1 R2}
    : Proper ((RB ==> RB ==> RB) ==> ((E1.eq ==> RA) ==> R1 ==> RB) ==> ((E2.eq ==> RA) ==> R2 ==> RB) ==> (E.eq ==> RA) ==> RelProd R1 R2 ==> RB)
             (@lift_eT_tT A B).
  Proof. t_Proper. Qed.

  Local Instance Proper_lift_eT_tt {A RA R1 R2}
    : Proper (((E1.eq ==> RA) ==> R1 ==> R1) ==> ((E2.eq ==> RA) ==> R2 ==> R2) ==> (E.eq ==> RA) ==> RelProd R1 R2 ==> RelProd R1 R2)
             (@lift_eT_tt A).
  Proof. t_Proper. Qed.

  Local Instance Proper_lift_eT_tt2 {A RA R1 R2}
    : Proper (((E1.eq ==> RA) ==> R1 ==> R1 * R1) ==> ((E2.eq ==> RA) ==> R2 ==> R2 * R2) ==> (E.eq ==> RA) ==> RelProd R1 R2 ==> (R1 * R2) * (R1 * R2))
             (@lift_eT_tt2 A).
  Proof. t_Proper. Qed.

  Local Existing Instance eq_subrelation.

  Global Instance In_compat : Proper (E.eq ==> eq ==> iff) In | 5.
  Proof.
    cbv [In].
    partial_application_tactic.
    partial_application_tactic.
    class_apply @subrelation_proper.
    exact _.
    exact _.
    repeat match goal with
           | [ |- subrelation (_ ==> _) (_ ==> _) ]
             => class_apply @subrelation_respectful
           end.
    all: try reflexivity.
    all: typeclasses eauto.
  Qed.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Definition Equal_alt : t -> t -> Prop := lift_ttT and W1.Equal W2.Equal.
  Definition Subset_alt : t -> t -> Prop := lift_ttT and W1.Subset W2.Subset.
  Definition Empty_alt : t -> Prop := lift_tT and W1.Empty W2.Empty.
  Definition For_all_alt : (elt -> Prop) -> t -> Prop := lift_eT_tT and W1.For_all W2.For_all.
  Definition Exists_alt : (elt -> Prop) -> t -> Prop := lift_eT_tT or W1.Exists W2.Exists.

  Lemma forall_lift_etT_dep {A f1 f2} (P : elt -> (t -> A) -> Prop)
    : (forall a : elt, P a (@lift_etT A f1 f2 a))
      <-> ((forall a : W1.elt, P (inl a) (fun v => f1 a (fst v)))
           /\ (forall a : W2.elt, P (inr a) (fun v => f2 a (snd v)))).
  Proof.
    cbv [lift_etT].
    split; [ intro H; split; intro x; [ specialize (H (inl x)) | specialize (H (inr x)) ]
           | intros [H1 H2] [x|x]; [ specialize (H1 x) | specialize (H2 x) ] ];
    assumption.
  Qed.

  Lemma exists_lift_etT_dep {A f1 f2} (P : elt -> (t -> A) -> Prop)
    : (exists a : elt, P a (@lift_etT A f1 f2 a))
      <-> ((exists a : W1.elt, P (inl a) (fun v => f1 a (fst v)))
           \/ (exists a : W2.elt, P (inr a) (fun v => f2 a (snd v)))).
  Proof.
    cbv [lift_etT].
    split; [ intros [[x|x] H]; constructor; exists x; assumption
           | intros [[x H]|[x H]]; (unshelve econstructor; [ constructor; exact x | assumption ]) ].
  Qed.

  Local Ltac t_alt_iff :=
    cbv [In
           Equal_alt Subset_alt Empty_alt For_all_alt Exists_alt
           Equal Subset Empty For_all Exists
           W1.Equal W1.Subset W1.Empty W1.For_all W1.Exists
           W2.Equal W2.Subset W2.Empty W2.For_all W2.Exists];
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
    | [ |- context[lift_etT ?f1 ?f2] ]
      => lazymatch goal with
         | [ |- (forall a : elt, @?P a) <-> _ ]
           => let P' := get_P (lift_etT f1 f2) P in
              setoid_rewrite (@forall_lift_etT_dep _ f1 f2 P')
         | [ |- (exists a : elt, @?P a) <-> _ ]
           => let P' := get_P (lift_etT f1 f2) P in
              setoid_rewrite (@exists_lift_etT_dep _ f1 f2 P')
         end
    end;
    try reflexivity.

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
    destruct (W1.eq_dec (fst x) (fst y)) as [H1|H1], (W2.eq_dec (snd x) (snd y)) as [H2|H2];
      [ left | right.. ];
      cbv [eq]; rewrite Equal_alt_iff; cbv [Equal_alt lift_ttT]; auto;
        intros [? ?]; auto.
  Defined.

  Lemma W1_In_empty_False_iff : forall x, W1.In x W1.empty <-> False.
  Proof. pose proof W1.empty_spec. firstorder. Qed.
  Lemma W2_In_empty_False_iff : forall x, W2.In x W2.empty <-> False.
  Proof. pose proof W2.empty_spec. firstorder. Qed.

  Create HintDb sum_set_alt discriminated.

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
       lift_ttT
       lift_etT
       lift_tT
       lift_ett
       lift_et
       lift_ttt
       lift_eT_tt
       lift_eT_tT
       lift_eT_tt2
       drop_eT
       flip
       choose_option
       choose_option_sum
       choose_option_sum_rev
       Empty_alt Equal_alt
    : sum_set_alt.

  Hint Rewrite Empty_alt_iff Equal_alt_iff Subset_alt_iff For_all_alt_iff Exists_alt_iff
       W1.is_empty_spec
       W1.mem_spec
       W1.add_spec
       W1.remove_spec
       W1.singleton_spec
       W1.union_spec
       W1.inter_spec
       W1.diff_spec
       W1.equal_spec
       W1.subset_spec
       W1.fold_spec
       W1.for_all_spec
       W1.exists_spec
       W1.partition_spec1
       W1.partition_spec2
       W1.filter_spec
       W1.cardinal_spec
       W1_In_empty_False_iff
       W2.is_empty_spec
       W2.mem_spec
       W2.add_spec
       W2.remove_spec
       W2.singleton_spec
       W2.union_spec
       W2.inter_spec
       W2.diff_spec
       W2.equal_spec
       W2.subset_spec
       W2.fold_spec
       W2.for_all_spec
       W2.exists_spec
       W2.partition_spec1
       W2.partition_spec2
       W2.filter_spec
       W2.cardinal_spec
       W2_In_empty_False_iff
       app_length
       map_length
       fold_left_app
       fold_left_map
       (@ForallOrdPairs_map_iff)
       Bool.andb_true_iff
       Bool.orb_true_iff
    : sum_set_alt.

  Local Hint Resolve
        W1.empty_spec
        W1.elements_spec2w
        W1.choose_spec1
        W1.choose_spec2
        W2.empty_spec
        W2.elements_spec2w
        W2.choose_spec1
        W2.choose_spec2
    : core.

  Local Ltac spec_t :=
    repeat first [ reflexivity
                 | progress cbn [fst snd E.eq sumwise] in *
                 | progress intros
                 | progress repeat autorewrite with sum_set_alt
                 | progress repeat autounfold with sum_set_alt in *
                 | progress auto
                 | break_innermost_match_step
                 | clear; tauto
                 | exact _
                 | apply conj; reflexivity ].

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
      cbv [In lift_tT lift_etT elements];
        rewrite InA_app_iff;
        break_innermost_match;
        progress rewrite <- ?W1.elements_spec1, <- ?W2.elements_spec1.
      all: split; [ intros [H|H]; revert H | ];
        try (apply InA_map_iff; reflexivity);
        try (intro H; constructor; revert H; apply InA_map_iff; reflexivity).
      all: intro H; exfalso; revert H.
      all: rewrite InA_alt; setoid_rewrite in_map_iff;
        intros [[?|?] [H1 [? [? ?]]]]; cbn [E.eq sumwise] in *;
          inversion_sum;
          try assumption.
    Qed.

    Lemma elements_spec2w : NoDupA E.eq (elements s).
    Proof using Type.
      clear.
      pose proof (W1.elements_spec2w (fst s)).
      pose proof (W2.elements_spec2w (snd s)).
      spec_t.
      apply NoDupA_app; try exact _.
      1,2: rewrite NoDupA_altdef, ForallOrdPairs_map_iff in *; assumption.
      { setoid_rewrite InA_alt; setoid_rewrite in_map_iff;
          firstorder; subst; cbv [E.eq sumwise] in *; break_innermost_match_hyps;
            try assumption. }
    Qed.
    Lemma choose_spec1 : choose s = Some x -> In x s.
    Proof using Type.
      pose proof (@W1.choose_spec1 (fst s)).
      pose proof (@W2.choose_spec1 (snd s)).
      cbv [In choose option_map choose_option choose_option_sum lift_etT lift_tT].
      break_innermost_match; intros; inversion_option; inversion_sum; subst; eauto.
    Qed.
    Lemma choose_spec2 : choose s = None -> Empty s.
    Proof using Type. spec_t; break_innermost_match_hyps; inversion_option; auto. Qed.
  End Spec.
End WSumSetsOn.

Module SumSetsOn (E1 : Orders.OrderedType) (E2 : Orders.OrderedType)
       (W1 : SetsOn E1) (W2 : SetsOn E2) (* <: SetsOn (SumOrderedType E1 E2) *).
  Include WSumSetsOn E1 E2 W1 W2.
  Module Import SumSetsOn_E.
    Module E := SumOrderedType E1 E2.
  End SumSetsOn_E.
  Local Existing Instances E.lt_strorder E.lt_compat.
  Local Existing Instances E.eq_equiv W1.In_compat W2.In_compat.

  Definition choose_comparison (x y : comparison) : comparison
    := match x with
       | Eq => y
       | _ => x
       end.

  Definition prod_lt {A B} (A_eq A_lt : relation A) (B_lt : relation B) : relation (A * B)
    := fun x y => A_lt (fst x) (fst y) \/ (A_eq (fst x) (fst y) /\ B_lt (snd x) (snd y)).

  Definition compare : t -> t -> comparison := lift_ttT choose_comparison W1.compare W2.compare.
  Definition min_elt : t -> option elt := lift_tT choose_option_sum W1.min_elt W2.min_elt.
  Definition max_elt : t -> option elt := lift_tT choose_option_sum_rev W1.max_elt W2.max_elt.
  Definition lt : t -> t -> Prop := prod_lt W1.eq W1.lt W2.lt.
  Hint Unfold compare min_elt max_elt lt W1.eq prod_lt : sum_set_alt.

  Instance lt_strorder : StrictOrder lt | 1.
  Proof.
    destruct W1.eq_equiv, W1.lt_strorder, W2.lt_strorder.
    cbv [W1.eq lt prod_lt] in *.
    split.
    { intros [x1 x2] H.
      pose proof (@irreflexivity _ W1.lt _ x1).
      pose proof (@irreflexivity _ W2.lt _ x2).
      pose proof (@reflexivity _ W1.Equal _ x1).
      cbv [complement] in *.
      destruct_head'_or; destruct_head'_and; eauto. }
    { intros [x1 x2] [y1 y2] [z1 z2]; cbn [fst snd] in *; intros.
      pose proof (@transitivity _ W1.lt _ x1 y1 z1).
      pose proof (@transitivity _ W2.lt _ x2 y2 z2).
      pose proof (@W1.lt_compat); cbv [Proper respectful] in *.
      split_iff.
      destruct_head'_or; destruct_head'_and; eauto 5. }
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt | 1.
  Proof.
    pose proof W1.lt_compat as H1; pose proof W2.lt_compat as H2.
    pose proof (@reflexivity _ W1.Equal _).
    pose proof (@reflexivity _ W2.Equal _).
    all: repeat first [ progress cbv [eq lt prod_lt W1.eq W2.eq Proper respectful fst snd Equal_alt lift_ttT] in *
                      | progress rewrite Equal_alt_iff in *
                      | progress destruct_head'_and
                      | progress intros
                      | progress split_iff
                      | progress break_innermost_match_hyps
                      | progress setoid_subst_rel W1.Equal
                      | progress setoid_subst_rel W2.Equal
                      | progress destruct_head'_or
                      | apply conj
                      | solve [ auto ] ].
  Qed.

  Local Ltac spec_t' :=
    repeat first [ reflexivity
                 | progress cbn [fst snd E.eq sumwise] in *
                 | progress intros
                 | progress repeat autorewrite with sum_set_alt
                 | progress repeat autounfold with sum_set_alt in *
                 | progress auto
                 | break_innermost_match_step
                 | clear; tauto
                 | exact _
                 | assumption
                 | symmetry; assumption
                 | apply conj; reflexivity
                 | progress break_innermost_match_hyps
                 | progress subst
                 | progress inversion_option
                 | progress inversion_sum
                 | progress destruct_head'_and
                 | exfalso; now eauto ].

  Section Spec.
    Variable s s': t.
    Variable x y : elt.

    Lemma compare_spec : CompSpec eq lt s s' (compare s s').
    Proof using Type.
      pose proof (@symmetry _ W1.Equal _).
      cbv [compare eq lt prod_lt lift_ttT choose_comparison W1.eq].
      destruct (W1.compare_spec (fst s) (fst s')), (W2.compare_spec (snd s) (snd s'));
        cbv [W1.eq W2.eq] in *;
        constructor; now spec_t'.
    Qed.

    Lemma elements_spec2 : sort E.lt (elements s).
    Proof using Type.
      cbv [elements lift_tT].
      eapply SortA_app; rewrite ?Sorted_map_iff;
        try (apply W1.elements_spec2 + apply W2.elements_spec2 + apply E.eq_equiv).
      cbv [sumwise].
      intros ??; setoid_rewrite InA_alt; setoid_rewrite in_map_iff; intros.
      repeat first [ progress destruct_head'_ex
                   | progress destruct_head'_and
                   | progress subst
                   | break_innermost_match_hyps_step
                   | exfalso; assumption
                   | exact I ].
    Qed.

    Ltac elt_spec lem1 lem2 lem3 :=
      spec_t';
      repeat match goal with
             | [ H : _ = _ :> option _ |- _ ]
               => (eapply lem1 in H + eapply lem2 in H + eapply lem3 in H); [ | (idtac + symmetry); eassumption.. ]
             end;
      try match goal with H : ~ ?R _ _ |- ~ _ => intro; apply H; clear H end;
      cbv [not W1.Empty W2.Empty] in *;
      spec_t'.

    Lemma min_elt_spec1 : min_elt s = Some x -> In x s.
    Proof using Type. elt_spec W1.min_elt_spec1 W2.min_elt_spec1 (). Qed.
    Lemma min_elt_spec2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
    Proof using Type. elt_spec W1.min_elt_spec2 W2.min_elt_spec2 W1.min_elt_spec3. Qed.
    Lemma min_elt_spec3 : min_elt s = None -> Empty s.
    Proof using Type. elt_spec W1.min_elt_spec3 W2.min_elt_spec3 (). Qed.

    Lemma max_elt_spec1 : max_elt s = Some x -> In x s.
    Proof using Type. elt_spec W1.max_elt_spec1 W2.max_elt_spec1 (). Qed.
    Lemma max_elt_spec2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
    Proof using Type. elt_spec W1.max_elt_spec2 W2.max_elt_spec2 W2.max_elt_spec3. Qed.
    Lemma max_elt_spec3 : max_elt s = None -> Empty s.
    Proof using Type. elt_spec W1.max_elt_spec3 W2.max_elt_spec3 (). Qed.

    Lemma choose_spec3 : choose s = Some x -> choose s' = Some y ->
                         Equal s s' -> E.eq x y.
    Proof using Type.
      rewrite Equal_alt_iff; cbv [Equal_alt lift_ttT].
      elt_spec W1.choose_spec3 W2.choose_spec3 ().
      all: cbv [W1.Equal W2.Equal] in *; split_iff.
      all: elt_spec W1.choose_spec2 W2.choose_spec2 ().
      all: elt_spec W1.choose_spec1 W2.choose_spec1 ().
    Qed.
  End Spec.
End SumSetsOn.

Module WSumSets (W1 : WSets) (W2 : WSets) <: WSets.
  Module E := SumDecidableType W1.E W2.E.
  Include WSumSetsOn W1.E W2.E W1 W2.
End WSumSets.

Module SumSets (W1 : Sets) (W2 : Sets) <: Sets.
  Module E := SumOrderedType W1.E W2.E.
  Include SumSetsOn W1.E W2.E W1 W2.
End SumSets.
